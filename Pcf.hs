{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module Pcf (Ty(..), Exp(..), compile, output) where
import           Bound
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Gen
import           Control.Monad.Trans
import           Control.Monad.Trans.Maybe
import           Control.Monad.Writer
import           Data.Foldable
import           Data.List           (elemIndex)
import qualified Data.Map            as M
import           Data.Maybe          (fromJust)
import qualified Data.Set            as S
import           Data.String
import           Data.Traversable    hiding (mapM)
import           Language.C.DSL
import           Data.Void
import           Prelude.Extras

data Ty = Arr Ty Ty
        | Nat
        deriving Eq

data Exp a = V a
           | App (Exp a) (Exp a)
           | Ifz (Exp a) (Exp a) (Scope () Exp a)
           | Lam Ty (Scope () Exp a)
           | Fix Ty (Scope () Exp a)
           | Suc (Exp a)
           | Zero
           deriving (Eq, Functor, Foldable, Traversable)

instance Eq1 Exp where
instance Applicative Exp where
  pure = return
  (<*>) = ap
instance Monad Exp where
  return = V
  V a >>= f = f a
  App l r >>= f = App (l >>= f) (r >>= f)
  Lam t body >>= f = Lam t (body >>>= f)
  Fix t body >>= f = Fix t (body >>>= f)
  Ifz i t e >>= f = Ifz (i >>= f) (t >>= f) (e >>>= f)
  Suc e >>= f = Suc (e >>= f)
  Zero >>= _ = Zero

--------------------------------------------------------
--------------- Type Checking --------------------------
--------------------------------------------------------

type TyM a = MaybeT (Gen a)

assertTy :: (Enum a, Ord a) => M.Map a Ty -> Exp a -> Ty -> TyM a ()
assertTy env e t = (== t) <$> typeCheck env e >>= guard

typeCheck :: (Enum a, Ord a) => M.Map a Ty -> Exp a -> TyM a Ty
typeCheck _   Zero = return Nat
typeCheck env (Suc e) = assertTy env e Nat >> return Nat
typeCheck env (V a) = MaybeT . return $ M.lookup a env
typeCheck env (App f a) = typeCheck env f >>= \case
  Arr fTy tTy -> assertTy env a fTy >> return tTy
  _ -> mzero
typeCheck env (Lam t bind) = do
  v <- gen
  Arr t <$> typeCheck (M.insert v t env) (instantiate1 (V v) bind)
typeCheck env (Fix t bind) = do
  v <- gen
  assertTy (M.insert v t env) (instantiate1 (V v) bind) t
  return t
typeCheck env (Ifz i t e) = do
  assertTy env i Nat
  ty <- typeCheck env t
  v <- gen
  assertTy (M.insert v Nat env) (instantiate1 (V v) e) ty
  return ty

--------------------------------------------------------
--------------- Closure Conversion ---------------------
--------------------------------------------------------

-- Invariant, Clos only contains VCs, can't be enforced statically due
-- to annoying monad instance
type Clos a = [ExpC a]

data ExpC a = VC a
            | AppC (ExpC a) (ExpC a)
            | LamC Ty (Clos a) (Scope Int ExpC a)
            | FixC Ty (Clos a) (Scope Int ExpC a)
            | IfzC (ExpC a) (ExpC a) (Scope () ExpC a)
            | SucC (ExpC a)
            | ZeroC
            deriving (Eq, Functor, Foldable, Traversable)

instance Eq1 ExpC where
instance Applicative ExpC where
  pure = return
  (<*>) = ap
instance Monad ExpC where
  return = VC
  VC a >>= f = f a
  AppC l r >>= f = AppC (l >>= f) (r >>= f)
  LamC t clos body >>= f = LamC t (map (>>= f) clos) (body >>>= f)
  FixC t clos body >>= f = FixC t (map (>>= f) clos) (body >>>= f)
  IfzC i t e >>= f = IfzC (i >>= f) (t >>= f) (e >>>= f)
  SucC e >>= f = SucC (e >>= f)
  ZeroC >>= _ = ZeroC

closConv :: (Eq a, Ord a, Enum a) => Exp a -> Gen a (ExpC a)
closConv (V a) = return (VC a)
closConv Zero = return ZeroC
closConv (Suc e) = SucC <$> closConv e
closConv (App f a) = AppC <$> closConv f <*> closConv a
closConv (Ifz i t e) = do
  v <- gen
  e' <- abstract1 v <$> closConv (instantiate1 (V v) e)
  IfzC <$> closConv i <*> closConv t <*> return e'
closConv (Fix t bind) = do
  v <- gen
  body <- closConv (instantiate1 (V v) bind)
  let freeVars = S.toList . S.delete v $ foldMap S.singleton body
      rebind v' = elemIndex v' freeVars <|>
                  guard (v' == v) *> (Just $ length freeVars)
  return $ FixC t (map VC freeVars) (abstract rebind body)
closConv (Lam t bind) = do
  v <- gen
  body <- closConv (instantiate1 (V v) bind)
  let freeVars = S.toList . S.delete v $ foldMap S.singleton body
      rebind v' = elemIndex v' freeVars <|>
                  guard (v' == v) *> (Just $ length freeVars)
  return $ LamC t (map VC freeVars) (abstract rebind body)

--------------------------------------------------------
--------------- Lambda + Fixpoint lifting --------------
--------------------------------------------------------
data BindSort = Fn | Y
data BindL a = RecL Ty [ExpL a] (Scope Int ExpL a)
             | NRecL Ty [ExpL a] (Scope Int ExpL a)
             deriving (Eq, Functor, Foldable, Traversable)
data ExpL a = VL a
            | AppL (ExpL a) (ExpL a)
            | LetL [BindL a] (Scope Int ExpL a)
            | IfzL (ExpL a) (ExpL a) (Scope () ExpL a)
            | SucL (ExpL a)
            | ZeroL
            deriving (Eq, Functor, Foldable, Traversable)

instance Eq1 ExpL where
instance Applicative ExpL where
  pure = return
  (<*>) = ap
instance Monad ExpL where
  return = VL
  VL a >>= f = f a
  AppL l r >>= f = AppL (l >>= f) (r >>= f)
  SucL e >>= f = SucL (e >>= f)
  ZeroL >>= _ = ZeroL
  IfzL i t e >>= f = IfzL (i >>= f) (t >>= f) (e >>>= f)
  LetL binds body >>= f = LetL (map go binds) (body >>>= f)
    where go (RecL t es scope) = RecL t (map (>>= f) es) (scope >>>= f)
          go (NRecL t es scope) = NRecL t (map (>>= f) es) (scope >>>= f)

trivLetBody :: Scope Int ExpL a
trivLetBody = fromJust . closed . abstract (const $ Just 0) $ VL ()

llift :: (Eq a, Ord a, Enum a) => ExpC a -> Gen a (ExpL a)
llift (VC a) = return (VL a)
llift ZeroC = return ZeroL
llift (SucC e) = SucL <$> llift e
llift (AppC f a) = AppL <$> llift f <*> llift a
llift (IfzC i t e) = do
  v <- gen
  e' <- abstract1 v <$> llift (instantiate1 (VC v) e)
  IfzL <$> llift i <*> llift t <*> return e'
llift (LamC t clos bind) = do
  vs <- replicateM (length clos + 1) gen
  body <- llift $ instantiate (VC . (!!) vs) bind
  clos' <- mapM llift clos
  let bind' = abstract (flip elemIndex vs) body
  return (LetL [NRecL t clos' bind'] trivLetBody)
llift (FixC t clos bind) = do
  vs <- replicateM (length clos + 1) gen
  body <- llift $ instantiate (VC . (!!) vs) bind
  clos' <- mapM llift clos
  let bind' = abstract (flip elemIndex vs) body
  return (LetL [RecL t clos' bind'] trivLetBody)

--------------------------------------------------------
--------------- Conversion to Faux-C -------------------
--------------------------------------------------------

-- Invariant: the Integer part of a FauxCTop is a globally unique
-- identifier that will be used as a name for that binding.
data IsRec = IsRec | NotRec deriving Eq
type NumArgs = Int
data FauxCTop a = FauxCTop IsRec Integer NumArgs (Scope Int FauxC a)
                deriving (Eq, Functor, Foldable, Traversable)
data BindFC a = NRecFC Integer [FauxC a]
              | RecFC Integer [FauxC a]
              deriving (Eq, Functor, Foldable, Traversable)
data FauxC a = VFC a
             | AppFC (FauxC a) (FauxC a)
             | IfzFC (FauxC a) (FauxC a) (Scope () FauxC a)
             | LetFC [BindFC a] (Scope Int FauxC a)
             | SucFC (FauxC a)
             | ZeroFC
             deriving (Eq, Functor, Foldable, Traversable)

instance Eq1 FauxC where
instance Applicative FauxC where
  pure = return
  (<*>) = ap
instance Monad FauxC where
  return = VFC
  VFC a >>= f = f a
  AppFC l r >>= f = AppFC (l >>= f) (r >>= f)
  SucFC e >>= f = SucFC (e >>= f)
  ZeroFC >>= _ = ZeroFC
  IfzFC i t e >>= f = IfzFC (i >>= f) (t >>= f) (e >>>= f)
  LetFC binds body >>= f = LetFC (map go binds) (body >>>= f)
    where go (NRecFC i es) = RecFC i (map (>>= f) es)
          go (RecFC i es) = NRecFC i (map (>>= f) es)

type FauxCM a = WriterT [FauxCTop a] (Gen a)

fauxc :: ExpL Integer -> FauxCM Integer (FauxC Integer)
fauxc (VL a) = return (VFC a)
fauxc (AppL f a) = AppFC <$> fauxc f <*> fauxc a
fauxc ZeroL = return ZeroFC
fauxc (SucL e) = SucFC <$> fauxc e
fauxc (IfzL i t e) = do
  v <- gen
  e' <- abstract1 v <$> fauxc (instantiate1 (VL v) e)
  IfzFC <$> fauxc i <*> fauxc t <*> return e'
fauxc (LetL binds e) = do
  binds' <- mapM liftBinds binds
  vs <- replicateM (length binds) gen
  body <- fauxc $ instantiate (VL . (!!) vs) e
  let e' = abstract (flip elemIndex vs) body
  return (LetFC binds' e')
  where lifter bindingConstr isRec numArgs clos bind = do
          guid <- gen
          vs <- replicateM (length binds + 1) gen
          body <- fauxc $ instantiate (VL . (!!) vs) bind
          let bind' = abstract (flip elemIndex vs) body
          tell [FauxCTop isRec guid (length clos + 1) bind']
          bindingConstr guid <$> mapM fauxc clos
        liftBinds (NRecL _ clos bind) =
          lifter NRecFC NotRec (length clos + 1) clos bind
        liftBinds (RecL _ clos bind) =
          lifter RecFC IsRec (length clos) clos bind

--------------------------------------------------------
--------------- Conversion to Real C -------------------
--------------------------------------------------------

type RealCM = WriterT [CBlockItem] (Gen Integer)

i2d :: Integer -> CDeclr
i2d = fromString . ('_':) . show

i2e :: Integer -> CExpr
i2e = var . fromString . ('_':) . show

tellDecl :: CExpr -> RealCM CExpr
tellDecl e = do
  i <- gen
  tell [CBlockDecl $ decl voidTy (ptr $ i2d i) $ Just e]
  return (i2e i)

realc :: FauxC CExpr -> RealCM CExpr
realc (VFC e) = return e
realc (AppFC f a) = ("apply" #) <$> mapM realc [f, a] >>= tellDecl
realc ZeroFC = tellDecl $ "mkZero" # []
realc (SucFC e) = realc e >>= tellDecl . ("inc"#) . (:[])
realc (IfzFC i t e) = do
  outi <- realc i
  deci <- tellDecl ("dec" # [outi])
  let e' = instantiate1 (VFC deci) e
  (outt, blockt) <- lift . runWriterT $ (realc t)
  (oute, blocke) <- lift . runWriterT $ (realc e')
  out <- tellDecl 0
  let branch block output =
        CCompound [] (block ++ [CBlockStmt . liftE $ out <-- output]) undefNode
      ifStat =
        cifElse ("isZ"#[outi]) (branch blockt outt) (branch blocke oute)
  tell [CBlockStmt ifStat]
  return out
realc (LetFC binds bind) = do
  bindings <- mapM goBind binds
  realc $ instantiate (VFC . (bindings !!)) bind
  where goBind (NRecFC i cs) =
          ("mkClos" #) <$> (i2e i:) <$> mapM realc cs >>= tellDecl
        goBind (RecFC i cs) = (i2e i #) <$> mapM realc cs >>= tellDecl

mkPtrFun :: CFunDef -> CFunDef
mkPtrFun (CFunDef ss dec as by a) = CFunDef ss (addPtr dec) as by a
  where addPtr (CDeclr i ds strs attrs a) =
          CDeclr i (ds ++ [CPtrDeclr [] a]) strs attrs a

topc :: FauxCTop CExpr -> Gen Integer CFunDef
topc (FauxCTop isRec i numArgs body) = do
  binds <- gen
  let getArg = (!!) (args (i2e binds) numArgs isRec)
  (out, block) <- runWriterT . realc $ instantiate getArg body
  return . mkPtrFun $
    fun [voidTy] ('_' : show i) [decl voidTy $ ptr (i2d binds)] $
      CCompound [] (block ++ [CBlockStmt . creturn $ out]) undefNode
  where indexArg binds i = binds ! i2e (toInteger i)
        args binds na NotRec = map (VFC . indexArg binds) [0..na - 1]
        args binds na IsRec =
          let exps = map (indexArg binds) [0..na - 2] in
           map VFC $ exps ++ [i2e i # [binds]]

compile :: Exp Integer -> Maybe CTranslUnit
compile e = runGen . runMaybeT $ do
  ty <- typeCheck M.empty e
  when (ty /= Nat) mzero
  funs <- lift $ pipe e
  return . transUnit . map export $ funs
  where pipe e = do
          simplified <- closConv e >>= llift
          (main, funs) <- runWriterT $ fauxc simplified
          i <- gen
          let topMain = FauxCTop NotRec i 1 (abstract (const Nothing) main)
              funs' = map (i2e <$>) (funs ++ [topMain])
          (++ [makeCMain i]) <$> mapM topc funs'
        makeCMain entry =
          fun [intTy] "main"[] $ block [
            intoB $ "call"#[i2e entry]
          ]

output :: Exp Integer -> IO ()
output e = case compile e of
  Nothing -> putStrLn "It didn't compile"
  Just p  -> print . pretty $ p
