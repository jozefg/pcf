{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Pcf where
import           Bound
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Gen
import           Control.Monad.Trans
import           Data.Foldable
import           Data.List           (elemIndex)
import qualified Data.Map            as M
import           Data.Maybe          (fromJust)
import qualified Data.Set            as S
import           Data.Traversable    hiding (mapM)
import           Data.Void
import           Prelude.Extras

data Ty = Arr Ty Ty
        | Nat
        deriving Eq

data Exp a = V a
           | App (Exp a) (Exp a)
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
  Suc e >>= f = Suc (e >>= f)
  Zero >>= _ = Zero

--------------------------------------------------------
--------------- Type Checking --------------------------
--------------------------------------------------------

type TyM a = GenT a Maybe

assertTy :: (Enum a, Ord a) => M.Map a Ty -> Exp a -> Ty -> TyM a ()
assertTy env e t = (== t) <$> typeCheck env e >>= guard

typeCheck :: (Enum a, Ord a) => M.Map a Ty -> Exp a -> TyM a Ty
typeCheck env Zero = return Nat
typeCheck env (Suc e) = assertTy env e Nat >> return Nat
typeCheck env (V a) = lift (M.lookup a env)
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

typeOf :: Exp Void -> Maybe Ty
typeOf = runGenT . typeCheck M.empty . fmap (absurd :: Void -> Integer)

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
  SucC e >>= f = SucC (e >>= f)
  ZeroC >>= _ = ZeroC

closConv :: (Eq a, Ord a, Enum a) => Exp a -> Gen a (ExpC a)
closConv (V a) = return (VC a)
closConv Zero = return ZeroC
closConv (Suc e) = SucC <$> closConv e
closConv (App f a) = AppC <$> closConv f <*> closConv a
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

data BindL a = RecL Ty [ExpL a] (Scope Int ExpL a)
             | NRecL Ty [ExpL a] (Scope Int ExpL a)
             deriving (Eq, Functor, Foldable, Traversable)
data ExpL a = VL a
            | AppL (ExpL a) (ExpL a)
            | LetL [BindL a] (Scope Int ExpL a)
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
