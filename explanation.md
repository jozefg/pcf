---
title: A Tiny Compiler For A Typed Higher Order Language
---

In this note I'll explain attempt to explain the whole thing, from
front to back.

## What's PCF

First things first, it's important to define the language we're
compiling. The language, PCF short for "partial computable functions",
is an extremely small language you generally find in a book on
programming languages, it originates with Plotkin if I'm not mistaken.

PCF is based around 3 core elements: natural numbers, functions
(closures), and general recursion. There are two constants for
creating numbers, `Zero` and `Suc`. `Zero` is self explanatory and
`Suc e` is the successor of the natural number `e` evaluates to. In
most programming languages this just means `Suc e = 1 + e` but `+`
isn't a primitive in PCF (we can define it as a normal
function).

For functions, we have lambdas like you'd find in any functional
language. Since PCF includes no polymorphism it's necessary to
annotate the function's argument with it's type.

Finally, the weird bit: recursion. In PCF we write recursive things
with `fix x : τ in e`. Here we get to use `x` in `e` and we should
understand that `x` "stands for" the whole expression, `fix ...`. As
an example, here's how we define `+`.

``` haskell
    plus =
          fix rec : nat -> nat -> nat in
            λ m : nat.
            λ n : nat.
              ifz m {
                  Zero  => n
                | Suc x => Suc (rec x n)
              }
```

## Now Let's Compile It

Now compilation is broken up into a bunch of phases and intermediate
languages. Even in this small of a compiler there are 3
languages so along with the source and target language there are 5
different languages running around inside of this compiler. Each phase
with the exception of typechecking is just translating one
intermediate language (IL) into another and in the process making one
small modification to the program as a whole.

### The AST

This compiler starts with an AST, I have no desire to write a parser
for this because parsers make me itchy. Here's the AST

``` haskell
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
```

What's interesting here is that our AST uses `bound` to manage
variables. Unfortunately there really isn't time to write both a bound
tutorial *and* a PCF compiler one. I've written about using bound
before [here][lambdapi] otherwise you can just check out the official
[docs][bound-docs]. The important bits here are that `Scope () ...`
binds one variable and that `a` stands for the free variables in an
expression. 3 constructs bind variables here, `Ifz` for pattern
matching, `Fix` for recursive bindings, and `Lam` for the
argument. Note also that `Fix` and `Lam` both must be annotated with a
type otherwise stuff like `fix x in x` and `fn x => x` are ambiguous.

### Type Checking

First up is type checking. This should be familiar to most people
we've written a type checker before since PCF is simply typed. We
simply have a `Map` of variables to types. Since we want to go under
binders defined using `Scope` we'll have to use `instantiate`. However
this demands we be able to create fresh free variables so we don't
accidentally cause clashes. To prevent this we use [monad-gen][mg] to
generate fresh free variables.

To warm up, here's a helper function to check that an expression has a
particular type. This uses the more general `typeCheck` function which
actually produces the type of an expression.

``` haskell
    type TyM a = MaybeT (Gen a)

    assertTy :: (Enum a, Ord a) => M.Map a Ty -> Exp a -> Ty -> TyM a ()
    assertTy env e t = (== t) <$> typeCheck env e >>= guard
```

This type checks the variable in an environment (something that stores
the types of all of the free variables). Once it receives that it
compares it to the type we expected and chucks the resulting boolean
into guard. This code is used in places like `Ifz` where we happen to
know that the first expression has the type `Nat`.

Now on to the main code, `typeCheck`

``` haskell
    typeCheck :: (Enum a, Ord a) => M.Map a Ty -> Exp a -> TyM a Ty
    typeCheck _   Zero = return Nat
    typeCheck env (Suc e) = assertTy env e Nat >> return Nat
```

The first two cases for `typeCheck` are nice and straightforward. All
we if we get a `Zero` then it has type `Nat`. If we get a `Suc e` we
assert that `e` is an integer and then the whole thing has the type
`Nat`.

``` haskell
    typeCheck env (V a) = MaybeT . return $ M.lookup a env
```

For variables we just look things up in the environment. Since this
returns a `Maybe` it's nice and easy to just jam it into our `MaybeT`.

``` haskell
    typeCheck env (App f a) = typeCheck env f >>= \case
      Arr fTy tTy -> assertTy env a fTy >> return tTy
      _ -> mzero
```

Application is a little more interesting. We recurse over the function
and make sure it has an actual function type. If it does, we assert
the argument has the argument type and return the domain. If it
doesn't have a function type, we just fail.

```
    typeCheck env (Lam t bind) = do
      v <- gen
      Arr t <$> typeCheck (M.insert v t env) (instantiate1 (V v) bind)
    typeCheck env (Fix t bind) = do
      v <- gen
      assertTy (M.insert v t env) (instantiate1 (V v) bind) t
      return t
```

Type checking lambdas and fixpoints is quite similar. In both cases we
generate a fresh variable to unravel the binder with. We know what
type this variable is supposed to have because we required explicit
annotations so we add that to the map constituting our
environment. Here's where they diverge.

For a fixpoint we want to make sure that the body has the type as we
said it would so we use `assertTy`. For a lambda we infer the body
type and return a function from the given argument type to the body
type.

```
    typeCheck env (Ifz i t e) = do
      assertTy env i Nat
      ty <- typeCheck env t
      v <- gen
      assertTy (M.insert v Nat env) (instantiate1 (V v) e) ty
      return ty
```

For `Ifz` we want to ensure that we actually are casing on a `Nat` so
we use `assertTy`. Next we figure out what type the zero branch
returns and make sure that the else branch has the same type.

All in all this type checker is not particularly fascinating since all
we have are simple types. Things get a bit more interesting with
[polymorphism][hm]. I'd suggest looking at that if you want to see a
more interesting type checker.

### Closure Conversion

Now for our first interesting compilation phase, closure
conversion. In this phase we make closures explicit by annotating
lambdas and fixpoints with the variables that they close over. Those
variables are then explicitly bound in the scope of the lambda. With
these changes, our new syntax tree looks like this

``` haskell
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
```

The interesting parts are the additions of `Clos` and the fact that
the `Scope` for a lambda and a fixpoint now binds an arbitrary number
of variables instead of just one. Here if a lambda or fixpoint binds
`n` variables, the first `n - 1` are stored in the `Clos` and the last
one is the "argument". Closure conversion is thus just the process of
converting an `Exp` to an `ExpC`.

``` haskell
    closConv :: Ord a => Exp a -> Gen a (ExpC a)
    closConv (V a) = return (VC a)
    closConv Zero = return ZeroC
    closConv (Suc e) = SucC <$> closConv e
    closConv (App f a) = AppC <$> closConv f <*> closConv a
    closConv (Ifz i t e) = do
      v <- gen
      e' <- abstract1 v <$> closConv (instantiate1 (V v) e)
      IfzC <$> closConv i <*> closConv t <*> return e'
```

Most of the cases here are just recursing and building things back up
applicatively. There's the moderately interesting case where we
instantiate the else branch of an `Ifz` with a fresh variable and
*then* recurse, but the interesting cases are for fixpoints and
lambdas. Since they're completely identical we only present the case
for `Fix`.

``` haskell
    closConv (Fix t bind) = do
      v <- gen
      body <- closConv (instantiate1 (V v) bind)
      let freeVars = S.toList . S.delete v $ foldMap S.singleton body
          rebind v' = elemIndex v' freeVars <|>
                      (guard (v' == v) *> (Just $ length freeVars))
      return $ FixC t (map VC freeVars) (abstract rebind body)
```

There's a lot going on here but it boils down into three parts.

 0. Recurse under the binder
 1. Gather all the free variables in the body
 2. Rebind the body together so that all the free variables map to
    their position in the closure and the argument is `n` where `n` is
    the number of free variables.

The first is accomplished in much the same way as in the above
cases. To gather the number of free variables all we need to is use
the readily available notion of a monoid on sets. The whole process is
just `foldMap S.singleton`! There's one small catch: we don't want to
put the argument into the list of variables we close over so we
carefully delete it from the closure. We then convert it to a list
which gives us an actual `Clos a`. Now for the third step we have
`rebind`.

`rebind` maps a free variable to `Maybe Int`. It maps a free variable
to it's binding occurrence it has one here.  This boils down to using
`elemIndex` to look up somethings position in the `Clos` we just built
up. We also have a special case for when the variable we're looking at
is the "argument" of the function we're fixing. In this case we want
to map it to the last thing we're binding, which is just
`length n`. To capture the "try this and then that" semantics we use
the alternative instance for `Maybe` which works wonderfully.

With this, we've removed implicit closures from our language: one
of the passes on our way to C.

### Lambda Lifting

Next up we remove both fixpoints and lambdas from being
expressions. We want them to have an explicit binding occurrence
because we plan to completely remove them from expressions soon. In
order to do this, we define a language with lambdas and fixpoints
explicitly declared in let expressions. The process of converting from
`ExpC` to this new language is called "lambda lifting" because we're
lifting things into let bindings.

Here's our new language.

``` haskell
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
```

Much here is the same except we've romved both lambdas and fixpoints
and replaced them with `LetL`. `LetL` works over bindings which are
either recursive (`Fix`) or nonrecursive (`Lam`). Lambda lifting in
this compiler is rather simplistic in how it lifts lambdas: we just
boost everything one level up and turn

``` haskell
    λ (x : τ). ...
```

into

``` haskell
    let foo = λ (x : τ). ...
    in foo
```

Just like before, this procedure is captured by transforming an `ExpC`
into an `ExpL`.

``` haskell
    llift :: Eq a => ExpC a -> Gen a (ExpL a)
    llift (VC a) = return (VL a)
    llift ZeroC = return ZeroL
    llift (SucC e) = SucL <$> llift e
    llift (AppC f a) = AppL <$> llift f <*> llift a
    llift (IfzC i t e) = do
      v <- gen
      e' <- abstract1 v <$> llift (instantiate1 (VC v) e)
      IfzL <$> llift i <*> llift t <*> return e'
```

Just like in `closConv` we start with a lot of very boring and trivial
"recurse and build back up" cases. These handle everything but the
cases where we actually convert constructs into a `LetL`.

Once again, the interesting cases are pretty much identical. Let's
look at the case for `LamC` for variety.

``` haskell
    llift (LamC t clos bind) = do
      vs <- replicateM (length clos + 1) gen
      body <- llift $ instantiate (VC . (!!) vs) bind
      clos' <- mapM llift clos
      let bind' = abstract (flip elemIndex vs) body
      return (LetL [NRecL t clos' bind'] trivLetBody)
```

Here we first generate a bunch of fresh variables and unbind the body
of our lambda. We then recurse on it. We also have to recurse across
all of our closed over arguments but since those are variables we know
that should be pretty trivial (why do we know this?). Once we've
straightened out the body and the closure all we do is transform the
lambda into a trivial let expression as shown above. Here
`trivLetBody` is.

``` haskell
    trivLetBody :: Scope Int ExpL a
    trivLetBody = fromJust . closed . abstract (const $ Just 0) $ VL ()
```

Which is just a body that returns the first thing bound in the
let. With this done, we've pretty much transformed our expression
language to C. In order to get rid of the nesting, we want to make one
more simplification before we actually generate C.

### C-With-Expression

C-With-Expressions is our next intermediate language. It has no notion
of nested functions or of fixpoints. I suppose now I should finally
fess up to why I keep talking about fixpoints and functions as if
they're the same and why this compiler is handling them
identically. The long and short of it is that fixpoints are really a
combination of a "fixed point combinator" and a function. Really when
we say

``` haskell
    fix x : τ in ...
```

It's as if we had sayed

``` haskell
    F (λ x : τ. ...)
```

Where `F` is a magical constant with the type

``` haskell
    F :: (a -> a) -> a
```

`F` calculates the fixpoint of a function. This means that `f (F f) =
F f`. This formula underlies all recursive bindings (in Haskell
too!). In the compiler we basically compile a `Fix` to a closure (the
runtime representation of a function) and pass it to a C function
`fixedPoint` which actually calculates the fixed point. Now it might
seem dubious that a function has a fixed point. After all, it would
seem that there's no `x` so that `(λ (x : nat). suc x) = x` right?
Well the key is to think of these functions as not ranging over just
values in our language, but a domain where infinite loops (bottom
values) are also represented. In the above equation, the solution is
that `x` should be bottom, an infinite loop. That's why

``` haskell
    fix x : nat in suc x
```

should loop! There's actual some wonderful math going on here about
how computable functions are continuous functions over a domain and
that we can always calculate the least fixed point of them in this
manner. The curious reader is encouraged to check out domain theory.

Anyways, so that's why I keep handling fixpoints and lambdas in the
same way, because to me a fixpoint *is* a lambda + some magic. This is
going to become very clear in C-With-Expressions (`FauxC` from now on)
because we're going to promote both sorts of let bindings to the same
thing, a `FauxC` toplevel function. Without further ado, here's the
next IL.

``` haskell
    -- Invariant: the Integer part of a FauxCTop is a globally unique
    -- identifier that will be used as a name for that binding.
    type NumArgs = Int
    data BindTy = Int | Clos deriving Eq

    data FauxCTop a = FauxCTop Integer NumArgs (Scope Int FauxC a)
                    deriving (Eq, Functor, Foldable, Traversable)
    data BindFC a = NRecFC Integer [FauxC a]
                  | RecFC BindTy Integer [FauxC a]
                  deriving (Eq, Functor, Foldable, Traversable)
    data FauxC a = VFC a
                 | AppFC (FauxC a) (FauxC a)
                 | IfzFC (FauxC a) (FauxC a) (Scope () FauxC a)
                 | LetFC [BindFC a] (Scope Int FauxC a)
                 | SucFC (FauxC a)
                 | ZeroFC
                 deriving (Eq, Functor, Foldable, Traversable)
```

The big difference is that we've lifted things out of let
bindings. They now contain references to some global function instead
of actually having the value right there. We also tag fixpoints as
either fixing an `Int` or a `Clos`. The reasons for this will be
apparent in a bit.

Now for the conversion. We don't just have a function from `ExpL` to
`FauxC` because we also want to make note of all the nested lets we're
lifting out of the program. Thus we use `WriterT` to gather a lift of
toplevel functions as we traverse the program. Other than that this is
much like what we've seen before.

```
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
```

In the first couple cases we just recurse. as we've seen
before. Things only get interesting once we get to `LetL`

``` haskell
    fauxc (LetL binds e) = do
      binds' <- mapM liftBinds binds
      vs <- replicateM (length binds) gen
      body <- fauxc $ instantiate (VL . (!!) vs) e
      let e' = abstract (flip elemIndex vs) body
      return (LetFC binds' e')
```

In this case we recurse with the function `liftBinds` across all the
bindings, then do what we've done before and unwrap the body of the
let and recurse in it. So the meat of this transformation is in
`liftBinds`.

``` haskell
      where liftBinds (NRecL t clos bind) = lifter NRecFC clos bind
            liftBinds (RecL t clos bind) = lifter (RecFC $ bindTy t) clos bind
            lifter bindingConstr clos bind = do
              guid <- gen
              vs <- replicateM (length clos + 1) gen
              body <- fauxc $ instantiate (VL . (!!) vs) bind
              let bind' = abstract (flip elemIndex vs) body
              tell [FauxCTop guid (length clos + 1) bind']
              bindingConstr guid <$> mapM fauxc clos
            bindTy (Arr _ _) = Clos
            bindTy Nat = Int
```

To lift a binding all we do is generate a globally unique identifier
for the toplevel. Once we have that we that we can unwrap the
particular binding we're looking at. This is going to comprise the
body of the `TopC` function we're building. Since we need it to be
`FauxC` code as well we recurse on it. No we have a bunch of faux-C
code for the body of the toplevel function. We then just repackage the
body up into a binding (a `FauxCTop` needs one) and use `tell` to make
a note of it. Once we've done that we return the stripped down let
binding that just remembers the guid that we created for the toplevel
function.

In an example, this code transformers

``` haskell
    let x = λ (x : τ). ... in
      ... x ...
```

into

``` haskell
    TOP = λ (x : τ). ...
    let x = TOP in
      ... x ...
```

With this done our language is now 80% of the way to C!

### Converting To SSA-ish C

Converting our faux-C language to actual C has one complication: C
doesn't have `let` expressions. Given this, we have to flatten out a
faux-C expression so we can turn a let expression into a normal C
declaration. This conversion is *almost* a conversion to single static
assignment form, SSA. I say almost because there's precisely one place
where we break the single assignment discipline. This is just because
it seemed rather pointless to me to introduce an SSA IL with φ just so
I could compile it to C. YMMV.

This is what LLVM uses for its intermediate language and because of
this I strongly suspect regearing this compiler to target LLVM should
be pretty trivial.

Now we're using a library called [c-dsl][c-dsl] to make generating the
C less painful, but there's still a couple of things we'd like to
add. First of all, all our names our integers so we have `i2e` and
`i2d` for converting an integer into a C declaration or an expression.

``` haskell
    i2d :: Integer -> CDeclr
    i2d = fromString . ('_':) . show

    i2e :: Integer -> CExpr
    i2e = var . fromString . ('_':) . show
```

We also have a shorthand for the type of all expression in our
generated C code.

``` haskell
    taggedTy :: CDeclSpec
    taggedTy = CTypeSpec "tagged_ptr"
```

Finally, we have our writer monad and helper function for implementing
the SSA conversion. We write C99 block items and use `tellDecl`
binding an expression to a fresh variable and then we return this
variable.

``` haskell
    type RealCM = WriterT [CBlockItem] (Gen Integer)

    tellDecl :: CExpr -> RealCM CExpr
    tellDecl e = do
      i <- gen
      tell [CBlockDecl $ decl taggedTy (i2d i) $ Just e]
      return (i2e i)
```

Next we have the conversion procedure. Most of this is pretty
straightforward because we shell out to calls in the runtime system
for all the hardwork. We have the following RTS functions

 - `mkZero`, create a zero value
 - `inc`, increment an integer value
 - `dec`, decrement an integer value
 - `apply`, apply a closure to an argument
 - `mkClos`, make a closure with a closing over some values
 - `EMPTY`, an empty pointer, useful for default values
 - `isZero`, check if something is zero
 - `fixedPoint`, find the fixed point of function
 - `INT_SIZE`, the size of the runtime representation of an integer
 - `CLOS_SIZE`, the size of the runtime representation of a closure

Most of this code is therefore just converting the expression to SSA
form and using the RTS functions to shell do the appropriate
computation at each step. Note that c-dsl provides a few overloaded
string instances and so to generate the C code to apply a function we
just use `"foo"#[1, "these", "are", "arguments"]`.

The first few cases for conversion are nice and straightforward.

``` haskell
    realc :: FauxC CExpr -> RealCM CExpr
    realc (VFC e) = return e
    realc (AppFC f a) = ("apply" #) <$> mapM realc [f, a] >>= tellDecl
    realc ZeroFC = tellDecl $ "mkZero" # []
    realc (SucFC e) = realc e >>= tellDecl . ("inc"#) . (:[])
```

We take advantage of the fact that `realc` returns it's result and we
can almost make this look like the applicative cases we had
before. One particularly slick case is how `Suc` works. We compute the
value of `e` and apply the result to `suc`. We then feed this
expression into `tellDecl` which binds it to a fresh variable and
returns the variable. Haskell is pretty slick.

``` haskell
    realc (IfzFC i t e) = do
      outi <- realc i
      deci <- tellDecl ("dec" # [outi])
      let e' = instantiate1 (VFC deci) e
      (outt, blockt) <- lift . runWriterT $ (realc t)
      (oute, blocke) <- lift . runWriterT $ (realc e')
      out <- tellDecl "EMPTY"
      let branch b tempOut =
            CCompound [] (b ++ [CBlockStmt . liftE $ out <-- tempOut]) undefNode
          ifStat =
            cifElse ("isZero"#[outi]) (branch blockt outt) (branch blocke oute)
      tell [CBlockStmt ifStat]
      return out
```

In this next case we're translating `Ifz`. For this we obviously need
to compute the value of `i`. We do that by recursing and storing the
result in `outi`. Now we want to be able to use 1 less than the value
of `i` in case we go into the successor branch. This is done by
calling `dec` on `outi` and storing it for later.

Next we do something a little odd. We recurse on the branches of `Ifz`
but we definitely don't want to compute both of them! So we can't just
use a normal recursive call. If we did they'd be added to the block
we're building up in the writer monad. So we use `lift . runWriterT`
to give us back the blocks *without* adding them to the current one
we're building. Now it's just a matter of generating the appropriate
`if` statement.

To do this we add one instruction to the end of both branches, to
assign to some output variable. This ensures that no matter which
branch we go down we'll end up the result in one place. This is also
the one place where we are no longer doing SSA. Properly speaking we
should write this with a φ but who has time for that? :)

Finally we build add the if statement and the handful of declarations
that precede it to our block. Now for the last case.

``` haskell
    realc (LetFC binds bind) = do
      bindings <- mapM goBind binds
      realc $ instantiate (VFC . (bindings !!)) bind
      where sizeOf Int = "INT_SIZE"
            sizeOf Clos = "CLOS_SIZE"
            goBind (NRecFC i cs) =
              ("mkClos" #) <$> (i2e i :) . (fromIntegral (length cs) :)
                           <$> mapM realc cs
                           >>= tellDecl
            goBind (RecFC t i cs) = do
              f <- ("mkClos" #) <$> (i2e i :) . (fromIntegral (length cs) :)
                                <$> mapM realc cs
                                >>= tellDecl
              tellDecl ("fixedPoint"#[f, sizeOf t])
```

For our last case we have to deal with lets. For this we simply
traverse all the bindings which are now flat and then flatten the
expression under the binder. When we `mapM` over the bindings we
actually get back a list of all the expressions each binding evaluated
to. This is perfect for use with `instantiate` making the actual
toplevel function quite pleasant. `goBind` is slightly less so.

In the nonrecursive case all we have to do is create a closure. So
`goBind` of a nonrecursive binding shells out to `mkClos`. This
`mkClos` is applied to the number of closed over expressions as well
as all the closed over expressions. This is because `mkClos` is
variadic. Finally we shove the result into `tellDecl` as usual. For a
recursive call there's a slight difference, namely after doing all of
that we apply `fixedPoint` to the output *and* to the size of the type
of the thing we're fixing. This is why we kept types around for these
bindings! With them we can avoid dragging the size with every value
since we know it statically.

Next, we have a function for converting a faux C function into an
actual function definition. This is the function that we use `realc`
in.

```haskel
    topc :: FauxCTop CExpr -> Gen Integer CFunDef
    topc (FauxCTop i numArgs body) = do
      binds <- gen
      let getArg = (!!) (args (i2e binds) numArgs)
      (out, block) <- runWriterT . realc $ instantiate getArg body
      return $
        fun [taggedTy] ('_' : show i) [decl taggedTy $ ptr (i2d binds)] $
          CCompound [] (block ++ [CBlockStmt . creturn $ out]) undefNode
      where indexArg binds i = binds ! fromIntegral i
            args binds na = map (VFC . indexArg binds) [0..na - 1]
```

This isn't the most interesting function. We have one array of
arguments to our C function, and then we unbind the body of the FauxC
function by indexing into this array. It's not explicitly stated in
the code but the array contains the closed over expressions for the
first n - 1 entries and the nth is the actual argument to the
function. This is inline with how the variables are actually bound in
the body of the function which makes unwrapping the body to index into
the argument array very simple. We then call `realc` which transforms
our faux-c expression into a block of actual C code. We add one last
statement to the end of the block that returns the final outputted
variable. All that's left to do is bind it up into a C function and
call it a day.

### Putting It All Together

Finally, at the end of it all we have a function from expression to
`Maybe CTranslUnit`, a C program.

``` haskell
    compile :: Exp Integer -> Maybe CTranslUnit
    compile e = runGen . runMaybeT $ do
      assertTy M.empty e Nat
      funs <- lift $ pipe e
      return . transUnit . map export $ funs
      where pipe e = do
              simplified <- closConv e >>= llift
              (main, funs) <- runWriterT $ fauxc simplified
              i <- gen
              let topMain = FauxCTop i 1 (abstract (const Nothing) main)
                  funs' = map (i2e <$>) (funs ++ [topMain])
              (++ [makeCMain i]) <$> mapM topc funs'
            makeCMain entry =
              fun [intTy] "main"[] $ hBlock ["call"#[i2e entry]]
```

This combines all the previous compilation passes together. First we
typecheck and ensure that the program is a `Nat`. Then we closure
convert it and immediately lambda lift. This simplified program is
then fed into `fauxc` giving a `fauxc` expression for main and a bunch
of functions called by main. We wrap up the main expression in a
function that ignores all it's arguments. We then map `realc` over all
of these fauxc functions. This gives us actual C code. Finally, we
take on a trivial C main to call the generated code and return the
whole thing.

And that's our PCF compiler.

## Wrap Up

Well if you've made it this far congratulations. We just went through
a full compiler from a typed higher order language to C. Along the way
we ended up implementing

 1. A Type Checker
 2. Closure Conversion
 3. Lambda Lifting
 4. Conversion to Faux-C
 5. SSA Conversion

If you'd like to fiddle a bit more, some fun project might be

 1. Writing type checkers for all the intermediate languages. They're
    all typeable except perhaps Faux-C
 2. Implement compilation to LLVM instead of C. As I said before, this
    shouldn't be awful

[pcf]: http://github.com/jozefg/pcf
[lambdapi]: https://jozefg.bitbucket.io/posts/2014-12-17-variables.html
[bound-docs]: https://hackage.haskell.io/package/bound-1.0.4/docs/Bound.html
[mg]: http://hackage.haskell.org/package/monad-gen
[c-dsl]: http://hackage.haskell.org/package/c-dsl
[hm]: http://github.com/jozefg/hm
