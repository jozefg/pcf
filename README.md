## pcf

A one file compiler for PCF to C. It's currently about 275 lines of
compiler and 75 lines of extremely boring instances. The compiler is
fully explained in `explanation.md`.

## What's PCF

PCF is a tiny typed, higher-order functional language. It has 3 main
constructs,

1. Natural Numbers

    In PCF there are two constants for natural numbers. `Zero` and
    `Suc`. `Zero` is pretty self explanatory. `Suc e` is the successor
    of a natural number, it's `1 + e` in other languages. Finally,
    when given a natural number you can pattern match on it with
    `ifz`.

        ifz e {
           Zero  => ...
         | Suc x => ...
        }

    Here the first branch runs if `e` evaluates to zero and the second
    branch is run if `e` evaluates to `Suc ...`. `x` is bound to the
    predecessor of `e` in the successor case.

2. Functions

   PCF has functions. They can close over variables and are higher
   order. Their pretty much what you would expect from a functional
   language. The relevant words here are `Lam` and `App`. Note that
   functions must be annotated with their arguments type.

3. General Recursion

   PCF has general recursion (and is thus Turing complete). It
   provides it in a slightly different way than you might be used
   to. In PCF you have the expression `fix x : t in ...` and in the
   `...` `x` would be bound. The intuition here is that `x` stands for
   the whole `fix x : t in ...` expression. If you're a Haskell person
   you can just desugar this to `fix $ \x : t -> ...`.


## Example

For a quick example of how this all hangs together, here is how you
would define `plus` in PCF

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

For this library we'd write this AST as

``` haskell
    let lam x e = Lam Nat $ abstract1 x e
        fix x e = Fix (Arr Nat (Arr Nat Nat)) $ abstract1 x e
        ifz i t x e = Ifz i t (abstract1 x e)
        plus = fix 1 $ lam 2 $ lam 3 $
                 ifz (V 2)
                     (V 3)
                     4 (Suc (App (V 1) (V 4) `App` (V 3)))
    in App (App plus (Suc Zero)) (Suc Zero)
```

We can then chuck this into the compiler and it will spit out the
following C code

``` c
    tagged_ptr _21(tagged_ptr * _30)
    {
        tagged_ptr _31 = dec(_30[1]);
        tagged_ptr _35 = EMPTY;
        if (isZero(_30[1]))
        {
            _35 = _30[2];
        }
        else
        {
            tagged_ptr _32 = apply(_30[0], _31);
            tagged_ptr _33 = apply(_32, _30[2]);
            tagged_ptr _34 = inc(_33);
            _35 = _34;
        }
        return _35;
    }
    tagged_ptr _18(tagged_ptr * _36)
    {
        tagged_ptr _37 = mkClos(_21, 2, _36[0], _36[1]);
        return _37;
    }
    tagged_ptr _16(tagged_ptr * _38)
    {
        tagged_ptr _39 = mkClos(_18, 1, _38[0]);
        return _39;
    }
    tagged_ptr _29(tagged_ptr * _40)
    {
        tagged_ptr _41 = mkClos(_16, 0);
        tagged_ptr _42 = fixedPoint(_41);
        tagged_ptr _43 = mkZero();
        tagged_ptr _49 = inc(_43);
        tagged_ptr _50 = apply(_42, _49);
        tagged_ptr _51 = mkZero();
        tagged_ptr _56 = inc(_51);
        tagged_ptr _57 = apply(_50, _56);
        return _57;
    }
    int main()
    {
        call(_29);
    }
```

Which when run with `preamble.c` pasted on top it prints out `2`. As
you'd hope.
