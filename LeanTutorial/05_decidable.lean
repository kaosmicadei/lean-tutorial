/-
> 🚨*Disclaimer*🚨 This file was written following the literate programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

As a reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.

# Decidability
Having propositions like `0 = 1 : Prop` or `succ n < 0 : Prop` are useful for expressing logical
statements, but they cannot be used directly for computation. For instance, we cannot use them in
an `if` expression to decide which branch to take.

However, we can turn binary propositions into computable ones by instantiating them to the
`Decidable` typeclass.

The `Decidable` typeclass allows us to determine whether a proposition is true or false in a
computable way. It's a inductive type class with two constructors: `isTrue` and `isFalse`. Each one
is paired with a proof `p`. `isTrue p` means the proposition is true with proof `p`, and
`isFalse p` means the proposition `p` implies `False`.

    class inductive Decidable (p : Prop) where
      | isFalse : (h : ¬p) → Decidable p
      | isTrue  : (h : p)  →  Decidable p

To see a concrete example, let's define a decidable equality for our custom natural
numbers.
-/

inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ

def ℕ.decEq (m n : ℕ) : Decidable (m = n) :=
  match m, n with
    | zero, zero => isTrue (by trivial)
    | zero, succ _ => isFalse (by intro h; nomatch h)
    | succ _, zero => isFalse (by intro h; nomatch h)
    | succ a, succ b =>
      match ℕ.decEq a b with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (by
          intro h'
          cases h' with
          | refl => contradiction
          )

/-
The trivial case is when `0 = 0`, which is true by definition. For `0 = succ n` and `succ m = 0`,
both cases are false since zero and successor are two distinct constructors of natural numbers.

For the case when `succ a = succ b`, the injectivity of the successor allows us to reduce the
problem to deciding whether `a = b`. In that case, instead of match against zero and the successor,
we match against `a = b`. If the equality holds, so there is a proof that `a = b` from which we can
construct a proof that `succ a = succ b`.

If `a = b` is false, that we have `succ a = succ b → False`. By introduce the hypothesis
`h' : succ a = succ b` and try to break into cases, the only possible case turns `h` into
`h : a ≠ a`, which is a contradiction.

With that, `ℕ.decEq` provides a complete decidable equality for our custom natural numbers. And now
we can instantiate it into the `Decidable` typeclass.
-/

instance (m n : ℕ) : Decidable (m = n) := ℕ.decEq m n

/-
Now, `ℕ.zero = ℕ.zero` still checks a proposition, but thanks to our `Decidable` instance, we can
also evaluate it to a boolean value.
-/

#check ℕ.zero = ℕ.zero
#eval ℕ.zero = ℕ.zero  -- true

#check ℕ.zero = ℕ.zero.succ
#eval ℕ.zero = ℕ.zero.succ  -- false

/-
Because decidability to equality is quite common, there is a more convenient way to automatically
derive it using the `deriving DecidableEq` mechanism.

    inductive ℕ : Type where
      | zero : ℕ
      | succ : ℕ → ℕ
    deriving DecidableEq

That would automatically generate the `Decidable` instance for equality, saving us from writing it
manually. But as usual, the reason we didn't go that route first was to see step by step how the
magic works.

Now, let's make the same decidability construction but for the less-than-or-equal relation on
natural numbers.

We start by defining the inductive relation `ℕ.le` that represents the less-than-or-equal relation
and instantiating it into the `LE` and `LT` typeclasses to allows us to use the standard `≤` and
`<` notations.
-/

inductive ℕ.le (n : ℕ) : ℕ → Prop where
  | refl : ℕ.le n n
  | step : ℕ.le n m → ℕ.le n (ℕ.succ m)

instance : LE ℕ where
  le := ℕ.le

instance : LT ℕ where
  lt := fun m n => ℕ.le (ℕ.succ m) n

/-
The order relation in the natural numbers follows the rules:
1. `0 ≤ 0`.
2. `∀ n, succ n ≤ 0 → False`.
3. `∀ m n, m ≤ succ n → (m = succ n) ∨ (m ≤ n)`.
-/

def ℕ.decLe (m n : ℕ) : Decidable (m ≤ n) :=
  match m, n with
  | zero, zero => isTrue (by exact ℕ.le.refl)
  | succ m', zero => isFalse (by intro h; nomatch h)
  | m', succ n' =>
    if h : m' = n'.succ then
      isTrue (by rw [h]; exact ℕ.le.refl)
    else
      -- h : ¬ (m' = n'.succ)
      match ℕ.decLe m' n' with
        | isTrue h1 => isTrue (by exact ℕ.le.step h1)
        | isFalse h1 => isFalse (by
          intro h2
          cases h2 with
          | refl => contradiction
          | step h3 => exact h1 h3
          )

/-
Now, we can instantiate our natural number to have decidable less-than-or-equal and less-than
relations.
-/

instance (m n : ℕ) : Decidable (m ≤ n) := ℕ.decLe m n
instance (m n : ℕ) : Decidable (m < n) := ℕ.decLe (m.succ) n

/-
So from now on, we can use `≤` and `<` for both propositions and boolean evaluations.
-/

#check ℕ.zero ≤ ℕ.zero
#eval ℕ.zero ≤ ℕ.zero

#check ℕ.zero < ℕ.zero.succ
#eval ℕ.zero < ℕ.zero.succ

#check ℕ.zero.succ < ℕ.zero
#eval ℕ.zero.succ < ℕ.zero

/-
As an extra exercise, let's make our inductive proposition of even numbers also decidable. That way
we can use `Even n` as a proposition as well as a boolean evaluation.
-/

inductive Even : Nat → Prop where
  | zero : Even 0
  | step : Even n → Even (n + 2)

def Even.dec (n : Nat) : Decidable (Even n) :=
  match n with
    | 0 => isTrue (Even.zero)
    | 1 => isFalse (by intro h; nomatch h)
    | n + 2 =>
      match Even.dec n with
        | isTrue h => isTrue (Even.step h)
        | isFalse h => isFalse (by
          intro h'
          cases h' with
          | step h'' => exact h h''
        )

instance (n : Nat) : Decidable (Even n) := Even.dec n

#check Even 4
#eval Even 4

#check Even 3
#eval Even 3

/-
# Summary
Here we saw a small example of how `Decidable` can turn binary propositions into boolean-like
evaluations, allowing us to use them in propositions and in `if-else` expressions.

Although not all decidability is trivial, the decidability of equality is straightforward enough to be automatised. So, for `DecidableEq` it's preferable to use the `deriving` mechanism.
-/
