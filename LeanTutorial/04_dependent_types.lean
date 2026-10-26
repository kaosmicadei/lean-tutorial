/-
> 🚨*Disclaimer*🚨 This file was written following the literate programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

As a reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.

In the file `01_logic.lean` we briefly mentioned that the universal quantifier `∀` can be seen as a dependent function type, a Π-type.

Here, let's dive a bit more into dependent type and see how they can be used to make type
signatures more expressive and safe and how that reflects to propositions.

# Dependent Types
The most common example of dependent types is a vector with a fixed length. Similar to lists, a
vector is defined as a inductive type with two constructors: `nil` for the empty vector and `cons`
for adding an element to the front of an existing vector. The difference to a list is that a vector
has its length encoded in its type. That means that a `Vec Nat 2` is a different type from a
`Vec Nat 3`. As consequence, many operations like inner product can enforce at type level that all
the vectors involved have the same length.
-/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

/-
What makes the `Vec` a dependent type is the fact that the type is only determined once the length `n` is specified. In other words, the type `Vec α n` depends on the value `n`.
-/

def Vec.inner_prod (u v : Vec Nat n) : Nat :=
  match u, v with
  | Vec.nil, Vec.nil => 0
  | Vec.cons x xs, Vec.cons y ys => x * y + Vec.inner_prod xs ys

/-
Because both vectors `u` and `v` are enforced by type to have the same length `n`, we don't need to
cover the cases one of them is `nil` and the other is not. Those cases are impossible by
construction.
-/

def u : Vec Nat 2 := Vec.cons 1 (Vec.cons 2 Vec.nil)
def v : Vec Nat 2 := Vec.cons 3 (Vec.cons 4 Vec.nil)
def w : Vec Nat 3 := Vec.cons 5 (Vec.cons 6 (Vec.cons 7 Vec.nil))

#eval Vec.inner_prod u v  -- should output 11
-- #eval Vec.inner_prod u w  -- should result in a type error because the lengths differ

/-
In these examples, the compiler will throw an error when we try to compute the inner product of
vectors with different lengths. This is different than we first check the length of the vectors at
runtime and then throw an error if they don't match.

Another example of dependent type is the *finite set*, which represents the set of natural numbers
smaller than a given natural number `n`. This is a very useful type for indexing because it ensures
the indices are always within bounds.

A finite set type is defined as a pair containing a natural number `val` and a proof that `val` is
smaller than `n`.
-/

structure Finite (n : Nat) : Type where
  val : Nat
  is_lt : val < n

#check (⟨2, by decide⟩ : Finite 3)
-- #check (⟨2, by decide⟩ : Finite 2)  -- should result in a type error because 2 is not less than 2

/-
Since the type `Finite n` only exists after we specify `n`, the same pair `⟨2, by decide⟩` can
behave differently depending on the value of `n`. In the examples above, it is a valid element of
`Finite 3` but not of `Finite 2`.

`Finite 0` is a very special case called *Empty Type* because, since `n` is a natural number, there
is no `n` such that `n < 0`.
-/

def impossible (n : Finite 0) : α := nomatch n

/-
The `nomatch` tactic is used here to indicate there is no constructor that can reach `n < 0`.

Let's see a practical example of using the `Finite` type to safely index into a vector.
-/

def Vec.get (u : Vec α n) (i : Finite n) : α :=
  match u, i with
  | Vec.cons x _, ⟨0, _⟩ => x
  | Vec.cons _ xs, ⟨j+1, h⟩ => Vec.get xs ⟨j, Nat.lt_of_succ_lt_succ h⟩

def xs : Vec Nat 3 := Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))
#eval Vec.get xs ⟨0, by decide⟩  -- should output 1
#eval Vec.get xs ⟨1, by decide⟩  -- should output 2
#eval Vec.get xs ⟨2, by decide⟩  -- should output 3
-- #eval Vec.get xs ⟨3, by decide⟩  -- should result in a type error because the index is out of bounds

/-
By the definition of `Vec.get` the length of the vector `Vec α n` determines the type of the index
`i : Finite n`. That means the compiler can catch any attempt to access an element out of bounds.

This ability to create "parametric types" and allow the compiler to check things that would
otherwise require runtime checks is one of the appealing features of dependent types in terms of
safety and correctness.

# Dependent Propositions
Ok, We saw how dependent types can be used to allow the compiler to enforce constraints. Now let's
see how the same idea can be applied to propositions, where the truth of a proposition can depend
on a value. For that, let's look a bit more in depth to the `Finite` type and see how the
constraint `val < n` is treated as a proposition.

Since the idea of order is not limited to numbers, Lean defines the `LE` and `LT` classes to
represent the less-equal and less-than relations for any type.

    class LE (α : Type u) where
      /-- The less-equal relation: `x ≤ y` -/
      le : α → α → Prop

    class LT (α : Type u) where
      /-- The less-than relation: `x < y` -/
      lt : α → α → Prop

Notice that `le` and `lt` don't return a type like `Bool` but a proposition (`Prop`). If we have
and `a : α` and a `b : α`, then `LE.le a b` is a proposition stating that `a` is less than or equal
to `b` and not a concrete boolean value.

To explain how exactly dependent types ca be used to represent propositions let's revisit our
natural numbers definition and define and make it compatible with the `LE` class.
-/

inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ

/-
We define the the relation order `≤` based on two properties:
1. Reflexivity: `n ≤ n` for any natural number `n`.
2. Step: if `n ≤ m` then `n ≤ succ m`.

Because in Lean 4, propositions are types, we can encode those properties in a inductive type, where each constructor represents a way to prove the proposition.
-/
inductive ℕ.le (n : ℕ) : ℕ → Prop where
  | refl : ℕ.le n n
  | step : ℕ.le n m → ℕ.le n (m.succ)

/-
Now, we can instantiate our natural numbers with the `LE` class so we can use the `≤` notation.
-/
instance : LE ℕ where
  le := ℕ.le

/-
As a form of see this definition in action,let's prove the transitivity of `≤` for our natural
numbers.
-/

theorem ℕ.le.trans {a b c : ℕ} : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  cases hbc with
  | refl => exact hab
  | step hbm =>
    have h1 := ℕ.le.trans hab hbm
    have h2 := ℕ.le.step h1
    exact h2

/-
Because `ℕ.le` is an inductive proposition, we need to prove the transitivity for every valid case
of `b ≤ c`.

The reflexivity case gives `b ≤ b`, replacing `c` with `b` in the final goal `a ≤ c` making the
result trivial.

The step case introduces a new variable `m†` representing the *predecessor of `c`* and a proof that
`b ≤ m†`. When we apply the `ℕ.le.trans` to this new proof, that is equivalent to perform a
inductive step. That means, `h1` is the inductive hypothesis.

In fact, because of the structure of `ℕ.le`, we could do the same proof using induction on the proof of `b ≤ c`.
-/

example (a b c : ℕ) : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  induction hbc with
  | refl => exact hab
  | step _ ih => exact ℕ.le.step ih

/-
The reason we didn't used induction straight away is mostly for pedagogical reasons. The
`induction` hides how the recursion is used here, making the result appears a bit magical.

Using `ℕ.le` we can also instantiate our natural number to the `LT` class, allowing us to use the `<` notation. That is done using the definition `a < b := (succ a) ≤ b`.
-/

instance : LT ℕ where
  lt := fun a b => ℕ.le a.succ b

/-
Because `ℕ.le` is a proposition, we can `check` its type using the `#check` command.
-/

#check ℕ.zero ≤ ℕ.zero
#check ℕ.zero.succ < ℕ.zero

/-
But also because `ℕ.le` is a proposition, we can write virtually anything like `(succ n) < 0` even
if it is not true. That is because a proposition needs a proof to be either true or false.

We could make our `ℕ.le` computable using the `Decidable` typeclass, but that will be a topic for
another time.

For now, let's focus on dependent propositions and proofs.

In the file `01_logic.lean` we have defined even natural numbers using the existential quantifier:

    def Even (n : Nat) := ∃ k : Nat, n = 2 * k

This is a computable definition of the even natural numbers and works fine. But we can also define
even numbers as an inductive proposition. Why? Because it allows us to reason about even numbers
using induction instead of a witness and computation. Both are valid approaches, the thing is
sometimes one is more convenient than the other.

We define an even natural number following two simple rules:
1. `0` is even (after all, zero is divisible by 2)
2. If `n` is even, then `n + 2` is even.

The second rule is essentially the "successor" rule.
-/

inductive Even : Nat → Prop where
  | zero : Even 0
  | step : Even n → Even (n + 2)

/-
Let's see an example of how prove that a number is even using the inductive definition.
-/

example : Even 4 := by
  constructor  -- uses `Even.step` to move the goal to `Even 2`
  constructor  -- uses `Even.step` to move the goal to `Even 0`
  constructor  -- uses `Even.zero` to solve the goal

/-
Here, instead of find a witness `k` such that `4 = 2 * k`, we use the valid constructors to break
the goal into a previous step until we reach the base case `Even 0`.

Being more verbose, for the first constructor `Even 4` doesn't match `Even.zero`, so Lean uses
`Even.step` to reduce the goal to `Even 2`. Similarly, for the second constructor `Even 2` doesn't
match `Even.zero`, so Lean uses `Even.step` to reduce the goal to `Even 0`. Finally, the third
constructor can only match `Even.zero`, which solves the goal.

In fact, we could be more succinct by using the `repeat` tactic.

    example : Even 4 := by
      repeat constructor

The `repeat` tactic will apply the same tactic over and over until there is no match for it any
more.

The reason we didn't use the `repeat` straight away was to give a more detailed explanation of how
the constructors work step by step.

Now, let's see what happens when a number is not even.
-/

example : ¬ Even 3 := by
  unfold Not
  intro h
  cases h with
  | step h' => nomatch h'

/-
Here we start with the assumption that `h : Even 3`. When we try to break `h` into cases, the case
`Even.zero` is obviously not applicable, so we can focus only in the case `Even.step`. In this
case, we have `h' : Even 1`. Now, here is the problem, `Even.zero` is again not a fit, but
`Even.step` is not applicable again because there is no `n : Nat` such that `1 = n + 2`. As a
result, there is no match case for `Even 1`. That closes the proof.

Finally, we said before that there is no difference in using `Even` as an inductive proposition or
a predicate using existential quantification. So, let's prove that both representations are
equivalent.
-/

example (n : Nat) : Even n ↔ ∃ k : Nat, n = 2 * k := by
  constructor
  . intro h
    induction h with
    | zero => exists 0
    | step h' ih =>
      obtain ⟨k, hk⟩ := ih
      rw [hk]
      exists k + 1
  . intro h
    obtain ⟨k, hk⟩ := h
    subst hk
    induction k with
    | zero => constructor
    | succ k' ih =>
      constructor
      exact ih

/-
# Summary
Here we had a short introduction to dependent types and propositions. The main goal was to show how
a type can hold more complex informations like the size of a vector and how propositions can be
encoded as types. That gives the compiler a lot of power in terms of type checking. It can avoid to
compile an inner product when we try to multiply two vectors with different sizes, or it can refuse
to accept a proof claiming that three is an even number.
-/
