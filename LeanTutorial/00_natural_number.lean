/-
> 🚨*Disclaimer*🚨 This file was written following the literate programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

I think a good way to learn Lean is by creating your own version of the natural numbers. This gives
a good view on: inductive types, constructors, pattern matching, recursion, and allows to explore
basics of theorem proving with proofs that forces you to think step by step.

This file shows a basic construction of the natural numbers, explains the use of pattern
matching and recursion to implement addition and multiplication, and some unnecessarily verbose
step-by-step proofs so the reader can follows the reasoning process.

A good reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.

# Definition of Natural Numbers
Inductive types are types with more than one constructor. If you are coming from programming
languages like C++, you will be familiar with the concept. If you are coming from languages like
Python, it basically means your class have multiple `__init__` methods, each one creating a
different instance of the same class.

So, with that in mind, let's get it started!

According to Peano's axioms, the natural type has two constructors: zero and the successor function.
-/

inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ

/-
> *Notation hint.* Lean accepts unicode symbols entered with LaTeX style. You can use `\N` for `ℕ`
> and `\r` for `→`.

By definition, `zero` and `succ` produces different objects of type `ℕ`. And we can use this
structural difference to prove one of the Peano's axioms:

> Zero is not the successor of any natural number.
-/

theorem ℕ.zero_ne_succ (n : ℕ) : ℕ.zero ≠ ℕ.succ n := by
  dsimp          -- expands definitions, in this case the definition of ≠
  unfold Not     -- replaces ¬ with its definition
  intro h        -- moves the proposition `ℕ.zero = ℕ.succ n` to the context under the name `h`
  contradiction  -- verifies the structural contradiction of `ℕ.zero = ℕ.succ n`

/-
The proof above is too verbose on purpose, to show the step-by-step reasoning in Lean. In practice,
Lean's compiler is way more powerful and could infer the structural contradiction automatically
during simplification. That would look like this:

    theorem ℕ.zero_ne_succ (n : ℕ) : ℕ.zero ≠ ℕ.succ n := by simp

But, for someone learning, it's nice to see the mechanics behind the magic. Even if all the
compiler details are still hidden from the user.

We can also use the structural difference of the constructors to prove another Peano's axiom:

> If the successor of m is equal to the successor of n, then m is equal to n.
-/

theorem ℕ.succ_injective (m n : ℕ) (h: ℕ.succ m = ℕ.succ n) : m = n := by
  injection h

/-
If different constructors produce different objects, the same constructor applied to different
arguments can only produce the same object if the arguments themselves are equal. This can be
formally captured by the `injection` tactic.

# Addition between Natural Numbers
The addition between two natural numbers has two rules:
* `0 + n = n`
* `succ m + n = succ (m + n)`

Because Lean is a functional programming language, we can abuse of pattern matching and recursion
to define `add(m, n)`. Think of pattern matching as a more descriptive if-else list that uses
deconstructor statements, and recursion as a structural way to perform loops.
-/

def ℕ.add (m n : ℕ) : ℕ :=
  match m with
  | .zero => n
  | .succ m' => .succ (ℕ.add m' n)

/-
Now that we had defined the addition function for natural numbers, it's convenient to instantiate
our `ℕ` type to the `Add` typeclass. That will allow us to use the `+` notation for addition and
write `m + n` instead of `ℕ.add m n`.

In functional programming languages like Lean, typeclasses allow to create polymorphism by defining
generic interfaces that can be implemented for different types. `Add`, for example, allows to any
type implementing some sort of addition operation to use the `+` operator with the only constraint
being the addition must be a monoid, `+ : A × A → A`.
-/

instance : Add ℕ where
  add := ℕ.add

/-
The definition of a function can be used by the Lean's compiler to simplify expressions and prove
theorems automatically. But they cannot be used as propositions directly. And be able to be used as
a proposition is important so we can rewrite expressions.

In order to use the definition of addition as propositions, we need to define the cases as separated
theorems. Think about theorems in Lean as functions that return propositions.
-/

theorem ℕ.zero_add (n : ℕ) : .zero + n = n := by trivial
theorem ℕ.succ_add (m n : ℕ) : .succ m + n = .succ (m + n) := by trivial

/-
Because these propositions can be derived directly from the definitions, they can be trivially
proven using the `trivial` tactic.

To name the theorems, I'm using the Mathlib convention where we name the mathematical fact and name
the main objects. In this case, when we have `0 + n`, the main object is zero and the mathematical
fact is the addition, so we name the theorem `zero_add`. The order also has a utility here, as it
serves to show which one appears first in the expression.

## Properties of addition
Now, let's see how we can use the `ℕ.zero_add` and `ℕ.succ_add` theorems to prove some properties
of the addition of natural numbers.

### Associativity of addition
The first proof that we can derive directly from `ℕ.zero_add` and `ℕ.succ_add` is the associativity
of addition.

Again, following the name convention of Mathlib, we name the theorem as `add_assoc`. The main
object here is the addition operation itself, and the mathematical fact is the associativity.

Associativity is proved by induction. Lean has a special pattern matching syntax for induction that
handles the base case, where `m = 0`, and the inductive case, where `m = succ m'` that also
provides an induction hypothesis `ih` about `m'`.
-/

theorem ℕ.add_assoc (m n k : ℕ) : (m + n) + k = m + (n + k) := by
  induction m with
  | zero => rw [ℕ.zero_add, ℕ.zero_add]  -- by definition, `trivial` would also work here
  | succ m' ih => rw [ℕ.succ_add, ℕ.succ_add, ℕ.succ_add, ih]

/-
The `rw` tactic is used to rewrite expressions using propositions. In this case, it uses
`ℕ.zero_add` to replace the first occurrence of `.zero + x` with just `x`. After each rewrite, `rw`
tries to verify if the goal has reached an obvious truth, like `x = x`.

### Commutativity of addition
The commutativity of addition is proved in three steps.

First, we prove that addition commutes with zero, i.e., `n + 0 = n`. We name this theorem
`ℕ.add_zero` to state that addition precedes zero in the expression.

Next, we prove that addition commutes with the successor, i.e., `n + succ m = succ (n + m)` a
theorem we name `ℕ.add_succ`.

Finally, we use all the previous theorems involving zero and the successor to prove the
commutativity of addition. We call this theorem `ℕ.add_comm` where the addition operation itself is
the main object and the mathematical fact is the commutativity.
-/

theorem ℕ.add_zero (n : ℕ) : n + .zero = n := by
  induction n with
  | zero => rw [ℕ.zero_add]  -- by definition, `trivial` would also work here
  | succ n' ih => rw [ℕ.succ_add, ih]

theorem ℕ.add_succ (m n : ℕ) : m + .succ n = .succ (m + n) := by
  induction m with
  | zero => rw [ℕ.zero_add, ℕ.zero_add]  -- by definition, `trivial` would also work here
  | succ m' ih => rw [ℕ.succ_add, ℕ.succ_add, ih]

theorem ℕ.add_comm (m n : ℕ) : m + n = n + m := by
  induction m with
  | zero => rw [ℕ.zero_add, ℕ.add_zero]
  | succ m' ih => rw [ℕ.succ_add, ℕ.add_succ, ih]

/-
# Multiplication of Natural Numbers
After the addition, the next basic arithmetic operation is the multiplication of two natural
numbers.

Here we proceed like we did for addition. First, we define the multiplication operation using
pattern matching and recursion.
-/

def ℕ.mul (m n : ℕ) : ℕ :=
  match m with
  | .zero => .zero
  | .succ m' => n + ℕ.mul m' n

/-
Then we instantiate our natural number type to the `Mul` typeclass so that we can use the `*`
notation for multiplication.
-/

instance : Mul ℕ where
  mul := ℕ.mul

/-
And we state the propositions based on the definition of multiplication.
-/

theorem ℕ.zero_mul (n : ℕ) : .zero * n = .zero := by trivial
theorem ℕ.succ_mul (m n : ℕ) : .succ m * n = n + (m * n) := by trivial

/-
## Properties of multiplication

### Commutativity of multiplication
Like in the addition case, the commutativity of multiplication is proved in three steps.
-/

theorem ℕ.mul_zero (n : ℕ) : n * .zero = .zero := by
  induction n with
  | zero => rw [ℕ.zero_mul]  -- by definition, `trivial` would also work here
  | succ n' ih => rw [ℕ.succ_mul, ih, ℕ.zero_add]

theorem ℕ.mul_succ (m n : ℕ) : m * .succ n = m * n + m := by
  induction m with
  | zero => rw [ℕ.zero_mul, ℕ.zero_mul, ℕ.zero_add]  -- `trivial` would also work here
  | succ m' ih => rw [ℕ.succ_mul, ℕ.succ_mul, ih, ℕ.succ_add, ℕ.add_succ, ℕ.add_assoc]

theorem ℕ.mul_comm (m n : ℕ) : m * n = n * m := by
  induction m with
  | zero => rw [ℕ.zero_mul, ℕ.mul_zero]
  | succ m' ih => rw [ℕ.succ_mul, ih, ℕ.mul_succ, ℕ.add_comm]

/-
### Distributive property of multiplication over addition
Before we are able to prove the associativity of multiplication, we first establish the distributive
property over addition.

The distributive property is defined in two ways: with the multiplication on the left of the
addition and with the multiplication on the right of the addition.
-/

theorem ℕ.mul_add (m n k : ℕ) : m * (n + k) = m * n + m * k := by
  induction m with
  | zero => rw [ℕ.zero_mul, ℕ.zero_mul, ℕ.zero_mul, ℕ.zero_add]  -- `trivial` would also work here
  | succ m' ih =>
    rw [ℕ.succ_mul, ℕ.succ_mul, ℕ.succ_mul, ih]
    rw [ℕ.add_comm k, ℕ.add_assoc, ℕ.add_comm k]
    rw [← ℕ.add_assoc, ← ℕ.add_assoc, ← ℕ.add_assoc]

/-
The `←` indicates we want to use the proposition on reverse. When `rw` sees a proposition like
`a = b`, it replaces the first occurrence of `a` with `b`. When we use `← a = b`, it goes in the
opposite direction and replaces the first occurrence of `b` with `a`.
-/

theorem ℕ.add_mul (m n k : ℕ) : (m + n) * k = m * k + n * k := by
  rw [ℕ.mul_comm (m + n), ℕ.mul_comm m, ℕ.mul_comm n]
  exact ℕ.mul_add k m n

/-
`ℕ.add_mul` does something clever here. It uses the fact that we have already proven the
commutativity of multiplication to transform the problem into a form where we can apply `ℕ.mul_add`.
Then, it states the solution is exactly `ℕ.mul_add` with the arguments rotated.

Since the multiplication appears multiple times and they are not eliminated by each rewrite, we
specify the first argument of each term to avoid driving the compiler crazy.

### Associativity of multiplication
The last property we will prove in this file is the associativity of multiplication.
-/

theorem ℕ.mul_assoc (m n k : ℕ) : (m * n) * k = m * (n * k) := by
  induction m with
  | zero => rw [ℕ.zero_mul, ℕ.zero_mul, ℕ.zero_mul]  -- `trivial` would also work here
  | succ m' ih => rw [ℕ.succ_mul, ℕ.succ_mul, ℕ.add_mul, ih]

/-
# Summary
Here, we had a glimpse of Lean and it can be used to prove some mathematical statements. We have
seen how to use inductive types by defining our own version of the natural numbers, and how to
prove basic properties of addition and multiplication using induction.

In reality, we don't need to define the natural numbers ourselves or prove these basic properties
from scratch. Lean's standard library already provides a well-defined natural number type, `Nat`
along with proofs of these fundamental properties. The Mathlib library also has its own definition
of natural numbers, `ℕ`, and provides a rich set of tools for working with them.
-/
