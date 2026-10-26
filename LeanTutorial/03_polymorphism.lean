/-
> 🚨*Disclaimer*🚨 This file was written following the literate programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

As a reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.

# Polymorphism
If you think that polymorphism is limited to object-oriented programming, let me show how you could
not be more wrong.

Being a functional programming language, Lean is already treats functions as first-class citizens.
Functions like `map`, `fold` and `filter` can operate on lists of any type. The trick there is that
the function passed to them determines the type of the input and output elements of the list. But
Lean can do much more than that. The real polymorphism comes from the *typeclasses*.

If you are coming from a language like Java or Rust you will recognise the idea of *interfaces* or
*traits*. That is essentially the role of a typeclass.

A typeclass encodes a set of operations and laws that a type must satisfy to be considered part of
the class. Think of it as a equivalence class.

For example, the addition have some properties that any type must to satisfy to be considered an
additive monoid. An additive monoid has an addition operation that takes two elements of the type
and returns another element of the same type. To be considered a monoid, it must have a neutral
element for the addition operation, usually called `zero`. Also, the addition operation must be
associative.
-/

class AddMonoid (α : Type) where
  add : α → α → α
  zero : α
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)

/-
Any type implementing such properties can be considered (or instantiated as) an Additive Monoid.

How that translates into polymorphism? Suppose we have a `sum` function that takes a list of some
type `α` and adds all its elements. The first question is what types `α` are available. Then, we
ask what addition means for a particular type `α`. We can abstract both questions by constraint the type `α` to be an `AddMonoid`.

-/

def sum {α : Type} [AddMonoid α] : List α → α
  | [] => AddMonoid.zero
  | x :: xs => AddMonoid.add x (sum xs)

/-
The way we did above ensure two things:
1. What ever is the type `α`, there is a base case for the sum, which is `AddMonoid.zero`.
2. There is a well-defined addition operation defined for the type `α` and associated to
   `AddMonoid.add`.

And that is exactly the essence of polymorphism.

To make this example clear, let's use our custom definition of the natural number once again. And
let's only look at the addition operations and properties.
-/

inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ

def ℕ.add (a b : ℕ) : ℕ :=
  match a with
  | ℕ.zero => b
  | ℕ.succ a' => ℕ.succ (ℕ.add a' b)

/-
Following the structure of our `AddMonoid` typeclass, the addition with zero must commute.
-/
theorem ℕ.zero_add (n : ℕ) : ℕ.add ℕ.zero n = n := by trivial
theorem ℕ.add_zero (n : ℕ) : ℕ.add n ℕ.zero = n := by
  induction n with
  | zero => rw [ℕ.zero_add]
  | succ n' ih => rw [ℕ.add, ih]

/-
We also need a proof that our `ℕ.add` is associative.
-/
theorem ℕ.add_assoc (a b c : ℕ) : ℕ.add (ℕ.add a b) c = ℕ.add a (ℕ.add b c) := by
  induction a with
  | zero => rw [ℕ.zero_add, ℕ.zero_add]
  | succ a' ih => rw [ℕ.add, ℕ.add, ℕ.add, ih]

/-
With that, we have all the necessary components to instantiate `ℕ` as an `AddMonoid`.
-/
instance : AddMonoid ℕ where
  add := ℕ.add
  zero := ℕ.zero
  add_zero := ℕ.add_zero
  zero_add := ℕ.zero_add
  add_assoc := ℕ.add_assoc

def one : ℕ := ℕ.succ ℕ.zero
def two : ℕ := ℕ.succ one
def three : ℕ := ℕ.succ two

/-
Now we can use our `sum` function to add up a list of natural numbers.
-/

#eval sum [one, two, three]

/-
# Inheritance vs Composition
Our `AddMonoid` typeclass is quite verbose and have many requirements. In practice, in Lean we
usually have typeclasses with fewer requirements and constraints, which could see as a "kind of"
inheritance style.

For example, Lean as a `Zero` typeclass that only requires a `zero` element. We could use that in our `AddMonoid` by writing our typeclass as an *extension* of the `Zero` typeclass.
-/

class AddMonoid₁ (α : Type) extends Zero α where
  add : α → α → α
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)

/-
Actually, we can do even better!

`Add` is a typeclass that defines only the binary addition operation `add`. We can then define
`AddMonoid` as an extension of both `Add` and `Zero`, which allows us to separate the concerns of
defining the addition operation and the additive identity.
-/

class AddMonoid₂ (α : Type) extends Add α, Zero α where
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)

/-
We can now instantiate `ℕ` as an `AddMonoid₂` by separately instantiating the `Add` and `Zero`
typeclasses, or by directly providing an instance of `AddMonoid₂` with all the required fields
(including the `add` and `zero` fields).

The advantage of instantiating `ℕ` separately, though, is that it allows us to reuse the `Add` and
`Zero` instances in other contexts without having to redefine them for every new typeclass that
extends them. That makes Lean polymorphism much more modular and composable.
-/

instance : Zero ℕ where
  zero := ℕ.zero

instance : Add ℕ where
  add := ℕ.add

instance : AddMonoid₂ ℕ where
  add_zero := ℕ.add_zero
  zero_add := ℕ.zero_add
  add_assoc := ℕ.add_assoc

/-
We could be as abstract and modular as we want by, for example, defining an `AddAssoc` typeclass
that only requires the associativity of addition, and then have `AddMonoid₃` extend it. This way,
we can reuse the `AddAssoc` instance in other contexts without having to redefine it for every new
typeclass that requires associativity.

-/

class AddAssoc (α : Type) extends Add α where
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)

class AddMonoid₃ (α : Type) extends AddAssoc α, Zero α where
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a

/-
From this perspective, `AddMonoid₃` is way more self explanatory than the original `AddMonoid`.

That is because the properties are split into smaller, but meaningful, typeclasses where each one
captures a single aspect of the algebraic structure.

`Add` captures the existence of a binary addition operation. `AddAssoc` extends the idea of addition
by claiming "if there is an addition operation, it must be associative." Then, `AddMonoid₃` goes
one step further and claims that "if the addition is associative and there is a zero element, then
we have an additive monoid."

None of those extensions forbids us to have a type that has an addition operation without
necessarily having a zero element or associativity. That is the power of composition.

Now, if we want to define a `Group` or a `SemiGroup`, we either extend the `AddMonoid₃` to define a
`Group` or use the `AddAssoc` instance to define a `SemiGroup`.

# Summary
Here we could have and idea of how Lean handles polymorphism and the benefits of using typeclasses
for modular and composable abstractions.

Lean Core has a long list of typeclasses that capture various algebraic structures and properties,
such as `Add`, `Mul`, `Zero`, `One`, `Functor`, `Monad`, and many more. Mathlib builds on top of
these core typeclasses to provide a rich hierarchy of algebraic structures and abstractions.
-/
