/-
> 🚨*Disclaimer*🚨 This file was written following the literate programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

If writing your own natural number types is a good way to start to learn Lean, then learning about
how to use logical operations and existential quantifiers is the best way to learn more about
tactics and proof strategies in Lean.

This file shows a few examples of logical statements and their proofs before diving into some proofs
involving quantifiers (∃ and ∀) and natural numbers.

As a reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.

# Propositional Logic
In classical logic, the basic elements to build logical statements are propositions (`P`) and
logical connectives: implication (`→`), negation (`¬`), conjunction (`∧`), disjunction (`∨`) and
biconditional (`↔`). These are the building blocks of propositional logic.

## Implication
In the Lean syntax, when we are defining functions, `A → B` represents a map from `A` to `B`.
However, thanks to the Curry-Howard correspondence, a function `P → Q` can be interpreted as a
logical implication `P → Q` because it can be read as:

> Taking a proof of `P` and applying the function `P → Q` to it, we obtain a proof of `Q`.

A simple example is the identity function.
-/

example (P : Prop) : P → P := by
  exact id

/-
The `id` function takes an input value and returns the same value as output. When this value is a
proof to the proposition `P`, it returns the same proof as output.

## Negation
`Not P` or `¬P` represents the negation of a proposition `P`. Since Lean uses constructive logic,
`¬P` requires to construct a proof that `P` is false. That means, `¬P` takes a proposition `P` and
returns a proof of `False`. Or in other words, `¬P` is defined as `P → False`.

Now, here is the catch. `False` is an empty type. That means, there is no valid construction of a
value of type `False`. So, an implication `P → False` holds only if `P` cannot be constructed
either.

For example, think about the case in the natural numbers where `0 ≠ succ n`. Since zero and the
successor are two distinct constructors of the natural numbers, there is no valid construction such
that `0 = succ n`. Therefore, `0 = succ n` cannot be constructed. Therefore, `0 = succ n` implies
`False`. In Lean, `a≠b` is a shorthand for `¬(a = b)`.

The Lean compiler, however, is way more powerful than that. It can handle more abstract reasoning
like working with opaque propositions. Here is an example:
-/

theorem contrapositive (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  intro h1
  unfold Not at *
  intro p
  have q := h p
  exact h1 q

/-
In the `contrapositive` example, we have two hypotheses: `h : P → Q` and `h1 : Q → False`. And we
want to show that `P → False`. The proposition `P` is introduced to the context as the variable
`p`. We recover the proposition `Q` by applying the hypothesis `h` to `p`, obtaining `q := h p`.
Finally, we apply `h1` to `q` to derive `False`.

## Conjunction and Disjunction
Conjunction (`∧`, "and") and disjunction (`∨`, "or") are the structures that allow us to combine
propositions.

In Lean, conjunction and disjunction are represented using two types of data structures:
* a "pair" or product type for conjunction ("A and B"),
* a sum type for disjunction ("either A or B").

The difference between them is that a product type is like a tuple and holds both values at the
same time. A sum type, on the other hand, is separated in cases where each case holds only one of
the possible values.

To give a practical example, let's look at the commutativity of conjunction and disjunction.
-/

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨p, q⟩ := h
  exact And.intro q p

/-
Here we have used `obtain` to break down the hypothesis `h : P ∧ Q` into its components `p : P` and
`q : Q`. The angle brackets `⟨ ⟩` (`\<` and `\>`) are used to pattern match on the components of  a
structure. To return the `And` structure, we need both `p` and `q` at the same time.

Now, let's see the difference when proving the commutativity of disjunction.
-/

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl p => exact Or.inr p
  | inr q => exact Or.inl q

/-
Here we have used `cases ... with` to split the hypothesis `h : P ∨ Q` into its possible cases.
The `inl` constructor (`intro left`) corresponds to the case where `P` holds, and the `inr`
constructor (`intro right`) corresponds to the case where `Q` holds. To return the `Or` structure, we need to specify which side of the disjunction we are providing, either `p` or `q`.

Although the logical OR accepts both propositions `P` and `Q` to be true, in practice it's enough to
have only one of them to be true at a time. So, encoding `P ∨ Q` as "either P or Q" makes sense and
turns the implementation more natural. Also, the `case ... with` tactic forces to cover both cases.

Let's see an example where both logical operators appear by proving the distributivity of
conjunction over disjunction.
-/

example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  intro abc
  obtain ⟨a, bc⟩ := abc
  cases bc with
  | inl b => exact Or.inl (And.intro a b)
  | inr c => exact Or.inr (And.intro a c)

/-
Here, the first hypothesis, `abc : A ∧ (B ∨ C)` is a conjunction of `A` and `B ∨ C`. We use
`obtain ⟨a, bc⟩ := abc` to break it down into `a : A` and `bc : B ∨ C`. Then, we use
`cases bc with` to handle the cases where `B` and `C` hold separately. That way, we can prove
either `A ∧ B` or `A ∧ C`.

Now, let's see an example of proof that mixes logical operators with natural numbers.
-/

example (n m : Nat) : m * n = 0 → m = 0 ∨ n = 0 := by
  intro h
  cases m with
  | zero =>
    left
    trivial
  | succ m' =>
    right
    rw [Nat.add_mul, Nat.one_mul, Nat.add_eq_zero_iff] at h
    exact h.right

/-
Here, the first thing that we notice is that we don't need to use `induction`. That is because we
can use the fact that zero is not a successor of any natural number to conclude that `n = 0` in the
second case.

The key part here are the tactics `left` and `right`. They allow us to specify which side of the
goal we want to follow.

In the first case, `m = 0`, so we follow the left side of the disjunction, while in the second
case, `m = succ m'` and therefore `n` must be zero. So we follow the right side of the disjunction.

## Biconditional
The last building block of propositional logic is the biconditional (↔). It represents the logical equivalence between two propositions, `P ↔ Q` means that `P → Q` and `Q → P` are both true. Like
the conjunction structure, in Lean, the biconditional is also a product type since both statements
must be true at the same time.

When working with biconditionals in Lean, we need to be able to prove both directions in order to
have our goal proved. To isolate each direction, we use the `constructor` tactic, which splits the biconditional into two separate goals.
-/

example (A B C : Prop) : A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C) := by
  constructor
  . -- Modus Ponens: A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
    intro h
    cases h with
    | inl a => exact And.intro (Or.inl a) (Or.inl a)
    | inr bc =>
      obtain ⟨b, c⟩ := bc
      exact And.intro (Or.inr b) (Or.inr c)
  . -- Modus Ponens Reverse: (A ∨ B) ∧ (A ∨ C) → A ∨ (B ∧ C)
    intro h
    obtain ⟨ab, ac⟩ := h
    cases ab with
    | inl a => exact Or.inl a
    | inr b =>
      cases ac with
      | inl a => exact Or.inl a
      | inr c => exact Or.inr (And.intro b c)

/-
The isolated dot (`.`) is used to visually indicate the beginning of a new goal when using the
`constructor` tactic. It's entirely optional but helps improve readability by separating the
different sub-goals.

Similarly to the conjunction that we can access each component using `.left` and `.right`, for
biconditionals, we can access the forward and backward implications using `.mp` (modus ponens) and
`.mpr` (modus ponens reverse) respectively. That means, if `h : P ↔ Q`, then `h.mp` gives us a
function `P → Q` and `h.mpr` gives us a function `Q → P`.

# First-Order Logic
With the propositional logic we can already do lots of things. But we can go one step further and
move to first-order logic by introducing the existential (∃) and universal (∀) quantifiers. The
allow us to introduce variables and treat propositions as functions.

## Existential Quantifier
The statement `∃x, P(x)` means that there exists some `x` such that the proposition `P(x)` is true.
In Lean, the `Exists` type is defined by a product type that holds a witness `x` and a proof of
`P(x)`.

Although we could write `Exists.intro x (P x)`, Lean provides a much nicer syntax, `∃ x, P x`.

There are two ways to interact with a `Exists` type. The first is when the existential qualifier is
on the goal of the proof. In that case, we need to provide a witness that satisfies the proposition. That is done using the `exists` tactic.
-/

example (n : Nat) : n ≠ 0 → ∃ k : Nat, n = k + 1 := by
  intro h
  cases n with
  | zero => contradiction
  | succ n' => exists n'

/-
The second way to interact with an `Exists` type is when the existential qualifier is in the hypothesis. In that case, we can extract the witness and the proof using the `obtain` tactic.
-/

def Even (n : Nat) := ∃ k : Nat, n = 2*k
def Odd (n : Nat) := ∃ k : Nat, n = 2*k + 1

theorem succ_even_to_odd (n : Nat) : Even n → Odd (n + 1) := by
  intro h
  unfold Even at h
  obtain ⟨k, hn⟩ := h
  rw [hn]
  unfold Odd
  exists k

theorem succ_odd_to_even (n : Nat) : Odd n → Even (n + 1) := by
  intro h
  unfold Odd at h
  obtain ⟨k, hn⟩ := h
  rw [hn]
  unfold Even
  exists (k + 1)

/-
## Universal Quantifier
The final element we consider is the universal quantifier (∀). The statement `∀ x, P(x)` means that
for every `x`, the proposition `P(x)` is true.

Because Lean is a type dependent language, the universal quantifier is defined as a primitive type
called Π-type. A Π-type is function signature `(x : A) → P(x)` that takes an element `x` of type
`A` and returns a *type* `P(x)` where the final form of the type depends on the value of `x`.

Thanks to the Curry-Howard correspondence, we can say that `(x : A) → P(x)` represents a function that takes an element `x` of type `A` and returns a proposition `P(x)`.

Because in Lean, theorem are functions that return a proposition, writing

    theorem my_theorem (x : A) : P x := by
      -- proof here

is the same as writing

    theorem my_theorem : ∀ (x : A), P x := by
      intro x
      -- proof here

Both forms have the type signature `(x : A) → P(x)`. That is why the universal quantifier is not a
structure in Lean like `Exists` is.

Here are two examples to put everything we have saw together.
-/

example : ∀ (n : Nat), Even n ∨ Odd n := by
  intro n
  induction n with
  | zero =>
    left
    unfold Even
    exists 0
  | succ n' ih =>
    cases ih with
    | inl h =>
      right
      exact succ_even_to_odd n' h
    | inr h =>
      left
      exact succ_odd_to_even n' h

example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n
  unfold Not
  intro h
  obtain ⟨he, ho⟩ := h
  unfold Even at he
  unfold Odd at ho
  obtain ⟨k, hk⟩ := he
  obtain ⟨l, hl⟩ := ho
  -- if n is even, then n % 2 = 0
  have h1 : n % 2 = 0 := by
    rw [hk, Nat.mul_mod_right]
  -- if n is odd, then n % 2 = 1
  have h2 : n % 2 = 1 := by
    rw [hl, Nat.add_mod, Nat.mul_mod_right, Nat.one_mod]
  -- this leads to a contradiction: 0 = 1; since the compiler cannot infer the contradiction
  -- automatically, we provide it explicitly.
  have h3 : 0 = 1 := by
    rw [← h1, ← h2]
  contradiction

/-
# Summary
Here we saw how the basic of propositional and first-order logic can be represented and used in
Lean. Those elements are enough to perform many types of proofs. But, as usual, that is just a
glimpse of what Lean can do. The Mathlib library contains many other structure that can be used
for more complex proofs like series summation, number theory, and algebraic structures.
-/
