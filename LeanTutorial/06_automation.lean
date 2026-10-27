/-
> 🚨*Disclaimer*🚨 This file was written following the literate programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

As a reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.

# Automation Tactics
So far, we have done proofs mostly by hand, providing explicit steps for each logical deduction,
with some exceptions of `by trivial` and `by decide`.

In this file, we will explore how to leverage Lean's automation tactics to simplify and streamline proofs.

We already covered how `decide` works in the file `05_decidable.lean`. Here we will focus on other
two automation tactics: `simp`, used to simplify goals and hypotheses, and `omega`, used to solve
goals involving linear arithmetic of natural and integer numbers.

## Simplifying List Proofs with `simp`
Rewrite goals may be a tedious and repetitive task. Also, it requires looking up and applying the
appropriate lemmas manually. Thankfully, Lean is equipped with a nice automation tactic called
`simp` that can simplify goals by automatically.

The way `simp` works is quite simple. It uses a database of lemmas and definitions. When we invoke
`simp`, it looks up for applicable lemmas and applies them until no further simplifications can be
made.

We can use `simp` to simplify the goal, or we can use `simp at h` to simplify a particular
hypothesis `h`. We can also add extra lemmas or definition to the simplification process by passing
them as arguments to `simp`, like `simp [lemma1, lemma2]`.

To see an example of `simp` in practice, let's go back the file `02_recursion.lean` where we
defined the `map` function for lists and proved its distributivity over list append.
-/

def map (f : α → β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x :: xs' => f x :: map f xs'

example (xs ys : List α) (f : α → β) : map f (xs ++ ys) = (map f xs) ++ (map f ys) := by
  induction xs with
  | nil =>
    rw [List.nil_append, map, List.nil_append]
  | cons x xs' ih =>
    rw [List.cons_append, map, map, List.cons_append, List.cons.injEq]
    constructor
    · -- f x = fx
      trivial
    · -- map f (xs' ++ ys) = map f xs' ++ map f ys
      exact ih

/-
Back then, we said that proof was verbose on purpose to illustrate each step clearly. But that is
not the intent of using a proof assistant like Lean. The idea is the to automatise the proof as
much as possible.
-/

example (xs ys : List α) (f : α → β) : map f (xs ++ ys) = (map f xs) ++ (map f ys) := by
  induction xs with
  | nil => simp [map]
  | cons x xs' ih => simp [map]; exact ih

/-
This version is much more compact! `simp` does the hard work of find the appropriate lemmas and
rewrite them. Because `map` is a user defined function, we add it to the list using `simp [map]`.

However, we could add `map` to the simplification database permanently by marking it with the
`@[simp]` attribute on its definition.
-/

@[simp] def map' (f : α → β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x :: xs' => f x :: map' f xs'

example (xs ys : List α) (f : α → β) : map' f (xs ++ ys) = (map' f xs) ++ (map' f ys) := by
  induction xs with
  | nil => simp
  | cons x xs' ih => simp; exact ih

/-
`simp` doesn't need to be everything "magical". In fact, there is a version of `simp` that exposes
its internal decisions. When ever you want to see which lemmas and definitions `simp` is using, you
can use `simp?` instead. It reports the exact list of lemmas it used as a `simp only [...]` turning
what was previously a black box into an explicit rewrite list.
-/

example (xs ys : List α) (f : α → β) : map' f (xs ++ ys) = (map' f xs) ++ (map' f ys) := by
  induction xs with
  | nil => simp?
  | cons x xs' ih => simp?; exact ih

/-
## Omega
The `omega` is "the ultimate" tactic for solving goals involving linear arithmetic of natural and
integer numbers. It uses Presburger arithmetic to close goals involving:
* Addition and subtraction of natural and integer numbers.
* Multiplication by constants.
* Inequalities involving the above operations.
* Logical connectives such as `and`, `or`, and `not`.
* Some support to division and modulo operations.
* Contradictions arising from the above operations.

It cannot handle non-linear arithmetic like multiplication of two variables or exponentiation. And
it cannot also reason about arithmetic over rationals and real numbers.

To see a practical example of `omega` in action, let's go back the file `01_logic.lean` where we
discussed even and odd numbers.
-/

def Even (n : Nat) := ∃ k : Nat, n = 2*k
def Odd (n : Nat) := ∃ k : Nat, n = 2*k + 1

example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n
  intro h
  obtain ⟨he, ho⟩ := h
  obtain ⟨k, hk⟩ := he
  obtain ⟨l, hl⟩ := ho
  have hfalse : 0 = 1 := calc
    0 = n % 2 := by
      rw [hk, Nat.mul_mod_right]
    _ = 1 := by
      rw [hl, Nat.add_mod, Nat.mul_mod_right, Nat.one_mod]
  contradiction

/-
In the original proof above, we claimed that we had to manually prove the
contradiction because the compiler could not infer it by itself.

However, `omega` can see we have two conflicting hypotheses about the parity of `n`,
    hk : n = 2*k
    hl : n = 2*l + 1

`omega` can, therefore, use these hypotheses to automatically derive a contradiction.
-/

example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n
  intro h
  obtain ⟨he, ho⟩ := h
  obtain ⟨k, hk⟩ := he
  obtain ⟨l, hl⟩ := ho
  omega

/-
Here it's worth a digression to mention the use of `intro` and `obtain` can also be "optimized" by
combining them into a single pattern match. `intro` can, in fact, introduce multiple variables and
hypotheses at once. `obtain` can destructure nested patterns in a single step.
-/

example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n h
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := h
  omega

/-
That is way more compact that our original proof. The reason we didn't do that before was to avoid
the question "how this magic works?" arises. Here we can use all those techniques because we are
sure about what they are trying to do behind curtains.

Now, let's see and example where the things really get messy and where we can appreciate the power
of automation.

We could call it the "distributivity of modulo over increment" lemma.
-/

example (a b : Nat) (hb : 0 < b) (h : a % b ≠ b - 1) : (a + 1) % b = a % b + 1 := by
  have hadd : (a + 1) % b = (a % b + 1) % b := by rw [Nat.mod_add_mod]
  have hdef : a % b < b := Nat.mod_lt a hb
  have hlt : a % b + 1 < b := by
    have hle : a % b + 1 ≤ b := Nat.le_of_pred_lt hdef
    have h1 : 1 ≤ b := Nat.le_of_pred_lt hb
    have hne : a % b + 1 ≠ b := by
      intro hcontra
      dsimp at h
      rw [← Nat.add_right_cancel_iff (n := 1), Nat.sub_add_cancel h1] at h
      exact h hcontra
    exact Nat.lt_of_le_of_ne hle hne
  rw [hadd, Nat.mod_eq_of_lt hlt]

/-
Confusing, I know.

The trick here is to show that `(a + 1) % b` is equal to `(a % b + 1) % b`. Then, from the
definition of module, `x % y < y`, we can conclude that `(a % b + 1) % b = a % b + 1` when
`a % b + 1 < b`.

From the module definition, we can immediately to prove that `a % b < b`. From the definition of
`<`, we can then show that `a % b + 1 ≤ b` since `x < y → x + 1 ≤ y`. Then, from the hypothesis
`a % b ≠ b - 1`, we can conclude that `a % b + 1 ≠ b`, which is the most complicated step in the
proof. Finally, we can prove that `a % b + 1 < b`.

But notice how all those steps are simple arithmetic manipulations of inequalities and
contradictions, which is exactly the kind of reasoning `omega` was designed to automate.
-/

example (a b : Nat) (hb : 0 < b) (h : a % b ≠ b - 1) : (a + 1) % b = a % b + 1 := by
  have hadd : (a + 1) % b = (a % b + 1) % b := by simp
  have hdef : a % b < b := Nat.mod_lt a hb
  have hlt : a % b + 1 < b := by omega  -- uses hdef and h
  rw [hadd, Nat.mod_eq_of_lt hlt]

/-
Much cleaner and easier to follow than the previous manual proof, isn't it?

# Summary
Here we have seen how real automation can simplify proofs. Obviously, there is a
lot more. But the goal here was to illustrate how using `simp` and `omega` can
make proofs much more concise and, now that the magic was revealed, easier to
follow.
-/
