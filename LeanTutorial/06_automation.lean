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
with some exceptions of `by trivial` and `by decide`. Those are tools that helps to close goals
"automagically".

In this file, we will explore some other automation tactics in Lean and how to make proofs more
concise and efficient. But we will not just use automation as "hey! look how smart Lean is". We will
focus on understanding how automation works and when it is appropriate to use it.

We already covered how `decide` works in the file `05_decidable.lean`. But it's worth to make a recap here.

`decide` is a tactic that can automatically determine if a boolean expression is true or false
based on its construction. For example, `decide (2 ≤ 3)` would use the construction of the order
relation on natural number, `Nat.le`, to determine that the statement is true.

`Nat.le` has two constructors: `Nat.le.refl` (`a ≤ a`) for reflexivity and `Nat.le.step`
(`a ≤ b → a ≤ b+1`) for the inductive step. `decide` uses the step first to trace back a proof that
`2 ≤ 3 → 2 ≤ 2` and then applies `Nat.le.refl` to close the goal.

## Simplifying List Proofs with `simp`
Rewrite goals may be a tedious and repetitive task. Also, it requires looking up for the appropriate lemmas and applying them in the correct order manually. Luckily for us, Lean has a smart
tactic called `simp` that can do this automatically most of the time.

`simp` uses a database of lemmas and definitions where it can look up for applicable cases for the
current goal or a particular hypothesis and use those options to simplify expressions.

Using `simp` only will try to simplify the current goal. We can also simplify an specific
hypothesis `h` in the context using `simp at h`.

Some times, `simp` cannot make progress because it doesn't have a particular lemma or definition in
its database. In those cases, we can provide the missing lemmas/definitions as arguments to `simp`, like `simp [lemma1, lemma2]`.

Let's see an example of `simp` in action by revisiting the proof of the distributivity of `map` over list append done in the file `02_recursion.lean`.
-/

def map (f : α → β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x :: xs' => f x :: map f xs'

/-
In the original proof, we moved step by step through the rewrites and constructor applications to show the distributivity of `map` over list append.
-/

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
not the intent of using a proof assistant like Lean.

The whole goal of an automated proof assistant is to... automatise the process of proving.

So, now that we have seen the magic behind the curtain, we can appreciate how `simp` can automate many of the tedious steps in proofs.
-/

example (xs ys : List α) (f : α → β) : map f (xs ++ ys) = (map f xs) ++ (map f ys) := by
  induction xs with
  | nil => simp [map]
  | cons x xs' ih => simp [map]; exact ih

/-
This version is much more compact! `simp` does the hard work of finding the appropriate lemmas to
use. But, because `map` is a user defined function, we need to pass it as an argument to `simp`
explicitly, `simp [map]`.

There is a way to add user definition to `simp` database, though. We can mark the definition with the `@[simp]` attribute. That will make the definition available to `simp` automatically.
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
Using `simp` is convenient, but, some times, we want to know exactly which lemmas and definitions
it is using. For that, `simp` has a trace version called `simp?` which shows the exact lemmas and
definitions it applied. It will show a `simp only [...]` list, that can be used, among other
things, for debugging.
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

It cannot handle non-linear arithmetic like multiplication of two variables or exponentiation.

Different than `simp` that uses a database of lemmas, `omega` reasons directly with the arithmetic
structure using the hypotheses and variables available in the context. That makes `omega` a great
way to close goals that otherwise would require tedious manual rewriting of arithmetic expressions.

Let's see a practical example of `omega` in action by revisiting the file `01_logic.lean` where we
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

Because `omega` can use any hypothesis available in the context, it can directly
derive the contradiction, `0 = 1`, using the hypotheses:
* hk : n = 2*k
* hl : n = 2*l + 1
-/

example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n
  intro h
  obtain ⟨he, ho⟩ := h
  obtain ⟨k, hk⟩ := he
  obtain ⟨l, hl⟩ := ho
  omega

/-
Since we are talking about making better use of automation, it's worth to make a
small digression and mention that `intro` and `obtain` can be better utilised here.

First, `intro` can introduce multiple variables and hypotheses at once, instead
of one by one. `obtain` is capable of destructuring nested patterns in a single
step.
-/

example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n h
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := h
  omega

/-
This is way more compact than our original proof. The reason we didn't used that
before was to avoid the question "how this magic works?" from arising. So, again,
once we have seen how the "magic" works, from now on we can use the more compact
forms.

Now, let's see and example where the things really get messy and where we can
appreciate the power of automation.

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

The trick here is to use the fact that if `x < y`, then `x % y = x`. But the
problem is that our `x` here is `a+1`, and we need to relate it to `a % b + 1`
somehow.

First, we use the fact that, for any three natural numbers `x`, `y`, and `z`,
we have `(x + y) % z = (x % z + y) % z`.

The next step is to show that `a % b + 1 < b`. We know from the definition of
modulo that `a % b < b`. The trick here comes from the definition of `<`, `x < y`
means `x + 1 ≤ y`. So, if we know `a % b < b`, then `a % b + 1 ≤ b`. Combining
this two we can conclude that `a % b + 1 ≤ b`. However, we need strict inequality,
`a % b + 1 < b`. Here is where our hypothesis `a % b ≠ b - 1` comes in.

From the hypothesis `h`, we can conclude that `a % b + 1 ≠ b` and, from then,
we can combine it with `a % b + 1 ≤ b` to conclude that `a % b + 1 < b`.

With all that in place we can conclude that
    `(a + 1) % b = (a % b + 1) % b = a % b + 1`

Ok, that is fine. But look at how many steps we had to go through to prove this
manually. And most of those steps just arithmetic manipulations. So, let's now
sit back and let automation handle it.
-/

example (a b : Nat) (hb : 0 < b) (h : a % b ≠ b - 1) : (a + 1) % b = a % b + 1 := by
  have hadd : (a + 1) % b = (a % b + 1) % b := by simp
  have hdef : a % b < b := Nat.mod_lt a hb
  have hlt : a % b + 1 < b := by omega  -- uses hdef and h
  rw [hadd, Nat.mod_eq_of_lt hlt]

/-
Much cleaner and easier to follow than the previous manual proof, isn't it?

The steps discussed are still there, but we let `simp` and `omega` to take care
of the repetitive middle steps for us, leaving the code focussed on the main goals.

# Summary
Here we have finally start to use Lean for automation. We saw how `simp` can
handle long simplifications and how `omega` can take care the arithmetic leaving
the main steps of the proof clean and easy to follow.

Now, there is on last question: what about `trivial`? That will be discussed in
the next section where we will talk about macros.
-/
