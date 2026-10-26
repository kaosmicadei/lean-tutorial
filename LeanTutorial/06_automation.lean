/-
> 🚨*Disclaimer*🚨 This file was written following the literate programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

As a reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.
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


example (xs ys : List α) (f : α → β) : map f (xs ++ ys) = (map f xs) ++ (map f ys) := by
  induction xs with
  | nil => simp [map]
  | cons x xs' ih => simp [map]; exact ih

@[simp] def map' (f : α → β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x :: xs' => f x :: map' f xs'

example (xs ys : List α) (f : α → β) : map' f (xs ++ ys) = (map' f xs) ++ (map' f ys) := by
  induction xs with
  | nil => simp
  | cons x xs' ih => simp; exact ih

def Even (n : Nat) := ∃ k : Nat, n = 2*k
def Odd (n : Nat) := ∃ k : Nat, n = 2*k + 1

example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n
  intro h
  obtain ⟨he, ho⟩ := h
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

example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n
  intro h
  obtain ⟨he, ho⟩ := h
  obtain ⟨k, hk⟩ := he
  obtain ⟨l, hl⟩ := ho
  omega

example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n h
  rcases h with ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  omega

example (a b : Nat) (hb : 0 < b) (h : a % b ≠ b - 1) : (a + 1) % b = a % b + 1 := by
  have hdef : a % b < b := Nat.mod_lt a hb
  have hlt : a % b + 1 < b := by
    have hle : a % b + 1 ≤ b := Nat.le_of_pred_lt hdef
    have h1 : 1 ≤ b := Nat.le_of_pred_lt hb
    have hne : a % b + 1 ≠ b := by
      intro hcontra
      apply h
      rw [← Nat.add_left_cancel_iff (n := 1), Nat.add_sub_cancel' h1, Nat.add_comm]
      exact hcontra
    exact Nat.lt_of_le_of_ne hle hne
  have hadd : (a + 1) % b = (a % b + 1) % b := by simp?
  rw [hadd, Nat.mod_eq_of_lt hlt]

example (a b : Nat) (hb : 0 < b) (h : a % b ≠ b - 1) : (a + 1) % b = a % b + 1 := by
  have hdef : a % b < b := Nat.mod_lt a hb
  have hlt : a % b + 1 < b := by omega
  have hadd : (a + 1) % b = (a % b + 1) % b := by simp?
  rw [hadd, Nat.mod_eq_of_lt hlt]
