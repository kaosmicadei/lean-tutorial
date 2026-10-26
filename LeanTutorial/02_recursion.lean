/-
> 🚨*Disclaimer*🚨 This file was written following the literate programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

As a reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.

As a functional programming language, Lean uses recursion to perform loops. The difference with
other functional programming languages is that Lean doesn't rely on simple termination case when
compiling a recursive function. The Lean compiler requires a proof that the recursion always
terminates. For that reason, the compiler relies on two types of recursion: structural recursion and well-founded recursion.


# Structural Recursion
A structural recursion is when a variable (or variables) are getting smaller with each recursive call, ensuring termination. One example of structural recursion is the Fibonacci function.
-/

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-
Here, the compiler can infer that: 1) the variable `n` has a lower bound (zero) and 2) it decreases with each recursive call.

A common use for structural recursion is to define functions over inductive data types, such as lists and trees.
-/

def map (f : α → β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x :: xs' => f x :: map f xs'

#eval map (· * 2) [1, 2, 3]  -- [2, 4, 6]


def fold (f : β → α → β) (acc : β) (xs : List α) : β :=
  match xs with
  | [] => acc
  | x :: xs' => fold f (f acc x) xs'

#eval fold (· + ·) 0 [1, 2, 3]  -- 6

/-
In the example above, the compiler can, in each call of `map` or `fold`, the argument `xs` is structurally smaller than in the previous call until it reaches the nil case, ensuring termination.

# Well-Founded Recursion
With non-structural recursion, we have two options. Either we add the `partial` keyword to the definition and tell the compiler "trust me, I know I'm doing"; or we provide a termination proof using well-founded recursion.

As an example of well-founded recursion, let's look at the Euclidean algorithm for computing the greatest common divisor (GCD).
-/

def gcd (a b : Nat) : Nat :=
  if _h : b = 0 then
    a
  else
    gcd b (a % b)
termination_by b
decreasing_by
  have h1 : 0 < b := Nat.pos_iff_ne_zero.mpr _h
  have h2 : a % b < b := Nat.mod_lt a h1
  exact h2

/-
Here, the problem is that that is no explicit base case. It uses `b = 0` but there is no guarantee
the second argument, `b` decreasing.

Yes, in every call of `gcd`, the second argument is being called using `a % b`, is is strictly smaller that `b`. But the compiler cannot infer that on its own.

So first, we need to tell the compiler which argument is responsible for the termination. In this
case, the second argument `b`. Then we need to provide a proof of why `b` is decreasing. And the
proof goes as follows:
* Because `b` is a natural number, when `b ≠ 0` we have `b > 0`.
* The modulo operation `a % b` always produces a result that is strictly less than `b`.
* Therefore, in the recursive call `gcd b (a % b)`, the second argument `a % b` is strictly smaller
  than `b`, ensuring termination.

That is a bit more verbose than a recursive function in other languages? Definitely! But the
benefit is that the compiler can now verify termination, ensuring that our function is total and
safe to use.

# Proofs involving structural recursion
That is quite easy. At this point the reader is already used to proofs with natural numbers using
`case ... with` and `induction ... with` constructs. But those tools can do much more than just handle natural numbers. They can also handle structural recursion on lists and other inductive types.

As a first example, let's consider the proof of the associativity of the `map` function on lists.
This is another way to say the `map` function preserves the order of elements in the list.q
-/

theorem map_assoc (xs ys : List α) (f : α → β) : map f (xs ++ ys) = (map f xs) ++ (map f ys) := by
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
The proof above was verbose on purpose so the reader can see each step of the proof clearly. In
practice a simpl `simp [map]` would be enough.

The point here is to illustration how the proof works with a recursive function like `map`.

In the case when `xs = []`, the term `map f xs` gets replaced by `[]` (following the definition of
`map`) and the term `xs ++ ys` gets replaced by `[] ++ ys` (following the definition of `++`). That
reaches a trivial equality, `map f ys = map f ys`.

When `xs = x :: xs'`, the term `map f (xs ++ ys)` gets replaced by `f x :: map f (xs' ++ ys)`
(following the definition of `map` and `++`). The term `(map f xs) ++ (map f ys)` gets replaced by
`f x :: (map f xs' ++ map f ys)` (also following the definition of `map`).

That means we have `f x :: map f (xs' ++ ys) = f x :: (map f xs' ++ map f ys)`.

By the injectivity of the `::` constructor, two lists `(x :: xs)` and `(y :: ys)` are equal if and
only if `x = y` and `xs = ys`. That means the equality is also verified recursively for the tail of
the list. How the compiler doesn't get crazy with that? Simple... Induction hypothesis!

At this point, the goal reduces to `f x = f x ∧ map f (xs' ++ ys) = (map f xs' ++ map f ys)`. By
breaking the goal into its two components using the `constructor` tactic, the first goal,
`f x = f x`, is trivially true, and the second goal `map f (xs' ++ ys) = (map f xs' ++ map f ys)`
is exactly the induction hypothesis. That is enough to the compiler to conclude the proof.

Now, let's see how this pattern applies to other recursive functions, such as `fold` by proving the
associativity of `fold`.
-/

theorem fold_assoc (f : β → α → β) (acc : β) (xs ys : List α) :
  fold f acc (xs ++ ys) = fold f (fold f acc xs) ys := by
  induction xs generalizing acc with
  | nil =>
    rw [List.nil_append, fold]
  | cons x xs' ih =>
    rw [List.cons_append, fold, fold]
    specialize ih (f acc x)
    exact ih

/-
Here we see something new compared to the `map` example. The induction hypothesis needs to
generalise the accumulator `acc`. Why? Glad that you asked.

When we use the induction over `xs`, when `xs = []`, the definition of `++` and `fold` both reduce
the goal to `fold f acc ys = fold f acc ys`.

However, when `xs = x :: xs'`, the term `fold f acc (xs ++ ys)` gets replaced by
`fold f (f acc x) (xs' ++ ys)` and the term `fold f (fold f acc (x :: xs')) ys` gets replaced by
`fold f (fold f (f acc x) xs') ys`.

The problems with that is the induction hypothesis, without the generalisation, is:

    ih : fold f acc (xs' ++ ys) = fold f (fold f acc xs') ys

Here the compiler doesn't know how to match the accumulator `acc` in the induction hypothesis with
the term `f acc x` in the goal.

But when we add the `generalizing acc` clause to the induction, the induction hypothesis becomes:

    ih : ∀ acc, fold f acc (xs' ++ ys) = fold f (fold f acc xs') ys

And now we can point that the generic `acc` is in fact `f acc x` using the `specialize` tactic.

Actually, it compiler now could infer by it itself without the need for the `specialize` tactic, but
the idea here was to show the step-by-step reasoning so the reader could see how the generalization
and specialization work.
-/
