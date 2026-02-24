/-!
# Basics: Functional Programming in Lean

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html>
-/

/-!
## Introduction

The _functional style_ of programming is founded on simple, everyday
mathematical intuitions: If a procedure or method has no side effects,
then all we need to understand about it is how it maps inputs to outputs
-- that is, we can think of it as just a concrete method for computing a
mathematical function.

The other sense in which functional programming is "functional" is that
it emphasizes the use of functions as _first-class_ values -- values that
can be passed as arguments to other functions, returned as results,
included in data structures, etc.

Other common features of functional languages include _algebraic data
types_ and _pattern matching_, which make it easy to construct and
manipulate rich data structures, and _polymorphic type systems_ supporting
abstraction and code reuse. Lean offers all of these features.

The first half of this chapter introduces some key elements of Lean's
functional programming language. The second half introduces some basic
_tactics_ that can be used to prove properties of programs.

**A note on proof style:** Lean encourages a mixed style where simple
proofs are written as _terms_ (direct expressions) and tactics are
reserved for more complex reasoning. We'll see both styles throughout
this chapter.

**naming convention:**
- Names of proofs of propositions (`theorem`/`lemma`) use `snake_case`
  (e.g., `add_comm`, `nat_bin_nat`).
- Names of computational terms (`def`, non-`Prop`) use `lowerCamelCase`
  (e.g., `nextWorkingDay`, `binToNat`).
- Names of types and proposition families use `UpperCamelCase`
  (e.g., `Nat`, `Bin`, `Even`).
-/

-- =====================================================================
-- # Data and Functions
-- =====================================================================

-- ## Enumerated Types

/-!
Lean ships with a rich set of built-in types (`Bool`, `Nat`, `String`,
`List`, etc.) baked into the compiler for performance. However, Lean also
provides the same powerful `inductive` mechanism for defining new data
types from scratch. To illustrate how this works, in
this course we will often re-define types ourselves rather than relying
on the standard library.
-/

-- ## Days of the Week

/-!
To see how the datatype definition mechanism works, let's start with a
very simple example. The following declaration tells Lean that we are
defining a set of data values -- a _type_.

Lean can infer `: Type`, but we write it explicitly here for clarity.
In subsequent definitions we will omit it.
-/

inductive Day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

/-!
The new type is called `Day`, and its members are `monday`, `tuesday`,
etc. Having defined `Day`, we can write functions that operate on days.

When Lean can infer the type from context, we can use _dot notation_:
`.monday` instead of `Day.monday`. This is idiomatic Lean.
-/

def nextWorkingDay (day : Day) : Day :=
  match day with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday

-- We can use `#eval` to evaluate expressions:
#eval nextWorkingDay .friday                       -- Day.monday
#eval nextWorkingDay (nextWorkingDay .saturday)  -- Day.tuesday

-- And we can record expected results as `example` assertions.
-- The proof term `rfl` checks that both sides are definitionally equal.
example : nextWorkingDay (nextWorkingDay .saturday) = .tuesday := rfl

-- ## Booleans

/-!
Lean has a built-in `Bool` type with constructors `true` and `false`.
To follow the book's spirit of building everything from scratch, we
define `MyBool` here. Later we'll switch to the built-in `Bool`.
-/

inductive MyBool where
  | true
  | false

def negb (b : MyBool) : MyBool :=
  match b with
  | .true => .false
  | .false => .true

def andb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | .true => b2
  | .false => .false

def orb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | .true => .true
  | .false => b2

-- Truth table for `orb`:
example : orb .true  .false = .true  := rfl
example : orb .false .false = .false := rfl
example : orb .false .true  = .true  := rfl
example : orb .true  .true  = .true  := rfl

-- We introduce infix notation. The number is the binding power
-- (precedence). We use `my&&`/`my||` to avoid clash with built-in
-- `&&`/`||`.
infixl:60 " my&& " => andb
infixl:55 " my|| " => orb

example : .false my|| .false my|| .true = .true := rfl

/-!
Here we use boolean `if`-`then`-`else`, where the condition must be
`Bool`. Since `MyBool` isn't the built-in `Bool`, we need to define a
coercion.

(There is also proposition-style `if h : P then ... else ...`, which
uses `Decidable P`. If you don't know typeclasses yet, skip this detail.)
-/

@[coe]
def MyBool.toBool (b : MyBool) : Bool :=
  match b with
  | .true => Bool.true
  | .false => Bool.false

instance : Coe MyBool Bool where coe := MyBool.toBool

def negb' (b : MyBool) : MyBool := if b then .false else .true
def andb' (b1 b2 : MyBool) : MyBool := if b1 then b2 else .false
def orb'  (b1 b2 : MyBool) : MyBool := if b1 then .true else b2

-- Coercion lets `MyBool` appear where `Bool` is expected (e.g. `if`):
example : (if (MyBool.true : MyBool) then MyBool.false else MyBool.true) = MyBool.false := rfl
example : negb' MyBool.true = negb MyBool.true := rfl

/-!
#### Exercise: 1 star, standard (nandb)

Remove `sorry` and complete the definition of `nandb`; then make sure
the `example` assertions pass. The function should return `.true` if
either or both of its inputs are `.false`.
-/

def nandb (b1 b2 : MyBool) : MyBool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry
example : nandb .true .false = .true :=
  /- FILL IN HERE -/ sorry
example : nandb .false .false = .true :=
  /- FILL IN HERE -/ sorry
example : nandb .false .true = .true :=
  /- FILL IN HERE -/ sorry
example : nandb .true .true = .false :=
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard (andb3)

This function should return `true` when all of its inputs are `true`,
and `false` otherwise.
-/

def andb3 (b1 b2 b3 : MyBool) : MyBool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry
example : andb3 .true .true .true = .true :=
  /- FILL IN HERE -/ sorry
example : andb3 .false .true .true = .false :=
  /- FILL IN HERE -/ sorry
example : andb3 .true .false .true = .false :=
  /- FILL IN HERE -/ sorry
example : andb3 .true .true .false = .false :=
  /- FILL IN HERE -/ sorry

-- From here on, we use Lean's built-in `Bool`.

-- ## Types

-- Every expression in Lean has a type. `#check` prints it.
#check true                     -- Bool
#check (true : Bool)
#check (not true : Bool)
#check (not : Bool → Bool)      -- function type: Bool → Bool

-- ## New Types from Old

/-!
Here is a more interesting type definition where one constructor takes
an argument:
-/

inductive RGB where
  | red
  | green
  | blue

inductive Color where
  | black
  | white
  | primary (p : RGB)

/-!
An `inductive` definition introduces a set of _constructors_ and groups
them into a named type. Constructor expressions are formed by applying a
constructor to the right number and types of arguments:
- `.red`, `.green`, `.blue` belong to `RGB`
- `.black`, `.white` belong to `Color`
- `.primary p` belongs to `Color` when `p : RGB`
-/

def monochrome (c : Color) : Bool :=
  match c with
  | .black     => true
  | .white     => true
  | .primary _ => false

-- Patterns can match on nested constructors:
def isRed (c : Color) : Bool :=
  match c with
  | .primary .red => true
  | _             => false

-- ## Namespaces

/-!
Lean's `namespace`/`end` scopes definitions. Names inside are accessed
as `Namespace.name` from outside.
-/

namespace Playground
def foo : RGB := .blue
end Playground

def foo : Bool := true

#check (Playground.foo : RGB)
#check (foo : Bool)

-- ## Tuples

namespace TuplePlayground
inductive Bit where
  | b1
  | b0

inductive Nybble where
  | bits (d0 d1 d2 d3 : Bit)

#check (Nybble.bits .b1 .b0 .b1 .b0 : Nybble)

def allZero (nb : Nybble) : Bool :=
  match nb with
  | .bits .b0 .b0 .b0 .b0 => true
  | .bits  _   _   _   _  => false

#eval allZero (Nybble.bits .b1 .b0 .b1 .b0)  -- false
#eval allZero (Nybble.bits .b0 .b0 .b0 .b0)  -- true
end TuplePlayground

-- ## Numbers

/-!
Lean has a built-in `Nat` type, but we define `NatPlayground.Nat` here
to see how it works from scratch.

Natural numbers use a _unary_ (base 1) representation: `zero` for 0, and
`succ n` for the successor of `n`.
-/

namespace NatPlayground
inductive Nat where
  | zero
  | succ (n : Nat)

-- A different encoding — names are arbitrary:
inductive OtherNat where
  | stop
  | tick (n : OtherNat)

def pred (n : Nat) : Nat :=
  match n with
  | .zero   => .zero
  | .succ n' => n'
end NatPlayground

-- From here on, we return to Lean's built-in `Nat`.
#check Nat.succ (.succ (.succ (.succ .zero)))  -- 4 : Nat
-- Dot notation: `n.succ` is `Nat.succ n`
#check Nat.zero.succ.succ.succ.succ            -- 4 : Nat

def minusTwo (n : Nat) : Nat :=
  match n with
  | 0          => 0
  | 1          => 0
  | .succ (.succ n') => n'

#eval minusTwo 4  -- 2

/-!
`Nat.succ` has type `Nat → Nat`, just like `Nat.pred` and `minusTwo`. But
there is a fundamental difference: `Nat.pred` and `minusTwo` are defined
by _computation rules_, while `Nat.succ` is just a constructor — it
doesn't compute anything, it's a way of writing down numbers.
-/

#check (Nat.succ : Nat → Nat)
#check (Nat.pred : Nat → Nat)
#check (minusTwo : Nat → Nat)

/-!
For most interesting computations involving numbers, we also need
recursion. In Lean, recursive functions are defined with the same `def`
keyword — Lean automatically checks termination.
-/

def even (n : Nat) : Bool :=
  match n with
  | 0          => true
  | 1          => false
  | .succ (.succ n') => even n'

def odd (n : Nat) : Bool := not (even n)

example : odd 1 = true  := rfl
example : odd 4 = false := rfl

namespace NatPlayground2
def plus (n m : Nat) : Nat :=
  match n with
  | .zero   => m
  | .succ n' => .succ (plus n' m)

#eval plus 3 2  -- 5

-- If two or more arguments have the same type, they can be grouped:
def mult (n m : Nat) : Nat :=
  match n with
  | .zero    => .zero
  | .succ n' => plus m (mult n' m)

example : mult 3 3 = 9 := rfl

-- We can match two expressions at once:
def minus (n m : Nat) : Nat :=
  match n, m with
  | .zero,    _        => .zero
  | .succ _,  .zero    => n
  | .succ n', .succ m' => minus n' m'
end NatPlayground2

def exp (base power : Nat) : Nat :=
  match power with
  | .zero   => .succ .zero
  | .succ p => Nat.mul base (exp base p)

/-!
#### Exercise: 1 star, standard (factorial)

    factorial(0)  =  1
    factorial(n)  =  n * factorial(n-1)     (if n>0)
-/

def factorial (n : Nat) : Nat :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry
example : factorial 3 = 6 :=
  /- FILL IN HERE -/ sorry
example : factorial 5 = Nat.mul 10 12 :=
  /- FILL IN HERE -/ sorry

-- Custom infix operators to avoid clashing with Lean's built-in `+`, `-`, `*`:
infixl:65 " my+ " => Nat.add
infixl:65 " my- " => Nat.sub
infixl:70 " my* " => Nat.mul

#check (((0 my+ 1) my+ 1) : Nat)

/-!
Even testing equality is user-definable. Here is `eqb` that tests
natural numbers for equality, yielding a `Bool`:
-/

def eqb (n m : Nat) : Bool :=
  match n, m with
  | .zero,    .zero    => true
  | .zero,    .succ _  => false
  | .succ _,  .zero    => false
  | .succ n', .succ m' => eqb n' m'

-- `leb` tests whether its first argument is ≤ (`\le`) its second:
def leb (n m : Nat) : Bool :=
  match n, m with
  | .zero,    _        => true
  | .succ _,  .zero    => false
  | .succ n', .succ m' => leb n' m'

example : leb 2 2 = true  := rfl
example : leb 2 4 = true  := rfl
example : leb 4 2 = false := rfl

infix:50 " =? " => eqb
infix:50 " <=? " => leb

example : (4 <=? 2) = false := rfl

/-!
We now have two symbols that both look like equality: `=` and `=?`.
`x = y` is a logical _proposition_ that we can prove, while `x =? y`
is a boolean _expression_ whose value we can compute.
-/

/-!
#### Exercise: 1 star, standard (ltb)

Define `ltb` in terms of previously defined functions.
-/

def ltb (n m : Nat) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

infix:50 " <? " => ltb

example : ltb 2 2 = false :=
  /- FILL IN HERE -/ sorry
example : ltb 2 4 = true :=
  /- FILL IN HERE -/ sorry
example : ltb 4 2 = false :=
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Proof by Simplification
-- =====================================================================

/-!
Each `example` so far used `rfl` (reflexivity) — both sides of the
equation evaluated to the same thing. The same approach works for more
general theorems.

In Lean, there are two main ways to write proofs:

1. **Term-mode** — the proof is a direct expression (like `rfl`, or
    `fun x => ...`). Lean is a dependently-typed language, so proofs _are_
    terms.
2. **Tactic-mode** — introduced with `by`, you give step-by-step
    instructions. Useful for complex proofs.

Idiomatic Lean uses term-mode for simple proofs and tactics when reasoning
gets complex.
-/

-- Term-mode: `rfl` is a term of type `a = a`.
example : 1 + 1 = 2 := rfl

/-!
Lean's `Nat.add` is defined by recursion on the _second_ argument:

    n + 0       = n            (by definition)
    n + (m + 1) = (n + m) + 1  (by definition)

So `n + 0 = n` holds by `rfl`, but `0 + n = n` does _not_ — it requires
the `simp` tactic. `Nat.mul` recurses on the second argument similarly.
-/

-- `0 + n = n` is NOT definitional, so `rfl` won't work; use `simp`:
theorem zero_add (n : Nat) : 0 + n = n := by simp

-- `n + 1 = succ n` IS definitional:
theorem add_one (n : Nat) : n + 1 = Nat.succ n := rfl

-- `0 * n = 0` is not definitional either:
theorem zero_mul (n : Nat) : 0 * n = 0 := by simp

-- =====================================================================
-- # Proof by Rewriting
-- =====================================================================

/-!
The following theorem talks about a specialized property that only holds
when `n = m`. The arrow `→` (type as `\r` or `\to`) is pronounced
"implies."
-/

-- Term-mode: `h ▸ rfl` substitutes using `h`, then checks reflexivity.
-- The `▸` operator (type as `\t` or `\rw`) is one of Lean's key tools
-- for rewriting in term mode.
theorem plus_id_example (n m : Nat) (h : n = m) : n + n = m + m :=
  h ▸ rfl

-- Same proof in tactic-mode with `rw` (short for "rewrite"):
theorem plus_id_example' (n m : Nat) (h : n = m) : n + n = m + m := by
  rw [h]

/-!
`rw [h]` rewrites left-to-right. `rw [← h]` rewrites right-to-left
(type `←` as `\l` or `\leftarrow`). After rewriting, `rw` automatically
closes the goal with `rfl` if both sides become definitionally equal.
-/

/-!
#### Exercise: 1 star, standard (plus_id_exercise)

Note: the theorem has _two_ hypotheses — `n = m` and `m = o`.
The quantifier `∀` can be typed as `\forall` or `\all`.
Style note: `∀ n, P n` and `(n : T) → P n` are equivalent; below we use
binders on the left of `:`.
-/

theorem plus_id_exercise (n m o : Nat) : n = m → m = o → n + m = m + o := by
  /- FILL IN HERE -/ sorry

-- We can rewrite using previously proved theorems, not just hypotheses:
#check Nat.mul_zero  -- n * 0 = 0
#check Nat.mul_succ  -- n * m.succ = n * m + n

theorem mul_zero_add_mul_zero_eq_zero (p q : Nat) : (p * 0) + (q * 0) = 0 := by
  rw [Nat.mul_zero, Nat.mul_zero]

/-!
#### Exercise: 1 star, standard (mult_n_1)

Use `Nat.mul_succ` and `Nat.mul_zero` (or `rw`/`simp`).
-/

theorem mul_one (p : Nat) : p * 1 = p := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Proof by Case Analysis
-- =====================================================================

/-!
Not everything can be proved by simplification and rewriting. When an
unknown value blocks simplification (because the function definition
matches on it), we need _case analysis_.

For example, `eqb` and `+` both match on their first argument. With an
unknown `n`, `(n + 1 =? 0)` cannot simplify. We need to consider the
cases `n = 0` and `n = succ n'` separately.

The `cases` tactic does exactly this:
-/

-- Using `cases` with the `<;>` combinator (applies tactic to all goals):
theorem add_one_neq_zero (n : Nat) : (n + 1 =? 0) = false := by
  cases n <;> rfl

/-!
`cases` generates one subgoal per constructor. In each subgoal, `n` is
replaced by the constructor, enabling further simplification.

For finite types like `Bool`, you can prove goals manually (with
pattern matching or `cases`) or use the `decide` tactic, which
exhaustively checks all cases automatically:
-/

-- Term-mode proof using pattern matching:
theorem not_involutive (b : Bool) : not (not b) = b :=
  match b with
  | true  => rfl
  | false => rfl

-- Tactic proof with `cases` + `<;>` (applies rfl to all goals):
theorem not_involutive' (b : Bool) : not (not b) = b := by
  cases b <;> rfl

-- `decide` exhaustively checks all cases. It needs a closed proposition
-- (no free variables), so we first prove a `∀` (`\forall`/`\all`) theorem
-- in `h`, then instantiate it with `b`.
theorem not_involutive'' (b : Bool) : not (not b) = b := by
  have h : ∀ b : Bool, not (not b) = b := by decide
  exact h b

/-!
**Lean note on `decide`:** `decide` works for any `Decidable` proposition
over finite types. It's very convenient for `Bool` theorems but cannot
handle universally quantified statements over infinite types like `Nat`
— for those, you need `cases` or `induction`.

The `·` (middle dot, type as `\.` or `\cdot`) is Lean's bullet marker
for focusing on subgoals. You can also use `next =>` or the `with` syntax:
-/

theorem and_commutative (b c : Bool) : and b c = and c b := by
  cases b
  · cases c <;> rfl    -- b = false: both subcases by rfl
  · cases c <;> rfl    -- b = true:  both subcases by rfl

-- Or simply:
theorem and_commutative' (b c : Bool) : and b c = and c b := by
  cases b <;> cases c <;> rfl

-- Or by exhaustive decision (prove a closed `∀` proposition in `h`,
-- then apply it to the local variables):
theorem and_commutative'' (b c : Bool) : and b c = and c b := by
  have h : ∀ b c : Bool, and b c = and c b := by decide
  exact h b c

theorem and3_exchange (b c d : Bool) :
    and (and b c) d = and (and b d) c := by
  cases b <;> cases c <;> cases d <;> rfl

/-!
#### Exercise: 2 stars, standard (andb_true_elim2)

Hint: You will need to `cases` both booleans. Simplifying hypotheses
(with `simp at h`) before the second `cases` can help.
-/

theorem and_true_elim2 (b c : Bool) : and b c = true → c = true := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard (zero_nbeq_add_one)
-/

theorem zero_nbeq_add_one (n : Nat) : (0 =? n + 1) = false := by
  /- FILL IN HERE -/ sorry

/-!
## Structural Recursion (Optional)

In Lean, every `def` is checked for termination automatically. The
compiler uses structural recursion analysis by default, and you can
provide hints via `termination_by` when the automatic analysis needs help.
-/

/-!
#### Exercise: 2 stars, standard, optional (decreasing)

Write a terminating recursive definition that Lean rejects because its
structural recursion checker cannot see a decreasing argument.
-/

/- FILL IN HERE -/

-- =====================================================================
-- # More Exercises
-- =====================================================================

-- ## Warmups

/-!
#### Exercise: 1 star, standard (identity_fn_applied_twice)
-/

theorem identity_fn_applied_twice (f : Bool → Bool) :
    (∀ x, f x = x) → (b : Bool) → f (f b) = b := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard (negation_fn_applied_twice)

State and prove a theorem similar to the above, but where the hypothesis
says that `f x = not x`.
-/

/- FILL IN HERE -/

/-!
#### Exercise: 3 stars, standard, optional (andb_eq_orb)

Hint: You will probably need both `cases` and `rw`.
-/

theorem andb_eq_orb (b c : Bool) : (and b c = or b c) → b = c := by
  /- FILL IN HERE -/ sorry

-- ## Course Late Policies, Formalized

/-!
We model a grading policy where a student's letter grade is lowered if
they submit too many homework assignments late.
-/

namespace LateDays

inductive Letter where
  | a | b | c | d | f

inductive Modifier where
  | plus | natural | minus

inductive Grade where
  | grade (l : Letter) (m : Modifier)

inductive Comparison where
  | eq | lt | gt

/-!
We define comparison by matching two values simultaneously. We can also
use `|` in patterns to match several possibilities at once:
`.c, .a | .c, .b` matches both `(.c, .a)` and `(.c, .b)`.
-/

def letterComparison (l1 l2 : Letter) : Comparison :=
  match l1, l2 with
  | .a, .a                             => .eq
  | .a, _                              => .gt
  | .b, .a                             => .lt
  | .b, .b                             => .eq
  | .b, _                              => .gt
  | .c, .a | .c, .b                    => .lt
  | .c, .c                             => .eq
  | .c, _                              => .gt
  | .d, .a | .d, .b | .d, .c          => .lt
  | .d, .d                             => .eq
  | .d, _                              => .gt
  | .f, .a | .f, .b | .f, .c | .f, .d => .lt
  | .f, .f                             => .eq

#eval letterComparison .b .a  -- .lt
#eval letterComparison .d .d  -- .eq
#eval letterComparison .b .f  -- .gt

/-!
#### Exercise: 1 star, standard (letter_comparison)

Prove that `letterComparison l l = .eq` for all `l`.
-/

theorem letter_comparison_eq (l : Letter) : letterComparison l l = .eq := by
  /- FILL IN HERE -/ sorry

def modifierComparison (m1 m2 : Modifier) : Comparison :=
  match m1, m2 with
  | .plus, .plus                     => .eq
  | .plus, _                         => .gt
  | .natural, .plus                  => .lt
  | .natural, .natural               => .eq
  | .natural, _                      => .gt
  | .minus, .plus | .minus, .natural => .lt
  | .minus, _                        => .eq

/-!
#### Exercise: 2 stars, standard (grade_comparison)

Use lexicographic ordering: compare letters first, then modifiers only
when letters are equal.

Hint: Match `g1` and `g2`, then do case analysis on the result of
`letterComparison` to get just 3 possibilities.
-/

def gradeComparison (g1 g2 : Grade) : Comparison :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : gradeComparison (.grade .a .minus) (.grade .b .plus) = .gt :=
  /- FILL IN HERE -/ sorry
example : gradeComparison (.grade .a .minus) (.grade .a .plus) = .lt :=
  /- FILL IN HERE -/ sorry
example : gradeComparison (.grade .f .plus) (.grade .f .plus) = .eq :=
  /- FILL IN HERE -/ sorry
example : gradeComparison (.grade .b .minus) (.grade .c .plus) = .gt :=
  /- FILL IN HERE -/ sorry

def lowerLetter (l : Letter) : Letter :=
  match l with
  | .a => .b
  | .b => .c
  | .c => .d
  | .d => .f
  | .f => .f  -- Can't go lower than F!

/-!
We might expect that lowering always produces a _lower_ letter. But
this isn't provable — the edge case of lowering `.f` returns `.f`
itself, so `letterComparison (lowerLetter .f) .f = .lt` is false.
-/

theorem lower_letter_f_is_f : lowerLetter .f = .f := rfl

/-!
#### Exercise: 2 stars, standard (lower_letter_lowers)

With the extra hypothesis ruling out `.f`, the theorem becomes provable.
-/

theorem lower_letter_lowers (l : Letter) :
    letterComparison .f l = .lt →
    letterComparison (lowerLetter l) l = .lt := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard (lower_grade)

Define `lowerGrade` to lower a grade by one step (unless already
`Grade.grade .f .minus`).

Hint: Use nested pattern matching on the modifier. The outer match
should consider only the modifier. Do _not_ enumerate all cases.
Our solution is under 10 lines.
-/

def lowerGrade (g : Grade) : Grade :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : lowerGrade (.grade .a .plus) = (.grade .a .natural) :=
  /- FILL IN HERE -/ sorry
example : lowerGrade (.grade .a .natural) = (.grade .a .minus) :=
  /- FILL IN HERE -/ sorry
example : lowerGrade (.grade .a .minus) = (.grade .b .plus) :=
  /- FILL IN HERE -/ sorry
example : lowerGrade (.grade .b .plus) = (.grade .b .natural) :=
  /- FILL IN HERE -/ sorry
example : lowerGrade (.grade .f .natural) = (.grade .f .minus) :=
  /- FILL IN HERE -/ sorry
example : lowerGrade (lowerGrade (.grade .b .minus)) = (.grade .c .natural) :=
  /- FILL IN HERE -/ sorry
example : lowerGrade (lowerGrade (lowerGrade (.grade .b .minus))) = (.grade .c .minus) :=
  /- FILL IN HERE -/ sorry

theorem lower_grade_f_minus :
    lowerGrade (.grade .f .minus) = (.grade .f .minus) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard (lower_grade_lowers)

Prove that `lowerGrade` indeed lowers the grade (as long as it starts
above F-). Judicious use of `cases` with rewriting is better than
destructing everything.
-/

theorem lower_grade_lowers (g : Grade) :
    gradeComparison (.grade .f .minus) g = .lt →
    gradeComparison (lowerGrade g) g = .lt := by
  /- FILL IN HERE -/ sorry

/-!
The late-days policy:

    # late days     penalty
      0  - 8        no penalty
      9  - 16       lower by one step
      17 - 20       lower by two steps
        >= 21       lower by three steps
-/

def applyLatePolicy (lateDays : Nat) (g : Grade) : Grade :=
  if lateDays <? 9 then g
  else if lateDays <? 17 then lowerGrade g
  else if lateDays <? 21 then lowerGrade (lowerGrade g)
  else lowerGrade (lowerGrade (lowerGrade g))

-- This unfold lemma lets us `rw` to expose the definition's body:
theorem apply_late_policy_unfold (lateDays : Nat) (g : Grade) :
    applyLatePolicy lateDays g
    = if lateDays <? 9 then g
      else if lateDays <? 17 then lowerGrade g
      else if lateDays <? 21 then lowerGrade (lowerGrade g)
      else lowerGrade (lowerGrade (lowerGrade g))
  := rfl

/-!
#### Exercise: 2 stars, standard (no_penalty_for_mostly_on_time)

Hint: use `rw [apply_late_policy_unfold]` then `rw` with the hypothesis.
-/

theorem no_penalty_for_mostly_on_time (lateDays : Nat) (g : Grade) :
    (lateDays <? 9) = true →
    applyLatePolicy lateDays g = g := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard (grade_lowered_once)
-/

theorem grade_lowered_once (lateDays : Nat) (g : Grade) :
    (lateDays <? 9) = false →
    (lateDays <? 17) = true →
    applyLatePolicy lateDays g = lowerGrade g := by
  /- FILL IN HERE -/ sorry

end LateDays

-- ## Binary Numerals

/-!
#### Exercise: 3 stars, standard (binary)

Binary representation: a sequence of `b0` (0) and `b1` (1) constructors,
terminated by `z`. Low-order bit is on the left.

    decimal     binary               unary
      0                 z              0
      1              b1 z              1
      2          b0 (b1 z)             2
      3          b1 (b1 z)             3
      4      b0 (b0 (b1 z))            4
      5      b1 (b0 (b1 z))            5
      8  b0 (b0 (b0 (b1 z)))           8

(Comprehension check: What does `b0 z` represent?)
-/

inductive Bin where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

def incr (m : Bin) : Bin :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

def binToNat (m : Bin) : Nat :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : (incr (.b1 .z)) = .b0 (.b1 .z) :=
  /- FILL IN HERE -/ sorry
example : (incr (.b0 (.b1 .z))) = .b1 (.b1 .z) :=
  /- FILL IN HERE -/ sorry
example : (incr (.b1 (.b1 .z))) = .b0 (.b0 (.b1 .z)) :=
  /- FILL IN HERE -/ sorry
example : binToNat (.b0 (.b1 .z)) = 2 :=
  /- FILL IN HERE -/ sorry
example : binToNat (incr (.b1 .z)) = 1 + binToNat (.b1 .z) :=
  /- FILL IN HERE -/ sorry
example : binToNat (incr (incr (.b1 .z))) = 2 + binToNat (.b1 .z) :=
  /- FILL IN HERE -/ sorry
example : binToNat (.b0 (.b0 (.b0 (.b1 .z)))) = 8 :=
  /- FILL IN HERE -/ sorry
