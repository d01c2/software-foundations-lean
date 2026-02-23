import SoftwareFoundations.Logic

/-!
# IndProp: Inductively Defined Propositions

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html>
-/

/-!
We have now seen many ways of writing propositions, including
conjunction, disjunction, and existential quantification. In this
chapter, we bring yet another tool into the mix: _inductively defined
propositions_.

To begin, some examples...
-/

-- =====================================================================
-- # Inductively Defined Propositions
-- =====================================================================

-- ## Example: The Collatz Conjecture

/-!
The _Collatz Conjecture_ is a famous open problem in number theory.

Its statement is quite simple. First, we define a function `csf` on
numbers, as follows (where `csf` stands for "Collatz step function"):
-/

def div2 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | .succ (.succ n) => .succ (div2 n)

def csf (n : Nat) : Nat :=
  if even n then div2 n
  else (3 * n) + 1

#eval csf 12  -- 6
#eval csf 6   -- 3
#eval csf 3   -- 10

/-!
Next, we look at what happens when we repeatedly apply `csf` to some
given starting number. For example, `csf 12` is `6`, and `csf 6` is
`3`, so by repeatedly applying `csf` we get the sequence
`12, 6, 3, 10, 5, 16, 8, 4, 2, 1`.

Similarly, if we start with `19`, we get the longer sequence
`19, 58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16,
8, 4, 2, 1`.

Both of these sequences eventually reach `1`. The question posed by
Collatz was: Is the sequence starting from _any_ positive natural
number guaranteed to reach `1` eventually?
-/

/-!
To formalize this question in Lean, we might try to define a recursive
_function_ that calculates the total number of steps that it takes for
such a sequence to reach `1`. But Lean's termination checker would
reject it, since the argument to the recursive call, `csf n`, is not
"obviously smaller" than `n`.

Indeed, this isn't just a pointless limitation: functions in Lean are
required to be total, to ensure logical consistency. Moreover, we
can't fix it by devising a more clever termination checker: deciding
whether this particular function is total would be equivalent to
settling the Collatz conjecture!
-/

/-!
Fortunately, there is another way: We can express the concept "reaches
`1` eventually in the Collatz sequence" as an _inductively defined
property_ of numbers. Intuitively, this property is defined by a set
of rules:

                  ------------------- (chfOne)
                  CollatzHoldsFor 1

     even n = true      CollatzHoldsFor (div2 n)
     --------------------------------------------- (chfEven)
                     CollatzHoldsFor n

     even n = false    CollatzHoldsFor ((3 * n) + 1)
     ------------------------------------------------- (chfOdd)
                    CollatzHoldsFor n
-/

inductive CollatzHoldsFor : Nat → Prop where
  | chfOne : CollatzHoldsFor 1
  | chfEven (n : Nat) : even n = true →
      CollatzHoldsFor (div2 n) → CollatzHoldsFor n
  | chfOdd (n : Nat) : even n = false →
      CollatzHoldsFor ((3 * n) + 1) → CollatzHoldsFor n

/-!
This definition says there are three ways to prove that a number `n`
eventually reaches `1` in the Collatz sequence:
- `n` is `1`;
- `n` is even and `div2 n` eventually reaches `1`;
- `n` is odd and `(3 * n) + 1` eventually reaches `1`.
-/

-- For particular numbers, we can prove that the Collatz sequence
-- reaches `1`:
example : CollatzHoldsFor 12 := by
  apply CollatzHoldsFor.chfEven; rfl; simp [div2]
  apply CollatzHoldsFor.chfEven; rfl; simp [div2]
  apply CollatzHoldsFor.chfOdd; rfl; simp [div2]
  apply CollatzHoldsFor.chfEven; rfl; simp [div2]
  apply CollatzHoldsFor.chfOdd; rfl; simp [div2]
  apply CollatzHoldsFor.chfEven; rfl; simp [div2]
  apply CollatzHoldsFor.chfEven; rfl; simp [div2]
  apply CollatzHoldsFor.chfEven; rfl; simp [div2]
  apply CollatzHoldsFor.chfEven; rfl; simp [div2]
  exact CollatzHoldsFor.chfOne

/-!
The Collatz conjecture then states that the sequence beginning from
_any_ positive number reaches `1`:
-/

-- If you succeed in proving this, you've got a bright future as a
-- number theorist! But don't spend too long on it — it's been open
-- since 1937.
axiom collatz : ∀ n, n ≠ 0 → CollatzHoldsFor n

-- =====================================================================
-- ## Example: Binary Relation for Comparing Numbers
-- =====================================================================

/-!
A binary _relation_ on a set `X` has type `X → X → Prop`. This is a
family of propositions parameterized by two elements of `X` — i.e., a
proposition about pairs of elements of `X`.

For example, one familiar binary relation on `Nat` is `le`, the
less-than-or-equal-to relation, which can be inductively defined by
two rules:

                           ------ (le_n)
                           le n n

                           le n m
                         ---------- (le_S)
                         le n (S m)

These rules say that there are two ways to show that a number is less
than or equal to another: either observe that they are the same
number, or, if the second has the form `m + 1`, give evidence that
the first is less than or equal to `m`.
-/

namespace LePlayground

  inductive Le : Nat → Nat → Prop where
    | le_n (n : Nat) : Le n n
    | le_S (n m : Nat) : Le n m → Le n (.succ m)

  -- This definition is simpler and more elegant than the boolean
  -- function `leb` we defined in Basics.

  example : Le 3 5 :=
    .le_S _ _ (.le_S _ _ (.le_n _))

end LePlayground

-- =====================================================================
-- ## Example: Transitive Closure
-- =====================================================================

/-!
The _transitive closure_ of a relation `R` is the smallest relation
that contains `R` and that is transitive. It can be defined by the
following two rules:

                     R x y
                ---------------- (tStep)
                ClosTrans R x y

       ClosTrans R x y    ClosTrans R y z
       ------------------------------------ (tTrans)
                ClosTrans R x z
-/

inductive ClosTrans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | tStep (x y : X) : R x y → ClosTrans R x y
  | tTrans (x y z : X) : ClosTrans R x y → ClosTrans R y z →
      ClosTrans R x z

-- For example, suppose we define a "parent of" relation on a group
-- of people:

inductive Person where | sage | cleo | ridley | moss

inductive ParentOf : Person → Person → Prop where
  | poSC : ParentOf .sage .cleo
  | poSR : ParentOf .sage .ridley
  | poCM : ParentOf .cleo .moss

-- `sage` is a parent of both `cleo` and `ridley`; and `cleo` is a
-- parent of `moss`.

-- The `ParentOf` relation is not transitive, but we can define an
-- "ancestor of" relation as its transitive closure:

def ancestorOf : Person → Person → Prop :=
  ClosTrans ParentOf

example : ancestorOf .sage .moss :=
  .tTrans _ .cleo _
    (.tStep _ _ .poSC)
    (.tStep _ _ .poCM)

-- =====================================================================
-- ## Example: Reflexive and Transitive Closure
-- =====================================================================

/-!
The _reflexive and transitive closure_ of a relation `R` is the
smallest relation that contains `R` and that is reflexive and
transitive. It can be defined by three rules:

                        R x y
                --------------------- (rtStep)
                ClosReflTrans R x y

                --------------------- (rtRefl)
                ClosReflTrans R x x

     ClosReflTrans R x y    ClosReflTrans R y z
     ---------------------------------------------- (rtTrans)
                ClosReflTrans R x z
-/

inductive ClosReflTrans {X : Type} (R : X → X → Prop) :
    X → X → Prop where
  | rtStep (x y : X) : R x y → ClosReflTrans R x y
  | rtRefl (x : X) : ClosReflTrans R x x
  | rtTrans (x y z : X) : ClosReflTrans R x y →
      ClosReflTrans R y z → ClosReflTrans R x z

-- This enables an equivalent definition of the Collatz conjecture.
-- First we define a binary relation corresponding to `csf`:

def cs (n m : Nat) : Prop := csf n = m

-- This Collatz step relation can be used with the reflexive and
-- transitive closure to define a "Collatz multi-step" relation:

def cms (n m : Nat) : Prop := ClosReflTrans cs n m

axiom collatz' : ∀ n, n ≠ 0 → cms n 1

/-!
#### Exercise: 1 star, standard, optional (clos_refl_trans_sym)

How would you modify the `ClosReflTrans` definition above so as to
define the reflexive, symmetric, and transitive closure?
-/

-- FILL IN HERE (informal answer)

-- =====================================================================
-- ## Example: Permutations
-- =====================================================================

/-!
The familiar mathematical concept of _permutation_ also has an
elegant formulation as an inductive relation. For simplicity, let's
focus on permutations of lists with exactly three elements.
-/

inductive Perm3 {X : Type} : List X → List X → Prop where
  | perm3Swap12 (a b c : X) : Perm3 [a, b, c] [b, a, c]
  | perm3Swap23 (a b c : X) : Perm3 [a, b, c] [a, c, b]
  | perm3Trans (l1 l2 l3 : List X) :
      Perm3 l1 l2 → Perm3 l2 l3 → Perm3 l1 l3

/-!
This definition says:
- If `l2` can be obtained from `l1` by swapping the first and second
  elements, then `l2` is a permutation of `l1`.
- If `l2` can be obtained from `l1` by swapping the second and third
  elements, then `l2` is a permutation of `l1`.
- If `l2` is a permutation of `l1` and `l3` is a permutation of `l2`,
  then `l3` is a permutation of `l1`.
-/

/-!
#### Exercise: 1 star, standard, optional (perm)

According to this definition, is `[1, 2, 3]` a permutation of itself?
-/

-- FILL IN HERE (informal answer)

-- =====================================================================
-- ## Example: Evenness (yet again)
-- =====================================================================

/-!
We've already seen two ways of stating a proposition that a number `n`
is even: We can say

  (1) `even n = true` (using the recursive boolean function `even`), or

  (2) `∃ k, n = double k` (using an existential quantifier, i.e., `Even n`).

A third possibility, which we'll use as a running example in this
chapter, is to say that a number is even if we can _establish_ its
evenness from the following two rules:

                          ---- (ev0)
                          Ev 0

                          Ev n
                      ------------ (evSS)
                      Ev (n + 2)

Intuitively these rules say:
- The number `0` is even.
- If `n` is even, then `n + 2` is even.
-/

/-!
To illustrate how this new definition of evenness works, let's imagine
using it to show that `4` is even:

                           ———— (ev0)
                           Ev 0
                       ———————————— (evSS)
                           Ev 2
                   ———————————————————— (evSS)
                           Ev 4
-/

inductive Ev : Nat → Prop where
  | ev0 : Ev 0
  | evSS (n : Nat) (h : Ev n) : Ev (n + 2)

/-!
This definition is interestingly different from previous uses of
`inductive` for defining data types like `Nat` or `List`. For one
thing, we are defining not a `Type` but rather a function from `Nat`
to `Prop` — that is, a property of numbers. But what is really new is
that, because the `Nat` argument of `Ev` appears to the _right_ of
the colon on the first line, it is allowed to take _different_ values
in the types of different constructors: `0` in the type of `ev0` and
`n + 2` in the type of `evSS`. Accordingly, the type of each
constructor must be specified explicitly.

In Lean terms, the `Nat` argument is an _index_ (it varies across
constructors) rather than a _parameter_ (which would be fixed).
-/

#check Ev.ev0 -- Ev 0
#check Ev.evSS -- ∀ (n : Nat), Ev n → Ev (n + 2)

-- These evidence constructors can be used to obtain evidence for `Ev`
-- of particular numbers:

theorem ev_4 : Ev 4 := by
  apply Ev.evSS; apply Ev.evSS; exact Ev.ev0

-- Or using function application syntax:
theorem ev_4' : Ev 4 :=
  Ev.evSS 2 (Ev.evSS 0 .ev0)

-- We can also prove theorems that have hypotheses involving `Ev`.
-- Note: In Lean, `4 + n` does not reduce when `n` is a variable
-- (since `+` recurses on the second argument), so we first rewrite
-- `4 + n` to `n + 4`, which reduces to `(n + 2) + 2`.
theorem ev_plus4 (n : Nat) (h : Ev n) : Ev (4 + n) := by
  rw [show 4 + n = n + 4 from by omega]
  apply Ev.evSS; apply Ev.evSS; exact h

/-!
#### Exercise: 1 star, standard (ev_double)
-/

theorem ev_double (n : Nat) : Ev (double n) := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## Constructing Evidence for Permutations
-- =====================================================================

/-!
Similarly we can apply the evidence constructors to obtain evidence
of `Perm3 [1, 2, 3] [3, 2, 1]`:
-/

theorem perm3_rev : Perm3 [1, 2, 3] [3, 2, 1] := by
  apply Perm3.perm3Trans (l2 := [2, 3, 1])
  · apply Perm3.perm3Trans (l2 := [2, 1, 3])
    · exact Perm3.perm3Swap12 ..
    · exact Perm3.perm3Swap23 ..
  · exact Perm3.perm3Swap12 ..

-- And again using function application syntax:
theorem perm3_rev' : Perm3 [1, 2, 3] [3, 2, 1] :=
  .perm3Trans _ [2, 3, 1] _
    (.perm3Trans _ [2, 1, 3] _
      (.perm3Swap12 ..)
      (.perm3Swap23 ..))
    (.perm3Swap12 ..)

/-!
#### Exercise: 1 star, standard (Perm3)
-/

theorem perm3_ex1 : Perm3 [1, 2, 3] [2, 3, 1] := by
  /- FILL IN HERE -/ sorry

theorem perm3_refl (X : Type) (a b c : X) :
    Perm3 [a, b, c] [a, b, c] := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Using Evidence in Proofs
-- =====================================================================

/-!
Besides _constructing_ evidence that numbers are even, we can also
_destruct_ such evidence, reasoning about how it could have been
built.

Defining `Ev` with an `inductive` declaration tells Lean not only that
the constructors `ev0` and `evSS` are valid ways to build evidence
that some number is `Ev`, but also that these two constructors are the
_only_ ways to build evidence that numbers are `Ev`.

In other words, if someone gives us evidence `e` for the proposition
`Ev n`, then we know that `e` must be one of two things:
- `e = Ev.ev0` and `n = 0`, or
- `e = Ev.evSS n' e'` and `n = n' + 2`, where `e'` is evidence for
  `Ev n'`.
-/

-- =====================================================================
-- ## Destructing and Inverting Evidence
-- =====================================================================

/-!
For some proofs we may want to analyze the evidence for `Ev n`
_directly_. We can formalize the intuitive characterization above
using `cases` (or `match`) on the evidence.
-/

theorem ev_inversion (n : Nat) (h : Ev n) :
    (n = 0) ∨ (∃ n', n = n' + 2 ∧ Ev n') := by
  cases h with
  | ev0 => left; rfl
  | evSS n' h' => right; exact ⟨n', rfl, h'⟩

/-!
Facts like this are often called "inversion lemmas" because they allow
us to "invert" some given information to reason about all the
different ways it could have been derived.

Here there are two ways to prove `Ev n`, and the inversion lemma makes
this explicit.
-/

/-!
#### Exercise: 1 star, standard (le_inversion)

Let's prove a similar inversion lemma for `≤`.
-/

theorem le_inversion (n m : Nat) (h : n ≤ m) :
    (n = m) ∨ (∃ m', m = Nat.succ m' ∧ n ≤ m') := by
  /- FILL IN HERE -/ sorry

/-!
We can use the inversion lemma to help structure proofs:
-/

theorem evSS_ev (n : Nat) (h : Ev (n + 2)) : Ev n := by
  cases h with
  | evSS _ h' => exact h'

/-!
In Lean, `cases` on evidence of an indexed inductive type
automatically eliminates impossible cases and extracts the relevant
equalities.
-/

-- `cases` can detect that `Ev 1` is impossible — neither `ev0` nor
-- `evSS` can produce `Ev 1`:
theorem one_not_even : ¬ Ev 1 := by
  intro h; cases h

/-!
#### Exercise: 1 star, standard (inversion_practice)

Prove the following result using `cases`.
-/

theorem SSSSev_even (n : Nat) (h : Ev (n + 4)) : Ev n := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard (ev5_nonsense)

Prove the following result using `cases`.
-/

theorem ev5_nonsense (h : Ev 5) : 2 + 2 = 9 := by
  /- FILL IN HERE -/ sorry

/-!
The `cases` tactic does quite a bit of work. When applied to evidence
for an inductively defined proposition, it generates one subgoal per
constructor that could have produced the evidence, eliminates
impossible constructors, and substitutes any equalities implied by the
constructor's index constraints.
-/

-- Some further examples of `cases` on evidence:
theorem inversion_ex1 (n m o : Nat) (h : [n, m] = [o, o]) :
    [n] = [m] := by
  cases h; rfl

theorem inversion_ex2 (n : Nat) (h : n + 1 = 0) : 2 + 2 = 5 := by
  cases h

-- =====================================================================
-- ## Induction on Evidence
-- =====================================================================

/-!
If this story feels familiar, it is no coincidence: We encountered
similar problems in the Induction chapter when trying to use case
analysis to prove results that required induction. And once again the
solution is... induction!

The behavior of `induction` on evidence is the same as its behavior on
data: It causes Lean to generate one subgoal for each constructor that
could have been used to build that evidence, while providing an
induction hypothesis for each recursive occurrence of the property in
question.

To prove that a property of `n` holds for all even numbers (i.e.,
those for which `Ev n` holds), we can use induction on `Ev n`. This
requires us to prove two things, corresponding to the two ways in
which `Ev n` could have been constructed. If it was constructed by
`ev0`, then `n = 0` and the property must hold of `0`. If it was
constructed by `evSS`, then the evidence of `Ev n` is of the form
`evSS n' e'`, where `n = n' + 2` and `e'` is evidence for `Ev n'`.
In this case, the inductive hypothesis says that the property we are
trying to prove holds for `n'`.
-/

theorem ev_Even (n : Nat) (h : Ev n) : Even n := by
  induction h with
  | ev0 => exact ⟨0, rfl⟩
  | evSS n' _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by subst hk; rfl⟩

-- The equivalence between the second and third definitions of evenness
-- now follows.

theorem ev_Even_iff (n : Nat) : Ev n ↔ Even n := by
  constructor
  · exact ev_Even n
  · intro ⟨k, hk⟩; subst hk; exact ev_double k

/-!
As we will see in later chapters, induction on evidence is a recurring
technique across many areas — in particular for formalizing the
semantics of programming languages.

The following exercises provide simpler examples of this technique, to
help you familiarize yourself with it.
-/

/-!
#### Exercise: 2 stars, standard (ev_sum)
-/

theorem ev_sum (n m : Nat) (h1 : Ev n) (h2 : Ev m) :
    Ev (n + m) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, advanced, especially useful (ev_ev__ev)
-/

theorem ev_ev__ev (n m : Nat) (h1 : Ev (n + m)) (h2 : Ev n) :
    Ev m := by
  -- Hint: There are two pieces of evidence you could attempt to
  -- induct upon here. If one doesn't work, try the other.
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard, optional (ev_plus_plus)

This exercise can be completed without induction or case analysis.
But, you will need a clever assertion and some tedious rewriting.
Hint: Is `(n + m) + (n + p)` even?
-/

theorem ev_plus_plus (n m p : Nat) (h1 : Ev (n + m))
    (h2 : Ev (n + p)) : Ev (m + p) := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## Multiple Induction Hypotheses
-- =====================================================================

/-!
Let's say that a relation on a type `X` is _diagonal_ if it refines
the identity relation — i.e., if `R x y` implies `x = y`.
-/

def isDiagonal {X : Type} (R : X → X → Prop) :=
  ∀ x y, R x y → x = y

/-!
Now consider the following lemma about diagonal relations. The
interesting thing about the `rtTrans` case is that there are _two_
induction hypotheses — one for each recursive component.
-/

theorem closure_of_diagonal_is_diagonal (X : Type) (R : X → X → Prop)
    (hDiag : isDiagonal R) : isDiagonal (ClosReflTrans R) := by
  intro x y h
  induction h with
  | rtStep x y h => exact hDiag x y h
  | rtRefl _ => rfl
  | rtTrans _ _ _ _ _ ih1 ih2 => rw [ih1, ← ih2]

/-!
#### Exercise: 4 stars, advanced, optional (ev'_ev)

In general, there may be multiple ways of defining a property
inductively. For example, here's a (slightly contrived) alternative
definition for `Ev`:
-/

inductive Ev' : Nat → Prop where
  | ev'0 : Ev' 0
  | ev'2 : Ev' 2
  | ev'Sum (n m : Nat) : Ev' n → Ev' m → Ev' (n + m)

/-!
Prove that this definition is logically equivalent to the old one.
-/

theorem ev'_ev (n : Nat) : Ev' n ↔ Ev n := by
  /- FILL IN HERE -/ sorry

/-!
We can do similar inductive proofs on the `Perm3` relation.
-/

theorem perm3_symm (X : Type) (l1 l2 : List X) (h : Perm3 l1 l2) :
    Perm3 l2 l1 := by
  induction h with
  | perm3Swap12 => exact .perm3Swap12 ..
  | perm3Swap23 => exact .perm3Swap23 ..
  | perm3Trans _ _ _ _ _ ih1 ih2 =>
    exact .perm3Trans _ _ _ ih2 ih1

/-!
#### Exercise: 2 stars, standard (Perm3_In)
-/

theorem perm3_In (X : Type) (x : X) (l1 l2 : List X) (h : Perm3 l1 l2)
    (hIn : In x l1) : In x l2 := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard, optional (Perm3_NotIn)
-/

theorem perm3_NotIn (X : Type) (x : X) (l1 l2 : List X) (h : Perm3 l1 l2)
    (hNotIn : ¬ In x l1) : ¬ In x l2 := by
  /- FILL IN HERE -/ sorry

theorem Perm3_In (X : Type) (x : X) (l1 l2 : List X) (h : Perm3 l1 l2)
    (hIn : In x l1) : In x l2 := by
  simpa using (perm3_In X x l1 l2 h hIn)

theorem Perm3_NotIn (X : Type) (x : X) (l1 l2 : List X) (h : Perm3 l1 l2)
    (hNotIn : ¬ In x l1) : ¬ In x l2 := by
  simpa using (perm3_NotIn X x l1 l2 h hNotIn)

/-!
#### Exercise: 2 stars, standard, optional (NotPerm3)

Proving that something is NOT a permutation is quite tricky. Some of
the lemmas above, like `Perm3_In`, can be useful for this.
-/

example : ¬ Perm3 [1, 2, 3] [1, 2, 4] := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Exercising with Inductive Relations
-- =====================================================================

/-!
A proposition parameterized by a number (such as `Ev`) can be thought
of as a _property_ — i.e., it defines a subset of `Nat`, namely those
numbers for which the proposition is provable. In the same way, a
two-argument proposition can be thought of as a _relation_ — i.e., it
defines a set of pairs for which the proposition is provable.
-/

namespace Playground

  -- Just like properties, relations can be defined inductively. One
  -- useful example is the "less than or equal to" relation on numbers.

  inductive Le : Nat → Nat → Prop where
    | le_n (n : Nat) : Le n n
    | le_S (n m : Nat) (h : Le n m) : Le n (.succ m)

  scoped notation:50 n " ≤ₗ " m => Le n m

  -- Proofs of facts about `≤ₗ` using the constructors `le_n` and
  -- `le_S` follow the same patterns as proofs about `Ev`.

  theorem test_le1 : 3 ≤ₗ 3 := Le.le_n _
  theorem test_le2 : 3 ≤ₗ 6 := .le_S _ _ (.le_S _ _ (.le_S _ _ (.le_n _)))

  theorem test_le3 (h : 2 ≤ₗ 1) : 2 + 2 = 5 := by cases h; rename_i h; cases h

  -- The "strictly less than" relation can be defined in terms of `Le`:

  def Lt (n m : Nat) := Le (.succ n) m

  scoped notation:50 n " <ₗ " m => Lt n m

  -- The `≥` operation is defined in terms of `≤`:

  def Ge (m n : Nat) : Prop := Le n m

  scoped notation:50 m " ≥ₗ " n => Ge m n

end Playground

/-!
From the definition of `Le`, we can sketch the behaviors of `cases`
and `induction` on a hypothesis `h : Le e1 e2`. Doing `cases h` will
generate two cases. In the first case, `e1 = e2`, and it will replace
instances of `e2` with `e1` in the goal and context. In the second
case, `e2 = .succ n'` for some `n'` for which `Le e1 n'` holds.
Doing `induction h` will, in the second case, add the induction
hypothesis that the goal holds when `e2` is replaced with `n'`.

Here are a number of facts about the `≤` and `<` relations that we
are going to need later in the course. The proofs make good practice
exercises.
-/

/-!
#### Exercise: 3 stars, standard, especially useful (le_facts)
-/

theorem le_trans (m n o : Nat) (h1 : m ≤ n) (h2 : n ≤ o) :
    m ≤ o := by
  /- FILL IN HERE -/ sorry

theorem zero_le_n (n : Nat) : 0 ≤ n := by
  /- FILL IN HERE -/ sorry

theorem n_le_m_Sn_le_Sm (n m : Nat) (h : n ≤ m) :
    Nat.succ n ≤ Nat.succ m := by
  /- FILL IN HERE -/ sorry

theorem Sn_le_Sm_n_le_m (n m : Nat) (h : Nat.succ n ≤ Nat.succ m) :
    n ≤ m := by
  /- FILL IN HERE -/ sorry

theorem le_plus_l (a b : Nat) : a ≤ a + b := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, especially useful (plus_le_facts1)
-/

theorem plus_le (n1 n2 m : Nat) (h : n1 + n2 ≤ m) :
    n1 ≤ m ∧ n2 ≤ m := by
  /- FILL IN HERE -/ sorry

theorem plus_le_cases (n m p q : Nat) (h : n + m ≤ p + q) :
    n ≤ p ∨ m ≤ q := by
  -- Hint: May be easiest to prove by induction on `n`.
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, especially useful (plus_le_facts2)
-/

theorem plus_le_compat_l (n m p : Nat) (h : n ≤ m) :
    p + n ≤ p + m := by
  /- FILL IN HERE -/ sorry

theorem plus_le_compat_r (n m p : Nat) (h : n ≤ m) :
    n + p ≤ m + p := by
  /- FILL IN HERE -/ sorry

theorem le_plus_trans (n m p : Nat) (h : n ≤ m) :
    n ≤ m + p := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard, optional (lt_facts)
-/

theorem lt_ge_cases (n m : Nat) : n < m ∨ n ≥ m := by
  /- FILL IN HERE -/ sorry

theorem n_lt_m_n_le_m (n m : Nat) (h : n < m) : n ≤ m := by
  /- FILL IN HERE -/ sorry

theorem plus_lt (n1 n2 m : Nat) (h : n1 + n2 < m) :
    n1 < m ∧ n2 < m := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 4 stars, standard, optional (leb_le)
-/

theorem leb_complete (n m : Nat) (h : (n <=? m) = true) :
    n ≤ m := by
  /- FILL IN HERE -/ sorry

theorem leb_correct (n m : Nat) (h : n ≤ m) :
    (n <=? m) = true := by
  /- FILL IN HERE -/ sorry

-- Hint: The next two can easily be proved without using induction.

theorem leb_iff (n m : Nat) : (n <=? m) = true ↔ n ≤ m := by
  /- FILL IN HERE -/ sorry

theorem leb_true_trans (n m o : Nat) (h1 : (n <=? m) = true)
    (h2 : (m <=? o) = true) : (n <=? o) = true := by
  /- FILL IN HERE -/ sorry

namespace R

  /-!
  #### Exercise: 3 stars, standard, especially useful (R_provability)

  We can define three-place relations, four-place relations, etc., in
  just the same way as binary relations. For example, consider the
  following three-place relation on numbers:
  -/

  inductive R : Nat → Nat → Nat → Prop where
    | c1 : R 0 0 0
    | c2 (m n o : Nat) : R m n o → R (.succ m) n (.succ o)
    | c3 (m n o : Nat) : R m n o → R m (.succ n) (.succ o)
    | c4 (m n o : Nat) : R (.succ m) (.succ n) (.succ (.succ o)) → R m n o
    | c5 (m n o : Nat) : R m n o → R n m o

  /-!
  - Which of the following propositions are provable?
    - `R 1 1 2`
    - `R 2 2 6`

  - If we dropped constructor `c5` from the definition of `R`, would
    the set of provable propositions change? Briefly explain your answer.

  - If we dropped constructor `c4` from the definition of `R`, would
    the set of provable propositions change? Briefly explain your answer.
  -/

  -- FILL IN HERE (informal answer)

  /-!
  #### Exercise: 3 stars, standard, optional (R_fact)

  The relation `R` above actually encodes a familiar function. Figure
  out which function; then state and prove this equivalence in Lean.
  -/

  def fR : Nat → Nat → Nat :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  theorem R_equiv_fR (m n o : Nat) : R m n o ↔ fR m n = o := by
    /- FILL IN HERE -/ sorry

end R

/-!
#### Exercise: 4 stars, advanced (subsequence)

A list is a _subsequence_ of another list if all of the elements in
the first list occur in the same order in the second list, possibly
with some extra elements in between.

Define an inductive proposition `Subseq` on `List Nat` that captures
what it means to be a subsequence. Then prove the theorems below.
-/

inductive Subseq : List Nat → List Nat → Prop where
  /- FILL IN HERE -/

theorem subseq_refl (l : List Nat) : Subseq l l := by
  /- FILL IN HERE -/ sorry

theorem subseq_app (l1 l2 l3 : List Nat) (h : Subseq l1 l2) :
    Subseq l1 (l2 ++ l3) := by
  /- FILL IN HERE -/ sorry

theorem subseq_trans (l1 l2 l3 : List Nat)
    (h1 : Subseq l1 l2) (h2 : Subseq l2 l3) :
    Subseq l1 l3 := by
  -- Hint: be careful about what you are doing induction on and which
  -- other things need to be generalized...
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, optional (total_relation)

Define an inductive binary relation `TotalRelation` that holds
between every pair of natural numbers.
-/

inductive TotalRelation : Nat → Nat → Prop where
  /- FILL IN HERE -/

theorem total_relation_is_total (n m : Nat) :
    TotalRelation n m := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, optional (empty_relation)

Define an inductive binary relation `EmptyRelation` (on numbers) that
never holds.
-/

inductive EmptyRelation : Nat → Nat → Prop where

theorem empty_relation_is_empty (n m : Nat) :
    ¬ EmptyRelation n m := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, optional (R_provability2)

Revisit relation `R` from above and explore additional provability facts.
-/

/- FILL IN HERE -/

-- =====================================================================
-- # Case Study: Regular Expressions
-- =====================================================================

/-!
To give a better sense of the power of inductively defined
propositions, we now show how to use them to model a classic concept
in computer science: _regular expressions_.
-/

-- =====================================================================
-- ## Definitions
-- =====================================================================

/-!
Regular expressions are a natural language for describing sets of
strings. Their syntax is defined as follows:
-/

inductive RegExp (T : Type) where
  | emptySet
  | emptyStr
  | char (t : T)
  | app (r1 r2 : RegExp T)
  | union (r1 r2 : RegExp T)
  | star (r : RegExp T)

/-!
Note that this definition is _polymorphic_: Regular expressions in
`RegExp T` describe strings with characters drawn from `T` — which we
represent as _lists_ with elements from `T`.

We connect regular expressions and strings by defining when a regular
expression _matches_ some string:

- `EmptySet` does not match any string.
- `EmptyStr` matches the empty string `[]`.
- `Char x` matches the one-character string `[x]`.
- If `re1` matches `s1` and `re2` matches `s2`, then `App re1 re2`
  matches `s1 ++ s2`.
- If at least one of `re1` and `re2` matches `s`, then
  `Union re1 re2` matches `s`.
- Finally, `Star re` matches any concatenation of zero or more strings
  each of which matches `re`. In particular, `Star re` always matches
  `[]`.
-/

inductive ExpMatch {T : Type} : List T → RegExp T → Prop where
  | mEmpty : ExpMatch [] .emptyStr
  | mChar (x : T) : ExpMatch [x] (.char x)
  | mApp (s1 : List T) (re1 : RegExp T) (s2 : List T) (re2 : RegExp T) :
      ExpMatch s1 re1 → ExpMatch s2 re2 →
      ExpMatch (s1 ++ s2) (.app re1 re2)
  | mUnionL (s1 : List T) (re1 re2 : RegExp T) :
      ExpMatch s1 re1 → ExpMatch s1 (.union re1 re2)
  | mUnionR (s2 : List T) (re1 re2 : RegExp T) :
      ExpMatch s2 re2 → ExpMatch s2 (.union re1 re2)
  | mStar0 (re : RegExp T) : ExpMatch [] (.star re)
  | mStarApp (s1 s2 : List T) (re : RegExp T) :
      ExpMatch s1 re → ExpMatch s2 (.star re) →
      ExpMatch (s1 ++ s2) (.star re)

infixl:50 " =~ " => ExpMatch

-- =====================================================================
-- ## Examples
-- =====================================================================

example : [1] =~ .char 1 := .mChar 1

example : [1, 2] =~ .app (.char 1) (.char 2) :=
  .mApp [1] _ [2] _ (.mChar 1) (.mChar 2)

-- We can also show that certain strings do _not_ match a regular
-- expression by deriving a contradiction from the evidence.

/-!
We can define helper functions for writing down regular expressions.
The `regExpOfList` function constructs a regular expression that
matches exactly the string that it receives as an argument:
-/

def regExpOfList {T : Type} (l : List T) : RegExp T :=
  match l with
  | [] => .emptyStr
  | x :: l' => .app (.char x) (regExpOfList l')

example : [1, 2, 3] =~ regExpOfList [1, 2, 3] := by
  simp [regExpOfList]
  exact .mApp [1] _ [2, 3] _ (.mChar 1)
    (.mApp [2] _ [3] _ (.mChar 2)
      (.mApp [3] _ [] _ (.mChar 3) .mEmpty))

/-!
We can also prove general facts about `ExpMatch`. For instance, the
following lemma shows that every string `s` matched by `re` is also
matched by `Star re`.
-/

theorem mStar1 {T : Type} (s : List T) (re : RegExp T)
    (h : s =~ re) : s =~ .star re := by
  rw [show s = s ++ [] from by simp]
  exact .mStarApp s [] re h (.mStar0 re)

/-!
#### Exercise: 3 stars, standard (exp_match_ex1)

The following lemmas show that the intuition about matching given at
the beginning of the chapter can be obtained from the formal inductive
definition.
-/

theorem emptySet_is_empty {T : Type} (s : List T) :
    ¬ (s =~ .emptySet) := by
  /- FILL IN HERE -/ sorry

theorem mUnion' {T : Type} (s : List T) (re1 re2 : RegExp T)
    (h : s =~ re1 ∨ s =~ re2) : s =~ .union re1 re2 := by
  /- FILL IN HERE -/ sorry

/-!
The next lemma is stated in terms of the `fold` function from the
Poly chapter: If `ss : List (List T)` represents a sequence of strings
`s1, ..., sn`, then `fold List.append ss []` is the result of
concatenating them all together.
-/

theorem mStar' {T : Type} (ss : List (List T)) (re : RegExp T)
    (h : ∀ s, In s ss → s =~ re) :
    fold List.append ss [] =~ .star re := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, optional (EmptyStr_not_needed)

Show that some uses of `emptyStr` in regular-expression proofs can be
eliminated by simpler reasoning.
-/

/- FILL IN HERE -/

/-!
Since the definition of `ExpMatch` has a recursive structure, we might
expect that proofs involving regular expressions will often require
induction on evidence.

For example, suppose we want to prove the following: If a string `s`
is matched by a regular expression `re`, then all elements of `s`
must occur as character literals somewhere in `re`.

To state this, we first define a function `reChars` that lists all
characters that occur in a regular expression:
-/

def reChars {T : Type} (re : RegExp T) : List T :=
  match re with
  | .emptySet => []
  | .emptyStr => []
  | .char x => [x]
  | .app re1 re2 => reChars re1 ++ reChars re2
  | .union re1 re2 => reChars re1 ++ reChars re2
  | .star re => reChars re

-- Now, the main theorem:

theorem in_re_match {T : Type} (s : List T) (re : RegExp T) (x : T)
    (hMatch : s =~ re) (hIn : In x s) : In x (reChars re) := by
  induction hMatch with
  | mEmpty => exact hIn
  | mChar x' => exact hIn
  | mApp s1 re1 s2 re2 _ _ ih1 ih2 =>
    simp [reChars]
    rw [In_app_iff] at hIn ⊢
    cases hIn with
    | inl h => left; exact ih1 h
    | inr h => right; exact ih2 h
  | mUnionL s1 re1 re2 _ ih =>
    simp [reChars]; rw [In_app_iff]; left; exact ih hIn
  | mUnionR s2 re1 re2 _ ih =>
    simp [reChars]; rw [In_app_iff]; right; exact ih hIn
  | mStar0 => exact hIn.elim
  | mStarApp s1 s2 re _ _ ih1 ih2 =>
    simp [reChars]
    rw [In_app_iff] at hIn
    cases hIn with
    | inl h => exact ih1 h
    | inr h => exact ih2 h

/-!
#### Exercise: 4 stars, standard (re_not_empty)

Write a recursive function `reNotEmpty` that tests whether a regular
expression matches some string. Prove that your function is correct.
-/

def reNotEmpty {T : Type} (re : RegExp T) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

theorem re_not_empty_correct {T : Type} (re : RegExp T) :
    (∃ s, s =~ re) ↔ reNotEmpty re = true := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## The `remember` Tactic
-- =====================================================================

/-!
One potentially confusing feature of the `induction` tactic is that it
will let you try to perform an induction over a term that isn't
sufficiently general. The effect of this is to lose information, and
leave you unable to complete the proof.

In Lean, when performing `induction` on evidence of an indexed
inductive type whose indices are not plain variables, we can use
`generalize` to abstract those indices before performing induction.
-/

theorem star_app {T : Type} (s1 s2 : List T) (re : RegExp T)
    (h1 : s1 =~ .star re) (h2 : s2 =~ .star re) :
    s1 ++ s2 =~ .star re := by
  -- We need induction on `h1`, but its index `.star re` is not a
  -- plain variable. We first generalize the statement, then induct.
  suffices ∀ (s1 : List T) (re' : RegExp T),
      s1 =~ re' → re' = .star re → s1 ++ s2 =~ .star re from
    this s1 _ h1 rfl
  intro s1 re' h hEq
  induction h with
  | mEmpty => exact absurd hEq RegExp.noConfusion
  | mChar _ => exact absurd hEq RegExp.noConfusion
  | mApp _ _ _ _ _ _ => exact absurd hEq RegExp.noConfusion
  | mUnionL _ _ _ _ => exact absurd hEq RegExp.noConfusion
  | mUnionR _ _ _ _ => exact absurd hEq RegExp.noConfusion
  | mStar0 _ => cases hEq; simp; exact h2
  | mStarApp s1' s2' _ h1' _ _ ih2 =>
    cases hEq; simp [List.append_assoc]
    exact .mStarApp s1' (s2' ++ s2) _ h1' (ih2 rfl)

/-!
#### Exercise: 4 stars, standard, optional (exp_match_ex2)

The `mStar''` lemma below (combined with its converse, the `mStar'`
exercise above), shows that our definition of `ExpMatch` for `Star`
is equivalent to the informal one given previously.
-/

theorem mStar'' {T : Type} (s : List T) (re : RegExp T)
    (h : s =~ .star re) :
    ∃ ss : List (List T),
      s = fold List.append ss [] ∧
      ∀ s', In s' ss → s' =~ re := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## The "Weak" Pumping Lemma
-- =====================================================================

/-!
One of the first really interesting theorems in the theory of regular
expressions is the so-called _pumping lemma_, which states, informally,
that any sufficiently long string `s` matching a regular expression
`re` can be "pumped" by repeating some middle section of `s` an
arbitrary number of times to produce a new string also matching `re`.

To get started, we need to define "sufficiently long." Since we are
working in a constructive logic, we actually need to be able to
_calculate_, for each regular expression `re`, a minimum length for
strings `s` to guarantee "pumpability."
-/

namespace Pumping

  def pumpingConstant {T : Type} (re : RegExp T) : Nat :=
    match re with
    | .emptySet => 1
    | .emptyStr => 1
    | .char _ => 2
    | .app re1 re2 => pumpingConstant re1 + pumpingConstant re2
    | .union re1 re2 => pumpingConstant re1 + pumpingConstant re2
    | .star r => pumpingConstant r

  -- You may find these lemmas about the pumping constant useful when
  -- proving the pumping lemma below.

  theorem pumping_constant_ge_1 {T : Type} (re : RegExp T) :
      pumpingConstant re ≥ 1 := by
    induction re with
    | emptySet | emptyStr => exact Nat.le.refl
    | char _ => simp [pumpingConstant]
    | app re1 _ ih1 _ | union re1 _ ih1 _ => simp [pumpingConstant]; omega
    | star _ ih => exact ih

  theorem pumping_constant_0_false {T : Type} (re : RegExp T)
      (h : pumpingConstant re = 0) : False := by
    have := pumping_constant_ge_1 re; omega

  -- An auxiliary function that repeats a string (appends it to itself)
  -- some number of times:

  def napp {T : Type} (n : Nat) (l : List T) : List T :=
    match n with
    | 0 => []
    | .succ n' => l ++ napp n' l

  -- This auxiliary lemma might also be useful:

  theorem napp_plus {T : Type} (n m : Nat) (l : List T) :
      napp (n + m) l = napp n l ++ napp m l := by
    induction n with
    | zero => simp [napp]
    | succ n' ih => simp [Nat.succ_add, napp, ih, List.append_assoc]

  theorem napp_star {T : Type} (m : Nat) (s1 s2 : List T)
      (re : RegExp T) (h1 : s1 =~ re) (h2 : s2 =~ .star re) :
      napp m s1 ++ s2 =~ .star re := by
    induction m with
    | zero => simp [napp]; exact h2
    | succ m' ih =>
      simp [napp, List.append_assoc]
      exact .mStarApp s1 (napp m' s1 ++ s2) _ h1 ih

  /-!
  The (weak) pumping lemma itself says that, if `s =~ re` and if the
  length of `s` is at least the pumping constant of `re`, then `s` can
  be split into three substrings `s1 ++ s2 ++ s3` in such a way that
  `s2` can be repeated any number of times and the result, when combined
  with `s1` and `s3`, will still match `re`. Since `s2` is also
  guaranteed not to be the empty string, this gives us a (constructive!)
  way to generate strings matching `re` that are as long as we like.

  This proof is quite long, so to make it more tractable we've broken it
  up into sub-proofs. Your job is to complete the proofs of the helper
  lemmas.
  -/

  /-!
  #### Exercise: 2 stars, standard (weak_pumping_char)
  -/

  theorem weak_pumping_char {T : Type} (x : T)
      (h : pumpingConstant (.char x) ≤ [x].length) :
      ∃ s1 s2 s3 : List T,
        [x] = s1 ++ s2 ++ s3 ∧
        s2 ≠ [] ∧
        (∀ m, s1 ++ napp m s2 ++ s3 =~ .char x) := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard (weak_pumping_app)
  -/

  theorem weak_pumping_app {T : Type} (s1 s2 : List T)
      (re1 re2 : RegExp T)
      (hMatch1 : s1 =~ re1) (hMatch2 : s2 =~ re2)
      (ih1 : pumpingConstant re1 ≤ s1.length →
        ∃ s2' s3 s4 : List T,
          s1 = s2' ++ s3 ++ s4 ∧ s3 ≠ [] ∧
          (∀ m, s2' ++ napp m s3 ++ s4 =~ re1))
      (ih2 : pumpingConstant re2 ≤ s2.length →
        ∃ s1' s3 s4 : List T,
          s2 = s1' ++ s3 ++ s4 ∧ s3 ≠ [] ∧
          (∀ m, s1' ++ napp m s3 ++ s4 =~ re2))
      (hLen : pumpingConstant (.app re1 re2) ≤ (s1 ++ s2).length) :
      ∃ s0 s3 s4 : List T,
        s1 ++ s2 = s0 ++ s3 ++ s4 ∧ s3 ≠ [] ∧
        (∀ m, s0 ++ napp m s3 ++ s4 =~ .app re1 re2) := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard (weak_pumping_union_l)
  -/

  theorem weak_pumping_union_l {T : Type} (s1 : List T)
      (re1 re2 : RegExp T)
      (hMatch : s1 =~ re1)
      (ih : pumpingConstant re1 ≤ s1.length →
        ∃ s2 s3 s4 : List T,
          s1 = s2 ++ s3 ++ s4 ∧ s3 ≠ [] ∧
          (∀ m, s2 ++ napp m s3 ++ s4 =~ re1))
      (hLen : pumpingConstant (.union re1 re2) ≤ s1.length) :
      ∃ s0 s2 s3 : List T,
        s1 = s0 ++ s2 ++ s3 ∧ s2 ≠ [] ∧
        (∀ m, s0 ++ napp m s2 ++ s3 =~ .union re1 re2) := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 2 stars, standard, optional (weak_pumping_star_zero)
  -/

  /- FILL IN HERE -/

  /-!
  #### Exercise: 4 stars, standard, optional (weak_pumping_star_app)
  -/

  /- FILL IN HERE -/

  theorem weak_pumping_union_r {T : Type} (s2 : List T)
      (re1 re2 : RegExp T)
      (hMatch : s2 =~ re2)
      (ih : pumpingConstant re2 ≤ s2.length →
        ∃ s1 s3 s4 : List T,
          s2 = s1 ++ s3 ++ s4 ∧ s3 ≠ [] ∧
          (∀ m, s1 ++ napp m s3 ++ s4 =~ re2))
      (hLen : pumpingConstant (.union re1 re2) ≤ s2.length) :
      ∃ s1 s0 s3 : List T,
        s2 = s1 ++ s0 ++ s3 ∧ s0 ≠ [] ∧
        (∀ m, s1 ++ napp m s0 ++ s3 =~ .union re1 re2) := by
    -- Symmetric to the previous...
    /- FILL IN HERE -/ sorry

  theorem weak_pumping {T : Type} (re : RegExp T) (s : List T)
      (hMatch : s =~ re)
      (hLen : pumpingConstant re ≤ s.length) :
      ∃ s1 s2 s3,
        s = s1 ++ s2 ++ s3 ∧
        s2 ≠ [] ∧
        ∀ m, s1 ++ napp m s2 ++ s3 =~ re := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 5 stars, advanced, optional (pumping)

  Now here is the usual version of the pumping lemma. In addition to
  requiring that `s2 ≠ []`, it also strengthens the result to include
  the claim that `s1.length + s2.length ≤ pumpingConstant re`.
  -/

  theorem pumping {T : Type} (re : RegExp T) (s : List T)
      (hMatch : s =~ re)
      (hLen : pumpingConstant re ≤ s.length) :
      ∃ s1 s2 s3,
        s = s1 ++ s2 ++ s3 ∧
        s2 ≠ [] ∧
        s1.length + s2.length ≤ pumpingConstant re ∧
        ∀ m, s1 ++ napp m s2 ++ s3 =~ re := by
    /- FILL IN HERE -/ sorry

end Pumping

-- =====================================================================
-- # Case Study: Improving Reflection
-- =====================================================================

/-!
We've seen in the Logic chapter that we sometimes need to relate
boolean computations to statements in `Prop`. But performing this
conversion can result in tedious proof scripts. Consider the proof of
the following theorem:
-/

theorem filter_not_empty_In (n : Nat) (l : List Nat)
    (h : filter (fun x => n =? x) l ≠ []) : In n l := by
  induction l with
  | nil => simp [filter] at h
  | cons m l' ih =>
    simp only [filter] at h
    by_cases hEq : (n =? m) = true
    · rw [if_pos hEq] at h
      left; exact ((eqb_eq n m).mp hEq).symm
    · rw [if_neg hEq] at h
      right; exact ih h

/-!
We can streamline this sort of reasoning by defining an inductive
proposition that yields a better case-analysis principle for `n =? m`.
Instead of generating the assumption `(n =? m) = true`, this principle
gives us right away the assumption we really need: `n = m`.

Following the terminology introduced in Logic, we call this the
"reflection principle for equality on numbers," and we say that the
boolean `n =? m` is _reflected in_ the proposition `n = m`.
-/

inductive Reflect (P : Prop) : Bool → Prop where
  | reflectT (h : P) : Reflect P true
  | reflectF (h : ¬ P) : Reflect P false

/-!
The `Reflect` property takes two arguments: a proposition `P` and a
boolean `b`. It states that the property `P` _reflects_ (intuitively,
is equivalent to) the boolean `b`: that is, `P` holds if and only if
`b = true`.

To see this, notice that, by definition, the only way we can produce
evidence for `Reflect P true` is by showing `P` and then using the
`reflectT` constructor. If we invert this statement, this means that
we can extract evidence for `P` from a proof of `Reflect P true`.

Similarly, the only way to show `Reflect P false` is by tagging
evidence for `¬ P` with the `reflectF` constructor.
-/

-- First, the statements `P ↔ b = true` and `Reflect P b` are
-- indeed equivalent.

theorem iff_reflect (P : Prop) (b : Bool) (h : P ↔ b = true) :
    Reflect P b := by
  cases b with
  | true => exact .reflectT (h.mpr rfl)
  | false => exact .reflectF (fun hp => by exact absurd (h.mp hp) (by decide))

/-!
#### Exercise: 2 stars, standard, especially useful (reflect_iff)

Now you prove the right-to-left implication:
-/

theorem reflect_iff (P : Prop) (b : Bool) (h : Reflect P b) :
    P ↔ b = true := by
  /- FILL IN HERE -/ sorry

/-!
We can think of `Reflect` as a variant of the usual "if and only if"
connective; the advantage of `Reflect` is that, by destructing a
hypothesis or lemma of the form `Reflect P b`, we can perform case
analysis on `b` while _at the same time_ generating appropriate
hypothesis in the two branches (`P` in the first subgoal and `¬ P`
in the second).
-/

-- Let's use `Reflect` to produce a smoother proof of
-- `filter_not_empty_In`. We begin by recasting the `eqb_eq` lemma
-- in terms of `Reflect`:

theorem eqbP (n m : Nat) : Reflect (n = m) (n =? m) :=
  iff_reflect _ _ (eqb_eq n m).symm

-- The proof of `filter_not_empty_In` now goes as follows. Notice how
-- the call to `cases (eqbP n m)` simultaneously does case analysis on
-- the boolean value AND gives us the appropriate propositional hypothesis.

theorem filter_not_empty_In' (n : Nat) (l : List Nat)
    (h : filter (fun x => n =? x) l ≠ []) : In n l := by
  induction l with
  | nil => simp [filter] at h
  | cons m l' ih =>
    -- Use `generalize` to turn `(n =? m)` into a variable, enabling
    -- dependent elimination on the `Reflect` proof from `eqbP`.
    have hRefl := eqbP n m
    revert h
    generalize hb : (n =? m) = b at hRefl
    cases hRefl with
    | reflectT hEq => intro _; left; exact hEq.symm
    | reflectF hNeq =>
      intro h
      simp [filter, hb] at h
      right; exact ih h

/-!
#### Exercise: 3 stars, standard, especially useful (eqbP_practice)

Use `eqbP` as above to prove the following:
-/

def count (n : Nat) (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'

theorem eqbP_practice (n : Nat) (l : List Nat)
    (hCount : count n l = 0) : ¬ In n l := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Additional Exercises
-- =====================================================================

/-!
#### Exercise: 3 stars, standard, especially useful (nostutter_defn)

Formulating inductive definitions of properties is an important skill
you'll need in this course.

We say that a list "stutters" if it repeats the same element
consecutively. The property `Nostutter mylist` means that `mylist`
does not stutter. Formulate an inductive definition for `Nostutter`.
-/

inductive Nostutter {X : Type} : List X → Prop where
  /- FILL IN HERE -/

-- Make sure each of these tests succeeds:

example : Nostutter [3, 1, 4, 1, 5, 6] := by
  /- FILL IN HERE -/ sorry

example : Nostutter ([] : List Nat) := by
  /- FILL IN HERE -/ sorry

example : Nostutter [5] := by
  /- FILL IN HERE -/ sorry

example : ¬ Nostutter [3, 1, 1, 4] := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 4 stars, advanced (filter_challenge)

Let's prove that our definition of `filter` from the Poly chapter
matches an abstract specification.

A list `l` is an "in-order merge" of `l1` and `l2` if it contains
all the same elements as `l1` and `l2`, in the same order as `l1`
and `l2`, but possibly interleaved.

Define an inductive relation `Merge` capturing this notion, then
prove the theorem below.
-/

inductive Merge {X : Type} : List X → List X → List X → Prop where
  /- FILL IN HERE -/

theorem merge_filter {X : Type} (test : X → Bool)
    (l l1 l2 : List X) (hMerge : Merge l1 l2 l)
    (hAll1 : All (fun n => test n = true) l1)
    (hAll2 : All (fun n => test n = false) l2) :
    filter test l = l1 := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 5 stars, advanced, optional (filter_challenge_2)
-/

/- FILL IN HERE -/

/-!
#### Exercise: 4 stars, standard, optional (palindromes)

A palindrome is a sequence that reads the same backwards as forwards.

- Define an inductive proposition `Pal` on `List X` that captures
  what it means to be a palindrome. (Hint: You'll need three cases.)

- Prove `pal_app_rev` and `pal_rev`.
-/

inductive Pal {X : Type} : List X → Prop where
  /- FILL IN HERE -/

theorem pal_app_rev {X : Type} (l : List X) :
    Pal (l ++ l.reverse) := by
  /- FILL IN HERE -/ sorry

theorem pal_rev {X : Type} (l : List X) (h : Pal l) :
    l = l.reverse := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 5 stars, standard, optional (palindrome_converse)

The converse direction is significantly more difficult.
-/

theorem palindrome_converse {X : Type} (l : List X) (h : l = l.reverse) :
    Pal l := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 4 stars, advanced, optional (NoDup)

Your first task is to use `In` to define a proposition `Disjoint X l1
l2`, which should be provable exactly when `l1` and `l2` are lists
(with elements of type `X`) that have no elements in common.
-/

def Disjoint {X : Type} (l1 l2 : List X) : Prop :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

/-!
Next, use `In` to define an inductive proposition `NoDup X l`, which
should be provable exactly when `l` is a list where every member is
different from every other.
-/

inductive NoDup {X : Type} : List X → Prop where
  /- FILL IN HERE -/

/-!
Finally, state and prove one or more interesting theorems relating
`Disjoint`, `NoDup` and `++` (list append).
-/

-- FILL IN HERE

/-!
#### Exercise: 5 stars, advanced, optional (pigeonhole_principle)

The _pigeonhole principle_ states a basic fact about counting: if we
distribute more than `n` items into `n` pigeonholes, some pigeonhole
must contain at least two items.
-/

-- First prove an easy and useful lemma:

theorem in_split {X : Type} (x : X) (l : List X) (h : In x l) :
    ∃ l1 l2, l = l1 ++ x :: l2 := by
  /- FILL IN HERE -/ sorry

-- Now define a property `Repeats`:

inductive Repeats {X : Type} : List X → Prop where
  /- FILL IN HERE -/

-- The pigeonhole principle:

theorem pigeonhole_principle (hem : excludedMiddle)
    {X : Type} (l1 l2 : List X)
    (hIn : ∀ x, In x l1 → In x l2)
    (hLen : l2.length < l1.length) :
    Repeats l1 := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Extended Exercise: A Verified Regular-Expression Matcher
-- =====================================================================

/-!
We have now defined a match relation over regular expressions and
polymorphic lists. We can use such a definition to manually prove that
a given regex matches a given string, but it does not give us a
program that we can run to determine a match automatically.

We'll implement such an algorithm, and verify that its value reflects
the match relation.
-/

-- We will implement a regex matcher that matches strings represented
-- as lists of `UInt8` characters:

abbrev AString := List UInt8

/-!
The proof of correctness of the regex matcher will combine properties
of the regex-matching function with properties of the `ExpMatch`
relation. We'll go ahead and prove some of the latter now.
-/

theorem provable_equiv_true (P : Prop) (h : P) : P ↔ True :=
  ⟨fun _ => trivial, fun _ => h⟩

theorem not_equiv_false (P : Prop) (h : ¬P) : P ↔ False :=
  ⟨fun hp => absurd hp h, fun hf => hf.elim⟩

theorem null_matches_none (s : AString) :
    (s =~ .emptySet) ↔ False :=
  not_equiv_false _ (fun h => by cases h)

theorem empty_matches_eps (s : AString) :
    s =~ .emptyStr ↔ s = [] :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; exact .mEmpty⟩

theorem empty_nomatch_ne (a : UInt8) (s : AString) :
    (a :: s =~ .emptyStr) ↔ False :=
  not_equiv_false _ (fun h => by
    generalize hL : (a :: s) = l at h
    cases h
    exact absurd hL (by simp))

theorem char_eps_suffix (a : UInt8) (s : AString) :
    a :: s =~ .char a ↔ s = [] :=
  ⟨fun h => by
    generalize hL : (a :: s) = l at h
    cases h with
    | mChar c => injection hL,
   fun h => by subst h; exact .mChar a⟩

theorem app_exists (s : AString) (re0 re1 : RegExp UInt8) :
    s =~ .app re0 re1 ↔
    ∃ s0 s1, s = s0 ++ s1 ∧ s0 =~ re0 ∧ s1 =~ re1 :=
  ⟨fun h => by
    cases h with
    | mApp s0 _ s1 _ h0 h1 => exact ⟨s0, s1, rfl, h0, h1⟩,
   fun ⟨s0, s1, hs, h0, h1⟩ => by subst hs; exact .mApp s0 _ s1 _ h0 h1⟩

/-!
#### Exercise: 3 stars, standard, optional (app_ne)
-/

theorem app_ne (a : UInt8) (s : AString) (re0 re1 : RegExp UInt8) :
    a :: s =~ .app re0 re1 ↔
    ([] =~ re0 ∧ a :: s =~ re1) ∨
    ∃ s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re0 ∧ s1 =~ re1 := by
  /- FILL IN HERE -/ sorry

theorem union_disj (s : AString) (re0 re1 : RegExp UInt8) :
    s =~ .union re0 re1 ↔ s =~ re0 ∨ s =~ re1 :=
  ⟨fun h => by cases h with
    | mUnionL _ _ _ h => left; exact h
    | mUnionR _ _ _ h => right; exact h,
   fun h => by cases h with
    | inl h => exact .mUnionL _ _ _ h
    | inr h => exact .mUnionR _ _ _ h⟩

/-!
#### Exercise: 3 stars, standard, optional (star_ne)
-/

theorem star_ne (a : UInt8) (s : AString) (re : RegExp UInt8) :
    a :: s =~ .star re ↔
    ∃ s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re ∧ s1 =~ .star re := by
  /- FILL IN HERE -/ sorry

/-!
The definition of our regex matcher will include two fixpoint
functions. The first function, given regex `re`, will evaluate to a
value that reflects whether `re` matches the empty string.
-/

def reflMatchesEps (m : RegExp UInt8 → Bool) :=
  ∀ re, Reflect ([] =~ re) (m re)

/-!
#### Exercise: 2 stars, standard, optional (match_eps)

Complete the definition of `matchEps` so that it tests if a given
regex matches the empty string:
-/

def matchEps (re : RegExp UInt8) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

/-!
#### Exercise: 3 stars, standard, optional (match_eps_refl)

Now, prove that `matchEps` indeed tests if a given regex matches the
empty string.
-/

theorem match_eps_refl : reflMatchesEps matchEps := by
  /- FILL IN HERE -/ sorry

/-!
The key operation that will be performed by our regex matcher will be
to iteratively construct a sequence of regex derivatives.
-/

def isDer (re : RegExp UInt8) (a : UInt8) (re' : RegExp UInt8) :=
  ∀ s, a :: s =~ re ↔ s =~ re'

def derives (d : UInt8 → RegExp UInt8 → RegExp UInt8) :=
  ∀ a re, isDer re a (d a re)

/-!
#### Exercise: 3 stars, standard, optional (derive)

Define `derive` so that it derives strings. One natural implementation
uses `matchEps` in some cases to determine if key regex's match the
empty string.
-/

def derive (a : UInt8) (re : RegExp UInt8) : RegExp UInt8 :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

/-!
#### Exercise: 4 stars, standard, optional (derive_corr)

Prove that `derive` in fact always derives strings.
-/

theorem derive_corr : derives derive := by
  /- FILL IN HERE -/ sorry

/-!
A function `m` _matches regexes_ if, given string `s` and regex `re`,
it evaluates to a value that reflects whether `re` matches `s`.
-/

def matchesRegex (m : AString → RegExp UInt8 → Bool) : Prop :=
  ∀ (s : AString) (re : RegExp UInt8), Reflect (s =~ re) (m s re)

/-!
#### Exercise: 2 stars, standard, optional (regex_match)

Complete the definition of `regexMatch` so that it matches regexes.
-/

def regexMatch (s : AString) (re : RegExp UInt8) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

/-!
#### Exercise: 3 stars, standard, optional (regex_match_correct)

Finally, prove that `regexMatch` in fact matches regexes.
-/

theorem regex_match_correct : matchesRegex regexMatch := by
  /- FILL IN HERE -/ sorry
