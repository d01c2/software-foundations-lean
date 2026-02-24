import SoftwareFoundations.Tactics

/-!
# Logic: Logic in Lean

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html>
-/

/-!
We have now seen many examples of factual claims (_propositions_) and
ways of presenting evidence of their truth (_proofs_). In particular,
we have worked extensively with equality propositions (`e1 = e2`),
implications (`P → Q`), and universally quantified propositions
(`∀ x, P`). In this chapter, we will see how Lean can be used to
carry out other familiar forms of logical reasoning.

Before diving into details, let's talk about the status of
mathematical statements in Lean. Lean is a _typed_ language, which
means that every sensible expression has an associated type. Logical
claims are no exception: any statement we might try to prove in Lean
has a type, namely `Prop`, the type of _propositions_.
-/

#check (∀ n m : Nat, n + m = m + n : Prop)

/-!
All syntactically well-formed propositions have type `Prop`,
regardless of whether they are true or not.

Simply _being_ a proposition is one thing; being _provable_ is
a different thing!
-/

#check (2 = 2 : Prop)
#check (3 = 2 : Prop)
#check (∀ n : Nat, n = 2 : Prop)

/-!
Indeed, propositions are _first-class_ entities that can be
manipulated in all the same ways as any of the other things in Lean's
world.

So far, we've seen one primary place where propositions can appear:
in `theorem` (and `example`) declarations.
-/

theorem plus_2_2_is_4 : 2 + 2 = 4 := rfl

/-!
But propositions can be used in other ways. For example, we can give
a name to a proposition using a `def`, just as we give names to other
kinds of expressions.
-/

def plusClaim : Prop := 2 + 2 = 4
#check (plusClaim : Prop)

-- We can later use this name as the claim in a `theorem` declaration:
theorem plus_claim_is_true : plusClaim := rfl

/-!
We can also write _parameterized_ propositions — that is, functions
that take arguments of some type and return a proposition.

For instance, the following function takes a number and returns a
proposition asserting that this number is equal to three:
-/

def isThree (n : Nat) : Prop := n = 3
#check (isThree : Nat → Prop)

/-!
In Lean, functions that return propositions are said to define
_properties_ of their arguments.

For instance, here's a (polymorphic) property defining the familiar
notion of an _injective function_.
-/

def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

theorem succ_inj : Injective Nat.succ := by
  intro x y h
  exact Nat.succ.inj h

/-!
The equality operator `=` is a (binary) function that returns a
`Prop`. The expression `n = m` is syntactic sugar for `@Eq Nat n m`.
Because `Eq` can be used with elements of any type, it is
polymorphic:
-/

#check @Eq  -- {α : Sort u} → α → α → Prop

-- =====================================================================
-- # Logical Connectives
-- =====================================================================

-- ## Conjunction

/-!
The _conjunction_, or _logical and_, of propositions `A` and `B` is
written `A ∧ B`; it represents the claim that both `A` and `B` are
true.
-/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  constructor
  · rfl
  · rfl

/-!
The `constructor` tactic generates two subgoals, one for each part of
the conjunction. Lean also provides the anonymous constructor syntax
`⟨_, _⟩` for building conjunction proofs directly in term mode:
-/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := ⟨rfl, rfl⟩

/-!
For any propositions `A` and `B`, if we have proofs of each, we can
combine them into a proof of `A ∧ B` using `And.intro` (or the
anonymous `⟨_, _⟩` syntax):
-/

#check @And.intro  -- {a b : Prop} → a → b → a ∧ b

/-!
Since applying a theorem with hypotheses generates as many subgoals
as there are hypotheses, we can apply `And.intro` to achieve the
same effect as `constructor`.
-/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  · rfl
  · rfl

/-!
#### Exercise: 2 stars, standard (plus_is_O)
-/

theorem plus_is_O : ∀ n m : Nat, n + m = 0 → n = 0 ∧ m = 0 := by
  /- FILL IN HERE -/ sorry

/-!
So much for proving conjunctive statements. To go in the other
direction — i.e., to _use_ a conjunctive hypothesis to help prove
something else — we can destructure it.

When the context contains a hypothesis `h : A ∧ B`, writing
`obtain ⟨ha, hb⟩ := h` (or pattern matching in `intro`) splits `h`
into two hypotheses: `ha : A` and `hb : B`.
-/

theorem and_example2 (n m : Nat) (h : n = 0 ∧ m = 0) : n + m = 0 := by
  obtain ⟨hn, hm⟩ := h
  rw [hn, hm]

-- We can also destructure right in the `intro`:
theorem and_example2' (n m : Nat) (h : n = 0 ∧ m = 0) : n + m = 0 := by
  rw [h.left, h.right]

/-!
You may wonder why we bothered packing the two hypotheses `n = 0`
and `m = 0` into a single conjunction, since we could also have
stated the theorem with two separate premises:
-/

theorem and_example2'' (n m : Nat) (hn : n = 0) (hm : m = 0) :
    n + m = 0 := by
  rw [hn, hm]

/-!
For this specific theorem, both formulations are fine. But it's
important to understand how to work with conjunctive hypotheses
because conjunctions often arise from intermediate steps in proofs.
Here's a simple example:
-/

-- This proof uses `plus_is_O` proved above. (It also works with `omega`.)
-- Since `plus_is_O` is left as an exercise, we prove it directly here.
theorem and_example3 (n m : Nat) (h : n + m = 0) : n * m = 0 := by
  cases n with
  | zero => simp
  | succ n' => simp at h

/-!
Another common situation is that we know `A ∧ B` but in some context
we need just `A` or just `B`. The projections `.left` and `.right`
(or `.1` and `.2`) extract each component:
-/

theorem proj1 (P Q : Prop) (h : P ∧ Q) : P := h.left

/-!
#### Exercise: 1 star, standard, optional (proj2)
-/

theorem proj2 (P Q : Prop) (h : P ∧ Q) : Q := by
  /- FILL IN HERE -/ sorry

/-!
Finally, we sometimes need to rearrange the order of conjunctions
and/or the grouping of multi-way conjunctions.
-/

theorem and_commut (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩

/-!
#### Exercise: 1 star, standard (and_assoc)

In the following proof of associativity, notice how the nested
pattern `⟨hp, hq, hr⟩` breaks the hypothesis `h : P ∧ (Q ∧ R)`
down into `hp : P`, `hq : Q`, and `hr : R`. Finish the proof.
-/

theorem and_assoc' (P Q R : Prop) (h : P ∧ (Q ∧ R)) :
    (P ∧ Q) ∧ R := by
  /- Hint: `obtain ⟨hp, hq, hr⟩ := h` destructures the hypothesis. -/
  /- FILL IN HERE -/ sorry

/-!
The infix notation `∧` is actually just syntactic sugar for
`And A B`. That is, `And` is a Lean type that takes two propositions
as arguments and yields a proposition.
-/

#check @And  -- Prop → Prop → Prop

-- ## Disjunction

/-!
Another important connective is the _disjunction_, or _logical or_,
of two propositions: `A ∨ B` is true when either `A` or `B` is. This
infix notation stands for `Or A B`.
-/

/-!
To use a disjunctive hypothesis in a proof, we proceed by case
analysis — which can be done with `cases` or `obtain`:
-/

theorem factor_is_O (n m : Nat) (h : n = 0 ∨ m = 0) : n * m = 0 := by
  cases h with
  | inl hn => subst hn; simp
  | inr hm => subst hm; simp

/-!
When we perform case analysis on a disjunction `A ∨ B`, we must
separately discharge two proof obligations, each showing that the
conclusion holds under a different assumption — `A` in the first
subgoal and `B` in the second.

Conversely, to show that a disjunction holds, it suffices to show
that one of its sides holds. This can be done with the `left` and
`right` tactics, or with `Or.inl` and `Or.inr` in term mode:
-/

theorem or_intro_l (A B : Prop) (ha : A) : A ∨ B :=
  Or.inl ha

theorem zero_or_succ (n : Nat) : n = 0 ∨ n = Nat.succ (Nat.pred n) := by
  cases n with
  | zero => left; rfl
  | succ n' => right; rfl

/-!
#### Exercise: 2 stars, standard (mult_is_O)
-/

theorem mult_is_O : ∀ n m : Nat, n * m = 0 → n = 0 ∨ m = 0 := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard (or_commut)
-/

theorem or_commut : ∀ P Q : Prop, P ∨ Q → Q ∨ P := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## Falsehood and Negation
-- =====================================================================

/-!
Up to this point, we have mostly been concerned with proving
"positive" statements — addition is commutative, appending lists is
associative, etc. We are sometimes also interested in negative
results, demonstrating that some proposition is _not_ true. Such
statements are expressed with the logical negation operator `¬`.

To see how negation works, recall the _principle of explosion_,
which asserts that, if we assume a contradiction, then any other
proposition can be derived.

Following this intuition, we could define `¬ P` ("not `P`") as
`∀ Q, P → Q`.

Lean actually makes an equivalent but slightly different choice,
defining `¬ P` as `P → False`, where `False` is a specific
un-provable proposition.
-/

namespace NotPlayground
  def not (P : Prop) := P → False

  #check (not : Prop → Prop)
end NotPlayground

/-!
Since `False` is a contradictory proposition, the principle of
explosion also applies to it. If we can get `False` into the context,
we can use `False.elim` (or the `exact absurd` tactic) to complete
any goal:
-/

theorem ex_falso_quodlibet (P : Prop) (h : False) : P :=
  h.elim

/-!
The Latin _ex falso quodlibet_ means, literally, "from falsehood
follows whatever you like"; this is another common name for the
principle of explosion.
-/

/-!
#### Exercise: 2 stars, standard, optional (not_implies_our_not)

Show that Lean's definition of negation implies the intuitive one
mentioned above.

Hint: `unfold Not` near the beginning may help while getting
accustomed to Lean's definition of `Not`.
-/

theorem not_implies_our_not (P : Prop) (h : ¬P) :
    ∀ (Q : Prop), P → Q := by
  /- FILL IN HERE -/ sorry

/-!
Inequality is a very common form of negated statement, so there is a
special notation for it: `x ≠ y` is defined as `¬(x = y)`.
-/

-- For example:
theorem zero_not_one : 0 ≠ 1 := by
  -- The proposition `0 ≠ 1` is exactly the same as
  -- `¬(0 = 1)` — that is, `(0 = 1) → False`.
  -- To prove it, we assume the opposite equality...
  intro contra
  -- ... and observe it's impossible (the constructors are disjoint).
  -- In Lean, `Nat.noConfusion` or `contradiction` handles this.
  exact absurd contra (by decide)

/-!
It takes a little practice to get used to working with negation in
Lean. Here are proofs of a few familiar facts to get you warmed up.
-/

theorem not_False : ¬False := fun h => h

theorem contradiction_implies_anything (P Q : Prop)
    (h : P ∧ ¬P) : Q := by
  exact absurd h.left h.right

theorem double_neg (P : Prop) (h : P) : ¬¬P :=
  fun hnp => hnp h

/-!
#### Exercise: 1 star, standard, especially useful (contrapositive)
-/

theorem contrapositive : ∀ (P Q : Prop), (P → Q) → (¬Q → ¬P) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard (not_both_true_and_false)
-/

theorem not_both_true_and_false : ∀ P : Prop, ¬(P ∧ ¬P) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard (de_morgan_not_or)

_De Morgan's Laws_, named for Augustus De Morgan, describe how
negation interacts with conjunction and disjunction. The following
law says that "the negation of a disjunction is the conjunction of
the negations." There is a dual law `de_morgan_not_and_not` to which
we will return at the end of this chapter.
-/

theorem de_morgan_not_or : ∀ (P Q : Prop), ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard, optional (not_S_inverse_pred)
-/

theorem not_S_inverse_pred : ¬(∀ n : Nat, Nat.succ (Nat.pred n) = n) := by
  /- FILL IN HERE -/ sorry

/-!
Since inequality involves a negation, it also requires a little
practice to be able to work with it fluently. Here is one useful
trick.

If you are trying to prove a goal that is nonsensical (e.g., the
goal state is `false = true`), use `contradiction` or `exact absurd`
to change the goal to `False`. This makes it easier to use
assumptions of the form `¬P` — in particular, assumptions of the
form `x ≠ y`.
-/

theorem not_true_is_false (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | true => exact absurd rfl h
  | false => rfl

-- Lean's `contradiction` tactic automates finding the contradiction:
theorem not_true_is_false' (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | true => contradiction
  | false => rfl

-- =====================================================================
-- ## Truth
-- =====================================================================

/-!
Besides `False`, Lean also defines `True`, a proposition that is
trivially true. To prove it, we use the constant `True.intro` (or
the `trivial` tactic):
-/

theorem True_is_true : True := trivial

/-!
`True` is used relatively rarely: it is trivial to prove as a goal,
and it provides no useful information when it appears as a
hypothesis.

However, `True` can be quite useful when defining complex `Prop`s
using conditionals or as a parameter to higher-order `Prop`s.

Let's see how we can use `True` and `False` to achieve an effect
similar to the `contradiction` tactic manually. Pattern-matching lets
us do different things for different constructors. If the result of
applying two different constructors were hypothetically equal, then
we could use `match` to convert an unprovable statement (like
`False`) to one that is provable (like `True`).
-/

def discFn (n : Nat) : Prop :=
  match n with
  | 0 => True
  | .succ _ => False

theorem disc_example (n : Nat) : ¬(0 = Nat.succ n) := by
  intro contra
  have h : discFn 0 := trivial
  rw [contra] at h
  exact h

/-!
The built-in `contradiction` tactic takes care of all this for us.
-/

/-!
#### Exercise: 2 stars, advanced, optional (nil_is_not_cons)

Use the same technique as above to show that `[] ≠ x :: xs`.
Do not use `contradiction`.
-/

theorem nil_is_not_cons {α : Type} (x : α) (xs : List α) :
    ¬([] = x :: xs) := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## Logical Equivalence
-- =====================================================================

/-!
The handy "if and only if" connective, which asserts that two
propositions have the same truth value, is the conjunction of two
implications.
-/

#check @Iff  -- Prop → Prop → Prop
#print Iff   -- structure with mp and mpr

theorem iff_sym (P Q : Prop) (h : P ↔ Q) : Q ↔ P :=
  ⟨h.mpr, h.mp⟩

theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  constructor
  · exact not_true_is_false b
  · intro h hn
    rw [h] at hn
    exact absurd hn (by decide)

/-!
We can also use `rw` with `↔` in either direction, without
explicitly thinking about the fact that it is really an `And`
underneath.
-/

theorem apply_iff_example1 (P Q R : Prop)
    (hiff : P ↔ Q) (hqr : Q → R) (hp : P) : R :=
  hqr (hiff.mp hp)

theorem apply_iff_example2 (P Q R : Prop)
    (hiff : P ↔ Q) (hpr : P → R) (hq : Q) : R :=
  hpr (hiff.mpr hq)

/-!
#### Exercise: 1 star, standard, optional (iff_properties)
-/

theorem iff_refl (P : Prop) : P ↔ P := by
  /- FILL IN HERE -/ sorry

theorem iff_trans (P Q R : Prop)
    (h1 : P ↔ Q) (h2 : Q ↔ R) : P ↔ R := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard (or_distributes_over_and)
-/

theorem or_distributes_over_and (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## Setoids and Logical Equivalence
-- =====================================================================

/-!
A "setoid" is a set equipped with an equivalence relation — that is,
a relation that is reflexive, symmetric, and transitive. When two
elements of a set are equivalent according to the relation, `rw` can
be used to replace one by the other.

We've seen this with `=` in Lean: when `x = y`, we can use `rw` to
replace `x` with `y`. Similarly, the logical equivalence `↔` is
reflexive, symmetric, and transitive, so we can use it to replace one
part of a proposition with another.

Lean's `rw` tactic works with `↔` in proposition contexts, and
`simp` can use `↔` facts as rewrite rules automatically.
-/

-- First, let's prove a couple of basic iff equivalences.
theorem mul_eq_0 (n m : Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 :=
  ⟨mult_is_O n m, factor_is_O n m⟩

theorem or_assoc' (P Q R : Prop) :
    P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inl (Or.inl h)
    | inr h =>
      cases h with
      | inl h => exact Or.inl (Or.inr h)
      | inr h => exact Or.inr h
  · intro h
    cases h with
    | inl h =>
      cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inl h)
    | inr h => exact Or.inr (Or.inr h)

/-!
We can now use these facts with `rw` and `rfl` to prove a ternary
version of the `mul_eq_0` fact above _without_ splitting the
top-level iff:
-/

theorem mul_eq_0_ternary (n m p : Nat) :
    n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  rw [mul_eq_0, mul_eq_0, or_assoc']

-- =====================================================================
-- ## Existential Quantification
-- =====================================================================

/-!
Another fundamental logical connective is _existential
quantification_. To say that there is some `x` of type `α` such
that some property `P` holds of `x`, we write `∃ x : α, P`.

To prove a statement of the form `∃ x, P`, we must show that `P`
holds for some specific choice for `x`, known as the _witness_. In
term mode, we use `⟨witness, proof⟩`:
-/

def Even (x : Nat) : Prop := ∃ n, x = double n
#check (Even : Nat → Prop)

theorem four_is_Even : Even 4 := ⟨2, rfl⟩

/-!
Conversely, if we have an existential hypothesis `∃ x, P x` in the
context, we can destructure it with `obtain` to get a witness and a
proof:
-/

theorem exists_example_2 (n : Nat) (h : ∃ m, n = 4 + m) :
    ∃ o, n = 2 + o := by
  obtain ⟨m, hm⟩ := h
  exact ⟨2 + m, by omega⟩

/-!
#### Exercise: 1 star, standard, especially useful (dist_not_exists)

Prove that "`P` holds for all `x`" implies "there is no `x` for
which `P` does not hold." (Hint: `obtain ⟨x, hx⟩ := h` works on
existential hypotheses.)
-/

theorem dist_not_exists {α : Type} (P : α → Prop)
    (h : ∀ x, P x) : ¬(∃ x, ¬P x) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard (dist_exists_or)

Prove that existential quantification distributes over disjunction.
-/

theorem dist_exists_or {α : Type} (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard, optional (leb_plus_exists)
-/

theorem leb_plus_exists : ∀ n m : Nat,
    (n <=? m) = true → ∃ x, m = n + x := by
  /- FILL IN HERE -/ sorry

theorem plus_exists_leb : ∀ n m : Nat,
    (∃ x, m = n + x) → (n <=? m) = true := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Programming with Propositions
-- =====================================================================

/-!
The logical connectives that we have seen provide a rich vocabulary
for defining complex propositions from simpler ones. To illustrate,
let's look at how to express the claim that an element `x` occurs in
a list `l`. Notice that this property has a simple recursive
structure:

- If `l` is the empty list, then `x` cannot occur in it, so the
  property "`x` appears in `l`" is simply `False`.

- Otherwise, `l` has the form `x' :: l'`. In this case, `x`
  occurs in `l` if it is equal to `x'` or it occurs in `l'`.

We can translate this directly into a recursive function taking an
element and a list and returning a proposition:
-/

def In {α : Type} (x : α) (l : List α) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x ∨ In x l'

/-!
When `In` is applied to a concrete list, it expands into a concrete
sequence of nested disjunctions.
-/

example : In 4 [1, 2, 3, 4, 5] := by
  -- unfolds to: 1 = 4 ∨ (2 = 4 ∨ (3 = 4 ∨ (4 = 4 ∨ (5 = 4 ∨ False))))
  right; right; right; left; rfl

example (n : Nat) (h : In n [2, 4]) : ∃ n', n = 2 * n' := by
  -- In n [2, 4] unfolds to: 2 = n ∨ (4 = n ∨ False)
  unfold In at h
  cases h with
  | inl h => exact ⟨1, h.symm⟩
  | inr h =>
    cases h with
    | inl h => exact ⟨2, h.symm⟩
    | inr h => exact h.elim

/-!
We can also reason about more generic statements involving `In`.
-/

theorem In_map {α β : Type} (f : α → β) (l : List α) (x : α)
    (h : In x l) : In (f x) (map f l) := by
  induction l with
  | nil => exact h
  | cons x' l' ih =>
    -- h : x' = x ∨ In x l'
    -- goal : f x' = f x ∨ In (f x) (map f l')
    unfold In at h ⊢
    simp only [map]
    cases h with
    | inl h => exact Or.inl (h ▸ rfl)
    | inr h => exact Or.inr (ih h)

/-!
#### Exercise: 2 stars, standard (In_map_iff)
-/

theorem In_map_iff {α β : Type} (f : α → β) (l : List α) (y : β) :
    In y (map f l) ↔ ∃ x, f x = y ∧ In x l := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard (In_app_iff)
-/

theorem In_app_iff {α : Type} (l l' : List α) (a : α) :
    In a (l ++ l') ↔ In a l ∨ In a l' := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard, especially useful (All)

We noted above that functions returning propositions can be seen as
_properties_ of their arguments. Drawing inspiration from `In`,
write a recursive function `All` stating that some property `P`
holds of all elements of a list `l`. To make sure your definition is
correct, prove the `All_In` theorem below.
-/

def All {α : Type} (P : α → Prop) (l : List α) : Prop :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

theorem All_In {α : Type} (P : α → Prop) (l : List α) :
    (∀ x, In x l → P x) ↔ All P l := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, optional (combine_odd_even)

Complete the definition of `combineOddEven` below. It takes as
arguments two properties of numbers, `Podd` and `Peven`, and it
should return a property `P` such that `P n` is equivalent to
`Podd n` when `n` is odd and equivalent to `Peven n` otherwise.
-/

def combineOddEven (Podd Peven : Nat → Prop) : Nat → Prop :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

theorem combine_odd_even_intro
    (Podd Peven : Nat → Prop) (n : Nat)
    (hodd : odd n = true → Podd n)
    (heven : odd n = false → Peven n) :
    combineOddEven Podd Peven n := by
  /- FILL IN HERE -/ sorry

theorem combine_odd_even_elim_odd
    (Podd Peven : Nat → Prop) (n : Nat)
    (h : combineOddEven Podd Peven n)
    (hodd : odd n = true) :
    Podd n := by
  /- FILL IN HERE -/ sorry

theorem combine_odd_even_elim_even
    (Podd Peven : Nat → Prop) (n : Nat)
    (h : combineOddEven Podd Peven n)
    (heven : odd n = false) :
    Peven n := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Applying Theorems to Arguments
-- =====================================================================

/-!
One feature that distinguishes Lean from some other proof assistants
is that it treats _proofs_ as first-class objects.

There is a great deal to be said about this, but it is not necessary
to understand it all in order to use Lean. This section gives just a
taste.

We have seen that we can use `#check` to ask Lean to print the type
of an expression. We can also use it to inspect what theorem a
particular identifier refers to:
-/

#check @Nat.add_comm  -- ∀ (n m : Nat), n + m = m + n

/-!
The statement of a theorem tells us what we can use that theorem for.
If we have a term of type `∀ n m, n = m → n + n = m + m` and we
provide it two numbers and a proof that `n = m`, we get back a proof
of `n + n = m + m`.

Operationally, by applying a theorem as if it were a function, we
can specialize its result without resorting to intermediate
assertions. For example:
-/

theorem add_comm3 (x y z : Nat) :
    x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm x]
  rw [Nat.add_comm y z]

/-!
We encountered the issue of `rw [Nat.add_comm]` applying to the
wrong occurrence. In Lean, we can guide `rw` by supplying arguments:
`rw [Nat.add_comm y z]` tells Lean to rewrite specifically the term
`y + z` into `z + y`.

Or we can use `have` to establish an intermediate fact:
-/

theorem add_comm3_take2 (x y z : Nat) :
    x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm x]
  have h : y + z = z + y := Nat.add_comm y z
  rw [h]

/-!
Here's another example of using a theorem like a function. Suppose
we have proved:
-/

theorem in_not_nil {α : Type} (x : α) (l : List α)
    (h : In x l) : l ≠ [] := by
  intro hl
  rw [hl] at h
  exact h

/-!
Note that one quantified variable (`x`) does not appear in the
conclusion (`l ≠ []`).

Intuitively, we should be able to use this theorem to prove the
special case where `x` is `42`. However, simply `apply in_not_nil`
will fail because it cannot infer the value of `x`. There are
several ways to work around this:
-/

-- A naive attempt using `apply in_not_nil` fails because Lean cannot
-- infer `x` from the goal alone:
--   theorem in_not_nil_42 (l : List Nat) (h : In 42 l) :
--       l ≠ [] := by
--     apply in_not_nil  -- ERROR: cannot synthesize `?x`

-- Supply the implicit argument explicitly:
theorem in_not_nil_42_take2 (l : List Nat) (h : In 42 l) :
    l ≠ [] :=
  in_not_nil 42 l h

-- Or apply with a named argument:
theorem in_not_nil_42_take3 (l : List Nat) (h : In 42 l) :
    l ≠ [] :=
  in_not_nil (x := 42) l h

-- Or let Lean infer from the hypothesis:
theorem in_not_nil_42_take4 (l : List Nat) (h : In 42 l) :
    l ≠ [] := by
  exact in_not_nil _ _ h

-- Or use `apply` with the hypothesis directly:
theorem in_not_nil_42_take5 (l : List Nat) (h : In 42 l) :
    l ≠ [] := by
  apply in_not_nil 42
  exact h

-- =====================================================================
-- # Working with Decidable Properties
-- =====================================================================

/-!
We've seen two different ways of expressing logical claims in Lean:
with _booleans_ (of type `Bool`), and with _propositions_ (of type
`Prop`).

Here are the key differences:

                                       Bool     Prop
                                       ====     ====
      decidable?                       yes       no
      useable with match/if?           yes       no
      works with rw tactic?            no        yes

The crucial difference is _decidability_. Every `Bool` expression
can be evaluated to `true` or `false` in finite time. By contrast,
`Prop` includes both decidable and undecidable propositions.

Since `Prop` includes _both_ decidable and undecidable properties,
we have two options when we want to formalize a property that happens
to be decidable: we can express it either as a boolean computation or
as a function into `Prop`.
-/

#eval even 42    -- true
#eval even 1001  -- false

example : even 42 = true := rfl

-- ...or there exists some `k` such that `n = double k`.
example : Even 42 := ⟨21, rfl⟩

/-!
Of course, it would be strange if these two characterizations of
evenness did not describe the same set of natural numbers.
Fortunately, they do!

To prove this, we first need two helper lemmas.
-/

theorem even_double (k : Nat) : even (double k) = true := by
  induction k with
  | zero => rfl
  | succ k' ih => simp [double, even]; exact ih

/-!
#### Exercise: 3 stars, standard (even_double_conv)
-/

theorem even_double_conv : ∀ n : Nat, ∃ k,
    n = if even n then double k else Nat.succ (double k) := by
  -- Hint: Use the `even_succ` theorem from Induction.
  /- FILL IN HERE -/ sorry

/-!
Now the main theorem:
-/

theorem even_bool_prop (n : Nat) : even n = true ↔ Even n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := even_double_conv n
    rw [h] at hk
    exact ⟨k, hk⟩
  · intro ⟨k, hk⟩
    rw [hk]
    exact even_double k

/-!
In view of this theorem, we can say that the boolean computation
`even n` is _reflected_ in the truth of the proposition
`∃ k, n = double k`.

Similarly, to state that two numbers `n` and `m` are equal, we can
say either that `n =? m` returns `true`, or that `n = m`. These two
notions are equivalent:
-/

-- `eqb_true` is an exercise (sorry) in Tactics. We provide a working
-- proof here since `eqb_eq` below needs it.
private theorem eqb_true_aux : ∀ n m : Nat, (n =? m) = true → n = m := by
  intro n
  induction n with
  | zero =>
    intro m h
    cases m with
    | zero => rfl
    | succ _ => simp [eqb] at h
  | succ n' ih =>
    intro m
    cases m with
    | zero => simp [eqb]
    | succ m' => simp [eqb]; exact ih m'

theorem eqb_eq (n1 n2 : Nat) : (n1 =? n2) = true ↔ n1 = n2 := by
  constructor
  · exact eqb_true_aux n1 n2
  · intro h; subst h; exact eqb_refl n1

/-!
### Choosing between `Bool` and `Prop`

Booleans are more useful for defining functions — there is no
effective way to _test_ whether a `Prop` is true, so we cannot
use `Prop`s in conditional expressions:
-/

-- This is rejected:
-- def isEvenPrime (n : Nat) : Bool :=
--   if n = 2 then true else false    -- error: `n = 2` is a `Prop`

-- Instead, we use a boolean equality test:
def isEvenPrime (n : Nat) : Bool :=
  if n =? 2 then true else false

#eval isEvenPrime 2  -- true
#eval isEvenPrime 3  -- false

/-!
Conversely, propositional equality is required for `rw`. Knowing
that `(n =? m) = true` is not directly useful for rewriting; but
converting it to `n = m` via `eqb_eq` lets us rewrite freely.

An important side benefit of stating facts with booleans is enabling
_proof by reflection_: computation with Lean terms.
-/

set_option maxRecDepth 2048 in
example : Even 1000 := ⟨500, rfl⟩

-- The boolean version is simpler — Lean's computation does the work:
example : even 1000 = true := rfl

-- We can combine the two via `even_bool_prop`:
example : Even 1000 := (even_bool_prop 1000).mp rfl

/-!
The negation of a boolean claim is also straightforward:
-/

example : even 1001 = false := rfl

-- The propositional version uses reflection:
example : ¬(Even 1001) := by
  intro ⟨k, hk⟩
  have : even 1001 = true := by rw [hk]; exact even_double k
  simp [even] at this

/-!
Conversely, there are situations where propositions are easier to
work with. In particular, knowing `(n =? m) = true` is of little
direct help; but converting to `n = m` lets us `rw` with it:
-/

theorem plus_eqb_example (n m p : Nat)
    (h : (n =? m) = true) : (n + p =? m + p) = true := by
  rw [eqb_eq] at h
  rw [h]
  exact eqb_refl (m + p)

/-!
#### Exercise: 2 stars, standard (logical_connectives)

The following theorems relate the propositional connectives studied
in this chapter to the corresponding boolean operations.
-/

theorem andb_true_iff (b1 b2 : Bool) :
    (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by
  /- FILL IN HERE -/ sorry

theorem orb_true_iff (b1 b2 : Bool) :
    (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard (eqb_neq)

The following theorem is an alternate "negative" formulation of
`eqb_eq` that is more convenient in certain situations.
Hint: `not_true_iff_false`.
-/

theorem eqb_neq (x y : Nat) : (x =? y) = false ↔ x ≠ y := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard (eqb_list)

Given a boolean operator `eqb` for testing equality of elements of
some type `α`, we can define a function `eqbList` for testing
equality of lists with elements in `α`.
-/

def eqbList {α : Type} (eqb : α → α → Bool)
    (l1 l2 : List α) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

theorem eqb_list_true_iff {α : Type} (eqb : α → α → Bool)
    (h : ∀ a1 a2, eqb a1 a2 = true ↔ a1 = a2)
    (l1 l2 : List α) :
    eqbList eqb l1 l2 = true ↔ l1 = l2 := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, especially useful (All_forallb)

Prove the theorem below, which relates `forallb` to the `All`
property defined above.
-/

def forallb {α : Type} (test : α → Bool) (l : List α) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

theorem forallb_true_iff {α : Type} (test : α → Bool)
    (l : List α) :
    forallb test l = true ↔ All (fun x => test x = true) l := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # The Logic of Lean
-- =====================================================================

/-!
Lean's logical core, the _Calculus of Inductive Constructions_,
differs in some important ways from other formal systems used by
mathematicians — in particular from Zermelo-Fraenkel Set Theory
(ZFC), the most popular foundation for paper-and-pencil mathematics.

We conclude this chapter with a brief discussion of some of the most
significant differences.
-/

-- =====================================================================
-- ## Functional Extensionality
-- =====================================================================

/-!
Lean's logic is quite minimalistic. This means that one occasionally
encounters cases where translating standard mathematical reasoning
into a proof assistant can be cumbersome — unless we enrich the core
logic with additional axioms.

For example, the equality assertions that we have seen so far mostly
concern elements of inductive types (`Nat`, `Bool`, etc.). But,
since `=` is polymorphic, we can write propositions claiming that
two _functions_ are equal:
-/

example : (fun x => 3 + x) = (fun x => (Nat.pred 4) + x) := rfl

/-!
This works when Lean can simplify both sides to the same expression.
But in general functions can be equal for more interesting reasons.

In common mathematical practice, two functions `f` and `g` are
considered equal if they produce the same output on every input:

    (∀ x, f x = g x) → f = g

This is known as the principle of _functional extensionality_.

Lean _supports functional extensionality out of the box_. It is
derived from Lean's quotient types (the `Quot.sound` axiom), so no
additional axioms need to be introduced. The tactic `funext`
implements this:
-/

example : (fun x => x + 1) = (fun x => 1 + x) := by
  funext x
  exact Nat.add_comm x 1

/-!
To check whether a proof relies on additional axioms, use
`#print axioms`:
-/

-- #print axioms function_equality_example
-- Shows: quot.sound (Lean's quotient axiom)

/-!
#### Exercise: 4 stars, standard (tr_rev_correct)

One problem with the definition of the list-reversing function `rev`
is that it performs a call to `++` on each step. Running `++` takes
time asymptotically linear in the size of the list, which means that
`rev` is asymptotically quadratic.

We can improve this with a tail-recursive definition:
-/

def rev {α : Type} (l : List α) : List α :=
  match l with
  | [] => []
  | x :: l' => rev l' ++ [x]

def revAppend {α : Type} (l1 l2 : List α) : List α :=
  match l1 with
  | [] => l2
  | x :: l1' => revAppend l1' (x :: l2)

def trRev {α : Type} (l : List α) : List α :=
  revAppend l []

/-!
This version of reverse is said to be _tail recursive_, because the
recursive call to the function is the last operation. A decent
compiler will generate efficient code in this case.

Prove that the two definitions are indeed equivalent. You will need
`funext`.
-/

theorem tr_rev_correct {α : Type} : @trRev α = @rev α := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## Classical vs. Constructive Logic
-- =====================================================================

/-!
We have seen that it is not possible to test whether an arbitrary
`Prop` holds while defining a Lean function. A similar restriction
applies in proofs: the following intuitive reasoning principle is not
derivable constructively:
-/

def excludedMiddle := ∀ P : Prop, P ∨ ¬P

/-!
To understand why, recall that to prove `P ∨ Q`, we must provide
either a proof of `P` or a proof of `Q`. But the universally
quantified `P` in `excludedMiddle` is arbitrary, and we don't have
enough information to choose which side holds.

However, in the special case where we happen to know that `P` is
reflected in some boolean term `b`, knowing whether it holds is
trivial:
-/

theorem restricted_excluded_middle (P : Prop) (b : Bool)
    (h : P ↔ b = true) : P ∨ ¬P := by
  cases b with
  | true => left; exact h.mpr rfl
  | false => right; intro hp; exact absurd (h.mp hp) (by decide)

-- In particular, the excluded middle is valid for `n = m`:
theorem restricted_excluded_middle_eq (n m : Nat) :
    n = m ∨ n ≠ m := by
  exact restricted_excluded_middle (n = m) (n =? m) (eqb_eq n m).symm

/-!
Lean's core logic is _constructive_: a proof of `∃ x, P x` always
includes a particular value of `x`, and a proof of `P ∨ Q` always
tells us which side holds.

Logics like Lean's are called _constructive logics_. Systems like
ZFC, where the excluded middle holds for arbitrary propositions, are
called _classical_.

That said, Lean's standard library _does_ include the law of
excluded middle as `Classical.em : ∀ (p : Prop), p ∨ ¬p`. It is
safe to use but renders proofs non-constructive. In these exercises
we work constructively.
-/

/-!
#### Exercise: 3 stars, standard (excluded_middle_irrefutable)

Proving the consistency of Lean with the general excluded middle
axiom requires complicated reasoning. However, the following theorem
implies that it is always safe to assume a decidability axiom for
any _particular_ `Prop P`. Why? Because the negation of such an
axiom leads to a contradiction.

Succinctly: for any proposition `P`,
    Lean is consistent → Lean + (`P ∨ ¬P`) is consistent.
-/

theorem excluded_middle_irrefutable (P : Prop) :
    ¬¬(P ∨ ¬P) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, advanced (not_exists_dist)

It is a theorem of classical logic that the following two assertions
are equivalent:

    ¬(∃ x, ¬P x)
    ∀ x, P x

The `dist_not_exists` theorem above proves one side. The other
direction cannot be proved constructively. Show that it is implied
by the excluded middle.
-/

theorem not_exists_dist (hem : excludedMiddle) {α : Type}
    (P : α → Prop) (h : ¬(∃ x, ¬P x)) : ∀ x, P x := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 5 stars, standard, optional (classical_axioms)

For those who like a challenge, here is an exercise adapted from
Bertot and Casteran's textbook (p. 123). Each of the following
five statements, together with `excludedMiddle`, can be considered
as characterizing classical logic. We can't prove any of them
constructively in Lean, but we can consistently add any one as an
axiom.

Prove that all six propositions are equivalent.

Hint: Rather than considering all pairs pairwise, prove a single
circular chain of implications.
-/

def peirce := ∀ P Q : Prop, ((P → Q) → P) → P

def doubleNegationElimination := ∀ P : Prop, ¬¬P → P

def deMorganNotAndNot := ∀ P Q : Prop, ¬(¬P ∧ ¬Q) → P ∨ Q

def impliesToOr := ∀ P Q : Prop, (P → Q) → (¬P ∨ Q)

def consequentiaMirabilis := ∀ P : Prop, (¬P → P) → P

-- Prove a circular chain of implications:

theorem em_implies_peirce (h : excludedMiddle) : peirce := by
  /- FILL IN HERE -/ sorry

theorem peirce_implies_dne (h : peirce) : doubleNegationElimination := by
  /- FILL IN HERE -/ sorry

theorem dne_implies_de_morgan (h : doubleNegationElimination) :
    deMorganNotAndNot := by
  /- FILL IN HERE -/ sorry

theorem de_morgan_implies_implies_to_or (h : deMorganNotAndNot) :
    impliesToOr := by
  /- FILL IN HERE -/ sorry

theorem implies_to_or_implies_cm (h : impliesToOr) :
    consequentiaMirabilis := by
  /- FILL IN HERE -/ sorry

theorem cm_implies_em (h : consequentiaMirabilis) : excludedMiddle := by
  /- FILL IN HERE -/ sorry
