import SoftwareFoundations.Poly

/-!
# Tactics: More Basic Tactics

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html>
-/

/-!
This chapter introduces several additional proof strategies and tactics
that allow us to begin proving more interesting properties of functional
programs.

We will see:
- how to use auxiliary lemmas in both "forward-" and "backward-style"
  proofs;
- how to reason about data constructors — in particular, how to use
  the fact that they are injective and disjoint;
- how to strengthen an induction hypothesis, and when such
  strengthening is required; and
- more details on how to reason by case analysis.
-/

-- =====================================================================
-- # The `apply` and `exact` Tactics
-- =====================================================================

/-!
We often encounter situations where the goal to be proved is _exactly_
the same as some hypothesis in the context or some previously proved
lemma.
-/

theorem silly1 (n m : Nat) (h : n = m) : n = m :=
  h

/-!
In tactic mode, `exact h` closes the goal when it matches hypothesis
`h` exactly. `apply h` is similar but also works when `h` is an
implication — it will replace the goal with the premise(s).
-/

theorem silly2 (n m o p : Nat)
    (h1 : n = m) (h2 : n = m → [n, o] = [m, p]) :
    [n, o] = [m, p] :=
  h2 h1

/-!
When we use `apply h` and `h` begins with universally quantified
variables, Lean tries to find appropriate values for these variables
by matching the goal against the conclusion of `h`. For example, in
the following proof, when we `apply h2`, the universal variable `q`
gets instantiated with `n` and `r` with `m`.
-/

theorem silly2a (n m : Nat)
    (h1 : (n, n) = (m, m))
    (h2 : ∀ q r : Nat, (q, q) = (r, r) → [q] = [r]) :
    [n] = [m] :=
  h2 n m h1

/-!
#### Exercise: 2 stars, standard, optional (silly_ex)

Complete the following proof using only `intro` and `exact`/`apply`.
-/

theorem silly_ex (p : Nat)
    (h1 : ∀ n, even n = true → even (n + 1) = false)
    (h2 : ∀ n, even n = false → odd n = true)
    (h3 : even p = true) :
    odd (p + 1) = true := by
  /- FILL IN HERE -/ sorry

/-!
To use `apply`, the conclusion of the fact being applied must match the
goal exactly (perhaps after simplification). `apply` will not work if
the left and right sides of the equality are swapped.
-/

theorem silly3 (n m : Nat) (h : n = m) : m = n := by
  rw [h]

/-!
We could also use `exact h.symm` in term mode or `exact h ▸ rfl` —
there are many ways to flip an equality.
-/

/-!
#### Exercise: 2 stars, standard (apply_exercise1)

You can use `apply` with previously defined theorems, not just
hypotheses in the context. Use `rev_involutive` from `Poly` as part
of your (relatively short) solution to this exercise. You do not need
`induction`.
-/

theorem rev_exercise1 {α : Type} (l l' : List α)
    (h : l = l'.reverse) : l' = l.reverse := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 1 star, standard, optional (apply_rewrite)

Briefly explain the difference between `apply`/`exact` and `rw`.

`exact h` closes the goal when `h` has exactly the goal's type.
`rw [h]` rewrites occurrences of one side of an equation `h` with
the other side. `rw` transforms the goal but doesn't close it
(unless the result is `rfl`-provable), while `exact` closes it.
Both can be useful when the goal matches a hypothesis, but `rw` is
more flexible for partial substitution, while `exact`/`apply` are
for direct use of hypotheses or lemmas.
-/

-- =====================================================================
-- # The `apply ... with` Pattern and `calc`
-- =====================================================================

/-!
The following example uses two rewrites to get from `[a, b]` to
`[e, f]`:
-/

example (a b c d e f : Nat)
    (h1 : [a, b] = [c, d]) (h2 : [c, d] = [e, f]) :
    [a, b] = [e, f] :=
  h1 ▸ h2

/-!
Since this is a common pattern, we might like to state transitivity
of equality as a reusable lemma:
-/

theorem trans_eq {α : Type} (x y z : α)
    (h1 : x = y) (h2 : y = z) : x = z :=
  h1 ▸ h2

/-!
Now we can use `trans_eq` to prove the above example. In Lean, when
Lean can infer most arguments but not all, we can supply the missing
one explicitly. Alternatively, `calc` blocks provide an elegant way
to chain equalities:
-/

example (a b c d e f : Nat)
    (h1 : [a, b] = [c, d]) (h2 : [c, d] = [e, f]) :
    [a, b] = [e, f] :=
  trans_eq _ _ _ h1 h2

-- Using `calc` for step-by-step reasoning:
example (a b c d e f : Nat)
    (h1 : [a, b] = [c, d]) (h2 : [c, d] = [e, f]) :
    [a, b] = [e, f] := calc
  [a, b] = [c, d] := h1
  _      = [e, f] := h2

/-!
Lean also has a built-in `Trans.trans` and `Eq.trans` that accomplish
the same purpose.
-/

#check @Eq.trans
#check @Trans.trans

/-!
#### Exercise: 3 stars, standard, optional (trans_eq_exercise)
-/

example (n m o p : Nat)
    (h1 : m = minusTwo o) (h2 : n + p = m) :
    n + p = minusTwo o := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # The `injection` Tactic and Constructor Properties
-- =====================================================================

/-!
Recall the definition of natural numbers:

    inductive Nat where
      | zero
      | succ (n : Nat)

It is obvious from this definition that every number has one of two
forms: either it is `zero` or it is built by applying `succ` to
another number. But there is more here than meets the eye: implicit
in the definition are two additional facts:

- The constructor `succ` is _injective_ (or _one-to-one_). That is,
  if `n + 1 = m + 1`, it must also be that `n = m`.

- The constructors `zero` and `succ` are _disjoint_. That is, `zero`
  is not equal to `n + 1` for any `n`.

Similar principles apply to every inductively defined type: all
constructors are injective, and the values built from distinct
constructors are never equal. For lists, `cons` is injective and
`[]` is different from every non-empty list. For booleans, `true`
and `false` are different.
-/

/-!
In Lean, the `Nat.succ.inj` lemma captures injectivity of `succ`.
We can also use the `omega` tactic or pattern matching to extract
this information.
-/

theorem S_injective (n m : Nat) (h : n + 1 = m + 1) : n = m := by
  omega

#check @Nat.succ.inj  -- Nat.succ.inj : n.succ = m.succ → n = m

-- Alternatively, via `Nat.succ.inj`:
theorem S_injective' (n m : Nat) (h : n + 1 = m + 1) : n = m :=
  Nat.succ.inj h

/-!
Here's a more interesting example showing how we can derive multiple
equalities from a single hypothesis about list constructors. When
`h : x :: y :: l = z :: j`, we can use `List.cons.inj` or pattern
match to extract that `x = z` and `y :: l = j`.
-/

theorem injection_ex1 (n m o : Nat)
    (h : [n, m] = [o, o]) : n = m := by
  have h1 : n = o := List.cons.inj h |>.1
  have h2 : m = o := List.cons.inj (List.cons.inj h |>.2) |>.1
  rw [h1, h2]

/-!
#### Exercise: 3 stars, standard (injection_ex3)
-/

example {α : Type} (x y z : α) (l j : List α)
    (h1 : x :: y :: l = z :: j) (h2 : j = z :: l) :
    x = y := by
  /- FILL IN HERE -/ sorry

-- ## Disjointness of Constructors

/-!
The principle of disjointness says that two terms beginning with
different constructors (like `zero` and `succ`, or `true` and
`false`) can never be equal. This means that, any time we find
ourselves in a context where we've _assumed_ that two such terms
are equal, we are justified in concluding anything we want, since
the assumption is nonsensical.

In Lean, the `contradiction` tactic (or `absurd`, `nomatch`, `nofun`)
handles this:
-/

theorem discriminate_ex1 (n m : Nat) (h : false = true) : n = m := by
  contradiction

theorem discriminate_ex2 (n : Nat) (h : n + 1 = 0) : 2 + 2 = 5 := by
  contradiction

/-!
These examples are instances of a logical principle known as the
_principle of explosion_, which asserts that a contradictory
hypothesis entails anything (even manifestly false things!).

If you find the principle of explosion confusing, remember that these
proofs are _not_ showing that the conclusion holds. Rather, they are
showing that, _if_ the nonsensical premise did somehow hold, _then_
the nonsensical conclusion would too.

We'll explore the principle of explosion in more detail in the next
chapter.
-/

/-!
#### Exercise: 1 star, standard (discriminate_ex3)
-/

example {α : Type} (x y z : α) (l j : List α)
    (h : x :: y :: l = []) : x = z := by
  /- FILL IN HERE -/ sorry

/-!
We can also use constructor disjointness to connect the boolean
equality `=?` with propositional equality `=`:
-/

theorem eqb_0_l (n : Nat) (h : (0 =? n) = true) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n' => contradiction

/-!
The injectivity of constructors allows us to reason that
`∀ n m, n + 1 = m + 1 → n = m`. The converse of this implication is
an instance of a more general fact about both constructors and
functions:
-/

theorem f_equal {α β : Type} (f : α → β) (x y : α) (h : x = y) :
    f x = f y :=
  h ▸ rfl

theorem eq_implies_succ_equal (n m : Nat) (h : n = m) :
    n + 1 = m + 1 :=
  h ▸ rfl

/-!
In tactic mode, `congr` (congruence) is the tactic that reduces a
goal of the form `f a₁ ... aₙ = f b₁ ... bₙ` to subgoals
`a₁ = b₁`, ..., `aₙ = bₙ`, automatically closing trivial ones.
-/

theorem eq_implies_succ_equal' (n m : Nat) (h : n = m) :
    n + 1 = m + 1 := by
  congr 1

-- =====================================================================
-- # Using Tactics on Hypotheses
-- =====================================================================

/-!
By default, most tactics work on the goal formula and leave the
context unchanged. However, many tactics also have variants that
operate on hypotheses.

For example, `simp at h` performs simplification on hypothesis `h`
in the context. Similarly, `rw [lemma] at h` rewrites in `h`.
-/

theorem S_inj (n m : Nat) (b : Bool) (h : ((n + 1) =? (m + 1)) = b) :
    (n =? m) = b := by
  simp [eqb] at h
  exact h

/-!
`apply lemma at h` matches `h` against the premise of `lemma` and
replaces `h` with the conclusion (forward reasoning). By contrast,
`apply lemma` on the goal is backward reasoning.

Here is a proof using forward reasoning throughout:
-/

theorem silly4 (n m p q : Nat)
    (h1 : n = m → p = q) (h2 : m = n) : q = p := by
  have h2' : n = m := h2.symm
  have h3 : p = q := h1 h2'
  exact h3.symm

-- =====================================================================
-- # Specializing Hypotheses
-- =====================================================================

/-!
When we have a universally quantified hypothesis `h : ∀ x, P x`, we
can specialize it to a particular value using `have` or `specialize`.
For example:
-/

theorem specialize_example (n : Nat)
    (h : ∀ m, m * n = 0) : n = 0 := by
  have h1 := h 1
  simp at h1
  exact h1

/-!
#### Exercise: 3 stars, standard (nth_error_always_none)

Use `specialize` or `have` to prove the following lemma. Do not use
`induction`.
-/

theorem nth_error_always_none (l : List Nat)
    (h : ∀ i, nthError l i = none) : l = [] := by
  /- FILL IN HERE -/ sorry

/-!
Using `specialize` before `apply` gives us another way to control
where `apply` does its work:
-/

example (a b c d e f : Nat)
    (h1 : [a, b] = [c, d]) (h2 : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  have h := trans_eq [a, b] [c, d] [e, f]
  exact h h1 h2

-- =====================================================================
-- # Varying the Induction Hypothesis
-- =====================================================================

/-!
Sometimes it is important to control the exact form of the induction
hypothesis when carrying out inductive proofs. In particular, we may
need to be careful about which assumptions we `intro`duce from the
goal into the context before invoking `induction`.

For example, suppose we want to show that `double` is injective —
i.e., that it maps different arguments to different results:

    theorem double_injective (n m : Nat) :
      double n = double m → n = m

The way we start this proof is a bit delicate: if we begin by doing
induction on `n` without first introducing `m`, then the induction
hypothesis will be sufficiently general.

But if we introduce _both_ `n` and `m` before doing induction on `n`,
we get stuck because the induction hypothesis only talks about a
_particular_ `m`, not all `m`.
-/

/-!
A successful proof of `double_injective` keeps `m` universally
quantified in the goal at the point where `induction` is invoked:
-/

theorem double_injective (n : Nat) : ∀ m, double n = double m → n = m := by
  induction n with
  | zero =>
    intro m h
    cases m with
    | zero => rfl
    | succ m' => simp [double] at h
  | succ n' ih =>
    intro m h
    cases m with
    | zero => simp [double] at h
    | succ m' =>
      congr 1
      apply ih
      simp [double] at h
      exact h

/-!
The thing to take away from all this is that you need to be careful,
when using induction, that you are not trying to prove something too
specific: when proving a property quantified over variables `n` and
`m` by induction on `n`, it is sometimes crucial to leave `m`
"generic."

Note that in Lean, when we write `induction n with`, `m` is
automatically reverted and re-introduced if necessary, depending on
how the proof is structured. However, the concept is the same: the
induction hypothesis must be general enough.
-/

/-!
#### Exercise: 2 stars, standard (eqb_true)
-/

theorem eqb_true (n m : Nat) (h : (n =? m) = true) : n = m := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, advanced, optional (eqb_true_informal)

Give a careful informal proof of `eqb_true`, being as explicit as
possible about quantifiers.

/- FILL IN HERE -/
-/

/-!
#### Exercise: 3 stars, standard, especially useful (plus_n_n_injective)

Practice using "in" variants in this proof.
-/

theorem plus_n_n_injective (n m : Nat)
    (h : n + n = m + m) : n = m := by
  /- FILL IN HERE -/ sorry

/-!
The strategy of doing fewer `intro`s before `induction` to obtain a
more general induction hypothesis doesn't always work; sometimes some
_rearrangement_ of quantified variables is needed. In Lean, we can
use `revert` to move a variable from the context back into the goal
(the opposite of `intro`).
-/

-- If we tried `induction m` directly here (with `n` and `h` already
-- in context), the induction hypothesis would only mention the specific
-- `n` and `h` we introduced — not a general `n`. The fix is to `revert n`
-- before performing induction, generalizing the hypothesis.

theorem double_injective_take2 (n m : Nat)
    (h : double n = double m) : n = m := by
  revert n
  induction m with
  | zero =>
    intro n h
    cases n with
    | zero => rfl
    | succ n' => simp [double] at h
  | succ m' ih =>
    intro n h
    cases n with
    | zero => simp [double] at h
    | succ n' =>
      congr 1
      apply ih
      simp [double] at h
      exact h

-- =====================================================================
-- # Rewriting with Conditional Statements
-- =====================================================================

/-!
When we `rw` with a conditional statement of the form `h : P → a = b`,
Lean rewrites `a` to `b` in the goal and then asks us to prove `P` as
a new subgoal. This makes it convenient to apply conditional rewrites
without manually using `have`.
-/

theorem leb_true_le (n m : Nat) (h : (n <=? m) = true) : n ≤ m := by
  induction n generalizing m with
  | zero => exact Nat.zero_le m
  | succ n' ih =>
    cases m with
    | zero => simp [leb] at h
    | succ m' =>
      simp [leb] at h
      exact Nat.succ_le_succ (ih m' h)

theorem sub_add_leb (n m : Nat)
    (h : (n <=? m) = true) : (m - n) + n = m := by
  have := leb_true_le n m h
  omega

/-!
#### Exercise: 3 stars, standard, especially useful (gen_dep_practice)

Prove this by induction on `l`.
-/

theorem nth_error_after_last (n : Nat) {α : Type} (l : List α)
    (h : l.length = n) : nthError l n = none := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Unfolding Definitions
-- =====================================================================

/-!
It sometimes happens that we need to manually unfold a name that has
been introduced by a `def` so that we can manipulate the expression
it stands for.

For example, if we define...
-/

def square (n : Nat) : Nat := n * n

#eval square 3   -- 9
#eval square 12  -- 144

/-!
...and try to prove a simple fact about `square`...
-/

theorem square_mult (n m : Nat) :
    square (n * m) = square n * square m := by
  simp [square, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-!
The `unfold` tactic replaces a defined constant by its right-hand side.
After unfolding, we can use rewriting with associativity and
commutativity lemmas to finish. `simp [square]` would also work for
many such goals.
-/

def myFoo (_x : Nat) : Nat := 5

theorem silly_fact_1 (m : Nat) : myFoo m + 1 = myFoo (m + 1) + 1 := by
  simp [myFoo]

/-!
Some definitions involve pattern matching, and `simp` may not fully
reduce them when the scrutinee is a variable. In that case, we can
either `unfold` the definition explicitly, or use `cases` to split
into branches where the match can reduce:
-/

def bar (x : Nat) : Nat :=
  match x with
  | 0 => 5
  | .succ _ => 5

theorem silly_fact_2 (m : Nat) : bar m + 1 = bar (m + 1) + 1 := by
  cases m <;> simp [bar]

-- =====================================================================
-- # Using `cases` on Compound Expressions
-- =====================================================================

/-!
We have seen many examples where `cases` is used to perform case
analysis on the value of some variable. Sometimes we need to reason
by cases on the result of some _expression_. We can do this with
`cases` combined with `show`, or by binding the expression with
`match` or `have`.
-/

def sillyfun (n : Nat) : Bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false

#eval sillyfun 3  -- false
#eval sillyfun 5  -- false
#eval sillyfun 7  -- false

theorem sillyfun_false (n : Nat) : sillyfun n = false := by
  unfold sillyfun
  cases h1 : n =? 3 with
  | true => rfl
  | false =>
    cases h2 : n =? 5 with
    | true => rfl
    | false => rfl

/-!
After unfolding `sillyfun`, we find ourselves stuck on
`if (n =? 3) then ... else ...`. We use `cases h1 : n =? 3` to split
on whether `n =? 3` is `true` or `false`, naming the equation `h1` so
we can use it later if needed.
-/

/-!
#### Exercise: 3 stars, standard (combine_split)

Recall the `split` function from `Poly`. Prove that `split` and
`combine` are inverses in the following sense:
-/

theorem combine_split {α β : Type} (l : List (α × β)) (l1 : List α)
    (l2 : List β) (h : split l = (l1, l2)) :
    combine l1 l2 = l := by
  /- FILL IN HERE -/ sorry

-- ## Compound expression case analysis — the `eqn:` pattern

/-!
When performing case analysis on a compound expression, it can be
critical to retain the equation showing which case we are in. In Lean,
`cases h : expr` records the result of the case split in hypothesis
`h`, which we can then use to make progress in the proof.
-/

def sillyfun1 (n : Nat) : Bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false

#eval sillyfun1 3  -- true
#eval sillyfun1 5  -- true
#eval sillyfun1 7  -- false

/-!
The key technique is using `cases h : expr` to split on an
expression's value while keeping the equation in `h` for further
reasoning.

Without the `h :` part, `cases` would substitute away all occurrences
of the expression without leaving a record of which case we're in.
We would then be stuck — unable to prove, say, that `n = 3` in the
branch where `n =? 3` was `true`.

Here is a concrete example. Proving `sillyfun1 n = true → odd n =
true` requires knowing *which* equality test succeeded. The
`cases h : (n =? 3)` pattern gives us that information. When the
result is `true`, we can apply `eqb_true` (an exercise above) to
learn that `n = 3`, then compute `odd 3 = true`. The `n =? 5` branch
works the same way:
-/

theorem sillyfun1_odd (n : Nat) (h : sillyfun1 n = true) :
    odd n = true := by
  unfold sillyfun1 at h
  cases h1 : n =? 3 with
  | true =>
    have := eqb_true n 3 h1
    subst this; rfl
  | false =>
    rw [h1] at h; simp at h
    cases h2 : n =? 5 with
    | true =>
      have := eqb_true n 5 h2
      subst this; rfl
    | false =>
      rw [h2] at h; simp at h

/-!
#### Exercise: 2 stars, standard (destruct_eqn_practice)
-/

theorem bool_fn_applied_thrice (f : Bool → Bool) (b : Bool) :
    f (f (f b)) = f b := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Review
-- =====================================================================

/-!
We've now covered many of Lean's fundamental tactics. Here are the
ones we've seen:

- `intro`: move hypotheses/variables from goal to context
- `rfl`: finish the proof when both sides are definitionally equal
- `exact h`: close the goal using hypothesis or term `h`
- `apply h`: prove goal using a hypothesis, lemma, or constructor
  (backward reasoning)
- `have h := ...`: introduce a new hypothesis via forward reasoning
- `rw [h]`: rewrite left-to-right using equality `h`
- `rw [← h]`: rewrite right-to-left
- `rw [h] at hyp`: rewrite in a hypothesis
- `simp`: powerful simplification tactic
- `simp at h`: simplify in a hypothesis
- `cases x with`: case analysis on values of inductively defined types
- `cases h : expr`: case split on expression, keeping equation in `h`
- `induction n with`: structural induction
- `omega`: linear arithmetic over `Nat`/`Int`
- `congr`: reduce `f a = f b` to `a = b`
- `contradiction`: close goal when context contains a contradiction
- `unfold f`: replace `f` with its definition
- `revert x`: move variable from context back into goal
- `specialize h e`: instantiate a universally quantified hypothesis
- `calc`: step-by-step equational reasoning
-/

-- =====================================================================
-- # Additional Exercises
-- =====================================================================

/-!
#### Exercise: 3 stars, standard (eqb_sym)
-/

theorem eqb_sym (n m : Nat) : (n =? m) = (m =? n) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, advanced, optional (eqb_sym_informal)

Give an informal proof of `eqb_sym`.

/- FILL IN HERE -/
-/

/-!
#### Exercise: 3 stars, standard, optional (eqb_trans)
-/

theorem eqb_trans (n m p : Nat)
    (h1 : (n =? m) = true) (h2 : (m =? p) = true) :
    (n =? p) = true := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, advanced (split_combine)

We proved, in an exercise above, that `combine` is the inverse of
`split`. Complete the definition of `split_combine_statement` below
with a property that states that `split` is the inverse of `combine`.
Then, prove that the property holds.

Hint: Take a look at the definition of `combine` in `Poly`. Your
property will need to account for the behavior of `combine` in its
base cases, which possibly drop some list elements.
-/

def split_combine_statement : Prop :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

theorem split_combine : split_combine_statement := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, advanced (filter_exercise)
-/

theorem filter_exercise {α : Type} (test : α → Bool)
    (x : α) (l lf : List α)
    (h : filter test l = x :: lf) : test x = true := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 4 stars, advanced, especially useful (forall_exists_challenge)

Define two recursive functions, `forallb` and `existsb`. The first
checks whether every element in a list satisfies a given predicate:

    forallb odd [1, 3, 5, 7, 9] = true
    forallb (fun _ => false) [0, 2, 4, 5] = false
    forallb (eqb 5) [] = true

The second checks whether there exists an element in the list that
satisfies a given predicate:

    existsb (eqb 5) [0, 2, 3, 6] = false
    existsb odd [1, 0, 0, 0, 0, 3] = true
    existsb even [] = false

Next, define a _nonrecursive_ version of `existsb` — call it
`existsb'` — using `forallb` and `!·` (boolean negation).

Finally, prove a theorem `existsb_existsb'` stating that `existsb'`
and `existsb` have the same behavior.
-/

namespace TacticsExercises

  def forallb {α : Type} (test : α → Bool) (l : List α) : Bool :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : forallb odd [1, 3, 5, 7, 9] = true :=
    /- FILL IN HERE -/ sorry

  example : forallb (fun _ => false) [false, false] = false :=
    /- FILL IN HERE -/ sorry

  example : forallb even [0, 2, 4, 5] = false :=
    /- FILL IN HERE -/ sorry

  example : forallb (eqb 5) [] = true :=
    /- FILL IN HERE -/ sorry

  def existsb {α : Type} (test : α → Bool) (l : List α) : Bool :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : existsb (eqb 5) [0, 2, 3, 6] = false :=
    /- FILL IN HERE -/ sorry

  example : existsb odd [1, 0, 0, 0, 0, 3] = true :=
    /- FILL IN HERE -/ sorry

  example : existsb even [] = false :=
    /- FILL IN HERE -/ sorry

  def existsb' {α : Type} (test : α → Bool) (l : List α) : Bool :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  theorem existsb_existsb' {α : Type} (test : α → Bool) (l : List α) :
      existsb test l = existsb' test l := by
    /- FILL IN HERE -/ sorry

end TacticsExercises
