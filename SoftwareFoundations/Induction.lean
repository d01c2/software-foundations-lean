import SoftwareFoundations.Basics

/-!
# Induction: Proof by Induction

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html>
-/

-- =====================================================================
-- # Proof by Induction
-- =====================================================================

/-!
Recall from Basics that Lean's `Nat.add` recurses on the _second_
argument:

    n + 0       = n            (definitional — `rfl` works)
    n + (m + 1) = (n + m) + 1  (definitional — `rfl` works)

So `n + 0 = n` holds by `rfl`. But `0 + n = n` does _not_ — when `n`
is an unknown variable, the recursive case cannot simplify because `+`
peels off from the second argument, not the first.

We proved `zero_add` in Basics using `simp`. There, `simp` succeeds by
rewriting with known lemmas (many arithmetic lemmas in the library are
proved by induction). To understand the proof structure, let's write the
induction proof explicitly.
-/

-- `n + 0 = n` is definitional — useful as a named lemma for later proofs:
theorem add_zero_right (n : Nat) : n + 0 = n := rfl

-- `0 + n = n` requires induction. Here is the explicit proof:
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    -- Goal: 0 + (n' + 1) = n' + 1
    -- By definition of +, this is Nat.succ (0 + n') = Nat.succ n'
    -- So we can rewrite with the induction hypothesis inside `Nat.succ`.
    show Nat.succ (0 + n') = Nat.succ n'
    rw [ih]

/-!
The `induction n with` tactic generates one subgoal per constructor of
`Nat`. In the `zero` case, `n` is replaced by `0` and the goal becomes
`0 + 0 = 0`, which holds by `rfl`. In the `succ` case, `n` is replaced
by `n' + 1`, and the induction hypothesis `ih : 0 + n' = n'` is added
to the context.

To prove interesting facts about numbers and other inductively defined
sets, we often need this kind of inductive reasoning. Recall the
_principle of induction over natural numbers_: If `P(n)` is some
proposition involving a natural number `n` and we want to show that `P`
holds for all numbers `n`, we can reason like this:
- show that `P(0)` holds;
- show that, for any `n'`, if `P(n')` holds, then so does `P(n' + 1)`;
- conclude that `P(n)` holds for all `n`.
-/

theorem minus_n_n (n : Nat) : n - n = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [ih]

/-!
#### Exercise: 2 stars, standard, especially useful (basic_induction)

Prove the following using induction. You might need previously proven
results.
-/

theorem mul_zero_right (n : Nat) : n * 0 = 0 := by
  /- FILL IN HERE -/ sorry

theorem succ_add_eq_add_succ (n m : Nat) : Nat.succ (n + m) = n + Nat.succ m := by
  /- FILL IN HERE -/ sorry

theorem add_comm (n m : Nat) : n + m = m + n := by
  /- FILL IN HERE -/ sorry

theorem add_assoc (n m p : Nat) : n + (m + p) = (n + m) + p := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard (double_plus)

Consider the following function, which doubles its argument:
-/

def double (n : Nat) : Nat :=
  match n with
  | .zero => 0
  | .succ n' => .succ (.succ (double n'))

#eval double 0  -- 0
#eval double 3  -- 6
#eval double 5  -- 10

-- Use induction to prove this simple fact about `double`:

theorem double_plus (n : Nat) : double n = n + n := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard (eqb_refl)

The following theorem relates the computational equality `=?` on `Nat`
with the definitional equality `=` on `Bool`.
-/

theorem eqb_refl (n : Nat) : (n =? n) = true := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, optional (even_succ)

One inconvenient aspect of our definition of `even n` is that it
recurses by peeling off _two_ successors at a time:

    even (.succ (.succ n')) = even n'

(equivalently, a recursive call "on `n - 2`"). This can make proofs
by induction on `n` awkward, since the step case may need information
about a value two steps smaller. The following lemma gives an
alternative characterization of `even (n + 1)` that works better with
induction:
-/

theorem even_succ (n : Nat) : even (.succ n) = not (even n) := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Proofs Within Proofs
-- =====================================================================

/-!
In Lean, as in informal mathematics, large proofs are often broken into
a sequence of theorems, with later proofs referring to earlier theorems.
But sometimes a proof will involve some miscellaneous fact that is too
trivial to bother giving its own top-level name. In such cases, it is
convenient to state and prove the fact inline using `have`.
-/

theorem mult_0_plus' (n m : Nat) : (n + 0 + 0) * m = n * m := by
  have h : n + 0 + 0 = n := by
    rw [add_zero_right (n + 0)]
    rw [add_zero_right n]
  rw [h]

/-!
As another example, suppose we want to prove that
`(n + m) + (p + q) = (m + n) + (p + q)`. The only difference between
the two sides is that the arguments `m` and `n` to the first inner `+`
are swapped, so it seems we should be able to use the commutativity of
addition (`Nat.add_comm`) to rewrite one into the other.

However, `rw [Nat.add_comm]` is not very smart about _where_ it applies the
rewrite. It rewrites the first match it finds, which may not be the one
we want.

In Lean, we can guide `rw` by supplying arguments to the lemma. Writing
`rw [Nat.add_comm n m]` tells Lean to rewrite specifically the term `n + m`
into `m + n`:
-/

theorem plus_rearrange (n m p q : Nat) :
    (n + m) + (p + q) = (m + n) + (p + q) := by
  rw [Nat.add_comm n m]

-- Alternatively, we can use `have` to establish an intermediate fact:
theorem plus_rearrange' (n m p q : Nat) :
    (n + m) + (p + q) = (m + n) + (p + q) := by
  have h : n + m = m + n := by rw [Nat.add_comm n m]
  rw [h]

-- =====================================================================
-- # Formal vs. Informal Proof
-- =====================================================================

/-!
_"Informal proofs are algorithms; formal proofs are code."_

What constitutes a successful proof of a mathematical claim? A rough
answer: a proof is a written text that convinces the reader that the
proposition is true — an unassailable argument for its truth.

When the "reader" is Lean, the proof must be a complete recipe of
tactics (or terms) that mechanically derive the proposition from the
type theory's rules. These are _formal_ proofs.

When the reader is a human, the proof is written in a natural language
and is necessarily _informal_. The criteria for success are less clear
— different readers may need different levels of detail. Mathematicians
have developed conventions that, within a community, make such
communication fairly reliable.

Because we are using Lean in this course, we work heavily with formal
proofs. But informal ones remain important! Formal proofs are not very
efficient for communicating ideas between humans.
-/

/-!
For example, here is a formal proof that addition is associative:
-/

-- Library lemma used below:
-- `Nat.succ_add : Nat.succ n + m = Nat.succ (n + m)`
theorem add_assoc' (n m p : Nat) : n + (m + p) = (n + m) + p := by
  induction n with
  | zero => simp
  | succ n' ih => simp [Nat.succ_add, ih]
-- In the `succ` case, `Nat.succ_add` corresponds to rewriting
-- `(n' + 1) + x` into `(n' + x) + 1` in the informal proof below.

/-!
Lean is perfectly happy with this. For a human, however, it is
difficult to make much sense of it — the "proof state" at each point
is completely implicit. Here is an informal version:

- _Theorem_: For any `n`, `m`, and `p`,

      n + (m + p) = (n + m) + p.

  _Proof_: By induction on `n`.

  - First, suppose `n = 0`. We must show that

        0 + (m + p) = (0 + m) + p.

    This follows directly from the definition of `+`.

  - Next, suppose `n = n' + 1`, where

        n' + (m + p) = (n' + m) + p.     (induction hypothesis)

    We must now show that

        (n' + 1) + (m + p) = ((n' + 1) + m) + p.

    By the definition of `+`, this follows from

        (n' + (m + p)) + 1 = ((n' + m) + p) + 1,

    which is immediate from the induction hypothesis. _Qed_.

The overall form of the proof is similar, and this is no accident:
Lean's `induction` tactic generates the same sub-goals, in the same
order, as the bullet points that a mathematician would write. But there
are significant differences of detail: the formal proof is more explicit
in some ways (e.g., the use of `rfl`) but less explicit in others (the
proof state is implicit, whereas the informal proof reminds the reader
several times where things stand).
-/

/-!
#### Exercise: 2 stars, advanced, optional (add_comm_informal)

Translate your solution for `add_comm` into an informal proof:

Theorem: Addition is commutative.

Proof: /- FILL IN HERE -/
-/

/-!
#### Exercise: 2 stars, standard, optional (eqb_refl_informal)

Write an informal proof of the following theorem. Don't just
paraphrase the Lean tactics into English!

Theorem: `(n =? n) = true` for any `n`.

Proof: /- FILL IN HERE -/
-/

-- =====================================================================
-- # More Exercises
-- =====================================================================

/-!
#### Exercise: 3 stars, standard, especially useful (add_shuffle3)

Use `have` (or supply arguments to `rw`) to help prove `add_shuffle3`.
You don't need induction yet.
-/

theorem add_shuffle3 (n m p : Nat) : n + (m + p) = m + (n + p) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard, especially useful (mul_comm)

Now prove commutativity of multiplication. You will probably want to
look for (or define and prove) a "helper" theorem to be used in the
proof of this one. Hint: what is `n * (1 + k)`?
-/

theorem mul_comm (m n : Nat) : m * n = n * m := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard, optional (more_exercises)

Take a moment to think about whether each theorem below can be proved
using only simplification and rewriting, also requires case analysis
(`cases`), or also requires induction. Then fill in the proof.
-/

theorem leb_refl (n : Nat) : (n <=? n) = true := by
  /- FILL IN HERE -/ sorry

theorem zero_neqb_succ (n : Nat) : (0 =? .succ n) = false := by
  /- FILL IN HERE -/ sorry

theorem andb_false_right (b : MyBool) : b my&& .false = .false := by
  /- FILL IN HERE -/ sorry

theorem succ_neqb_zero (n : Nat) : (.succ n =? 0) = false := by
  /- FILL IN HERE -/ sorry

theorem mul_one_left (n : Nat) : 1 * n = n := by
  /- FILL IN HERE -/ sorry

theorem all_three_spec (b c : MyBool) :
    orb (andb b c) (orb (negb b) (negb c)) = .true := by
  /- FILL IN HERE -/ sorry

theorem mul_add_distr_right (n m p : Nat) :
    (n + m) * p = (n * p) + (m * p) := by
  /- FILL IN HERE -/ sorry

theorem mult_assoc (n m p : Nat) : n * (m * p) = (n * m) * p := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Nat to Bin and Back to Nat
-- =====================================================================

/-!
#### Exercise: 3 stars, standard, especially useful (binary_commute)

Prove that the following diagram commutes:

                    incr
          Bin ---------------> Bin
          |                      |
binToNat  |                      |  binToNat
          |                      |
          v                      v
          Nat ---------------> Nat
                      S

That is, incrementing a binary number and then converting it to a
(unary) natural number yields the same result as first converting it to
a natural number and then incrementing.
-/

theorem bin_to_nat_pres_incr (b : Bin) :
    binToNat (incr b) = 1 + (binToNat b) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard (nat_bin_nat)

Write a function to convert natural numbers to binary numbers.
-/

def natToBin (n : Nat) : Bin :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

/-!
Prove that, if we start with any `Nat`, convert it to `Bin`, and convert
it back, we get the same `Nat` we started with.

Hint: This proof should go through smoothly using `bin_to_nat_pres_incr`
as a lemma. If not, revisit your definitions and consider whether they
are more complicated than necessary.
-/

theorem nat_bin_nat (n : Nat) : binToNat (natToBin n) = n := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Bin to Nat and Back to Bin (Advanced)
-- =====================================================================

/-!
The opposite direction -- starting with a `Bin`, converting to `Nat`,
then converting back to `Bin` -- turns out to be problematic. The
following theorem does not hold:

    theorem bin_nat_bin_fails : ∀ b, natToBin (binToNat b) = b

The reason is that there are multiple `Bin` values representing the same
natural number. For example, `Bin.b0 Bin.z` and `Bin.z` both represent
zero. Converting to `Nat` and back produces the _canonical_ form, which
may differ from the original.
-/

/-!
#### Exercise: 2 stars, advanced (double_bin)

Prove this lemma about `double`:
-/

theorem double_incr (n : Nat) :
    double (.succ n) = .succ (.succ (double n)) := by
  /- FILL IN HERE -/ sorry

/-!
Now define a similar doubling function for `Bin`.
-/

def doubleBin (b : Bin) : Bin :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

-- Check that your function correctly doubles zero:
example : doubleBin .z = .z :=
  /- FILL IN HERE -/ sorry

/-!
Prove this lemma, which corresponds to `double_incr`:
-/

theorem double_incr_bin (b : Bin) :
    doubleBin (incr b) = incr (incr (doubleBin b)) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 4 stars, advanced (bin_nat_bin)

Define `normalize`. You will need to keep its definition as simple as
possible for later proofs to go smoothly. Do not use `binToNat` or
`natToBin`, but do use `doubleBin`.

Hint: Structure the recursion such that it _always_ reaches the end of
the `Bin` and _only_ processes each bit once. Do not try to "look
ahead" at future bits.
-/

def normalize (b : Bin) : Bin :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : normalize (.b0 (.b0 (.b1 .z))) = .b0 (.b0 (.b1 .z)) :=
  /- FILL IN HERE -/ sorry
example : normalize (.b0 (.b0 .z)) = .z :=
  /- FILL IN HERE -/ sorry

/-!
Finally, prove the main theorem. The inductive cases could be a bit
tricky.

Hint: Start by trying to prove the main statement, see where you get
stuck, and see if you can find a lemma -- perhaps requiring its own
inductive proof -- that will allow the main proof to make progress.
-/

theorem bin_nat_bin (b : Bin) :
    natToBin (binToNat b) = normalize b := by
  /- FILL IN HERE -/ sorry
