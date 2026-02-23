import SoftwareFoundations.Maps

/-!
# Imp: Simple Imperative Programs

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html>
-/

/-!
In this chapter, we take a more serious look at how to use Lean as a tool to
study other things. Our case study is a _simple imperative programming language_
called Imp, embodying a tiny core fragment of conventional mainstream languages
such as C and Java.

Here is a familiar mathematical function written in Imp:

    Z := X;
    Y := 1;
    while Z <> 0 do
      Y := Y * Z;
      Z := Z - 1
    end

We concentrate here on defining the _syntax_ and _semantics_ of Imp; later,
in _Programming Language Foundations_ (_Software Foundations_, volume 2), we
develop a theory of _program equivalence_ and introduce _Hoare Logic_, a
popular logic for reasoning about imperative programs.
-/

-- =====================================================================
-- # Arithmetic and Boolean Expressions
-- =====================================================================

-- ## Syntax

namespace AExpModule

  /-!
  These two inductive types specify the _abstract syntax_ of arithmetic and
  boolean expressions.
  -/

  inductive AExp where
    | aNum (n : Nat)
    | aPlus (a1 a2 : AExp)
    | aMinus (a1 a2 : AExp)
    | aMult (a1 a2 : AExp)
  deriving DecidableEq, Repr

  inductive BExp where
    | bTrue
    | bFalse
    | bEq (a1 a2 : AExp)
    | bNeq (a1 a2 : AExp)
    | bLe (a1 a2 : AExp)
    | bGt (a1 a2 : AExp)
    | bNot (b : BExp)
    | bAnd (b1 b2 : BExp)
  deriving Repr

  open AExp BExp

  /-!
  For comparison, here's a conventional BNF grammar defining the same abstract
  syntax:

      a := nat
          | a + a
          | a - a
          | a * a

      b := true
          | false
          | a = a
          | a <> a
          | a <= a
          | a > a
          | ~ b
          | b && b
  -/

  -- ## Evaluation

  -- _Evaluating_ an arithmetic expression produces a number.

  def aeval : AExp → Nat
    | .aNum n => n
    | .aPlus a1 a2 => aeval a1 + aeval a2
    | .aMinus a1 a2 => aeval a1 - aeval a2
    | .aMult a1 a2 => aeval a1 * aeval a2

  #eval aeval (aPlus (aNum 2) (aNum 2))    -- 4
  #eval aeval (aMinus (aNum 10) (aNum 3))  -- 7

  example : aeval (aPlus (aNum 2) (aNum 2)) = 4 := rfl

  -- Similarly, evaluating a boolean expression yields a boolean.

  def beval : BExp → Bool
    | .bTrue => true
    | .bFalse => false
    | .bEq a1 a2 => aeval a1 == aeval a2
    | .bNeq a1 a2 => !(aeval a1 == aeval a2)
    | .bLe a1 a2 => aeval a1 <= aeval a2
    | .bGt a1 a2 => !(aeval a1 <= aeval a2)
    | .bNot b1 => !beval b1
    | .bAnd b1 b2 => beval b1 && beval b2

  #eval beval (bLe (aNum 3) (aNum 5))  -- true
  #eval beval (bGt (aNum 2) (aNum 7))  -- false

  -- ## Optimization

  /-!
  We define a function that slightly simplifies an arithmetic expression,
  changing every occurrence of `0 + e` into just `e`.
  -/

  def optimize0plus : AExp → AExp
    | .aNum n => .aNum n
    | .aPlus (.aNum 0) e2 => optimize0plus e2
    | .aPlus e1 e2 => .aPlus (optimize0plus e1) (optimize0plus e2)
    | .aMinus e1 e2 => .aMinus (optimize0plus e1) (optimize0plus e2)
    | .aMult e1 e2 => .aMult (optimize0plus e1) (optimize0plus e2)

  example :
      optimize0plus (aPlus (aNum 2) (aPlus (aNum 0) (aPlus (aNum 0) (aNum 1))))
      = aPlus (aNum 2) (aNum 1) := rfl

  /-!
  To gain confidence that our optimization is correct -- that evaluating an
  optimized expression _always_ gives the same result as the original -- we
  prove it.
  -/

  theorem optimize0plus_sound (a : AExp) :
      aeval (optimize0plus a) = aeval a := by
    induction a with
    | aNum _ => rfl
    | aPlus a1 a2 ih1 ih2 =>
      cases a1 with
      | aNum n =>
        cases n with
        | zero => simp [optimize0plus, aeval, ih2]
        | succ _ => simp [optimize0plus, aeval, ih2]
      | aPlus _ _ => simp_all [optimize0plus, aeval]
      | aMinus _ _ => simp_all [optimize0plus, aeval]
      | aMult _ _ => simp_all [optimize0plus, aeval]
    | aMinus _ _ ih1 ih2 => simp [optimize0plus, aeval, ih1, ih2]
    | aMult _ _ ih1 ih2 => simp [optimize0plus, aeval, ih1, ih2]

  -- =====================================================================
  -- # Lean Automation
  -- =====================================================================

  /-!
  The amount of repetition in the last proof is a little annoying. Lean provides
  powerful facilities for constructing parts of proofs automatically. This section
  introduces some of them.
  -/

  -- ## Tacticals

  /-!
  Lean supports combinators that sequence or compose tactics, similar to what
  other proof assistants call "tacticals."
  -/

  -- ### The `try` combinator

  /-!
  If `t` is a tactic, then `try t` is a tactic that behaves like `t` except
  that, if `t` fails, `try t` successfully does nothing (rather than failing).
  -/

  theorem silly1 (P : Prop) (hp : P) : P := by
    try rfl  -- `rfl` would fail here, but `try rfl` just does nothing
    exact hp

  theorem silly2 (ae : AExp) : aeval ae = aeval ae := by
    try rfl  -- this just does `rfl`

  -- ### The `<;>` combinator (simple form)

  /-!
  The `<;>` combinator takes two tactics. `t1 <;> t2` first performs `t1` and
  then performs `t2` on _each subgoal_ generated by `t1`.
  -/

  theorem myFoo (n : Nat) : (0 ≤ n) = true := by
    simp

  /-!
  Using `try` and `<;>` together, we can produce a more concise version of
  `optimize0plus_sound`.
  -/

  theorem optimize0plus_sound' (a : AExp) :
      aeval (optimize0plus a) = aeval a := by
    induction a with
    | aPlus a1 _ ih1 ih2 =>
      cases a1 with
      | aNum n => cases n <;> simp_all [optimize0plus, aeval]
      | _ => simp_all [optimize0plus, aeval]
    | _ => simp_all [optimize0plus, aeval]

  -- ### The `repeat` tactic

  /-!
  The `repeat` tactic keeps applying a given tactic until it fails or makes no
  progress. Be careful: `repeat t` with a tactic that always succeeds and makes
  progress will loop forever!
  -/

  -- ### `omega` tactic

  /-!
  The `omega` tactic decides linear arithmetic over `Nat` and `Int`. If the goal
  is a universally quantified formula made out of numeric constants, addition,
  subtraction, multiplication by constants, equality, and ordering, then `omega`
  will either solve it or fail.
  -/

  example (m n o p : Nat) (h : m + n ≤ n + o ∧ o + 3 = p + 3) : m ≤ p := by
    omega

  example (m n : Nat) : m + n = n + m := by omega

  example (m n p : Nat) : m + (n + p) = m + n + p := by omega

  -- ## A Few More Handy Tactics

  /-!
  Here are some commonly used Lean tactics:

  - `clear h` : Remove hypothesis `h` from the context.
  - `subst x` : Given `x = e` or `e = x`, replace `x` throughout and clear it.
  - `rename_i name` : Rename the most recent unnamed hypothesis.
  - `assumption` : Find a hypothesis matching the goal and apply it.
  - `contradiction` : Find contradictory hypotheses and close the goal.
  - `constructor` : Apply the first applicable constructor from an inductive type.
  -/

  /-!
  #### Exercise: 3 stars, standard (optimize_0plus_b_sound)

  Since the `optimize0plus` transformation doesn't change the value of `AExp`s,
  we should be able to apply it to all the `AExp`s that appear in a `BExp`
  without changing the `BExp`'s value. Write such a function and prove it sound.
  -/

  def optimize0plusB (b : BExp) : BExp :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example :
      optimize0plusB (bNot (bGt (aPlus (aNum 0) (aNum 4)) (aNum 8)))
      = bNot (bGt (aNum 4) (aNum 8)) :=
    /- FILL IN HERE -/ sorry

  example :
      optimize0plusB (bAnd (bLe (aPlus (aNum 0) (aNum 4)) (aNum 5)) bTrue)
      = bAnd (bLe (aNum 4) (aNum 5)) bTrue :=
    /- FILL IN HERE -/ sorry

  theorem optimize0plusB_sound (b : BExp) :
      beval (optimize0plusB b) = beval b :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 4 stars, standard, optional (optimize)

  Design a more sophisticated optimizer for arithmetic/boolean expressions
  and prove it sound.
  -/

  /- FILL IN HERE -/

  -- =====================================================================
  -- # Evaluation as a Relation
  -- =====================================================================

  /-!
  We have presented `aeval` and `beval` as recursive functions. Another way to
  think about evaluation -- one that is often more flexible -- is as a _relation_
  between expressions and their values. This leads to inductive definitions like
  the following.
  -/

  inductive AEvalR : AExp → Nat → Prop where
    | e_ANum (n : Nat) :
        AEvalR (.aNum n) n
    | e_APlus (e1 e2 : AExp) (n1 n2 : Nat) :
        AEvalR e1 n1 →
        AEvalR e2 n2 →
        AEvalR (.aPlus e1 e2) (n1 + n2)
    | e_AMinus (e1 e2 : AExp) (n1 n2 : Nat) :
        AEvalR e1 n1 →
        AEvalR e2 n2 →
        AEvalR (.aMinus e1 e2) (n1 - n2)
    | e_AMult (e1 e2 : AExp) (n1 n2 : Nat) :
        AEvalR e1 n1 →
        AEvalR e2 n2 →
        AEvalR (.aMult e1 e2) (n1 * n2)

  scoped infixl:50 " a==> " => AEvalR

  /-!
  #### Exercise: 1 star, standard, optional (beval_rules)

  Write boolean evaluation as an inference-rule relation matching `beval`.
  -/

  /- FILL IN HERE -/

  -- ## Equivalence of the Definitions

  /-!
  It is straightforward to prove that the relational and functional definitions
  of evaluation agree.
  -/

  theorem aevalR_iff_aeval (a : AExp) (n : Nat) :
      (a a==> n) ↔ aeval a = n := by
    constructor
    · intro h
      induction h with
      | e_ANum => rfl
      | e_APlus _ _ _ _ _ _ ih1 ih2 => simp [aeval, ih1, ih2]
      | e_AMinus _ _ _ _ _ _ ih1 ih2 => simp [aeval, ih1, ih2]
      | e_AMult _ _ _ _ _ _ ih1 ih2 => simp [aeval, ih1, ih2]
    · intro h
      subst h
      induction a with
      | aNum n => exact AEvalR.e_ANum n
      | aPlus a1 a2 ih1 ih2 => exact AEvalR.e_APlus _ _ _ _ ih1 ih2
      | aMinus a1 a2 ih1 ih2 => exact AEvalR.e_AMinus _ _ _ _ ih1 ih2
      | aMult a1 a2 ih1 ih2 => exact AEvalR.e_AMult _ _ _ _ ih1 ih2

  /-!
  #### Exercise: 3 stars, standard (bevalR)

  Write a relation `BEvalR` in the same style as `AEvalR`, and prove that
  it is equivalent to `beval`.
  -/

  -- FILL IN HERE: define constructors for BEvalR
  inductive BEvalR : BExp → Bool → Prop where
    /- FILL IN HERE -/

  theorem bevalR_iff_beval (b : BExp) (bv : Bool) :
      BEvalR b bv ↔ beval b = bv :=
    /- FILL IN HERE -/ sorry

end AExpModule

-- ## Computational vs. Relational Definitions

/-!
For arithmetic and boolean expressions, the choice between functional and
relational definitions is mainly a matter of taste.

However, relational definitions become essential when dealing with features
like division (which may be undefined) or nondeterminism (where evaluation
is not a function). A relational approach handles both gracefully: we simply
omit rules for undefined inputs, and for nondeterministic features, the
relation naturally admits multiple outputs for the same input.

On the other hand, functional definitions can be more convenient: functions
are automatically deterministic and total, and we can use Lean's computation
mechanism to simplify expressions during proofs.
-/

-- =====================================================================
-- # Expressions With Variables
-- =====================================================================

-- ## States

/-!
To enrich our expressions with variables, we need a notion of _state_ -- a
mapping from variable names to their current values. We represent the state
as a `TotalMap Nat`, using `0` as the default value for uninitialized
variables.
-/

def State := TotalMap Nat

-- ## Syntax

/-!
We add variables to arithmetic expressions by including an `aId` constructor.
-/

inductive AExp where
  | aNum (n : Nat)
  | aId (x : String)
  | aPlus (a1 a2 : AExp)
  | aMinus (a1 a2 : AExp)
  | aMult (a1 a2 : AExp)
deriving Repr

-- A few variable names as shorthands:

def W : String := "W"
def X : String := "X"
def Y : String := "Y"
def Z : String := "Z"

-- The definition of `BExp` is unchanged (except it now refers to the new `AExp`):

inductive BExp where
  | bTrue
  | bFalse
  | bEq (a1 a2 : AExp)
  | bNeq (a1 a2 : AExp)
  | bLe (a1 a2 : AExp)
  | bGt (a1 a2 : AExp)
  | bNot (b : BExp)
  | bAnd (b1 b2 : BExp)
deriving Repr

-- ## Evaluation

/-!
The evaluators must now take a state `st` as an extra argument, to look up
variable values.
-/

def aeval (st : State) : AExp → Nat
  | .aNum n => n
  | .aId x => st x
  | .aPlus a1 a2 => aeval st a1 + aeval st a2
  | .aMinus a1 a2 => aeval st a1 - aeval st a2
  | .aMult a1 a2 => aeval st a1 * aeval st a2

def beval (st : State) : BExp → Bool
  | .bTrue => true
  | .bFalse => false
  | .bEq a1 a2 => aeval st a1 == aeval st a2
  | .bNeq a1 a2 => !(aeval st a1 == aeval st a2)
  | .bLe a1 a2 => aeval st a1 <= aeval st a2
  | .bGt a1 a2 => !(aeval st a1 <= aeval st a2)
  | .bNot b1 => !beval st b1
  | .bAnd b1 b2 => beval st b1 && beval st b2

-- The empty state maps every variable to `0`.

def emptyState : State := t! 0

example :
    aeval (X !→ 5; t! 0) (.aPlus (.aNum 3) (.aMult (.aId X) (.aNum 2)))
    = 13 := by native_decide

example :
    aeval (X !→ 5; Y !→ 4; t! 0)
      (.aPlus (.aId Z) (.aMult (.aId X) (.aId Y)))
    = 20 := by native_decide

example :
    beval (X !→ 5; t! 0)
      (.bAnd .bTrue (.bNot (.bLe (.aId X) (.aNum 4))))
    = true := by native_decide

-- =====================================================================
-- # Commands
-- =====================================================================

-- ## Syntax

/-!
Informally, commands `c` are described by the following BNF grammar:

    c := skip
       | x := a
       | c ; c
       | if b then c else c end
       | while b do c end

Here is the formal definition of the abstract syntax:
-/

inductive Com where
  | cSkip
  | cAsgn (x : String) (a : AExp)
  | cSeq (c1 c2 : Com)
  | cIf (b : BExp) (c1 c2 : Com)
  | cWhile (b : BExp) (c : Com)
deriving Repr

open Com

#check Com.cWhile
#check (State : Type)

-- Example: the factorial program

def factInLean : Com :=
  .cSeq (.cAsgn Z (.aId X))
    (.cSeq (.cAsgn Y (.aNum 1))
      (.cWhile (.bNeq (.aId Z) (.aNum 0))
        (.cSeq (.cAsgn Y (.aMult (.aId Y) (.aId Z)))
          (.cAsgn Z (.aMinus (.aId Z) (.aNum 1))))))

-- A few more examples:

def plus2 : Com :=
  .cAsgn X (.aPlus (.aId X) (.aNum 2))

def xTimesYInZ : Com :=
  .cAsgn Z (.aMult (.aId X) (.aId Y))

def subtractSlowlyBody : Com :=
  .cSeq (.cAsgn Z (.aMinus (.aId Z) (.aNum 1)))
    (.cAsgn X (.aMinus (.aId X) (.aNum 1)))

def subtractSlowly : Com :=
  .cWhile (.bNeq (.aId X) (.aNum 0)) subtractSlowlyBody

def subtract3From5Slowly : Com :=
  .cSeq (.cAsgn X (.aNum 3))
    (.cSeq (.cAsgn Z (.aNum 5)) subtractSlowly)

-- An infinite loop:

def loop : Com :=
  .cWhile .bTrue .cSkip

-- =====================================================================
-- # Evaluating Commands
-- =====================================================================

-- ## Evaluation as a Function (Failed Attempt)

/-!
Here's an attempt at defining an evaluation function for commands, with a
bogus `while` case that simply returns the state unchanged.
-/

def cevalFunNoWhile (st : State) : Com → State
  | .cSkip => st
  | .cAsgn x a => (x !→ aeval st a; st)
  | .cSeq c1 c2 =>
    let st' := cevalFunNoWhile st c1
    cevalFunNoWhile st' c2
  | .cIf b c1 c2 =>
    if beval st b then cevalFunNoWhile st c1
    else cevalFunNoWhile st c2
  | .cWhile _ _ => st  -- bogus

/-!
In a language like Haskell or OCaml we could add the `while` case with a
recursive call, but Lean rejects such definitions because the function is not
guaranteed to terminate -- and indeed, applied to `loop`, it would never
terminate.

Since Lean is both a programming language and a consistent logic, any
potentially non-terminating function needs to be rejected. If we could write

    def loopFalse (n : Nat) : False := loopFalse n

then `False` would become provable, destroying logical consistency.
-/

-- ## Evaluation as a Relation

/-!
A better approach: define `ceval` as a _relation_ rather than a function.
This frees us from requiring termination and naturally accommodates
nondeterminism.

We write `CEval c st st'` to mean that executing command `c` starting in
state `st` results in state `st'`.
-/

namespace Imp

  inductive CEval : Com → State → State → Prop where
    | e_Skip (st : State) :
        CEval .cSkip st st
    | e_Asgn (st : State) (a : AExp) (n : Nat) (x : String) :
        aeval st a = n →
        CEval (.cAsgn x a) st (x !→ n; st)
    | e_Seq (c1 c2 : Com) (st st' st'' : State) :
        CEval c1 st st' →
        CEval c2 st' st'' →
        CEval (.cSeq c1 c2) st st''
    | e_IfTrue (st st' : State) (b : BExp) (c1 c2 : Com) :
        beval st b = true →
        CEval c1 st st' →
        CEval (.cIf b c1 c2) st st'
    | e_IfFalse (st st' : State) (b : BExp) (c1 c2 : Com) :
        beval st b = false →
        CEval c2 st st' →
        CEval (.cIf b c1 c2) st st'
    | e_WhileFalse (b : BExp) (st : State) (c : Com) :
        beval st b = false →
        CEval (.cWhile b c) st st
    | e_WhileTrue (st st' st'' : State) (b : BExp) (c : Com) :
        beval st b = true →
        CEval c st st' →
        CEval (.cWhile b c) st' st'' →
        CEval (.cWhile b c) st st''

  scoped notation:40 st " =[ " c " ]=> " st' => CEval c st st'

  /-!
  The cost of defining evaluation as a relation is that we now need to construct
  a _proof_ that some program evaluates to some result state.
  -/

  example :
      emptyState =[
        .cSeq (.cAsgn X (.aNum 2))
          (.cIf (.bLe (.aId X) (.aNum 1))
            (.cAsgn Y (.aNum 3))
            (.cAsgn Z (.aNum 4)))
      ]=> (Z !→ 4; X !→ 2; t! 0) := by
    apply CEval.e_Seq _ _ _ (X !→ 2; t! 0)
    · exact CEval.e_Asgn _ _ _ _ rfl
    · apply CEval.e_IfFalse
      · native_decide
      · exact CEval.e_Asgn _ _ _ _ rfl

  /-!
  #### Exercise: 2 stars, standard (ceval_example2)
  -/

  example :
      emptyState =[
        .cSeq (.cAsgn X (.aNum 0))
          (.cSeq (.cAsgn Y (.aNum 1))
            (.cAsgn Z (.aNum 2)))
      ]=> (Z !→ 2; Y !→ 1; X !→ 0; t! 0) :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard, optional (pup_to_n)

  Write an Imp program that sums the numbers from `1` to `X` (inclusive) in the
  variable `Y`.
  -/

  def pupToN : Com :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  theorem pup_to_2_ceval :
      (X !→ 2; t! 0) =[
        pupToN
      ]=> (X !→ 0; Y !→ 3; X !→ 1; Y !→ 2; Y !→ 0; X !→ 2; t! 0) :=
    /- FILL IN HERE -/ sorry

  -- ## Determinism of Evaluation

  /-!
  Changing the evaluation relation to a function would make it easier
  to reason about determinism. But for `while` loops, such a function
  might not terminate. So we prove determinism as a property of the
  relational definition: if `c / st ==> st1` and `c / st ==> st2`,
  then `st1 = st2`.
  -/

  theorem ceval_deterministic (c : Com) (st st1 st2 : State)
      (h1 : st =[ c ]=> st1) (h2 : st =[ c ]=> st2) :
      st1 = st2 := by
    revert st2
    induction h1 with
    | e_Skip => intro _ h2; cases h2; rfl
    | e_Asgn st a n x ha =>
      intro _ h2; cases h2; rename_i ha'; rw [← ha, ← ha']
    | e_Seq c1 c2 st st' st'' _ _ ih1 ih2 =>
      intro st2 h2
      cases h2; rename_i h2a h2b
      have heq := ih1 _ h2a; subst heq
      exact ih2 _ h2b
    | e_IfTrue st st' b c1 c2 hb _ ih =>
      intro st2 h2
      cases h2
      · rename_i h2c; exact ih _ h2c
      · rename_i hb' _; simp [hb] at hb'
    | e_IfFalse st st' b c1 c2 hb _ ih =>
      intro st2 h2
      cases h2
      · rename_i hb' _; simp [hb] at hb'
      · rename_i h2c; exact ih _ h2c
    | e_WhileFalse b st c hb =>
      intro st2 h2
      cases h2
      · rfl
      · rename_i hb' _ _; simp [hb] at hb'
    | e_WhileTrue st st' st'' b c hb _ _ ihc ihw =>
      intro st2 h2
      cases h2
      · rename_i hb'; simp [hb] at hb'
      · rename_i _ h2c h2w
        have heq := ihc _ h2c; subst heq
        exact ihw _ h2w

  -- =====================================================================
  -- # Reasoning About Imp Programs
  -- =====================================================================

  theorem plus2_spec (st : State) (n : Nat) (st' : State)
      (hx : st X = n) (heval : st =[ plus2 ]=> st') :
      st' X = n + 2 := by
    cases heval with
    | e_Asgn _ _ _ _ ha =>
      simp [tUpdate]
      rw [← ha, aeval, aeval, aeval, hx]

  /-!
  #### Exercise: 3 stars, standard, optional (XtimesYinZ_spec)

  State and prove a specification of `xTimesYInZ`.
  -/

  /- FILL IN HERE -/

  /-!
  #### Exercise: 3 stars, standard, especially useful (loop_never_stops)
  -/

  theorem loop_never_stops (st st' : State) :
      ¬ (st =[ loop ]=> st') :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard (no_whiles_eqv)
  -/

  def noWhiles : Com → Bool
    | .cSkip => true
    | .cAsgn _ _ => true
    | .cSeq c1 c2 => noWhiles c1 && noWhiles c2
    | .cIf _ ct cf => noWhiles ct && noWhiles cf
    | .cWhile _ _ => false

  -- FILL IN HERE: define constructors for NoWhilesR
  inductive NoWhilesR : Com → Prop where
    /- FILL IN HERE -/

  theorem no_whiles_eqv (c : Com) :
      noWhiles c = true ↔ NoWhilesR c :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 4 stars, standard (no_whiles_terminating)

  Imp programs that don't involve while loops always terminate.
  State and prove a theorem `no_whiles_terminating` that says this.
  -/

  /- FILL IN HERE -/

  -- =====================================================================
  -- # Additional Exercises
  -- =====================================================================

  /-!
  #### Exercise: 3 stars, standard (stack_compiler)
  -/

  inductive SInstr where
    | sPush (n : Nat)
    | sLoad (x : String)
    | sPlus
    | sMinus
    | sMult

  open SInstr

  /-!
  Write a function to evaluate programs in the stack language. It should take
  a state, a stack (as a list of numbers, with the top item at the head), and
  a program (as a list of instructions), and return the stack after executing
  the program.
  -/

  def sExecute (st : State) (stack : List Nat)
      (prog : List SInstr) : List Nat :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example :
      sExecute emptyState [] [sPush 5, sPush 3, sPush 1, sMinus]
      = [2, 5] :=
    /- FILL IN HERE -/ sorry

  example :
      sExecute (X !→ 3; t! 0) [3, 4] [sPush 4, sLoad X, sMult, sPlus]
      = [15, 4] :=
    /- FILL IN HERE -/ sorry

  /-!
  Next, write a function that compiles an `AExp` into a stack machine program.
  -/

  def sCompile (e : AExp) : List SInstr :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example :
      sCompile (.aMinus (.aId X) (.aMult (.aNum 2) (.aId Y)))
      = [sLoad X, sPush 2, sLoad Y, sMult, sMinus] :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard (execute_app)

  Execution can be decomposed: executing `p1 ++ p2` is the same as executing
  `p1`, then executing `p2` from the resulting stack.
  -/

  theorem execute_app (st : State) (p1 p2 : List SInstr) (stack : List Nat) :
      sExecute st stack (p1 ++ p2) = sExecute st (sExecute st stack p1) p2 :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard (stack_compiler_correct)
  -/

  theorem s_compile_correct_aux (st : State) (e : AExp) (stack : List Nat) :
      sExecute st stack (sCompile e) = aeval st e :: stack :=
    /- FILL IN HERE -/ sorry

  theorem s_compile_correct (st : State) (e : AExp) :
      sExecute st [] (sCompile e) = [aeval st e] :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard, optional (short_circuit)

  Add short-circuit Boolean operators to Imp and adapt evaluation.
  -/

  /- FILL IN HERE -/

  /-!
  #### Exercise: 4 stars, standard, optional (break_imp)

  We extend Imp with a `break` statement for interrupting loops.
  -/

  namespace BreakImp

    inductive BCom where
      | cSkip
      | cBreak
      | cAsgn (x : String) (a : AExp)
      | cSeq (c1 c2 : BCom)
      | cIf (b : BExp) (c1 c2 : BCom)
      | cWhile (b : BExp) (c : BCom)

    inductive Result where
      | sContinue
      | sBreak

    open BCom Result

    /-!
    The evaluation relation now also produces a `Result` indicating whether
    a `break` was encountered. `BCEval c st s st'` means that executing
    `c` in state `st` terminates in state `st'` with signal `s`.
    -/

    inductive BCEval : BCom → State → Result → State → Prop where
      | e_Skip (st : State) :
          BCEval .cSkip st .sContinue st
      -- FILL IN HERE

    theorem break_ignore (c : BCom) (st st' : State) (s : Result)
        (h : BCEval (.cSeq .cBreak c) st s st') : st = st' :=
      /- FILL IN HERE -/ sorry

    theorem while_continue (b : BExp) (c : BCom) (st st' : State) (s : Result)
        (h : BCEval (.cWhile b c) st s st') : s = .sContinue :=
      /- FILL IN HERE -/ sorry

    theorem while_stops_on_break (b : BExp) (c : BCom) (st st' : State)
        (hb : beval st b = true) (hc : BCEval c st .sBreak st') :
        BCEval (.cWhile b c) st .sContinue st' :=
      /- FILL IN HERE -/ sorry

    theorem seq_continue (c1 c2 : BCom) (st st' st'' : State)
        (h1 : BCEval c1 st .sContinue st')
        (h2 : BCEval c2 st' .sContinue st'') :
        BCEval (.cSeq c1 c2) st .sContinue st'' :=
      /- FILL IN HERE -/ sorry

    theorem seq_stops_on_break (c1 c2 : BCom) (st st' : State)
        (h1 : BCEval c1 st .sBreak st') :
        BCEval (.cSeq c1 c2) st .sBreak st' :=
      /- FILL IN HERE -/ sorry

    /-!
    #### Exercise: 4 stars, advanced, optional (ceval_deterministic)
    -/

    theorem ceval_deterministic (c : BCom) (st : State)
        (s1 s2 : Result) (st1 st2 : State)
        (h1 : BCEval c st s1 st1) (h2 : BCEval c st s2 st2) :
        st1 = st2 ∧ s1 = s2 := by
      /- FILL IN HERE -/ sorry

  end BreakImp

  /-!
  #### Exercise: 3 stars, advanced, optional (while_break_true)
  -/

  /- FILL IN HERE -/

  /-!
  #### Exercise: 4 stars, standard, optional (add_for_loop)
  -/

  /- FILL IN HERE -/

end Imp
