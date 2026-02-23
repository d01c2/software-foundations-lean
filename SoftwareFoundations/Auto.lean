import SoftwareFoundations.Imp

/-!
# Auto: More Automation

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Auto.html>
-/

namespace Auto

  open Imp

  #check @CEval
  #check @Com.rec

  /-!
  Up to now, we've used the manual part of Lean's tactic facilities.
  In this chapter, we'll learn more about some of Lean's powerful
  automation features: proof search via `simp` and related tactics,
  automated forward reasoning via custom tactic macros, and Lean's
  seamless handling of metavariables in `apply`. Using these features
  together will enable us to make some of our proofs startlingly
  short! Used properly, they can also make proofs more maintainable
  and robust to changes in underlying definitions.

  (There's one other major category of automation we haven't discussed
  much yet, namely built-in decision procedures for specific kinds of
  problems: `omega` is one example, but there are others. This topic
  will be deferred for a while longer.)

  Our motivating example will be the following proof, repeated with
  just a few small changes from the `Imp` chapter. We will simplify
  this proof in several stages.
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
  -- # The `simp` Tactic
  -- =====================================================================

  /-!
  Thus far, our proof scripts mostly apply relevant hypotheses or
  lemmas by name, and only one at a time.

  In Lean, the primary automation tactic is `simp`, which performs
  equational simplification using a database of lemmas marked with
  the `@[simp]` attribute. Combined with `assumption` (which searches
  the hypotheses for one matching the goal), these tactics can free us
  from much drudgery.
  -/

  example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (h3 : P) : R :=
    h2 (h1 h3)

  /-!
  For goals involving purely propositional reasoning, term-mode proofs
  are often the most concise. But for more complex goals, tactic
  combinations shine. Here `exact` chains the hypotheses:
  -/

  example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
    exact h2 (h1 h3)

  /-!
  Here is a larger example. The proof requires finding the right
  sequence of hypothesis applications:
  -/

  example (P Q R S T U : Prop)
      (h1 : P → Q) (_h2 : P → R) (_h3 : T → R)
      (h4 : S → T → U) (h5 : (P → Q) → P → S)
      (h6 : T) (h7 : P) : U := by
    exact h4 (h5 h1 h7) h6

  /-!
  Proof search could, in principle, take an arbitrarily long time,
  so automation tactics have limits on search depth. When `simp`
  cannot solve a goal, it does nothing (it never fails or changes
  the goal to something unprovable). This "safety" property is
  important: you can always try `simp` without risk.
  -/

  example (P Q R S T U : Prop)
      (h1 : P → Q) (h2 : Q → R) (h3 : R → S)
      (h4 : S → T) (h5 : T → U) (h6 : P) : U :=
    h5 (h4 (h3 (h2 (h1 h6))))

  /-!
  `simp` also knows about standard logical connectives. For
  example, it can handle goals involving `∨` and `∧` when combined
  with hypotheses. More commonly, `constructor` and `exact` work
  well for structured goals:
  -/

  example (P Q R : Prop) (hq : Q) (hqr : Q → R) : P ∨ (Q ∧ R) :=
    .inr ⟨hq, hqr hq⟩

  example : 2 = 2 := rfl

  example (P _Q R S T _U _W : Prop)
      (_h1 : _U → T) (_h2 : _W → _U) (h3 : R → S)
      (h4 : S → T) (h5 : P → R) (_h6 : _U → T) (h7 : P) : T :=
    h4 (h3 (h5 h7))

  -- =====================================================================
  -- # Lemma Databases with `@[simp]`
  -- =====================================================================

  /-!
  We can extend what `simp` knows by marking lemmas with the `@[simp]`
  attribute. This tells `simp` to use the lemma as a rewrite rule
  automatically.

  For example, `simp` alone cannot use `le_antisym` since it's not a
  simple rewrite rule. But `omega` handles it directly:
  -/

  theorem le_antisym' (n m : Nat) (h : n ≤ m ∧ m ≤ n) : n = m := by
    omega

  example (n m p q : Nat)
      (h1 : p = q → n ≤ m ∧ m ≤ n) (h2 : p = q) : n = m := by
    have := h1 h2; omega

  /-!
  Of course, in any given development there will probably be some
  specific lemmas that are used very often in proofs. We can add
  these to the `simp` set by writing:

      @[simp] theorem myLemma : ... := ...

  at the top level. It is good practice to be selective about what
  you add to the global `simp` set — adding too many lemmas can
  slow down `simp` or cause it to loop.
  -/

  -- ## Unfolding Definitions

  /-!
  It is also sometimes necessary to tell `simp` to unfold a
  definition. We do this with `simp [f]` or `simp only [f]`, where
  `f` is the definition to unfold. Without this, `simp` treats
  definitions as opaque.
  -/

  def isFortytwo (x : Nat) : Prop := x = 42

  example (x : Nat) (h : x ≤ 42 ∧ 42 ≤ x) : isFortytwo x := by
    simp only [isFortytwo]; omega

  -- Alternatively, `unfold` makes the definition transparent:
  example (x : Nat) (h : x ≤ 42 ∧ 42 ≤ x) : isFortytwo x := by
    unfold isFortytwo; omega

  -- =====================================================================
  -- # Streamlining with `simp_all`
  -- =====================================================================

  /-!
  Let's take a pass over `ceval_deterministic`, using `simp_all` to
  simplify the proof script. The `simp_all` tactic is a powerful
  variant of `simp` that simplifies all hypotheses _and_ the goal
  simultaneously. It can find contradictions between hypotheses (e.g.,
  `h1 : E = true` and `h2 : E = false`) and close goals automatically.

  After `induction` and `cases`, most subgoals are either:
  - **Trivial:** Both derivations match, so the results are equal (`rfl`).
  - **Inductive:** Both use the same constructor, so we apply the IH.
  - **Contradictory:** Conflicting boolean conditions (`simp_all`
    handles these).

  Here is the streamlined proof. Every contradiction case — where
  `beval st b` is required to be both `true` and `false` — is now
  handled by a single call to `simp_all`:
  -/

  theorem ceval_deterministic' (c : Com) (st st1 st2 : State)
      (h1 : st =[ c ]=> st1) (h2 : st =[ c ]=> st2) :
      st1 = st2 := by
    revert st2
    induction h1 with
    | e_Skip => intro _ h2; cases h2; rfl
    | e_Asgn st a n x ha =>
      intro _ h2; cases h2; rename_i ha'; rw [← ha, ← ha']
    | e_Seq _ _ _ _ _ _ _ ih1 ih2 =>
      intro st2 h2
      cases h2; rename_i h2a h2b
      have := ih1 _ h2a; subst this; exact ih2 _ h2b
    | e_IfTrue _ _ _ _ _ hb _ ih =>
      intro st2 h2; cases h2
      · rename_i h2c; exact ih _ h2c
      · simp_all
    | e_IfFalse _ _ _ _ _ hb _ ih =>
      intro st2 h2; cases h2
      · simp_all
      · rename_i h2c; exact ih _ h2c
    | e_WhileFalse _ _ _ hb =>
      intro st2 h2; cases h2
      · rfl
      · simp_all
    | e_WhileTrue _ _ _ _ _ hb _ _ ihc ihw =>
      intro st2 h2; cases h2
      · simp_all
      · rename_i _ h2c h2w
        have heq := ihc _ h2c; subst heq; exact ihw _ h2w

  -- =====================================================================
  -- # Adding `repeat` to the Language
  -- =====================================================================

  /-!
  The big payoff of this automation approach is that proofs become
  robust in the face of changes to the language. To test this, let's
  add a `repeat` command to the language.

  `repeat` behaves like `while`, except that the loop guard is checked
  _after_ each execution of the body, with the loop repeating as long
  as the guard stays _false_. Because of this, the body always executes
  at least once.
  -/

  namespace RepeatExercise

    inductive RCom where
      | cSkip
      | cAsgn (x : String) (a : AExp)
      | cSeq (c1 c2 : RCom)
      | cIf (b : BExp) (c1 c2 : RCom)
      | cWhile (b : BExp) (c : RCom)
      | cRepeat (c : RCom) (b : BExp)

    inductive RCEval : RCom → State → State → Prop where
      | e_Skip : ∀ st,
          RCEval .cSkip st st
      | e_Asgn : ∀ st a n x,
          aeval st a = n →
          RCEval (.cAsgn x a) st (x !→ n; st)
      | e_Seq : ∀ c1 c2 st st' st'',
          RCEval c1 st st' →
          RCEval c2 st' st'' →
          RCEval (.cSeq c1 c2) st st''
      | e_IfTrue : ∀ st st' b c1 c2,
          beval st b = true →
          RCEval c1 st st' →
          RCEval (.cIf b c1 c2) st st'
      | e_IfFalse : ∀ st st' b c1 c2,
          beval st b = false →
          RCEval c2 st st' →
          RCEval (.cIf b c1 c2) st st'
      | e_WhileFalse : ∀ b st c,
          beval st b = false →
          RCEval (.cWhile b c) st st
      | e_WhileTrue : ∀ st st' st'' b c,
          beval st b = true →
          RCEval c st st' →
          RCEval (.cWhile b c) st' st'' →
          RCEval (.cWhile b c) st st''
      | e_RepeatEnd : ∀ st st' b c,
          RCEval c st st' →
          beval st' b = true →
          RCEval (.cRepeat c b) st st'
      | e_RepeatLoop : ∀ st st' st'' b c,
          RCEval c st st' →
          beval st' b = false →
          RCEval (.cRepeat c b) st' st'' →
          RCEval (.cRepeat c b) st st''

    /-!
    Despite adding two new constructors (`e_RepeatEnd` and
    `e_RepeatLoop`), the proof structure is the same: apply the IH,
    substitute, and use `simp_all` for contradictions. The `simp_all`
    tactic automatically handles the new contradiction cases where
    `beval st' b` is both `true` and `false`.
    -/

    theorem rceval_deterministic (c : RCom) (st st1 st2 : State)
        (h1 : RCEval c st st1) (h2 : RCEval c st st2) :
        st1 = st2 := by
      revert st2
      induction h1 with
      | e_Skip => intro _ h2; cases h2; rfl
      | e_Asgn _ _ _ _ ha =>
        intro _ h2; cases h2; rename_i ha'; rw [← ha, ← ha']
      | e_Seq _ _ _ _ _ _ _ ih1 ih2 =>
        intro st2 h2; cases h2; rename_i h2a h2b
        have := ih1 _ h2a; subst this; exact ih2 _ h2b
      | e_IfTrue _ _ _ _ _ hb _ ih =>
        intro st2 h2; cases h2
        · rename_i h; exact ih _ h
        · simp_all
      | e_IfFalse _ _ _ _ _ hb _ ih =>
        intro st2 h2; cases h2
        · simp_all
        · rename_i h; exact ih _ h
      | e_WhileFalse _ _ _ hb =>
        intro st2 h2; cases h2
        · rfl
        · simp_all
      | e_WhileTrue _ _ _ _ _ hb _ _ ihc ihw =>
        intro st2 h2; cases h2
        · simp_all
        · rename_i _ h2c h2w
          have := ihc _ h2c; subst this; exact ihw _ h2w
      | e_RepeatEnd _ _ _ _ _ hb ihc =>
        intro st2 h2; cases h2 with
        | e_RepeatEnd _ _ _ _ hc' _ => exact ihc _ hc'
        | e_RepeatLoop _ _ _ _ _ hc' hb' _ =>
          have := ihc _ hc'; subst this; simp_all
      | e_RepeatLoop _ _ _ _ _ _ hb _ ihc ihw =>
        intro st2 h2; cases h2 with
        | e_RepeatEnd _ _ _ _ hc' hb' =>
          have := ihc _ hc'; subst this; simp_all
        | e_RepeatLoop _ _ _ _ _ hc' _ hw' =>
          have := ihc _ hc'; subst this; exact ihw _ hw'

  end RepeatExercise

  /-!
  These examples illustrate the spirit of "hyper-automation." In Lean,
  the key tools are:

  - `simp` / `simp_all` — simplification using lemma databases and
    hypotheses
  - `omega` — linear arithmetic
  - `<;>` — apply a tactic to all generated subgoals
  - Custom `macro` tactics — automate repetitive patterns

  Together they handle much of the proof drudgery, and adding new cases
  to the language rarely breaks existing proofs.
  -/

  -- ## Custom Tactic Macros

  /-!
  Lean allows defining custom tactic macros with `macro_rules` or
  `macro`. For example, we can define a tactic that searches through
  hypotheses for an equality and tries rewriting with each:
  -/

  macro "find_rwd" : tactic =>
    `(tactic| first
      | (rw [‹_ = _›])
      | (rw [‹_ = _›] at *)
      | (simp_all))

  /-!
  The tactic `find_rwd` tries a sequence of rewrites and simplification
  steps. We can then use it alongside `simp_all` to automate forward
  reasoning in proofs that involve equalities from case analysis.

  Custom macros like these let us build proof-search strategies by
  combining existing tactics into reusable automation.
  -/

  -- =====================================================================
  -- # Metavariables in `apply`
  -- =====================================================================

  /-!
  Let's look at another convenience feature of Lean: its ability to
  delay instantiation of quantifiers. When `apply` is used with a
  lemma whose conclusion matches the goal but leaves some arguments
  undetermined, Lean introduces _metavariables_ (written `?_`) for
  those arguments. These metavariables are resolved later as more
  information becomes available from subsequent proof steps.

  To motivate this feature, recall this example from the `Imp` chapter:
  -/

  example :
      emptyState =[
        .cSeq (.cAsgn X (.aNum 2))
          (.cIf (.bLe (.aId X) (.aNum 1))
            (.cAsgn Y (.aNum 3))
            (.cAsgn Z (.aNum 4)))
      ]=> (Z !→ 4; X !→ 2; t! 0) := by
    -- We supply the intermediate state explicitly:
    apply CEval.e_Seq _ _ _ (X !→ 2; t! 0)
    · exact CEval.e_Asgn _ _ _ _ rfl
    · apply CEval.e_IfFalse
      · native_decide
      · exact CEval.e_Asgn _ _ _ _ rfl

  /-!
  In the first step, we had to explicitly provide the intermediate
  state `(X !→ 2; t! 0)` to help Lean instantiate `st'` in
  `CEval.e_Seq`. This was needed because `e_Seq` is quantified over
  `st'`, which does not appear in the conclusion, so unifying the
  conclusion with the goal doesn't determine `st'`.

  But we don't actually _need_ to supply this. The `apply` tactic
  creates a metavariable for `st'`, and the next step resolves it:
  -/

  example :
      emptyState =[
        .cSeq (.cAsgn X (.aNum 2))
          (.cIf (.bLe (.aId X) (.aNum 1))
            (.cAsgn Y (.aNum 3))
            (.cAsgn Z (.aNum 4)))
      ]=> (Z !→ 4; X !→ 2; t! 0) := by
    apply CEval.e_Seq  -- metavariable `?st'` created
    · exact CEval.e_Asgn _ _ _ _ rfl  -- resolves `?st'`
    · apply CEval.e_IfFalse
      · native_decide
      · exact CEval.e_Asgn _ _ _ _ rfl

  /-!
  After `apply CEval.e_Seq`, the intermediate state is a metavariable.
  The next step (`exact CEval.e_Asgn _ _ _ _ rfl`) determines it to
  be `(X !→ 2; t! 0)`. This resolved value then propagates to the
  second subgoal.

  The `exact` tactic with `_` placeholders also lets Lean infer
  arguments. For instance, `exact f _ _ h` asks Lean to figure out
  the first two arguments from the type of `h`.
  -/

  -- =====================================================================
  -- # Constraints on Metavariables
  -- =====================================================================

  /-!
  In order for a proof to be accepted, all metavariables must be
  determined by the end. If any remain unresolved, Lean will reject
  the proof.

  Here is an example showing how metavariables get resolved through
  later proof steps:
  -/

  theorem silly1 (P : Nat → Nat → Prop) (Q : Nat → Prop)
      (hp : ∀ x y, P x y) (hq : ∀ x y, P x y → Q x) : Q 42 := by
    exact hq 42 0 (hp 42 0)

  /-!
  An additional constraint is that metavariables cannot be filled with
  terms containing variables that did not exist when the metavariable
  was created. For example, destructing an existential _after_
  introducing a metavariable can leave the metavariable unsolvable
  because the witness variable isn't in its scope.

  The fix is to destruct the existential _before_ introducing the
  metavariable:
  -/

  theorem silly2_fixed (P : Nat → Nat → Prop) (Q : Nat → Prop)
      (hp : ∃ y, P 42 y) (hq : ∀ x y, P x y → Q x) : Q 42 := by
    obtain ⟨y, hp'⟩ := hp
    exact hq 42 y hp'

  /-!
  In the proof above, by destructing `hp` _before_ applying `hq`,
  the variable `y` is in scope when we need to provide it.

  The `exact` tactic can also solve this in one step, using `_`
  placeholders to let Lean infer arguments:
  -/

  theorem silly2_eauto (P : Nat → Nat → Prop) (Q : Nat → Prop)
      (hp : ∃ y, P 42 y) (hq : ∀ x y, P x y → Q x) : Q 42 := by
    obtain ⟨y, hp'⟩ := hp
    exact hq _ _ hp'

  /-!
  In this last step, `exact hq _ _ hp'` lets Lean infer both `x`
  and `y` from the type of `hp'`. Lean's unifier is powerful enough
  that `apply` and `exact` with `_` placeholders handle most
  metavariable resolution automatically.

  **Pro tip:** One might think that since `apply` handles
  metavariables, we should always rely on inference. In practice,
  leaving too many metavariables can make proofs fragile — small
  changes in the goal can cause unification to fail in unexpected
  ways. It's good practice to provide explicit arguments when the
  intent is clear, and rely on metavariables only when the value
  truly will be determined by a later step.
  -/

end Auto
