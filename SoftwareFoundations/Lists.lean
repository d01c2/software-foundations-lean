import SoftwareFoundations.Induction

/-!
# Lists: Working with Structured Data

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html>
-/

namespace NatList

  -- =====================================================================
  -- # Pairs of Numbers
  -- =====================================================================

  /-!
  In an `inductive` type definition, each constructor can take any number
  of arguments — none (as with `true` and `zero`), one (as with `succ`),
  or more than one:
  -/

  inductive NatProd where
    | pair (n1 n2 : Nat)

  /-!
  This declaration can be read: "The one and only way to construct a pair
  of numbers is by applying the constructor `pair` to two arguments of
  type `Nat`."
  -/

  #check (NatProd.pair 3 5 : NatProd)

  -- Functions for extracting the first and second components of a pair
  -- can be defined by pattern matching:

  def fst (p : NatProd) : Nat :=
    match p with
    | .pair x _ => x

  def snd (p : NatProd) : Nat :=
    match p with
    | .pair _ y => y

  #eval fst (.pair 3 5)  -- 3

  /-!
  Since pairs will be used heavily in what follows, it will be convenient
  to write them with the standard mathematical notation `(x, y)` instead
  of `.pair x y`. We define a coercion from Lean's built-in product type:
  -/

  @[coe]
  def toNatProd (t : Nat × Nat) : NatProd := .pair t.1 t.2
  instance : Coe (Nat × Nat) NatProd where coe := toNatProd

  -- The coercion lets us write pairs naturally:
  #eval fst (3, 5)  -- 3

  def swapPair (p : NatProd) : NatProd :=
    match p with
    | .pair x y => .pair y x

  /-!
  If we state properties of pairs in a slightly peculiar way, we can
  sometimes complete their proofs with just `rfl`:
  -/

  theorem surjective_pairing' (n m : Nat) :
      (n, m) = (fst (n, m), snd (n, m)) := rfl

  /-!
  But just `rfl` is not enough if we state the lemma in a more natural
  way — when `p` is an unknown `NatProd`, the `match` in `fst` and `snd`
  cannot reduce. We need to expose `p`'s structure with `cases`:
  -/

  theorem surjective_pairing (p : NatProd) :
      p = (fst p, snd p) := by
    cases p with
    | pair n m => rfl

  /-!
  Notice that `cases` generates just _one_ subgoal here, because
  `NatProd` has only one constructor.
  -/

  /-!
  #### Exercise: 1 star, standard (snd_fst_is_swap)
  -/

  theorem snd_fst_is_swap (p : NatProd) :
      (snd p, fst p) = swapPair p := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 1 star, standard, optional (fst_swap_is_snd)
  -/

  theorem fst_swap_is_snd (p : NatProd) :
      fst (swapPair p) = snd p := by
    /- FILL IN HERE -/ sorry

  -- =====================================================================
  -- # Lists of Numbers
  -- =====================================================================

  /-!
  Generalizing the definition of pairs, we can describe the type of
  _lists_ of numbers like this: "A list is either the empty list or else
  a pair of a number and another list."
  -/

  inductive NatList where
    | nil
    | cons (n : Nat) (l : NatList)

  -- For example, here is a three-element list:
  def myList : NatList := .cons 1 (.cons 2 (.cons 3 .nil))

  /-!
  As with pairs, it is convenient to write lists in familiar notation.
  The following declarations allow us to use `::` as an infix `cons`
  operator and square brackets as notation for constructing lists.

  The `scoped` keyword ensures these notations are only active inside
  the `NatList` namespace (or when it is explicitly opened), so they
  do not clash with Lean's built-in `List` notations elsewhere.
  -/

  scoped infixr:60 " :: " => NatList.cons
  scoped notation "[]" => NatList.nil

  -- Lean's `scoped macro_rules` let us define list literal syntax
  -- that is confined to this namespace.
  -- We use `,` as the separator (Lean convention):
  scoped macro_rules
    | `([$hd:term , $tl:term,*]) => `(NatList.cons $(Lean.quote hd) ([$tl,*]))
    | `([$hd:term])    => `(NatList.cons $(Lean.quote hd) NatList.nil)
    | `([])      => `(NatList.nil)

  -- These three definitions are all the same list:
  def myList1 : NatList := 1 :: (2 :: (3 :: .nil))
  def myList2 : NatList := 1 :: 2 :: 3 :: .nil
  def myList3 : NatList := [1, 2, 3]

  -- ## Repeat

  /-!
  The `repeatN` function takes a number `n` and a `count` and returns a
  list of length `count` in which every element is `n`.

  (We use `repeatN` because `repeat` is a keyword in Lean.)
  -/

  def repeatN (n count : Nat) : NatList :=
    match count with
    | .zero => []
    | .succ count' => n :: repeatN n count'

  -- ## Length

  def length (l : NatList) : Nat :=
    match l with
    | [] => 0
    | _ :: t => 1 + length t

  -- ## Append

  def app (l1 l2 : NatList) : NatList :=
    match l1 with
    | [] => l2
    | h :: t => h :: app t l2

  scoped infixr:60 " ++ " => app

  example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := rfl
  example : [] ++ [4, 5] = [4, 5] := rfl
  example : [1, 2, 3] ++ [] = [1, 2, 3] := rfl

  -- ## Head and Tail

  /-!
  The `hd` function returns the first element (the "head") of the list,
  while `tl` returns everything but the first element (the "tail"). Since
  the empty list has no first element, we pass a default value to be
  returned in that case.
  -/

  def hd (default : Nat) (l : NatList) : Nat :=
    match l with
    | [] => default
    | h :: _ => h

  def tl (l : NatList) : NatList :=
    match l with
    | [] => []
    | _ :: t => t

  example : hd 0 [1, 2, 3] = 1 := rfl
  example : hd 0 [] = 0 := rfl
  example : tl [1, 2, 3] = [2, 3] := rfl

  -- ## Exercises

  /-!
  #### Exercise: 2 stars, standard, especially useful (list_funs)

  Complete the definitions of `nonzeros`, `oddmembers`, and
  `countOddMembers` below. Have a look at the tests to understand what
  these functions should do.
  -/

  def nonzeros (l : NatList) : NatList :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3] :=
    /- FILL IN HERE -/ sorry

  def oddmembers (l : NatList) : NatList :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3] :=
    /- FILL IN HERE -/ sorry

  /-!
  For the next problem, the header uses `def` rather than a recursive
  definition, to encourage you to implement the function by using
  already-defined functions rather than writing your own recursion.
  -/

  def countOddMembers (l : NatList) : Nat :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : countOddMembers [1, 0, 3, 1, 4, 5] = 4 :=
    /- FILL IN HERE -/ sorry
  example : countOddMembers [0, 2, 4] = 0 :=
    /- FILL IN HERE -/ sorry
  example : countOddMembers [] = 0 :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, advanced (alternate)

  Complete the following definition of `alternate`, which interleaves two
  lists into one, alternating between elements taken from the first list
  and elements from the second. See the tests below for examples.

  Hint: if you encounter termination issues, consider pattern matching
  against both lists at the same time.
  -/

  def alternate (l1 l2 : NatList) : NatList :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6] :=
    /- FILL IN HERE -/ sorry
  example : alternate [1] [4, 5, 6] = [1, 4, 5, 6] :=
    /- FILL IN HERE -/ sorry
  example : alternate [1, 2, 3] [4] = [1, 4, 2, 3] :=
    /- FILL IN HERE -/ sorry
  example : alternate [] [20, 30] = [20, 30] :=
    /- FILL IN HERE -/ sorry

  -- =====================================================================
  -- ## Bags via Lists
  -- =====================================================================

  /-!
  A _bag_ (or _multiset_) is like a set, except that each element can
  appear multiple times rather than just once. One way of representing a
  bag of numbers is as a list.
  -/

  def Bag := NatList

  /-!
  #### Exercise: 3 stars, standard, especially useful (bag_functions)

  Complete the following definitions for the functions `count`, `sum`,
  `add`, and `member` for bags.
  -/

  def count (v : Nat) (s : Bag) : Nat :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : count 1 [1, 2, 3, 1, 4, 1] = 3 :=
    /- FILL IN HERE -/ sorry
  example : count 6 [1, 2, 3, 1, 4, 1] = 0 :=
    /- FILL IN HERE -/ sorry

  /-!
  Multiset `sum` is similar to set union: `sum a b` contains all the
  elements of `a` and those of `b`.

  Implement `sum` in terms of an already-defined function, without
  changing the header.
  -/

  def sum : Bag → Bag → Bag :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3 :=
    /- FILL IN HERE -/ sorry

  def add (v : Nat) (s : Bag) : Bag :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : count 1 (add 1 [1, 4, 1]) = 3 :=
    /- FILL IN HERE -/ sorry
  example : count 5 (add 1 [1, 4, 1]) = 0 :=
    /- FILL IN HERE -/ sorry

  def member (v : Nat) (s : Bag) : Bool :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : member 1 [1, 4, 1] = true :=
    /- FILL IN HERE -/ sorry
  example : member 2 [1, 4, 1] = false :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard, optional (bag_more_functions)

  Here are some more bag functions for you to practice with.

  When `removeOne` is applied to a bag without the number to remove, it
  should return the same bag unchanged.
  -/

  def removeOne (v : Nat) (s : Bag) : Bag :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : count 5 (removeOne 5 [2, 1, 5, 4, 1]) = 0 :=
    /- FILL IN HERE -/ sorry
  example : count 5 (removeOne 5 [2, 1, 4, 1]) = 0 :=
    /- FILL IN HERE -/ sorry
  example : count 4 (removeOne 5 [2, 1, 4, 5, 1, 4]) = 2 :=
    /- FILL IN HERE -/ sorry
  example : count 5 (removeOne 5 [2, 1, 5, 4, 5, 1, 4]) = 1 :=
    /- FILL IN HERE -/ sorry

  def removeAll (v : Nat) (s : Bag) : Bag :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : count 5 (removeAll 5 [2, 1, 5, 4, 1]) = 0 :=
    /- FILL IN HERE -/ sorry
  example : count 5 (removeAll 5 [2, 1, 4, 1]) = 0 :=
    /- FILL IN HERE -/ sorry
  example : count 4 (removeAll 5 [2, 1, 4, 5, 1, 4]) = 2 :=
    /- FILL IN HERE -/ sorry
  example : count 5 (removeAll 5 [2, 1, 5, 4, 5, 1, 4, 5, 1, 4]) = 0 :=
    /- FILL IN HERE -/ sorry

  def included (s1 : Bag) (s2 : Bag) : Bool :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : included [1, 2] [2, 1, 4, 1] = true :=
    /- FILL IN HERE -/ sorry
  example : included [1, 2, 2] [2, 1, 4, 1] = false :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 2 stars, standard, optional (add_inc_count)

  Adding a value to a bag should increase the value's count by one. State
  this as a theorem and prove it.
  -/

  theorem add_inc_count (v : Nat) (s : Bag) :
      count v (add v s) = 1 + count v s := by
    /- FILL IN HERE -/ sorry

  -- =====================================================================
  -- # Reasoning About Lists
  -- =====================================================================

  /-!
  As with numbers, simple facts about list-processing functions can
  sometimes be proved entirely by simplification. For example, just `rfl`
  is enough for this theorem:
  -/

  theorem nil_app (l : NatList) : [] ++ l = l := rfl

  /-!
  ...because `[]` is substituted into the scrutinee (the expression being
  matched) in the definition of `app`, allowing the match to reduce.

  As with numbers, it is sometimes helpful to perform case analysis on
  the possible shapes — empty or non-empty — of an unknown list:
  -/

  theorem tl_length_pred (l : NatList) :
      Nat.pred (length l) = length (tl l) := by
    cases l with
    | nil => rfl
    | cons _ _ => simp [length, tl]

  -- =====================================================================
  -- ## Induction on Lists
  -- =====================================================================

  /-!
  Proofs by induction over datatypes like `NatList` are a little less
  familiar than standard natural number induction, but the idea is equally
  simple. Each `inductive` declaration defines a set of data values that
  can be built up using the declared constructors. Moreover, applications
  of the declared constructors are the _only_ possible shapes that
  elements of an inductively defined set can have.

  This directly gives rise to a way of reasoning about inductively defined
  sets. If we have in mind some proposition `P` that mentions a list `l`
  and we want to argue that `P` holds for _all_ lists, we can reason:

  - First, show that `P` is true of `l` when `l` is `[]`.
  - Then show that `P` is true of `l` when `l` is `n :: l'` for some
    number `n` and some smaller list `l'`, assuming that `P` is true
    for `l'`.

  Here's a concrete example:
  -/

  theorem app_assoc (l1 l2 l3 : NatList) :
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
    induction l1 with
    | nil => rfl
    | cons h t ih => simp [app]; rw [ih]

  /-!
  For comparison, here is an informal proof of the same theorem:

  - _Theorem_: For all lists `l1`, `l2`, and `l3`,
    `(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)`.

    _Proof_: By induction on `l1`.

    - First, suppose `l1 = []`. We must show

          ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

      which follows directly from the definition of `++`.

    - Next, suppose `l1 = n :: l1'`, with

          (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)     (induction hypothesis)

      We must show

          ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

      By the definition of `++`, this follows from

          n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

      which is immediate from the induction hypothesis. _Qed_.

  The form mirrors the formal proof: Lean's `induction` generates the
  same sub-goals as the bullet points a mathematician would write. The
  key difference is that the formal proof leaves the proof state implicit,
  while the informal proof reminds the reader where things stand.
  -/

  -- =====================================================================
  -- ## Generalizing Statements
  -- =====================================================================

  /-!
  In some situations, it is necessary to _generalize_ a statement in
  order to prove it by induction. Intuitively, the reason is that a more
  general statement also yields a more general (stronger) inductive
  hypothesis. If you find yourself stuck in a proof, it may help to step
  back and see whether you can prove a stronger statement.

  For example, trying to prove `repeatN n c ++ repeatN n c = repeatN n
  (c + c)` directly by induction on `c` gets stuck in the successor case,
  because the induction hypothesis only talks about `c' + c'`, not about
  an arbitrary second summand. The generalized version goes through:
  -/

  theorem repeat_plus (c1 c2 n : Nat) :
      repeatN n c1 ++ repeatN n c2 = repeatN n (c1 + c2) := by
    induction c1 with
    | zero => simp [repeatN, app]
    | succ c1' ih =>
      simp [repeatN, app]
      rw [ih, Nat.succ_add, repeatN]

  -- =====================================================================
  -- ## Reversing a List
  -- =====================================================================

  /-!
  Here we use `app` to define a list-reversing function `rev`:
  -/

  def rev (l : NatList) : NatList :=
    match l with
    | [] => []
    | h :: t => rev t ++ [h]

  example : rev [1, 2, 3] = [3, 2, 1] := rfl
  example : rev [] = [] := rfl

  /-!
  Let's prove that reversing a list does not change its length. We'll
  need a helper lemma about the length of an appended singleton:
  -/

  theorem app_length_succ (l : NatList) (n : Nat) :
      length (l ++ [n]) = Nat.succ (length l) := by
    induction l with
    | nil => rfl
    | cons h t ih => simp [app, length]; rw [ih]; omega

  theorem rev_length (l : NatList) : length (rev l) = length l := by
    induction l with
    | nil => rfl
    | cons h t ih =>
      simp [rev, length]
      rw [app_length_succ, ih]; omega

  /-!
  We can also prove a more general version of the length lemma for any
  two lists:
  -/

  theorem app_length (l1 l2 : NatList) :
      length (l1 ++ l2) = length l1 + length l2 := by
    induction l1 with
    | nil => simp [app, length]
    | cons h t ih => simp [app, length]; rw [ih]; omega

  -- =====================================================================
  -- ## Search
  -- =====================================================================

  /-!
  In Lean, you can use `#check` to inspect the type of a theorem, and
  `example` or `exact?` in tactic mode to search for applicable lemmas.
  The Lean 4 VS Code extension also provides a "Lean 4: Search" panel
  (`Ctrl+Shift+P` then search "Lean") for finding theorems by pattern.
  -/

  -- =====================================================================
  -- ## List Exercises, Part 1
  -- =====================================================================

  /-!
  #### Exercise: 3 stars, standard (list_exercises)

  More practice with lists:
  -/

  theorem app_nil_r (l : NatList) : l ++ [] = l := by
    /- FILL IN HERE -/ sorry

  theorem rev_app_distr (l1 l2 : NatList) :
      rev (l1 ++ l2) = rev l2 ++ rev l1 := by
    /- FILL IN HERE -/ sorry

  /-!
  An _involution_ is a function that is its own inverse. That is,
  applying the function twice yields the original input.
  -/

  theorem rev_involutive (l : NatList) : rev (rev l) = l := by
    /- FILL IN HERE -/ sorry

  /-!
  There is a short solution to the next one. If you find yourself getting
  tangled up, step back and try to look for a simpler way.
  -/

  theorem app_assoc4 (l1 l2 l3 l4 : NatList) :
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4 := by
    /- FILL IN HERE -/ sorry

  -- An exercise about your implementation of `nonzeros`:

  theorem nonzeros_app (l1 l2 : NatList) :
      nonzeros (l1 ++ l2) = nonzeros l1 ++ nonzeros l2 := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 2 stars, standard (eqblist)

  Fill in the definition of `eqbList`, which compares lists of numbers
  for equality. Prove that `eqbList l l` yields `true` for every list `l`.
  -/

  def eqbList (l1 l2 : NatList) : Bool :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : eqbList [] [] = true :=
    /- FILL IN HERE -/ sorry
  example : eqbList [1, 2, 3] [1, 2, 3] = true :=
    /- FILL IN HERE -/ sorry
  example : eqbList [1, 2, 3] [1, 2, 4] = false :=
    /- FILL IN HERE -/ sorry

  theorem eqbList_refl (l : NatList) : true = eqbList l l := by
    /- FILL IN HERE -/ sorry

  -- =====================================================================
  -- ## List Exercises, Part 2
  -- =====================================================================

  /-!
  Here are a couple of little theorems to prove about your definitions
  about bags above.
  -/

  /-!
  #### Exercise: 1 star, standard (count_member_nonzero)
  -/

  theorem count_member_nonzero (s : Bag) :
      (1 <=? count 1 (1 :: s)) = true := by
    /- FILL IN HERE -/ sorry

  /-!
  The following lemma about `leb` might help you in the next exercise
  (it will also be useful in later chapters).
  -/

  theorem leb_n_succ (n : Nat) : (n <=? Nat.succ n) = true := by
    induction n with
    | zero => rfl
    | succ n' ih => simp [leb]; rw [ih]

  /-!
  #### Exercise: 3 stars, advanced (remove_does_not_increase_count)
  -/

  theorem remove_does_not_increase_count (s : Bag) :
      (count 0 (removeOne 0 s) <=? count 0 s) = true := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard, optional (bag_count_sum)

  Write down an interesting theorem about bags involving the functions
  `count` and `sum`, and prove it. (You may find that the difficulty of
  the proof depends on how you defined `count`!)
  -/

  -- /- FILL IN HERE -/

  /-!
  #### Exercise: 3 stars, advanced (involution_injective)

  Prove that every involution is injective. An _injective_ function is
  one-to-one: it maps distinct inputs to distinct outputs, without any
  collisions.
  -/

  theorem involution_injective (f : Nat → Nat)
      (h : ∀ n : Nat, n = f (f n))
      (n1 n2 : Nat) (heq : f n1 = f n2) : n1 = n2 := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 2 stars, advanced (rev_injective)

  Prove that `rev` is injective. Do not prove this by induction — that
  would be hard. Instead, re-use the same proof technique that you used
  for `involution_injective`.
  -/

  theorem rev_injective (l1 l2 : NatList)
      (h : rev l1 = rev l2) : l1 = l2 := by
    /- FILL IN HERE -/ sorry

  -- =====================================================================
  -- # Options
  -- =====================================================================

  /-!
  Suppose we want to write a function that returns the nth element of
  some list. If we give it type `NatList → Nat → Nat`, then we'll have to
  choose some number to return when the list is too short...
  -/

  def nthBad (l : NatList) (n : Nat) : Nat :=
    match l with
    | [] => 42
    | a :: l' =>
      match n with
      | 0 => a
      | .succ n' => nthBad l' n'

  /-!
  This solution is not so good: if `nthBad` returns 42, we don't know
  whether that value actually appears in the input or whether we gave bad
  arguments. A better alternative is to change the return type to include
  an error value as a possible outcome. We call this type `NatOption`.
  -/

  inductive NatOption where
    | some (n : Nat)
    | none

  /-!
  We can then rewrite the function to return `.none` when the list is too
  short and `.some a` when the list has enough members:
  -/

  def nthError (l : NatList) (n : Nat) : NatOption :=
    match l with
    | [] => .none
    | a :: l' =>
      match n with
      | 0 => .some a
      | .succ n' => nthError l' n'

  example : nthError [4, 5, 6, 7] 0 = .some 4 := rfl
  example : nthError [4, 5, 6, 7] 3 = .some 7 := rfl
  example : nthError [4, 5, 6, 7] 9 = .none := rfl

  /-!
  The function below pulls the `Nat` out of a `NatOption`, returning a
  supplied default in the `.none` case.
  -/

  def optionElim (d : Nat) (o : NatOption) : Nat :=
    match o with
    | .some n' => n'
    | .none => d

  /-!
  #### Exercise: 2 stars, standard (hd_error)

  Using the same idea, fix the `hd` function from earlier so we don't
  have to pass a default element for the `nil` case.
  -/

  def hdError (l : NatList) : NatOption :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : hdError [] = .none :=
    /- FILL IN HERE -/ sorry
  example : hdError [1] = .some 1 :=
    /- FILL IN HERE -/ sorry
  example : hdError [5, 6] = .some 5 :=
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 1 star, standard, optional (option_elim_hd)

  This exercise relates your new `hdError` to the old `hd`.
  -/

  theorem option_elim_hd (l : NatList) (default : Nat) :
      hd default l = optionElim default (hdError l) := by
    /- FILL IN HERE -/ sorry

end NatList

-- =====================================================================
-- # Partial Maps
-- =====================================================================

/-!
As a final illustration of how data structures can be defined, here is
a simple _partial map_ data type, analogous to the map or dictionary
data structures found in most programming languages.

First, we define a new inductive datatype `MyId` to serve as the "keys"
of our partial maps. (We use `MyId` because `id` is already defined in
Lean's standard library.)
-/

inductive MyId where
  | mk (n : Nat)

/-!
Internally, a `MyId` is just a number. Introducing a separate type by
wrapping each `Nat` with the tag `mk` makes definitions more readable
and gives us flexibility to change representations later.
-/

def eqbId (x1 x2 : MyId) : Bool :=
  match x1, x2 with
  | .mk n1, .mk n2 => n1 =? n2

/-!
#### Exercise: 1 star, standard (eqb_id_refl)
-/

theorem eqb_id_refl (x : MyId) : eqbId x x = true := by
  /- FILL IN HERE -/ sorry

/-!
Now we define the type of partial maps:
-/

namespace PartialMap
  export NatList (NatOption)

  inductive PartialMap where
    | empty
    | record (i : MyId) (v : Nat) (m : PartialMap)

  /-!
  The `update` function overrides the entry for a given key in a partial
  map by shadowing it with a new one (or simply adds a new entry if the
  given key is not already present).
  -/

  def update (d : PartialMap) (x : MyId) (value : Nat) : PartialMap :=
    .record x value d

  /-!
  The `find` function searches a `PartialMap` for a given key. It returns
  `.none` if the key was not found and `.some val` if the key was
  associated with `val`. If the same key is mapped to multiple values,
  `find` will return the first one it encounters.
  -/

  def find (x : MyId) (d : PartialMap) : NatOption :=
    match d with
    | .empty => .none
    | .record y v d' =>
      if eqbId x y then .some v else find x d'

  /-!
  #### Exercise: 1 star, standard (update_eq)
  -/

  theorem update_eq (d : PartialMap) (x : MyId) (v : Nat) :
      find x (update d x v) = .some v := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 1 star, standard (update_neq)
  -/

  theorem update_neq (d : PartialMap) (x y : MyId) (o : Nat)
      (h : eqbId x y = false) : find x (update d y o) = find x d := by
    /- FILL IN HERE -/ sorry

end PartialMap
