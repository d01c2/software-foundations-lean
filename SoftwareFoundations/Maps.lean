/-!
# Maps: Total and Partial Maps

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html>
-/

/-!
Maps (or dictionaries) are ubiquitous data structures both in ordinary
programming and in the theory of programming languages; we need them in
many places in the coming chapters.

They also make a nice case study using ideas we've seen in previous
chapters, including building data structures out of higher-order
functions (from `Basics` and `Poly`) and the use of reflection to
streamline proofs (from `IndProp`).

We define two flavors of maps: *total maps*, which include a "default"
element to be returned when a key being looked up doesn't exist, and
*partial maps*, which instead return an `Option` to indicate success or
failure. Partial maps are defined in terms of total maps, using `none`
as the default element.
-/

-- =====================================================================
-- # The Lean Standard Library
-- =====================================================================

/-!
This chapter is self-contained -- it uses definitions and theorems
directly from Lean's standard library rather than importing previous
chapters.

Lean provides several useful commands for exploring the library:

- `#check` shows the type of an expression.
- `#print` shows the full definition of a term.
- `exact?` and `apply?` search for lemmas that close the current goal.
-/

#check (Nat.add : Nat → Nat → Nat)

-- =====================================================================
-- # Identifiers
-- =====================================================================

/-!
To define maps, we first need a type for the keys that we will use to
index into our maps. We use the `String` type from Lean's standard
library.

Lean's `String` has a `DecidableEq` instance, so we can compare strings
with `==` (boolean) or use `if x = y then ... else ...` (propositional,
via decidability). We also get `BEq` and `LawfulBEq` instances, giving
us useful lemmas like `beq_iff_eq`.
-/

#check (inferInstance : DecidableEq String)
#check @beq_iff_eq (α := String)
#check @beq_self_eq_true (α := String)
#check @bne_iff_ne (α := String)

-- =====================================================================
-- # Total Maps
-- =====================================================================

/-!
Our main job in this chapter will be to build a definition of partial
maps that is similar in behavior to the one we saw in the `Lists`
chapter, plus accompanying lemmas about its behavior.

This time around, though, we're going to use *functions*, rather than
lists of key-value pairs, to build maps. The advantage of this
representation is that it offers a more "extensional" view of maps:
two maps that respond to queries in the same way will be represented
as exactly the same function, rather than just as "equivalent" list
structures. This, together with the `funext` axiom, simplifies proofs
that use maps.
-/

/-!
We build up to partial maps in two steps. First, we define a type of
*total maps* that return a default value when we look up a key that is
not present in the map.

A total map over an element type `α` is just a function from `String`
to `α`.
-/

def TotalMap (α : Type) := String → α

/-!
Intuitively, a total map over an element type `α` is just a function
that can be used to look up `String`s, yielding `α`s.

The function `tEmpty` yields an empty total map, given a default
element; this map always returns the default element when applied to
any string.
-/

def tEmpty {α : Type} (v : α) : TotalMap α :=
  fun _ => v

/-!
More interesting is the map-updating function, which takes a map `m`,
a key `x`, and a value `v` and returns a new map that takes `x` to `v`
and takes every other key to whatever `m` does. The novelty here is
that we achieve this effect by wrapping a new function around the old
one.
-/

def tUpdate {α : Type} (m : TotalMap α) (x : String) (v : α) : TotalMap α :=
  fun x' => if x == x' then v else m x'

/-!
This definition is a nice example of higher-order programming:
`tUpdate` takes a *function* `m` and yields a new function
`fun x' => ...` that behaves like the desired map.

For example, we can build a map taking `String`s to `Bool`s, where
`"foo"` and `"bar"` are mapped to `true` and every other key is
mapped to `false`, like this:
-/

def exampleMap :=
  tUpdate (tUpdate (tEmpty false) "foo" true) "bar" true

/-!
Next, let's introduce some notations to facilitate working with maps.

- `t! v` represents an empty total map with default value `v`.
- `(x !→ v; m)` extends map `m` by binding key `x` to value `v`.

Looking up a key is just function application — no separate `find`
needed.
-/

notation:100 "t! " v => tEmpty v
notation:100 x " !→ " v "; " m => tUpdate m x v

-- We also provide a "singleton state" notation for later use in `Imp`,
-- where maps default to `0`.
notation:100 x " !→ " v => tUpdate (tEmpty 0) x v

-- The `exampleMap` above can now be defined as follows:

def exampleMap' : TotalMap Bool :=
  ("bar" !→ true; "foo" !→ true; t! false)

/-!
This completes the definition of total maps. Note that we don't need
to define a `find` operation on this representation of maps because it
is just function application!
-/

#eval exampleMap' "baz"   -- false
#eval exampleMap' "foo"   -- true

example : exampleMap' "baz" = false := rfl
example : exampleMap' "foo" = true := rfl
example : exampleMap' "quux" = false := rfl
example : exampleMap' "bar" = true := rfl

/-!
When we use maps in later chapters, we'll need several fundamental
facts about how they behave.

Even if you don't work the following exercises, make sure you
thoroughly understand the statements of the lemmas!

Some of the proofs require the functional extensionality axiom
(`funext`), which is available as a built-in in Lean.
-/

/-!
#### Exercise: 1 star, standard, optional (t_apply_empty)

The empty map returns its default element for all keys.
-/

theorem t_apply_empty (α : Type) (x : String) (v : α) :
    (t! v) x = v := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, optional (t_update_eq)

If we update a map `m` at a key `x` with a new value `v` and then
look up `x` in the resulting map, we get back `v`.
-/

theorem t_update_eq (α : Type) (m : TotalMap α) (x : String) (v : α) :
    (x !→ v; m) x = v := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, optional (t_update_neq)

If we update a map `m` at a key `x1` and then look up a *different*
key `x2` in the resulting map, we get the same result that `m` would
have given.
-/

theorem t_update_neq (α : Type) (m : TotalMap α) (x1 x2 : String) (v : α)
    (h : x1 ≠ x2) : (x1 !→ v; m) x2 = m x2 := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, optional (t_update_shadow)

If we update a map `m` at key `x` with `v1` then again at `x` with
`v2`, the result behaves the same as just updating `m` at `x` with
`v2`.
-/

theorem t_update_shadow (α : Type) (m : TotalMap α) (x : String) (v1 v2 : α) :
    (x !→ v2; x !→ v1; m) = (x !→ v2; m) := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard (t_update_same)

Given `String`s `x1` and `x2`, we can use `by_cases (h : x1 = x2)` to
simultaneously perform case analysis and generate hypotheses about
the equality of `x1` and `x2`. Use this to prove the following theorem,
which states that if we update a map to assign key `x` the same value
as it already has in `m`, then the result is equal to `m`.
-/

theorem t_update_same (α : Type) (m : TotalMap α) (x : String) :
    (x !→ m x; m) = m := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard, especially useful (t_update_permute)

Use `by_cases` to prove one final property of the `update` function:
If we update a map `m` at two distinct keys, it doesn't matter in
which order we do the updates.
-/

theorem t_update_permute (α : Type) (m : TotalMap α) (v1 v2 : α)
    (x1 x2 : String) (h : x2 ≠ x1) :
    (x1 !→ v1; x2 !→ v2; m) = (x2 !→ v2; x1 !→ v1; m) := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Partial Maps
-- =====================================================================

/-!
Lastly, we define *partial maps* on top of total maps. A partial map
with elements of type `α` is simply a total map with elements of type
`Option α` and default element `none`.
-/

namespace Maps

  def PartialMap (α : Type) := TotalMap (Option α)

  def PartialMap.empty {α : Type} : PartialMap α :=
    tEmpty none

  def PartialMap.update {α : Type} (m : PartialMap α)
      (x : String) (v : α) : PartialMap α :=
    (x !→ some v; m)

  -- We introduce a similar notation for partial maps:
  scoped notation:100 x " ↦ " v "; " m => PartialMap.update m x v

  -- We can also hide the last case when it is empty.
  scoped notation:100 x " ↦ " v => PartialMap.update PartialMap.empty x v

  def examplePmap :=
    ("Church" ↦ true; "Turing" ↦ false)

  /-!
  We now straightforwardly lift all of the basic lemmas about total maps
  to partial maps.
  -/

  theorem PartialMap.apply_empty (α : Type) (x : String) :
      @PartialMap.empty α x = none :=
    t_apply_empty (Option α) x none

  theorem PartialMap.update_eq (α : Type) (m : PartialMap α)
      (x : String) (v : α) : (x ↦ v; m) x = some v :=
    t_update_eq (Option α) m x (some v)

  /-!
  The `PartialMap.update_eq` lemma is used very often in proofs. Adding
  it to Lean's `simp` set allows automation tactics to find it.
  -/
  attribute [simp] PartialMap.update_eq

  theorem PartialMap.update_neq (α : Type) (m : PartialMap α)
      (x1 x2 : String) (v : α) (h : x2 ≠ x1) :
      (x2 ↦ v; m) x1 = m x1 :=
    t_update_neq (Option α) m x2 x1 (some v) h

  theorem PartialMap.update_shadow (α : Type) (m : PartialMap α)
      (x : String) (v1 v2 : α) :
      (x ↦ v2; x ↦ v1; m) = (x ↦ v2; m) :=
    t_update_shadow (Option α) m x (some v1) (some v2)

  theorem PartialMap.update_same (α : Type) (m : PartialMap α)
      (x : String) (v : α) (h : m x = some v) :
      (x ↦ v; m) = m := by
    unfold PartialMap.update; rw [← h]; exact t_update_same (Option α) m x

  theorem PartialMap.update_permute (α : Type) (m : PartialMap α)
      (x1 x2 : String) (v1 v2 : α) (h : x2 ≠ x1) :
      (x1 ↦ v1; x2 ↦ v2; m) = (x2 ↦ v2; x1 ↦ v1; m) :=
    t_update_permute (Option α) m (some v1) (some v2) x1 x2 h

  /-!
  One last thing: For partial maps, it's convenient to introduce a
  notion of map inclusion, stating that all the entries in one map are
  also present in another:
  -/

  def PartialMap.includedIn {α : Type} (m m' : PartialMap α) : Prop :=
    ∀ x v, m x = some v → m' x = some v

  -- We can then show that map update preserves map inclusion:

  theorem PartialMap.includedIn_update (α : Type) (m m' : PartialMap α)
      (x : String) (vx : α) (h : PartialMap.includedIn m m') :
      PartialMap.includedIn (x ↦ vx; m) (x ↦ vx; m') := by
    intro y vy hm
    by_cases hxy : x = y
    · subst hxy
      rw [PartialMap.update_eq] at hm
      rw [PartialMap.update_eq]
      exact hm
    · rw [PartialMap.update_neq α m y x vx hxy] at hm
      rw [PartialMap.update_neq α m' y x vx hxy]
      exact h y vy hm

  /-!
  This property is quite useful for reasoning about languages with
  variable binding -- e.g., the Simply Typed Lambda Calculus, which we
  will see in *Programming Language Foundations*, where maps are used to
  keep track of which program variables are defined in a given scope.
  -/

end Maps
