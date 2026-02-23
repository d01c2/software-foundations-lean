import SoftwareFoundations.Lists

/-!
# Poly: Polymorphism and Higher-Order Functions

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html>
-/

/-!
In this chapter we continue our development of basic concepts of
functional programming. The critical new ideas are _polymorphism_
(abstracting functions over the types of the data they manipulate)
and _higher-order functions_ (treating functions as data). We begin
with polymorphism.
-/

-- =====================================================================
-- # Polymorphism
-- =====================================================================

-- ## Polymorphic Lists

/-!
In the last chapter, we worked with lists containing just numbers.
Obviously, interesting programs also need to be able to manipulate
lists with elements from other types — lists of booleans, lists of
lists, etc. We _could_ just define a new inductive datatype for each
of these, for example...
-/

inductive BoolList where
  | nil
  | cons (b : Bool) (l : BoolList)

/-!
...but this would quickly become tedious: not only would we have to
make up different constructor names for each datatype, but — even
worse — we would also need to define new versions of all the list
manipulating functions (`length`, `app`, `rev`, etc.) and all their
properties (`rev_length`, `app_assoc`, etc.) for each new definition.

To avoid this, Lean supports _polymorphic_ inductive type definitions.
In fact, Lean's own `List α` is exactly this — a list parameterized
by the element type `α`.

Here is how we can define a polymorphic list from scratch:
-/

namespace PolyPlayground

  inductive MyList (α : Type) where
    | nil
    | cons (x : α) (l : MyList α)

  /-!
  This is exactly like the definition of `NatList` from the previous
  chapter, except that the `Nat` argument to the `cons` constructor has
  been replaced by an arbitrary type `α`, a binding for `α` has been
  added to the header, and occurrences of `NatList` in the types of the
  constructors have been replaced by `MyList α`.

  What sort of thing is `MyList` itself? A good way to think about it
  is that `MyList` is a _function_ from `Type`s to `Type`s. For any
  particular type `α`, the type `MyList α` is the inductively defined
  set of lists whose elements are of type `α`.
  -/

  #check (MyList : Type → Type)

  /-!
  The `α` in the definition of `MyList` automatically becomes a
  parameter to the constructors `nil` and `cons`. When we use them, Lean
  infers the type parameter from context.
  -/

  #check (MyList.nil : MyList Nat)
  #check (MyList.cons 3 .nil : MyList Nat)

  /-!
  In Lean, the type of `MyList.nil` is `MyList α` where `α` is
  inferred from context. Similarly, `MyList.cons` takes an element of
  type `α` and a `MyList α`, returning a `MyList α`. If Lean cannot
  infer the type, we can provide it explicitly with a type annotation:

      (MyList.nil : MyList Nat)

  or with the `(α := Nat)` syntax:

      @MyList.nil Nat
  -/

  /-!
  We can now define polymorphic versions of all the list-processing
  functions that we wrote before. Here is `repeatN`, for example:
  -/

  def repeatN (x : α) (count : Nat) : MyList α :=
    match count with
    | 0 => .nil
    | .succ count' => .cons x (repeatN x count')

  example : repeatN 4 2 = .cons 4 (.cons 4 .nil) := rfl
  example : repeatN false 1 = .cons false .nil := rfl

end PolyPlayground

/-!
In what follows, we will use Lean's built-in `List α` instead of our
hand-rolled `MyList`. Lean's lists come with standard notation:

- `[]` for the empty list
- `x :: xs` for cons
- `[1, 2, 3]` for list literals

Since Lean's `List` is already polymorphic, we get polymorphism for
free.
-/

/-!
#### Exercise: 2 stars, standard, optional (mumble_grumble)

Consider the inductive types `mumble` and `grumble` from the SF chapter,
and determine which candidate terms are well-typed inhabitants of
`grumble X`.
-/

/- FILL IN HERE -/

/-!
#### Exercise: 2 stars, standard (poly_exercises)

Here are a few simple exercises for practice with polymorphism.
Complete the proofs below.
-/

theorem app_nil_r {α : Type} (l : List α) : l ++ [] = l := by
  /- FILL IN HERE -/ sorry

theorem app_assoc {α : Type} (l m n : List α) :
    l ++ m ++ n = (l ++ m) ++ n := by
  /- FILL IN HERE -/ sorry

theorem app_length {α : Type} (l1 l2 : List α) :
    (l1 ++ l2).length = l1.length + l2.length := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard (more_poly_exercises)

Here are some slightly more interesting ones...
-/

theorem rev_app_distr {α : Type} (l1 l2 : List α) :
    (l1 ++ l2).reverse = l2.reverse ++ l1.reverse := by
  /- FILL IN HERE -/ sorry

theorem rev_involutive {α : Type} (l : List α) :
    l.reverse.reverse = l := by
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## Polymorphic Pairs
-- =====================================================================

/-!
Following the same pattern, the definition of pairs of numbers that we
gave in the last chapter can be generalized to _polymorphic pairs_,
often called _products_. Lean's built-in `Prod α β` (written `α × β`)
serves this purpose, but let's see how to define it from scratch:
-/

namespace ProdPlayground

  inductive MyProd (α β : Type) where
    | pair (x : α) (y : β)

  /-!
  In Lean, we already have the built-in product type `α × β` with
  constructor `(a, b)` and projections `.1` (or `.fst`) and `.2`
  (or `.snd`). From here on, we will use Lean's built-in products.
  -/

end ProdPlayground

/-!
Lean's built-in projections and pattern matching make working with
pairs easy:
-/

def myFst {α β : Type} (p : α × β) : α := p.1
def mySnd {α β : Type} (p : α × β) : β := p.2

/-!
The following function takes two lists and combines them into a list
of pairs. In many functional languages it is called `zip`; Lean's
standard library calls it `List.zip`.
-/

def combine {α β : Type} (lx : List α) (ly : List β)
    : List (α × β) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: combine tx ty

#eval combine [1, 2] [false, false, true, true]
-- [(1, false), (2, false)]

/-!
#### Exercise: 1 star, standard, optional (combine_checks)

Try answering the following questions on paper and checking your
answers:
- What is the type of `combine`?
- What does `combine [1, 2] [false, false, true, true]` return?
-/

/-!
#### Exercise: 2 stars, standard, especially useful (split)

The function `split` is the right inverse of `combine`: it takes a
list of pairs and returns a pair of lists. In many functional
languages, it is called `unzip`.

Fill in the definition of `split` below. Make sure it passes the
given unit test.
-/

def split {α β : Type} (l : List (α × β)) : List α × List β :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : split [(1, false), (2, false)] = ([1, 2], [false, false]) :=
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## Polymorphic Options
-- =====================================================================

/-!
Lean's standard library provides `Option α`, which generalizes the
`NatOption` type from the previous chapter. It has two constructors:

- `some (x : α)` — carries a value
- `none` — signals the absence of a value

We can rewrite the `nthError` function so that it works with any type
of list:
-/

def nthError {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | a :: l' =>
    match n with
    | 0 => some a
    | .succ n' => nthError l' n'

example : nthError [4, 5, 6, 7] 0 = some 4 := rfl
example : nthError [[1], [2]] 1 = some [2] := rfl
example : nthError [true] 2 = none := rfl

/-!
#### Exercise: 1 star, standard, optional (hd_error_poly)

Complete the definition of a polymorphic version of the `hdError`
function from the last chapter. Be sure that it passes the unit
tests below.
-/

def hdError {α : Type} (l : List α) : Option α :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

#check (@hdError : {α : Type} → List α → Option α)

example : hdError [1, 2] = some 1 :=
  /- FILL IN HERE -/ sorry
example : hdError [[1], [2]] = some [1] :=
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- # Functions as Data
-- =====================================================================

/-!
Like most modern programming languages — especially other "functional"
languages, including OCaml, Haskell, Racket, Scala, Clojure, etc. —
Lean treats functions as first-class citizens, allowing them to be
passed as arguments to other functions, returned as results, stored in
data structures, etc.
-/

-- =====================================================================
-- ## Higher-Order Functions
-- =====================================================================

/-!
Functions that manipulate other functions are often called
_higher-order_ functions. Here's a simple one:
-/

def doit3times {α : Type} (f : α → α) (n : α) : α :=
  f (f (f n))

/-!
The argument `f` here is itself a function (from `α` to `α`); the
body of `doit3times` applies `f` three times to some value `n`.
-/

#check (@doit3times : {α : Type} → (α → α) → α → α)

example : doit3times minusTwo 9 = 3 := rfl
example : doit3times (!·) true = false := rfl

-- =====================================================================
-- ## Filter
-- =====================================================================

/-!
Here is a more useful higher-order function, taking a list of `α`s
and a _predicate_ on `α` (a function from `α` to `Bool`) and
"filtering" the list to yield a new list containing just those
elements for which the predicate returns `true`.
-/

def filter {α : Type} (test : α → Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: filter test t
    else filter test t

/-!
For example, if we apply `filter` to the predicate `even` and a list
of numbers, it returns a list containing just the even members.
-/

example : filter even [1, 2, 3, 4] = [2, 4] := rfl

def lengthIs1 {α : Type} (l : List α) : Bool :=
  l.length == 1

example :
    filter lengthIs1 [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := rfl

/-!
We can use `filter` to give a concise version of the
`countOddMembers` function from the `Lists` chapter.
-/

def countOddMembers' (l : List Nat) : Nat :=
  (filter odd l).length

example : countOddMembers' [1, 0, 3, 1, 4, 5] = 4 := rfl
example : countOddMembers' [0, 2, 4] = 0 := rfl
example : countOddMembers' [] = 0 := rfl

-- =====================================================================
-- ## Anonymous Functions
-- =====================================================================

/-!
It is arguably a little sad, in the example just above, to be forced
to define the function `lengthIs1` and give it a name just to be able
to pass it as an argument to `filter`, since we will probably never
use it again. Indeed, when using higher-order functions, we _often_
want to pass as arguments "one-off" functions that we will never use
again; having to give each of these functions a name would be tedious.

Fortunately, we can construct a function "on the fly" without declaring
it at the top level or giving it a name:
-/

example : doit3times (fun n => n * n) 2 = 256 := rfl

/-!
The expression `fun n => n * n` can be read as "the function that,
given a number `n`, yields `n * n`."

Lean also supports the lightweight `·` (term-hole) syntax for simple
anonymous functions, where `·` stands for the argument:
-/

example : doit3times (· + 1) 5 = 8 := rfl

-- Here is the `filter` example, rewritten to use an anonymous function:
example :
    filter (fun l => l.length == 1)
           [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := rfl

/-!
#### Exercise: 2 stars, standard (filter_even_gt7)

Use `filter` (instead of a recursive `def`) to write a function
`filterEvenGt7` that takes a list of natural numbers as input and
returns a list of just those that are even and greater than 7.
-/

def filterEvenGt7 (l : List Nat) : List Nat :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : filterEvenGt7 [1, 2, 6, 9, 10, 3, 12, 8] = [10, 12, 8] :=
  /- FILL IN HERE -/ sorry

example : filterEvenGt7 [5, 2, 6, 19, 129] = [] :=
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 3 stars, standard (partition)

Use `filter` to write a function `partition` that, given a type `α`,
a predicate of type `α → Bool`, and a `List α`, returns a pair of
lists. The first member of the pair is the sublist of the original
list containing the elements that satisfy the test, and the second is
the sublist containing those that fail the test. The order of
elements in the two sublists should be the same as their order in the
original list.
-/

def partition {α : Type}
    (test : α → Bool)
    (l : List α)
    : List α × List α :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : partition odd [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) :=
  /- FILL IN HERE -/ sorry
example : partition (fun _ => false) [5, 9, 0] = ([], [5, 9, 0]) :=
  /- FILL IN HERE -/ sorry

-- =====================================================================
-- ## Map
-- =====================================================================

/-!
Another handy higher-order function is called `map`.
-/

def map {α β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | h :: t => f h :: map f t

/-!
It takes a function `f` and a list `[n1, n2, n3, ...]` and returns
the list `[f n1, f n2, f n3, ...]`, where `f` has been applied to
each element in turn. For example:
-/

example : map (fun x => x + 3) [2, 0, 2] = [5, 3, 5] := rfl

/-!
The element types of the input and output lists need not be the
same, since `map` takes _two_ type arguments, `α` and `β`; it can
thus be applied to a list of numbers and a function from numbers to
booleans to yield a list of booleans:
-/

example : map odd [2, 1, 2, 5] = [false, true, false, true] := rfl

/-!
It can even be applied to a list of numbers and a function from
numbers to _lists_ of booleans to yield a _list of lists_ of
booleans:
-/

example :
    map (fun n => [even n, odd n]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]] := rfl

-- ## Exercises

/-!
#### Exercise: 3 stars, standard (map_rev)

Show that `map` and `rev` commute. You may need to define an
auxiliary lemma.
-/

theorem map_rev {α β : Type} (f : α → β) (l : List α) :
    map f l.reverse = (map f l).reverse := by
  /- FILL IN HERE -/ sorry

/-!
#### Exercise: 2 stars, standard, especially useful (flat_map)

The function `map` maps a `List α` to a `List β` using a function
of type `α → β`. We can define a similar function, `flatMap`, which
maps a `List α` to a `List β` using a function `f` of type
`α → List β`. Your definition should work by "flattening" the
results of `f`, like so:

    flatMap (fun n => [n, n + 1, n + 2]) [1, 5, 10]
      = [1, 2, 3, 5, 6, 7, 10, 11, 12]
-/

def flatMap {α β : Type} (f : α → List β) (l : List α)
    : List β :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example :
    flatMap (fun n => [n, n, n]) [1, 5, 4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4] :=
  /- FILL IN HERE -/ sorry

/-!
Lists are not the only inductive type for which `map` makes sense.
Here is a `map` for the `Option` type:
-/

def optionMap {α β : Type} (f : α → β) (xo : Option α)
    : Option β :=
  match xo with
  | none => none
  | some x => some (f x)

/-!
#### Exercise: 2 stars, standard, optional (implicit_args)

Replace selected implicit parameters with explicit ones and check which
type arguments Lean can infer.
-/

-- =====================================================================
-- ## Fold
-- =====================================================================

/-!
An even more powerful higher-order function is called `fold`. This
function is the inspiration for the "reduce" operation that lies at
the heart of Google's map/reduce distributed programming framework.
-/

def fold {α β : Type} (f : α → β → β) (l : List α) (b : β)
    : β :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)

/-!
Intuitively, the behavior of the `fold` operation is to insert a given
binary operator `f` between every pair of elements in a given list.
For example, `fold (· + ·) [1, 2, 3, 4]` intuitively means
`1 + 2 + 3 + 4`. To make this precise, we also need a "starting
element" that serves as the initial second input to `f`. So, for
example,

    fold (· + ·) [1, 2, 3, 4] 0

yields

    1 + (2 + (3 + (4 + 0))).
-/

example : fold (· && ·) [true, true, false, true] true = false := rfl
example : fold (· * ·) [1, 2, 3, 4] 1 = 24 := rfl
example : fold (· ++ ·) [[1], [], [2, 3], [4]] [] = [1, 2, 3, 4] := rfl
example : fold (fun l n => l.length + n) [[1], [], [2, 3, 2], [4]] 0 = 5 := rfl

/-!
#### Exercise: 1 star, standard, optional (fold_types_different)

Give another example where `fold` is useful with different element and
accumulator types.
-/

/- FILL IN HERE -/

-- =====================================================================
-- ## Functions That Construct Functions
-- =====================================================================

/-!
Most of the higher-order functions we have talked about so far take
functions as arguments. Let's look at some examples that involve
_returning_ functions as the results of other functions. To begin,
here is a function that takes a value `x` (drawn from some type `α`)
and returns a function from `Nat` to `α` that yields `x` whenever it
is called, ignoring its `Nat` argument.
-/

def constFun {α : Type} (x : α) : Nat → α :=
  fun _ => x

def ftrue := constFun true

example : ftrue 0 = true := rfl
example : (constFun 5) 99 = 5 := rfl

/-!
In fact, the multiple-argument functions we have already seen are also
examples of passing functions as data. To see why, recall the type
of `Nat.add`:
-/

#check (Nat.add : Nat → Nat → Nat)

/-!
Each `→` in this type is actually a _binary_ operator on types. This
operator is _right-associative_, so the type of `Nat.add` is really a
shorthand for `Nat → (Nat → Nat)` — i.e., it reads as "a function
that takes a `Nat` and returns a function from `Nat` to `Nat`." When
we apply `Nat.add` to just one argument, we get a new function:
-/

def plus3 := Nat.add 3
#check (plus3 : Nat → Nat)

example : plus3 4 = 7 := rfl
example : doit3times plus3 0 = 9 := rfl
example : doit3times (· + 3) 0 = 9 := rfl

/-!
This is called *partial application*. We can think of `fold` not as
a three-argument function, but as a one-argument function that:

1. Takes an argument `f` of type `α → β → β`
2. Returns a function of type `List α → β → β` that "remembers" `f`

When we write `fold (· + ·)`, we're giving `fold` its first argument
and getting back a specialized function that can sum up the elements
of any list of numbers. This new function still expects two more
arguments: a list and a starting value.
-/

-- =====================================================================
-- # Additional Exercises
-- =====================================================================

namespace Exercises

  /-!
  #### Exercise: 2 stars, standard (fold_length)

  Many common functions on lists can be implemented in terms of `fold`.
  For example, here is an alternative definition of `length`:
  -/

  def foldLength {α : Type} (l : List α) : Nat :=
    fold (fun _ n => n + 1) l 0

  example : foldLength [4, 7, 0] = 3 := rfl

  /-!
  Prove the correctness of `foldLength`.

  Hint: it may help to use `unfold foldLength` before `simp` or
  `induction` so that Lean can see the `fold` inside.
  -/

  theorem fold_length_correct {α : Type} (l : List α) :
      foldLength l = l.length := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 3 stars, standard (fold_map)

  We can also define `map` in terms of `fold`. Finish `foldMap` below.
  -/

  def foldMap {α β : Type} (f : α → β) (l : List α) : List β :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  /-!
  Write down a theorem `fold_map_correct` stating that `foldMap` is
  correct, and prove it.
  -/

  theorem fold_map_correct {α β : Type} (f : α → β) (l : List α) :
      foldMap f l = map f l := by
    /- FILL IN HERE -/ sorry

  /-!
  #### Exercise: 2 stars, advanced (currying)

  The type `α → β → γ` can be read as describing functions that take
  two arguments, one of type `α` and another of type `β`, and return
  an output of type `γ`. Recall from our discussion of partial
  application that this type is written `α → (β → γ)` when fully
  parenthesized. That is, if we have `f : α → β → γ`, and we give `f`
  an input of type `α`, it will give us as output a function of type
  `β → γ`. If we then give that function an input of type `β`, it will
  return an output of type `γ`. That is, every function in Lean takes
  only one input, but some functions return a function as output. This
  is precisely what enables partial application.

  By contrast, functions of type `α × β → γ` — which when fully
  parenthesized is written `(α × β) → γ` — require their single input
  to be a pair. Both arguments must be given at once; there is no
  possibility of partial application.

  It is possible to convert a function between these two types.
  Converting from `α × β → γ` to `α → β → γ` is called _currying_, in
  honor of the logician Haskell Curry. Converting from `α → β → γ` to
  `α × β → γ` is called _uncurrying_.
  -/

  -- We can define currying as follows:
  def prodCurry {α β γ : Type}
      (f : α × β → γ) (x : α) (y : β) : γ :=
    f (x, y)

  -- As an exercise, define its inverse, `prodUncurry`:
  def prodUncurry {α β γ : Type}
      (f : α → β → γ) (p : α × β) : γ :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  -- As a (trivial) example of the usefulness of currying:
  example : map (· + 3) [2, 0, 2] = [5, 3, 5] := rfl

  #check (@prodCurry : {α β γ : Type} → (α × β → γ) → α → β → γ)
  #check (@prodUncurry : {α β γ : Type} → (α → β → γ) → α × β → γ)

  theorem uncurry_curry {α β γ : Type}
      (f : α → β → γ) (x : α) (y : β) :
      prodCurry (prodUncurry f) x y = f x y := by
    /- FILL IN HERE -/ sorry

  theorem curry_uncurry {α β γ : Type}
      (f : α × β → γ) (p : α × β) :
      prodUncurry (prodCurry f) p = f p := by
    /- FILL IN HERE -/ sorry

  -- =====================================================================
  -- ## Church Numerals (Advanced)
  -- =====================================================================

  /-!
  The following exercises explore an alternative way of defining natural
  numbers using the _Church numerals_, which are named after their
  inventor, the mathematician Alonzo Church. We can represent a natural
  number `n` as a function that takes a function `f` as a parameter and
  returns `f` iterated `n` times.
  -/

  namespace Church

    def Cnat := (α : Type) → (α → α) → α → α

    /-!
    Let's see how to write some numbers with this notation. Iterating a
    function once should be the same as just applying it. Thus:
    -/

    def one : Cnat :=
      fun _ f x => f x

    -- Similarly, `two` should apply `f` twice to its argument:
    def two : Cnat :=
      fun _ f x => f (f x)

    /-!
    Defining `zero` is somewhat trickier: how can we "apply a function
    zero times"? The answer is actually simple: just return the argument
    untouched.
    -/

    def zero : Cnat :=
      fun _ _ x => x

    /-!
    More generally, a number `n` can be written as
    `fun α f x => f (f ... (f x) ...)`, with `n` occurrences of `f`.
    Let's informally notate that as `fun α f x => f^n x`, with the
    convention that `f^0 x` is just `x`. Note how the `doit3times`
    function we've defined previously is actually just the Church
    representation of 3.
    -/

    def three : Cnat := @doit3times

    /-!
    So `n α f x` represents "do it `n` times", where `n` is a Church
    numeral and "it" means applying `f` starting with `x`.

    Another way to think about the Church representation is that function
    `f` represents the successor operation on `α`, and value `x`
    represents the zero element of `α`. We could even rewrite with those
    names to make it clearer:
    -/

    def zero' : Cnat :=
      fun _ _ zero => zero
    def one' : Cnat :=
      fun _ succ zero => succ zero
    def two' : Cnat :=
      fun _ succ zero => succ (succ zero)

    /-!
    If we passed in `Nat.succ` as `succ` and `0` as `zero`, we'd even
    get the Peano naturals as a result:
    -/

    example : zero Nat Nat.succ 0 = 0 := rfl
    example : one Nat Nat.succ 0 = 1 := rfl
    example : two Nat Nat.succ 0 = 2 := rfl

    /-!
    One very interesting implication of the Church numerals is that we
    don't strictly need the natural numbers to be built-in to a functional
    programming language, or even to be definable with an inductive data
    type. It's possible to represent them purely (if not efficiently) with
    functions.

    Of course, it's not enough just to "represent" numerals; we need to be
    able to do arithmetic with the representation. Show that we can by
    completing the definitions of the following functions. Make sure that
    the corresponding unit tests pass by proving them with `rfl`.
    -/

    /-!
    #### Exercise: 2 stars, advanced (church_scc)

    Define a function that computes the successor of a Church numeral.
    Given a Church numeral `n`, its successor `scc n` should iterate its
    function argument once more than `n`. That is, given
    `fun α f x => f^n x` as input, `scc` should produce
    `fun α f x => f^(n+1) x` as output. In other words, do it `n` times,
    then do it once more.
    -/

    def scc (n : Cnat) : Cnat :=
      /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

    example : scc zero = one :=
      /- FILL IN HERE -/ sorry
    example : scc one = two :=
      /- FILL IN HERE -/ sorry
    example : scc two = three :=
      /- FILL IN HERE -/ sorry

    /-!
    #### Exercise: 3 stars, advanced (church_plus)

    Define a function that computes the addition of two Church numerals.
    Given `fun α f x => f^n x` and `fun α f x => f^m x` as input,
    `cplus` should produce `fun α f x => f^(n + m) x` as output. In other
    words, do it `n` times, then do it `m` more times.

    Hint: the "zero" argument to a Church numeral need not be just `x`.
    -/

    def cplus (n m : Cnat) : Cnat :=
      /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

    example : cplus zero one = one :=
      /- FILL IN HERE -/ sorry
    example : cplus two three = cplus three two :=
      /- FILL IN HERE -/ sorry
    example :
        cplus (cplus two two) three = cplus one (cplus three three) :=
      /- FILL IN HERE -/ sorry

    /-!
    #### Exercise: 3 stars, advanced (church_mult)

    Define a function that computes the multiplication of two Church
    numerals.

    Hint: the "successor" argument to a Church numeral need not be just
    `f`.
    -/

    def cmult (n m : Cnat) : Cnat :=
      /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

    example : cmult one one = one :=
      /- FILL IN HERE -/ sorry
    example : cmult zero (cplus three three) = zero :=
      /- FILL IN HERE -/ sorry
    example : cmult two three = cplus three three :=
      /- FILL IN HERE -/ sorry

    /-!
    #### Exercise: 3 stars, advanced (church_exp)

    Exponentiation:

    Define a function that computes the exponentiation of two Church
    numerals.

    Hint: the type argument to a Church numeral need not just be `α`.
    -/

    def cexp (n m : Cnat) : Cnat :=
      /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

    example : cexp two two = cplus two two :=
      /- FILL IN HERE -/ sorry
    example : cexp three zero = one :=
      /- FILL IN HERE -/ sorry
    example : cexp three two = cplus (cmult two (cmult two two)) one :=
      /- FILL IN HERE -/ sorry

  end Church

end Exercises
