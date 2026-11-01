module DASHI.Physics.YangMills.P06ConstructiveSpanningTreeDFS where

------------------------------------------------------------------------
-- P06 constructive spanning-tree DFS surface.
--
-- This is the replacement for the opaque `RootedTree` / `TreeDFSWalk`
-- interface.  A tree stores both directions of every tree edge, because
-- Graph.Adj is directed in GraphCombinatorics and a closed DFS tour needs
-- the return edge explicitly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Nat.Base using (ℕ; _+_; _∸_; _≤_; _<_; zero; suc)
open import Data.Nat.Properties using (+-suc; +-assoc; +-comm)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans; _≢_)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; _∈_
        ; here
        ; there
        ; _⊆_
        ; NoDuplicates
        ; NonEmpty
        ; nonempty
        ; head
        ; last
        ; ConsecutiveEdges
        ; edges-single
        ; edges-step
        ; Path
        ; PathIn
        ; SimplePathIn
        ; SameVertexSet
        ; ∈-++-left
        ; ∈-++-right
        ; ∈-++-split
        ; CanonicalSkeletonObject
        ; RootedConnectedSkeleton
        ; connectedGivesPathInSkeleton
        ; pathSimplifyInsideSubset
        ; pathLength
        ; nonEmpty-length-suc-pred
        )

------------------------------------------------------------------------
-- The natural DFS coding length.  A closed tree tour traverses every
-- tree edge in both directions.
------------------------------------------------------------------------

p06DFSWalkLength : ℕ → ℕ
p06DFSWalkLength n = (n ∸ 1) + (n ∸ 1)

------------------------------------------------------------------------
-- Eliminable rooted tree data.  `backward` is intentionally not inferred
-- from `forward`: the ambient Graph API has no adjacency-symmetry law.
------------------------------------------------------------------------

mutual

  record RootedTreeChild
    (G : Graph)
    (u : Graph.Vertex G) : Set₁ where
    inductive
    field
      root : Graph.Vertex G
      forward : Graph.Adj G u root
      backward : Graph.Adj G root u
      subtree : RootedTreeNode G root

  data RootedTreeNode
    (G : Graph)
    : Graph.Vertex G → Set₁ where
    leaf : (u : Graph.Vertex G) → RootedTreeNode G u
    branch : (u : Graph.Vertex G) →
      List (RootedTreeChild G u) →
      RootedTreeNode G u

open RootedTreeChild public

mutual

  flattenTree :
    {G : Graph} {u : Graph.Vertex G} →
    RootedTreeNode G u → List (Graph.Vertex G)
  flattenTree (leaf u) = u ∷ []
  flattenTree (branch u children) = u ∷ flattenForest children

  flattenForest :
    {G : Graph} {u : Graph.Vertex G} →
    List (RootedTreeChild G u) → List (Graph.Vertex G)
  flattenForest [] = []
  flattenForest (child ∷ children) =
    flattenTree (subtree child) ++ flattenForest children

------------------------------------------------------------------------
-- Exact Euler/DFS tour.  It begins and ends at the root of the current
-- tree.  The proof record below makes all geometric claims explicit.
------------------------------------------------------------------------

mutual

  dfsTour :
    {G : Graph} {u : Graph.Vertex G} →
    RootedTreeNode G u → List (Graph.Vertex G)
  dfsTour (leaf u) = u ∷ []
  dfsTour (branch u children) = u ∷ dfsExcursions u children

  dfsTourTail :
    {G : Graph} {u : Graph.Vertex G} →
    RootedTreeNode G u → List (Graph.Vertex G)
  dfsTourTail (leaf u) = []
  dfsTourTail (branch u children) = dfsExcursions u children

  dfsExcursions :
    {G : Graph} (u : Graph.Vertex G) →
    List (RootedTreeChild G u) → List (Graph.Vertex G)
  dfsExcursions u [] = []
  dfsExcursions u (child ∷ children) =
    root child ∷
    (dfsTourTail (subtree child) ++
      (u ∷ dfsExcursions u children))

------------------------------------------------------------------------
-- Proof-relevant tour steps and structural tree edges.  These are kept
-- independent of any application-specific edge-code representation: the
-- path-union reifier can record that an insertion link is a tree edge, and
-- this module then certifies that the closed DFS tour actually traverses it.
------------------------------------------------------------------------

data TourStepOccurs
  {A : Set} (x y : A) : List A → Set where
  step-here : ∀ {xs} → TourStepOccurs x y (x ∷ y ∷ xs)
  step-there : ∀ {z xs} → TourStepOccurs x y xs →
    TourStepOccurs x y (z ∷ xs)

stepOccursPrepend :
  {A : Set} {x y : A} →
  (prefix xs : List A) →
  TourStepOccurs x y xs → TourStepOccurs x y (prefix ++ xs)
stepOccursPrepend [] xs occurrence = occurrence
stepOccursPrepend (z ∷ prefix) xs occurrence =
  step-there (stepOccursPrepend prefix xs occurrence)

stepOccursAppendLeft :
  {A : Set} {x y : A} →
  (xs ys : List A) →
  TourStepOccurs x y xs → TourStepOccurs x y (xs ++ ys)
stepOccursAppendLeft (z ∷ z′ ∷ xs) ys step-here = step-here
stepOccursAppendLeft (z ∷ []) ys (step-there ())
stepOccursAppendLeft [] ys ()
stepOccursAppendLeft (z ∷ xs) ys (step-there occurrence) =
  step-there (stepOccursAppendLeft xs ys occurrence)

stepOccursTransport :
  {A : Set} {x y : A} {xs ys : List A} →
  xs ≡ ys → TourStepOccurs x y xs → TourStepOccurs x y ys
stepOccursTransport refl occurrence = occurrence

dfsTourWithSuffix :
  {G : Graph} {u : Graph.Vertex G} →
  (tree : RootedTreeNode G u) →
  (suffix : List (Graph.Vertex G)) →
  dfsTour tree ++ suffix ≡ u ∷ (dfsTourTail tree ++ suffix)
dfsTourWithSuffix (leaf u) suffix = refl
dfsTourWithSuffix (branch u children) suffix = refl

-- A proof-free edge relation for a rooted tree node.  The constructor
-- records only parent/child vertices and a position in the child forest;
-- it never compares the recursive proof fields carried by `RootedTreeChild`.
mutual

  data TreeEdgeOccurs
    {G : Graph} {u : Graph.Vertex G} :
    {tree : RootedTreeNode G u} →
    Graph.Vertex G → Graph.Vertex G → Set₁ where
    direct-tree-edge : ∀ {children : List (RootedTreeChild G u)}
      {child : RootedTreeChild G u} →
      ChildOccurs child children →
      TreeEdgeOccurs {tree = branch u children} u (root child)
    below-tree-edge : ∀ {children : List (RootedTreeChild G u)}
      {child : RootedTreeChild G u} {p q : Graph.Vertex G} →
      ChildOccurs child children →
      TreeEdgeOccurs {tree = subtree child} p q →
      TreeEdgeOccurs {tree = branch u children} p q

  data ChildOccurs
    {G : Graph} {u : Graph.Vertex G}
    (child : RootedTreeChild G u) :
    List (RootedTreeChild G u) → Set₁ where
    child-here : ∀ {children} → ChildOccurs child (child ∷ children)
    child-there : ∀ {entry children} → ChildOccurs child children →
      ChildOccurs child (entry ∷ children)

mutual

  dfsTourDirectChildStep :
    {G : Graph} {u : Graph.Vertex G}
    (children : List (RootedTreeChild G u)) →
    {child : RootedTreeChild G u} →
    ChildOccurs child children →
    TourStepOccurs u (root child) (dfsTour (branch u children))
  dfsTourDirectChildStep {u = u} (child ∷ children) child-here = step-here
  dfsTourDirectChildStep {u = u} (entry ∷ children) (child-there child∈) =
    stepOccursPrepend
      (u ∷ root entry ∷ dfsTourTail (subtree entry))
      (u ∷ dfsExcursions u children)
      (dfsTourDirectChildStep children child∈)

  dfsTourSubtreeStep :
    {G : Graph} {u : Graph.Vertex G}
    (children : List (RootedTreeChild G u)) →
    {child : RootedTreeChild G u} {p q : Graph.Vertex G} →
    ChildOccurs child children →
    TourStepOccurs p q (dfsTour (subtree child)) →
    TourStepOccurs p q (dfsTour (branch u children))
  dfsTourSubtreeStep {u = u} (child ∷ children) child-here occurrence =
    stepOccursTransport
      (cong (u ∷_)
        (dfsTourWithSuffix (subtree child)
          (u ∷ dfsExcursions u children)))
      (stepOccursAppendLeft
        (u ∷ dfsTour (subtree child))
        (u ∷ dfsExcursions u children)
        (step-there occurrence))
  dfsTourSubtreeStep {u = u} (entry ∷ children) (child-there child∈) occurrence =
    stepOccursPrepend
      (u ∷ root entry ∷ dfsTourTail (subtree entry))
      (u ∷ dfsExcursions u children)
      (dfsTourSubtreeStep children child∈ occurrence)

  dfsTourTreeEdgeStep :
    {G : Graph} {u p q : Graph.Vertex G} →
    {tree : RootedTreeNode G u} →
    TreeEdgeOccurs {tree = tree} p q →
    TourStepOccurs p q (dfsTour tree)
  dfsTourTreeEdgeStep (direct-tree-edge {children = children} child∈) =
    dfsTourDirectChildStep children child∈
  dfsTourTreeEdgeStep (below-tree-edge {children = children} child∈ edge∈) =
    dfsTourSubtreeStep children child∈ (dfsTourTreeEdgeStep edge∈)

record DFSTourInvariant
  {G : Graph} {u : Graph.Vertex G}
  (tree : RootedTreeNode G u) : Set₁ where
  field
    nonEmpty : NonEmpty (dfsTour tree)
    startsAtRoot : head (dfsTour tree) nonEmpty ≡ u
    endsAtRoot : last (dfsTour tree) nonEmpty ≡ u
    adjacent : ConsecutiveEdges G (dfsTour tree)
    rangeExact : SameVertexSet (dfsTour tree) (flattenTree tree)
    lengthExact :
      length (dfsTour tree) ∸ 1
        ≡ (length (flattenTree tree) ∸ 1)
          + (length (flattenTree tree) ∸ 1)

------------------------------------------------------------------------
-- Exact tour length, proved structurally before the richer path/range
-- invariant.  The forest statement is the useful induction form: each
-- child excursion contributes twice the size of that child subtree.
------------------------------------------------------------------------

length-++ :
  {A : Set} → (xs ys : List A) →
  length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

double-sum : (m n : ℕ) →
  (m + m) + (n + n) ≡ (m + n) + (m + n)
double-sum m n =
  trans (+-assoc m m (n + n))
    (trans (cong (m +_) (sym (+-assoc m n n)))
      (trans (cong (m +_) (cong (_+ n) (+-comm m n)))
        (trans (cong (m +_) (+-assoc n m n))
          (sym (+-assoc m n (m + n))))))

child-excursion-length : (m n : ℕ) →
  suc ((m + m) + suc (n + n))
    ≡ (suc m + n) + (suc m + n)
child-excursion-length m n
  rewrite +-suc (m + m) (n + n)
        | +-suc (m + n) (m + n)
        | double-sum m n = refl

suc-∸-one : (n : ℕ) → suc n ∸ 1 ≡ n
suc-∸-one n = refl

flattenTree-nonEmpty :
  {G : Graph} {u : Graph.Vertex G} →
  (tree : RootedTreeNode G u) → NonEmpty (flattenTree tree)
flattenTree-nonEmpty (leaf u) = nonempty
flattenTree-nonEmpty (branch u children) = nonempty

mutual

  dfsTourTailLengthExact :
    {G : Graph} {u : Graph.Vertex G} →
    (tree : RootedTreeNode G u) →
    length (dfsTourTail tree)
      ≡ (length (flattenTree tree) ∸ 1)
        + (length (flattenTree tree) ∸ 1)
  dfsTourTailLengthExact (leaf u) = refl
  dfsTourTailLengthExact (branch u children) =
    dfsExcursionsLengthExact u children

  dfsExcursionsLengthExact :
    {G : Graph} (u : Graph.Vertex G) →
    (children : List (RootedTreeChild G u)) →
    length (dfsExcursions u children)
      ≡ length (flattenForest children) + length (flattenForest children)
  dfsExcursionsLengthExact u [] = refl
  dfsExcursionsLengthExact u (child ∷ children)
    rewrite length-++ (dfsTourTail (subtree child))
              (u ∷ dfsExcursions u children)
          | length-++ (flattenTree (subtree child))
              (flattenForest children)
          | dfsTourTailLengthExact (subtree child)
          | dfsExcursionsLengthExact u children
          | suc-∸-one (length (flattenTree (subtree child)))
          | nonEmpty-length-suc-pred
              (flattenTree-nonEmpty (subtree child)) =
    child-excursion-length
      (length (flattenTree (subtree child)) ∸ 1)
      (length (flattenForest children))

dfsTourLengthExact :
  {G : Graph} {u : Graph.Vertex G} →
  (tree : RootedTreeNode G u) →
  length (dfsTour tree) ∸ 1
    ≡ (length (flattenTree tree) ∸ 1)
      + (length (flattenTree tree) ∸ 1)
dfsTourLengthExact (leaf u) = refl
dfsTourLengthExact (branch u children) =
  dfsExcursionsLengthExact u children

------------------------------------------------------------------------
-- Tour range.  This is deliberately proved by membership induction, so
-- it does not depend on a particular flattening order or on cardinality
-- facts.  The repeated parent vertex in an Euler excursion is harmless at
-- this extensional level.
------------------------------------------------------------------------

dfsTour-shape :
  {G : Graph} {u : Graph.Vertex G} →
  (tree : RootedTreeNode G u) →
  dfsTour tree ≡ u ∷ dfsTourTail tree
dfsTour-shape (leaf u) = refl
dfsTour-shape (branch u children) = refl

flattenTree-root :
  {G : Graph} {u : Graph.Vertex G} →
  (tree : RootedTreeNode G u) → u ∈ flattenTree tree
flattenTree-root (leaf u) = here
flattenTree-root (branch u children) = here

cons-append-membership :
  {A : Set} {x y : A} {xs ys : List A} →
  x ∈ (y ∷ xs) → x ∈ (y ∷ (xs ++ ys))
cons-append-membership here = here
cons-append-membership (there x∈) =
  there (∈-++-left _ _ x∈)

mutual

  dfsTourRangeSound :
    {G : Graph} {u : Graph.Vertex G} {x : Graph.Vertex G} →
    (tree : RootedTreeNode G u) →
    x ∈ dfsTour tree → x ∈ flattenTree tree
  dfsTourRangeSound (leaf u) here = here
  dfsTourRangeSound (leaf u) (there x∈) with x∈
  ... | ()
  dfsTourRangeSound (branch u children) here = here
  dfsTourRangeSound (branch u children) (there x∈)
    with dfsExcursionsRangeSound u children x∈
  ... | here = here
  ... | there x∈forest = there x∈forest

  dfsTourRangeComplete :
    {G : Graph} {u : Graph.Vertex G} {x : Graph.Vertex G} →
    (tree : RootedTreeNode G u) →
    x ∈ flattenTree tree → x ∈ dfsTour tree
  dfsTourRangeComplete (leaf u) here = here
  dfsTourRangeComplete (leaf u) (there x∈) with x∈
  ... | ()
  dfsTourRangeComplete (branch u children) here = here
  dfsTourRangeComplete (branch u children) (there x∈) =
    there (dfsExcursionsRangeComplete u children x∈)

  dfsTourTailRangeSound :
    {G : Graph} {u : Graph.Vertex G} {x : Graph.Vertex G} →
    (tree : RootedTreeNode G u) →
    x ∈ dfsTourTail tree → x ∈ flattenTree tree
  dfsTourTailRangeSound {x = x} tree x∈ =
    subst
      (λ vs → x ∈ vs → x ∈ flattenTree tree)
      (dfsTour-shape tree)
      (λ x∈tour → dfsTourRangeSound tree x∈tour)
      (there x∈)

  dfsTourRangeCompleteAsCons :
    {G : Graph} {u : Graph.Vertex G} {x : Graph.Vertex G} →
    (tree : RootedTreeNode G u) →
    x ∈ flattenTree tree → x ∈ (u ∷ dfsTourTail tree)
  dfsTourRangeCompleteAsCons {x = x} tree x∈ =
    subst
      (λ vs → x ∈ vs)
      (dfsTour-shape tree)
      (dfsTourRangeComplete tree x∈)

  dfsExcursionsRangeSound :
    {G : Graph} (u : Graph.Vertex G) {x : Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    x ∈ dfsExcursions u children → x ∈ (u ∷ flattenForest children)
  dfsExcursionsRangeSound u [] ()
  dfsExcursionsRangeSound u (child ∷ children) here =
    there
      (∈-++-left
        (flattenTree (subtree child))
        (flattenForest children)
        (flattenTree-root (subtree child)))
  dfsExcursionsRangeSound u (child ∷ children) (there x∈)
    with ∈-++-split
           (dfsTourTail (subtree child))
           (u ∷ dfsExcursions u children)
           x∈
  ... | inj₁ x∈tail =
    there
      (∈-++-left
        (flattenTree (subtree child))
        (flattenForest children)
        (dfsTourTailRangeSound (subtree child) x∈tail))
  ... | inj₂ here = here
  ... | inj₂ (there x∈rest)
    with dfsExcursionsRangeSound u children x∈rest
  ... | here = here
  ... | there x∈forest =
    there
      (∈-++-right
        (flattenTree (subtree child))
        (flattenForest children)
        x∈forest)

  dfsExcursionsRangeComplete :
    {G : Graph} (u : Graph.Vertex G) {x : Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    x ∈ flattenForest children → x ∈ dfsExcursions u children
  dfsExcursionsRangeComplete u [] ()
  dfsExcursionsRangeComplete u (child ∷ children) x∈
    with ∈-++-split
           (flattenTree (subtree child))
           (flattenForest children)
           x∈
  ... | inj₁ x∈child =
    cons-append-membership
      (dfsTourRangeCompleteAsCons (subtree child) x∈child)
  ... | inj₂ x∈rest =
    there
      (∈-++-right
        (dfsTourTail (subtree child))
        (u ∷ dfsExcursions u children)
        (there (dfsExcursionsRangeComplete u children x∈rest)))

dfsTourRangeExact :
  {G : Graph} {u : Graph.Vertex G} →
  (tree : RootedTreeNode G u) →
  SameVertexSet (dfsTour tree) (flattenTree tree)
dfsTourRangeExact tree =
  dfsTourRangeSound tree , dfsTourRangeComplete tree

------------------------------------------------------------------------
-- Consecutive-edge validity.  The continuation lemma is the list-level
-- form of joining a finished path to a nonempty next path by one edge.
------------------------------------------------------------------------

appendConsecutiveContinue :
  {G : Graph} {xs : List (Graph.Vertex G)}
  {y : Graph.Vertex G} {ys : List (Graph.Vertex G)} →
  (xs-ne : NonEmpty xs) →
  ConsecutiveEdges G xs →
  Graph.Adj G (last xs xs-ne) y →
  ConsecutiveEdges G (y ∷ ys) →
  ConsecutiveEdges G (xs ++ (y ∷ ys))
appendConsecutiveContinue {G = G} {xs = x ∷ []} {y = y}
  xs-ne edges-single xy next =
  edges-step
    (subst
      (λ v → Graph.Adj G v y)
      (last-single xs-ne)
      xy)
    next
  where
  last-single :
    {A : Set} {x : A} →
    (ne : NonEmpty (x ∷ [])) → last (x ∷ []) ne ≡ x
  last-single nonempty = refl
appendConsecutiveContinue {G} {xs = x ∷ z ∷ xs} xs-ne
  (edges-step xz rest) zy next =
  edges-step xz
    (appendConsecutiveContinue {G} {xs = z ∷ xs}
      nonempty rest
      (subst
        (λ v → Graph.Adj G v _)
        (last-cons xs-ne nonempty)
        zy)
      next)
  where
  last-cons :
    {A : Set} {x z : A} {xs : List A} →
    (whole-ne : NonEmpty (x ∷ z ∷ xs)) →
    (tail-ne : NonEmpty (z ∷ xs)) →
    last (x ∷ z ∷ xs) whole-ne ≡ last (z ∷ xs) tail-ne
  last-cons nonempty nonempty = refl

dfsTour-nonEmpty :
  {G : Graph} {u : Graph.Vertex G} →
  (tree : RootedTreeNode G u) → NonEmpty (dfsTour tree)
dfsTour-nonEmpty (leaf u) = nonempty
dfsTour-nonEmpty (branch u children) = nonempty

appendNonEmpty :
  {A : Set} {xs ys : List A} →
  NonEmpty ys → NonEmpty (xs ++ ys)
appendNonEmpty {xs = []} ys-ne = ys-ne
appendNonEmpty {xs = x ∷ xs} ys-ne = nonempty

lastAppend :
  {A : Set} (xs ys : List A) →
  (ys-ne : NonEmpty ys) →
  last (xs ++ ys) (appendNonEmpty ys-ne) ≡ last ys ys-ne
lastAppend [] ys ys-ne = refl
lastAppend (x ∷ []) (y ∷ ys) nonempty = refl
lastAppend (x ∷ z ∷ xs) (y ∷ ys) nonempty =
  lastAppend (z ∷ xs) (y ∷ ys) nonempty

mutual

  dfsTourEndsAtRoot :
    {G : Graph} {u : Graph.Vertex G} →
    (tree : RootedTreeNode G u) →
    last (dfsTour tree) (dfsTour-nonEmpty tree) ≡ u
  dfsTourEndsAtRoot (leaf u) = refl
  dfsTourEndsAtRoot (branch u children) =
    dfsExcursionsEndAtRoot u children

  dfsExcursionsEndAtRoot :
    {G : Graph} (u : Graph.Vertex G) →
    (children : List (RootedTreeChild G u)) →
    last (u ∷ dfsExcursions u children) nonempty ≡ u
  dfsExcursionsEndAtRoot u [] = refl
  dfsExcursionsEndAtRoot u (child ∷ children) =
    trans
      (lastAppend
        (u ∷ root child ∷ dfsTourTail (subtree child))
        (u ∷ dfsExcursions u children)
        nonempty)
      (dfsExcursionsEndAtRoot u children)

mutual

  dfsTourAdjacent :
    {G : Graph} {u : Graph.Vertex G} →
    (tree : RootedTreeNode G u) →
    ConsecutiveEdges G (dfsTour tree)
  dfsTourAdjacent (leaf u) = edges-single
  dfsTourAdjacent (branch u children) =
    dfsExcursionsAdjacent u children

  dfsExcursionsAdjacent :
    {G : Graph} (u : Graph.Vertex G) →
    (children : List (RootedTreeChild G u)) →
    ConsecutiveEdges G (u ∷ dfsExcursions u children)
  dfsExcursionsAdjacent u [] = edges-single
  dfsExcursionsAdjacent {G = G} u (child ∷ children) =
    edges-step (forward child)
      (subst
        (λ vs →
          ConsecutiveEdges G
            (vs ++ (u ∷ dfsExcursions u children)))
        (dfsTour-shape (subtree child))
        (appendConsecutiveContinue
          (dfsTour-nonEmpty (subtree child))
          (dfsTourAdjacent (subtree child))
          (subst
            (λ v → Graph.Adj G v u)
            (sym (dfsTourEndsAtRoot (subtree child)))
            (backward child))
          (dfsExcursionsAdjacent u children)))

dfsTourStartsAtRoot :
  {G : Graph} {u : Graph.Vertex G} →
  (tree : RootedTreeNode G u) →
  head (dfsTour tree) (dfsTour-nonEmpty tree) ≡ u
dfsTourStartsAtRoot (leaf u) = refl
dfsTourStartsAtRoot (branch u children) = refl

dfsTourInvariant :
  {G : Graph} {u : Graph.Vertex G} →
  (tree : RootedTreeNode G u) →
  DFSTourInvariant tree
dfsTourInvariant tree = record
  { nonEmpty = dfsTour-nonEmpty tree
  ; startsAtRoot = dfsTourStartsAtRoot tree
  ; endsAtRoot = dfsTourEndsAtRoot tree
  ; adjacent = dfsTourAdjacent tree
  ; rangeExact = dfsTourRangeExact tree
  ; lengthExact = dfsTourLengthExact tree
  }

dfsTourPath :
  {G : Graph} {u : Graph.Vertex G} {tree : RootedTreeNode G u} →
  DFSTourInvariant tree → Path G u u
dfsTourPath invariant = record
  { vertices = dfsTour _
  ; nonEmptyWitness = DFSTourInvariant.nonEmpty invariant
  ; startsAt = DFSTourInvariant.startsAtRoot invariant
  ; endsAt = DFSTourInvariant.endsAtRoot invariant
  ; adjacent = DFSTourInvariant.adjacent invariant
  }

------------------------------------------------------------------------
-- A constructive spanning tree includes the exact range correspondence.
-- Its recursive construction from connectedness is deliberately a theorem
-- obligation, not an axiom hidden in this record.
------------------------------------------------------------------------

record ConstructiveRootedSpanningTree
  (G : Graph)
  (r : Graph.Vertex G)
  (X : List (Graph.Vertex G)) : Set₁ where
  field
    tree : RootedTreeNode G r
    flattenedVertices : List (Graph.Vertex G)
    flattenCorrect : flattenedVertices ≡ flattenTree tree
    noDuplicateVertices : NoDuplicates flattenedVertices
    covers : X ⊆ flattenedVertices
    containsOnlyX : flattenedVertices ⊆ X
    rootIsRoot : r ∈ X
    flattenSize : length flattenedVertices ≡ length X

constructiveTreeRangeIs :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} →
  (tree : ConstructiveRootedSpanningTree G r X) →
  SameVertexSet (flattenTree (ConstructiveRootedSpanningTree.tree tree)) X
constructiveTreeRangeIs tree =
  subst
    (λ ys → SameVertexSet ys _)
    (ConstructiveRootedSpanningTree.flattenCorrect tree)
    ( ConstructiveRootedSpanningTree.containsOnlyX tree
    , ConstructiveRootedSpanningTree.covers tree )

------------------------------------------------------------------------
-- The concrete DFS payload for a canonical skeleton.  Once constructed,
-- every geometric field needed by the exact-length walk semantics is owned
-- by the payload; no legacy TreeDFSWalk is involved.
------------------------------------------------------------------------

record CanonicalSkeletonExactDFS
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  (obj : CanonicalSkeletonObject G r n) : Set₁ where
  field
    spanningTree :
      ConstructiveRootedSpanningTree G r
        (CanonicalSkeletonObject.skelVertices obj)
    tourInvariant :
      DFSTourInvariant
        (ConstructiveRootedSpanningTree.tree spanningTree)

  treeRange :
    SameVertexSet
      (flattenTree (ConstructiveRootedSpanningTree.tree spanningTree))
      (CanonicalSkeletonObject.skelVertices obj)
  treeRange = constructiveTreeRangeIs spanningTree

  tourRange :
    SameVertexSet
      (dfsTour (ConstructiveRootedSpanningTree.tree spanningTree))
      (CanonicalSkeletonObject.skelVertices obj)
  tourRange =
    let open DFSTourInvariant tourInvariant
        left = rangeExact
        right = treeRange
    in
      (λ x∈ → proj₁ right (proj₁ left x∈)) ,
      (λ x∈ → proj₂ left (proj₂ right x∈))

  tourLength :
    length (dfsTour (ConstructiveRootedSpanningTree.tree spanningTree)) ∸ 1
      ≡ p06DFSWalkLength n
  tourLength =
    trans
      (DFSTourInvariant.lengthExact tourInvariant)
      (trans
        (congLength
          (sym (cong length
            (ConstructiveRootedSpanningTree.flattenCorrect spanningTree))))
        (trans
          (congLength
            (ConstructiveRootedSpanningTree.flattenSize spanningTree))
          (congLength (CanonicalSkeletonObject.size obj))))
    where
    shape : ℕ → ℕ
    shape m = (m ∸ 1) + (m ∸ 1)

    congLength : {a b : ℕ} → a ≡ b → shape a ≡ shape b
    congLength = cong shape

record CanonicalSkeletonConstructiveDFSProvider
  {G : Graph} {r : Graph.Vertex G} {n : ℕ} : Set₁ where
  field
    construct :
      (obj : CanonicalSkeletonObject G r n) →
      CanonicalSkeletonExactDFS obj

canonicalSkeletonExactDFSFromConstructiveTree :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ} →
  (obj : CanonicalSkeletonObject G r n) →
  (spanningTree :
    ConstructiveRootedSpanningTree G r
      (CanonicalSkeletonObject.skelVertices obj)) →
  CanonicalSkeletonExactDFS obj
canonicalSkeletonExactDFSFromConstructiveTree obj spanningTree = record
  { spanningTree = spanningTree
  ; tourInvariant =
      dfsTourInvariant
        (ConstructiveRootedSpanningTree.tree spanningTree)
  }

------------------------------------------------------------------------
-- P06-local directedness and finite-connectivity interfaces.
--
-- Nothing below changes `Graph`: directed graph clients remain valid.  A
-- closed DFS only needs reverse edges while it is inside the skeleton, so
-- that is exactly the scope of the symmetry premise.
------------------------------------------------------------------------

record UndirectedGraphStructure (G : Graph) : Set₁ where
  field
    adjSym : ∀ {u v} → Graph.Adj G u v → Graph.Adj G v u

record SkeletonAdjacencySymmetry
  {G : Graph}
  (X : List (Graph.Vertex G)) : Set₁ where
  field
    reverseInside :
      ∀ {u v} → u ∈ X → v ∈ X →
      Graph.Adj G u v → Graph.Adj G v u

undirectedGraphGivesSkeletonSymmetry :
  {G : Graph} {X : List (Graph.Vertex G)} →
  UndirectedGraphStructure G →
  SkeletonAdjacencySymmetry {G = G} X
undirectedGraphGivesSkeletonSymmetry {G} {X} undirected = record
  { reverseInside = λ {u} {v} u∈ v∈ uv →
      UndirectedGraphStructure.adjSym undirected uv }

record RootedPathConnected
  (G : Graph)
  (r : Graph.Vertex G)
  (X : List (Graph.Vertex G)) : Set₁ where
  field
    rootIn : r ∈ X
    pathTo : ∀ v → v ∈ X → SimplePathIn G X r v

rootedConnectedSkeletonToRootedPathConnected :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} →
  RootedConnectedSkeleton G r X →
  RootedPathConnected G r X
rootedConnectedSkeletonToRootedPathConnected {G} {r} {X} connected = record
  { rootIn = RootedConnectedSkeleton.r-in-X connected
  ; pathTo = λ v v∈ →
      pathSimplifyInsideSubset
        (PathIn.path (connectedGivesPathInSkeleton connected v v∈))
        (PathIn.insideX (connectedGivesPathInSkeleton connected v v∈))
  }

-- Selection of shortest internal paths is the remaining finite-search
-- construction.  `minimal` is deliberately explicit: arbitrary selected
-- paths do not yield a rank-decreasing parent map.
record RootedShortestPathSelector
  (G : Graph)
  (r : Graph.Vertex G)
  (X : List (Graph.Vertex G)) : Set₁ where
  field
    selected : ∀ v → v ∈ X → SimplePathIn G X r v
    minimal : ∀ v → (v∈ : v ∈ X) →
      (q : SimplePathIn G X r v) →
      pathLength (PathIn.path (SimplePathIn.pathIn (selected v v∈))) ≤
      pathLength (PathIn.path (SimplePathIn.pathIn q))

record RankedBidirectionalParentTree
  (G : Graph)
  (r : Graph.Vertex G)
  (X : List (Graph.Vertex G)) : Set₁ where
  field
    rank : Graph.Vertex G → ℕ
    parent : (v : Graph.Vertex G) → v ∈ X → v ≢ r → Graph.Vertex G
    parentIn : ∀ v v∈ v≢ → parent v v∈ v≢ ∈ X
    parentForward : ∀ v v∈ v≢ → Graph.Adj G (parent v v∈ v≢) v
    parentReturn : ∀ v v∈ v≢ → Graph.Adj G v (parent v v∈ v≢)
    rankDrops : ∀ v v∈ v≢ → rank (parent v v∈ v≢) < rank v
    rootRank : rank r ≡ 0

-- This is the exact constructive boundary still to be inhabited by finite
-- least-path search.  It is a record, not a postulate: a caller must supply
-- an eliminable parent tree with the descent proof that DFS needs.
record ShortestPathParentConstruction
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)}
  (symmetry : SkeletonAdjacencySymmetry {G = G} X)
  (paths : RootedShortestPathSelector G r X) : Set₁ where
  field
    rankedTree : RankedBidirectionalParentTree G r X

-- Once finite least-path selection has constructed the recursive spanning
-- tree and its induction invariant, this adapter has no additional graph
-- assumptions and produces the exact DFS payload used downstream.
record BidirectionalCanonicalDFSInput
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  (obj : CanonicalSkeletonObject G r n) : Set₁ where
  field
    symmetry : SkeletonAdjacencySymmetry (CanonicalSkeletonObject.skelVertices obj)
    paths : RootedShortestPathSelector G r (CanonicalSkeletonObject.skelVertices obj)
    parentConstruction : ShortestPathParentConstruction symmetry paths
    spanningTree :
      ConstructiveRootedSpanningTree G r
        (CanonicalSkeletonObject.skelVertices obj)
    tourInvariant : DFSTourInvariant
      (ConstructiveRootedSpanningTree.tree spanningTree)

bidirectionalCanonicalDFSInputToExactDFS :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {obj : CanonicalSkeletonObject G r n} →
  BidirectionalCanonicalDFSInput obj →
  CanonicalSkeletonExactDFS obj
bidirectionalCanonicalDFSInputToExactDFS input = record
  { spanningTree = BidirectionalCanonicalDFSInput.spanningTree input
  ; tourInvariant = BidirectionalCanonicalDFSInput.tourInvariant input
  }
