module DASHI.Physics.YangMills.P06PathUnionSpanningTreeClosure where

------------------------------------------------------------------------
-- P06 path-union spanning-tree closure: finite list core.
--
-- The construction never decides adjacency.  It receives an actual path
-- and uses only decidable membership in the finite, already-built carrier
-- to choose the *last* vertex where that path meets the partial tree.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat.Base using (ℕ; _∸_; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans; _≢_)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( _∈_
        ; _∉_
        ; NoDuplicates
        ; here
        ; there
        ; memberDec
        ; PathIn
        ; SimplePathIn
        ; SameVertexSet
        ; Path
        ; ConsecutiveEdges
        ; NonEmpty
        ; nonempty
        ; mapList
        ; map-elem
        ; noDup-nil
        ; noDup-cons
        ; ++-noDup
        ; last
        ; vertices
        ; pathVerticesAsCons
        ; appendSingle-length
        ; appendSingle-nonEmpty
        ; nonEmpty-length-suc-pred
        ; last-append-single
        ; sameVertexSetNoDuplicatesLength
        )

open import DASHI.Physics.YangMills.P06ConstructiveSpanningTreeDFS as CDFS
  using ( SkeletonAdjacencySymmetry
        ; RootedPathConnected
        ; RootedTreeNode
        ; RootedTreeChild
        ; ConstructiveRootedSpanningTree
        ; CanonicalSkeletonExactDFS
        ; flattenTree
        ; flattenForest
        ; rootedConnectedSkeletonToRootedPathConnected
        ; canonicalSkeletonExactDFSFromConstructiveTree
        )

open CDFS.RootedTreeChild using (root; forward; backward; subtree)

-- The tree child payload contains a recursive subtree and therefore lives
-- in Set₁.  GraphCombinatorics membership is intentionally Set-valued, so
-- the tree reification layer needs its own universe-polymorphic analogue.
data _∈₁_ {A : Set₁} (x : A) : List A → Set₁ where
  here₁ : ∀ {xs} → x ∈₁ (x ∷ xs)
  there₁ : ∀ {y xs} → x ∈₁ xs → x ∈₁ (y ∷ xs)

memberInPlainAppendRight :
  {A : Set} (prefix suffix : List A) {x : A} →
  x ∈ suffix → x ∈ (prefix ++ suffix)
memberInPlainAppendRight [] suffix x∈ = x∈
memberInPlainAppendRight (y ∷ prefix) suffix x∈ =
  there (memberInPlainAppendRight prefix suffix x∈)

------------------------------------------------------------------------
-- A list split immediately after its final member of `marked`.
-- `afterFresh` is the key path-union invariant: appending `after` to the
-- partial tree cannot create a second intersection with the old carrier.
------------------------------------------------------------------------

FreshFor : {A : Set} → List A → List A → Set
FreshFor marked xs = ∀ {x} → x ∈ xs → x ∉ marked

AnyMarked : {A : Set} → List A → List A → Set
AnyMarked marked xs = Σ _ λ x → x ∈ xs × x ∈ marked

record LastMarkedSplit {A : Set}
  (marked xs : List A) : Set where
  field
    before : List A
    attachment : A
    after : List A
    reconstruct : xs ≡ before ++ attachment ∷ after
    attachmentMarked : attachment ∈ marked
    afterFresh : FreshFor marked after

open LastMarkedSplit public

anyMarkedDec :
  {A : Set} →
  (marked : List A) →
  ((x : A) → Dec (x ∈ marked)) →
  (xs : List A) →
  Dec (AnyMarked marked xs)
anyMarkedDec marked marked? [] = no (λ { (_ , () , _) })
anyMarkedDec marked marked? (x ∷ xs)
  with marked? x
... | yes xMarked = yes (x , here , xMarked)
... | no xFresh
  with anyMarkedDec marked marked? xs
... | yes tailMarked =
  yes (proj₁ tailMarked , there (proj₁ (proj₂ tailMarked)) , proj₂ (proj₂ tailMarked))
... | no noTailMarked = no λ
  { (z , here , zMarked) → xFresh zMarked
  ; (z , there z∈xs , zMarked) → noTailMarked (z , z∈xs , zMarked)
  }

prependBefore :
  {A : Set} {marked xs : List A} →
  (x : A) →
  LastMarkedSplit marked xs →
  LastMarkedSplit marked (x ∷ xs)
prependBefore x split = record
  { before = x ∷ before split
  ; attachment = attachment split
  ; after = after split
  ; reconstruct = cong (λ ys → x ∷ ys) (reconstruct split)
  ; attachmentMarked = attachmentMarked split
  ; afterFresh = afterFresh split
  }

splitAtHeadOrImpossible :
  {A : Set} →
  (marked : List A) →
  ((z : A) → Dec (z ∈ marked)) →
  (x : A) →
  (xs : List A) →
  (noTailMarked : ¬ AnyMarked marked xs) →
  Dec (x ∈ marked) →
  AnyMarked marked (x ∷ xs) →
  LastMarkedSplit marked (x ∷ xs)
splitAtHeadOrImpossible marked marked? x xs noTailMarked (yes xMarked) has = record
  { before = []
  ; attachment = x
  ; after = xs
  ; reconstruct = refl
  ; attachmentMarked = xMarked
  ; afterFresh = λ z∈xs zMarked →
      noTailMarked (_ , z∈xs , zMarked)
  }
splitAtHeadOrImpossible marked marked? x xs noTailMarked (no xFresh) has =
  ⊥-elim (impossible has)
  where
  impossible : AnyMarked marked (x ∷ xs) → _
  impossible (_ , here , zMarked) = xFresh zMarked
  impossible (z , there z∈xs , zMarked) =
    noTailMarked (z , z∈xs , zMarked)

lastMarkedSplit :
  {A : Set} →
  (marked : List A) →
  ((x : A) → Dec (x ∈ marked)) →
  (xs : List A) →
  AnyMarked marked xs →
  LastMarkedSplit marked xs
lastMarkedSplit marked marked? [] (_ , () , _)
lastMarkedSplit marked marked? (x ∷ xs) has
  with anyMarkedDec marked marked? xs
... | yes tailMarked =
  prependBefore x (lastMarkedSplit marked marked? xs tailMarked)
... | no noTailMarked =
  splitAtHeadOrImpossible marked marked? x xs noTailMarked (marked? x) has

-- Convenient specialization for the canonical vertex labels.  It is the
-- exact splitter used by the future path-union fold.
lastMemberSplit :
  {G : GC.Graph} →
  (marked xs : List (GC.Graph.Vertex G)) →
  AnyMarked marked xs →
  LastMarkedSplit marked xs
lastMemberSplit {G} marked xs =
  lastMarkedSplit marked
    (λ x → memberDec (GC.vertexEqDec {G}) x marked)
    xs

------------------------------------------------------------------------
-- Rooted internal paths always meet a partial tree containing the root.
-- This is the precise bridge from `RootedPathConnected.pathTo` to the
-- generic last-marked splitter above.
------------------------------------------------------------------------

simplePathStartsMember :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r v : GC.Graph.Vertex G} →
  (p : SimplePathIn G X r v) →
  r ∈ vertices (PathIn.path (SimplePathIn.pathIn p))
simplePathStartsMember {r = r} p
  with pathVerticesAsCons (PathIn.path (SimplePathIn.pathIn p))
... | tail , vertices≡ =
  subst (λ ys → r ∈ ys) (sym vertices≡) here

splitSimplePathAfterLastIncluded :
  {G : GC.Graph} {X included : List (GC.Graph.Vertex G)}
  {r v : GC.Graph.Vertex G} →
  (p : SimplePathIn G X r v) →
  r ∈ included →
  LastMarkedSplit included
    (vertices (PathIn.path (SimplePathIn.pathIn p)))
splitSimplePathAfterLastIncluded {G = G} {included = included} {r = r} p r∈included =
  lastMemberSplit {G = G} included
    (vertices (PathIn.path (SimplePathIn.pathIn p)))
    (r , simplePathStartsMember p , r∈included)

------------------------------------------------------------------------
-- Dropping a prefix from a consecutive-edge list preserves adjacency.
------------------------------------------------------------------------

tailConsecutive :
  {G : GC.Graph} {x y : GC.Graph.Vertex G}
  {xs : List (GC.Graph.Vertex G)} →
  ConsecutiveEdges G (x ∷ y ∷ xs) →
  ConsecutiveEdges G (y ∷ xs)
tailConsecutive (GC.edges-step _ rest) = rest

dropPrefixAdjacent :
  {G : GC.Graph} (prefix : List (GC.Graph.Vertex G))
  {a : GC.Graph.Vertex G} (after : List (GC.Graph.Vertex G)) →
  ConsecutiveEdges G (prefix ++ a ∷ after) →
  ConsecutiveEdges G (a ∷ after)
dropPrefixAdjacent [] after adj = adj
dropPrefixAdjacent (x ∷ []) after (GC.edges-step _ rest) = rest
dropPrefixAdjacent (x ∷ y ∷ prefix) after (GC.edges-step _ rest) =
  dropPrefixAdjacent (y ∷ prefix) after rest

lastMarkedSplitAdjacent :
  {G : GC.Graph} {marked xs : List (GC.Graph.Vertex G)} →
  (split : LastMarkedSplit marked xs) →
  ConsecutiveEdges G xs →
  ConsecutiveEdges G
    (LastMarkedSplit.attachment split ∷ LastMarkedSplit.after split)
lastMarkedSplitAdjacent {G = G} split adj =
  dropPrefixAdjacent
    (LastMarkedSplit.before split)
    (LastMarkedSplit.after split)
    (subst (ConsecutiveEdges G) (LastMarkedSplit.reconstruct split) adj)

simplePathAttachment :
  {G : GC.Graph} {X included : List (GC.Graph.Vertex G)}
  {r v : GC.Graph.Vertex G} →
  (p : SimplePathIn G X r v) →
  r ∈ included →
  Σ (LastMarkedSplit included
      (vertices (PathIn.path (SimplePathIn.pathIn p))))
    (λ split →
      ConsecutiveEdges G
        (LastMarkedSplit.attachment split ∷ LastMarkedSplit.after split))
simplePathAttachment p r∈included =
  let split = splitSimplePathAfterLastIncluded p r∈included
  in split ,
     lastMarkedSplitAdjacent split
       (Path.adjacent (PathIn.path (SimplePathIn.pathIn p)))

------------------------------------------------------------------------
-- Carrier and no-duplicate consequences of a last-marked split.
------------------------------------------------------------------------

memberInAppendRight :
  {A : Set} (prefix : List A) {a : A} (suffix : List A) {x : A} →
  x ∈ suffix →
  x ∈ (prefix ++ a ∷ suffix)
memberInAppendRight [] suffix x∈ = there x∈
memberInAppendRight (y ∷ prefix) suffix x∈ =
  there (memberInAppendRight prefix suffix x∈)

memberInAppendLeft :
  {A : Set} (prefix suffix : List A) {x : A} →
  x ∈ prefix → x ∈ (prefix ++ suffix)
memberInAppendLeft prefix [] x∈ =
  subst (λ ys → _ ∈ ys) (sym (++-identityʳ prefix)) x∈
memberInAppendLeft (y ∷ prefix) suffix here = here
memberInAppendLeft (y ∷ prefix) suffix (there x∈) =
  there (memberInAppendLeft prefix suffix x∈)

memberAttachmentInAppend :
  {A : Set} (prefix : List A) {a : A} (suffix : List A) →
  a ∈ (prefix ++ a ∷ suffix)
memberAttachmentInAppend [] suffix = here
memberAttachmentInAppend (y ∷ prefix) suffix =
  there (memberAttachmentInAppend prefix suffix)

AllIn :
  {G : GC.Graph} →
  List (GC.Graph.Vertex G) →
  List (GC.Graph.Vertex G) → Set
AllIn carrier xs = ∀ x → x ∈ xs → x ∈ carrier

suffixInCarrier :
  {G : GC.Graph} {X included : List (GC.Graph.Vertex G)}
  {r v : GC.Graph.Vertex G} →
  (p : SimplePathIn G X r v) →
  (split : LastMarkedSplit included
    (vertices (PathIn.path (SimplePathIn.pathIn p)))) →
  (∀ {x} →
    x ∈ vertices (PathIn.path (SimplePathIn.pathIn p)) →
    x ∈ X) →
  AllIn {G = G} X (LastMarkedSplit.after split)
suffixInCarrier p split inside = λ x x∈after →
  inside
    (subst
      (λ ys → x ∈ ys)
      (sym (LastMarkedSplit.reconstruct split))
      (memberInAppendRight
        (LastMarkedSplit.before split)
        (LastMarkedSplit.after split)
        x∈after))

dropPrefixNoDuplicates :
  {A : Set} (prefix ys : List A) →
  NoDuplicates (prefix ++ ys) →
  NoDuplicates ys
dropPrefixNoDuplicates [] ys noDup = noDup
dropPrefixNoDuplicates (x ∷ prefix) ys (GC.noDup-cons x∉ rest) =
  dropPrefixNoDuplicates prefix ys rest

splitAfterNoDuplicates :
  {A : Set} {marked xs : List A} →
  (split : LastMarkedSplit marked xs) →
  NoDuplicates xs →
  NoDuplicates (LastMarkedSplit.attachment split ∷ LastMarkedSplit.after split)
splitAfterNoDuplicates split noDup =
  dropPrefixNoDuplicates
    (LastMarkedSplit.before split)
    (LastMarkedSplit.attachment split ∷ LastMarkedSplit.after split)
    (subst NoDuplicates (LastMarkedSplit.reconstruct split) noDup)

afterNoDuplicates :
  {A : Set} {x : A} {xs : List A} →
  NoDuplicates (x ∷ xs) →
  NoDuplicates xs
afterNoDuplicates (GC.noDup-cons _ rest) = rest

splitAttachmentInCarrier :
  {G : GC.Graph} {X included : List (GC.Graph.Vertex G)}
  {r v : GC.Graph.Vertex G} →
  (p : SimplePathIn G X r v) →
  (split : LastMarkedSplit included
    (vertices (PathIn.path (SimplePathIn.pathIn p)))) →
  (inside : ∀ {x} →
    x ∈ vertices (PathIn.path (SimplePathIn.pathIn p)) → x ∈ X) →
  LastMarkedSplit.attachment split ∈ X
splitAttachmentInCarrier p split inside =
  inside
    (subst
      (λ ys → LastMarkedSplit.attachment split ∈ ys)
      (sym (LastMarkedSplit.reconstruct split))
      (memberAttachmentInAppend
        (LastMarkedSplit.before split)
        (LastMarkedSplit.after split)))

------------------------------------------------------------------------
-- A branch-local bidirectional adjacency witness.  The forward edge is
-- supplied by the path; the reverse edge is supplied by carrier symmetry.
------------------------------------------------------------------------

data BidirectionalConsecutiveEdges
  {G : GC.Graph} : List (GC.Graph.Vertex G) → Set where
  bidirectional-single :
    {x : GC.Graph.Vertex G} →
    BidirectionalConsecutiveEdges {G = G}
      (x ∷ [])
  bidirectional-step :
    {x y : GC.Graph.Vertex G} {xs : List (GC.Graph.Vertex G)} →
    GC.Graph.Adj G x y →
    GC.Graph.Adj G y x →
    BidirectionalConsecutiveEdges {G = G} (y ∷ xs) →
    BidirectionalConsecutiveEdges {G = G} (x ∷ y ∷ xs)

consecutiveToBidirectional :
  {G : GC.Graph} {X xs : List (GC.Graph.Vertex G)} →
  (symmetry : CDFS.SkeletonAdjacencySymmetry {G = G} X) →
  AllIn {G = G} X xs →
  ConsecutiveEdges G xs →
  BidirectionalConsecutiveEdges {G = G} xs
consecutiveToBidirectional symmetry allIn GC.edges-single =
  bidirectional-single
consecutiveToBidirectional {X = X} {xs = x ∷ y ∷ xs}
  symmetry allIn (GC.edges-step xy rest) =
  bidirectional-step
    xy
    (CDFS.SkeletonAdjacencySymmetry.reverseInside
      symmetry
      (allIn x here)
      (allIn y (there here))
      xy)
    (consecutiveToBidirectional
      symmetry
      (λ x x∈ → allIn x (there x∈))
      rest)

record FreshBranchAttachment
  (G : GC.Graph)
  (X included : List (GC.Graph.Vertex G))
  : Set₁ where
  field
    attachment : GC.Graph.Vertex G
    suffix : List (GC.Graph.Vertex G)
    attachmentIncluded : attachment ∈ included
    suffixFresh : ∀ x → x ∈ suffix → x ∉ included
    suffixInCarrierProof : AllIn {G = G} X suffix
    suffixNoDuplicates : NoDuplicates suffix
    bidirectionalEdges :
      BidirectionalConsecutiveEdges {G = G} (attachment ∷ suffix)

open FreshBranchAttachment public

freshBranchFromSimplePath :
  {G : GC.Graph} {X included : List (GC.Graph.Vertex G)}
  {r v : GC.Graph.Vertex G} →
  (symmetry : CDFS.SkeletonAdjacencySymmetry {G = G} X) →
  (p : SimplePathIn G X r v) →
  (rootIncluded : r ∈ included) →
  (inside : ∀ {x} →
    x ∈ vertices (PathIn.path (SimplePathIn.pathIn p)) → x ∈ X) →
  NoDuplicates (vertices (PathIn.path (SimplePathIn.pathIn p))) →
      FreshBranchAttachment G X included
freshBranchFromSimplePath {G = G} {X = X} {included = included}
  symmetry p rootIncluded inside pathNoDup =
  let split = splitSimplePathAfterLastIncluded p rootIncluded
      suffixAll = suffixInCarrier p split inside
      branchAll : AllIn {G = G} X
        (LastMarkedSplit.attachment split ∷ LastMarkedSplit.after split)
      branchAll = λ x → λ
        { here → splitAttachmentInCarrier p split inside
        ; (there x∈) → suffixAll x x∈
        }
      branchEdges = consecutiveToBidirectional
        symmetry branchAll
        (lastMarkedSplitAdjacent split
          (Path.adjacent (PathIn.path (SimplePathIn.pathIn p))))
      suffixNoDup = afterNoDuplicates (splitAfterNoDuplicates split pathNoDup)
  in record
  { attachment = LastMarkedSplit.attachment split
  ; suffix = LastMarkedSplit.after split
  ; attachmentIncluded = LastMarkedSplit.attachmentMarked split
  ; suffixFresh = λ x x∈ x∈included →
      LastMarkedSplit.afterFresh split x∈
        x∈included
  ; suffixInCarrierProof = suffixAll
  ; suffixNoDuplicates = suffixNoDup
  ; bidirectionalEdges = branchEdges
  }

------------------------------------------------------------------------
-- Insertion history.  The parent relation is stored as ordered edge
-- certificates rather than as a dependent function over membership proofs.
-- This makes the acyclicity witness structural: every new child is appended
-- after its already-present parent.
------------------------------------------------------------------------

record ParentLink
  {G : GC.Graph}
  (X : List (GC.Graph.Vertex G)) : Set where
  field
    parent child : GC.Graph.Vertex G
    forward : GC.Graph.Adj G parent child
    backward : GC.Graph.Adj G child parent

open ParentLink public

data ParentLinksDescribeInsertionOrder
  {G : GC.Graph}
  {X : List (GC.Graph.Vertex G)}
  (r : GC.Graph.Vertex G) :
  List (GC.Graph.Vertex G) → List (ParentLink {G = G} X) → Set₁ where
  root-only :
    ParentLinksDescribeInsertionOrder r (r ∷ []) []
  append-child :
    {included : List (GC.Graph.Vertex G)}
    {links : List (ParentLink {G = G} X)}
    {parent child : GC.Graph.Vertex G}
    → ParentLinksDescribeInsertionOrder r included links
    → parent ∈ included
    → child ∉ included
    → (link : ParentLink {G = G} X)
    → ParentLink.parent {G = G} {X = X} link ≡ parent
    → ParentLink.child {G = G} {X = X} link ≡ child
    → ParentLinksDescribeInsertionOrder r
        (included ++ child ∷ [])
        (links ++ link ∷ [])

record PartialPathUnionTree
  {G : GC.Graph}
  (r : GC.Graph.Vertex G)
  (X : List (GC.Graph.Vertex G)) : Set₁ where
  field
    included : List (GC.Graph.Vertex G)
    links : List (ParentLink {G = G} X)
    includedNoDuplicates : NoDuplicates included
    includedInCarrier : ∀ {x} → x ∈ included → x ∈ X
    rootIncluded : r ∈ included
    history : ParentLinksDescribeInsertionOrder r included links

open PartialPathUnionTree public

parentLinksAlong :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  (a : GC.Graph.Vertex G) (suffix : List (GC.Graph.Vertex G))
  → AllIn {G = G} X (a ∷ suffix)
  → BidirectionalConsecutiveEdges {G = G} (a ∷ suffix)
  → List (ParentLink {G = G} X)
parentLinksAlong a [] allIn bidirectional-single = []
parentLinksAlong {G = G} {X = X} a (y ∷ ys) allIn
  (bidirectional-step forward backward rest) =
  record
  { parent = a
  ; child = y
  ; forward = forward
  ; backward = backward
  }
  ∷ parentLinksAlong {G = G} {X = X} y ys
      (λ x x∈ → allIn x (there x∈))
      rest

parentLinksAlong-empty :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  (a : GC.Graph.Vertex G)
  (allIn : AllIn {G = G} X (a ∷ []))
  (bidirectional : BidirectionalConsecutiveEdges {G = G} (a ∷ [])) →
  parentLinksAlong a [] allIn bidirectional ≡ []
parentLinksAlong-empty {G = G} {X = X} a allIn bidirectional-single = refl

------------------------------------------------------------------------
-- Extending an insertion history by a fresh path suffix.
------------------------------------------------------------------------

appendMemberCases :
  {A : Set} (x : A) {xs ys : List A} →
  x ∈ (xs ++ ys) → x ∈ xs ⊎ x ∈ ys
appendMemberCases x {xs = []} {ys = ys} x∈ = inj₂ x∈
appendMemberCases x {xs = y ∷ xs} {ys = ys} here = inj₁ here
appendMemberCases x {xs = y ∷ xs} {ys = ys} (there x∈) with
  appendMemberCases x {xs = xs} {ys = ys} x∈
... | inj₁ x∈xs = inj₁ (there x∈xs)
... | inj₂ x∈ys = inj₂ x∈ys

memberSingletonCases :
  {A : Set} {x y : A} → x ∈ (y ∷ []) → x ≡ y
memberSingletonCases here = refl

notEqualToHeadFromNoDuplicates :
  {A : Set} {x y : A} {ys : List A} →
  x ∈ ys →
  NoDuplicates (y ∷ ys) →
  x ≢ y
notEqualToHeadFromNoDuplicates {x = x} {y = y} {ys = ys}
  x∈ys (GC.noDup-cons y∉ys nd) x≡y =
  y∉ys (subst (λ z → z ∈ ys) x≡y x∈ys)

freshAfterOneContradiction :
  {A : Set} {included : List A} {y : A} {ys : List A} →
  FreshFor included (y ∷ ys) →
  NoDuplicates (y ∷ ys) →
  (x : A) →
  x ∈ ys →
  x ∈ (included ++ (y ∷ [])) →
  ⊥
freshAfterOneContradiction {A = A} {included = included} {y = y} {ys = ys}
  fresh (GC.noDup-cons y∉ys nd-ys) x x∈ys x∈new =
  noAppendSingleton
    (fresh (there x∈ys))
    (notEqualToHeadFromNoDuplicates x∈ys (GC.noDup-cons y∉ys nd-ys))
    x∈new
  where
    noAppendSingleton :
      {x y : A} {included : List A} →
      x ∉ included →
      x ≢ y →
      x ∉ (included ++ (y ∷ []))
    noAppendSingleton {included = []} old neq here = neq refl
    noAppendSingleton {included = []} old neq (there ())
    noAppendSingleton {included = z ∷ included} old neq here =
      old here
    noAppendSingleton {included = z ∷ included} old neq (there p) =
      noAppendSingleton
        (λ q → old (there q))
        neq
        p

freshAfterOne :
  {A : Set} {included : List A} {y : A} {ys : List A} →
  FreshFor included (y ∷ ys) →
  NoDuplicates (y ∷ ys) →
  FreshFor (included ++ (y ∷ [])) ys
freshAfterOne {A = A} {included = included} {y = y} {ys = ys}
  fresh (GC.noDup-cons y∉ys nd-ys)
  {x} x∈ys x∈new =
  freshAfterOneContradiction
    fresh (GC.noDup-cons y∉ys nd-ys) x x∈ys x∈new

appendInsertionHistory :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink X)} →
  ParentLinksDescribeInsertionOrder r included links →
  (parent : GC.Graph.Vertex G) →
  parent ∈ included →
  (suffix : List (GC.Graph.Vertex G)) →
  FreshFor included suffix →
  NoDuplicates suffix →
  (allIn : AllIn {G = G} X (parent ∷ suffix)) →
  (bidirectional : BidirectionalConsecutiveEdges {G = G}
    (parent ∷ suffix)) →
  ParentLinksDescribeInsertionOrder r
    (included ++ suffix)
    (links ++ parentLinksAlong {G = G} {X = X}
      parent suffix allIn bidirectional)
appendInsertionHistory {G = G} {X = X} {r = r}
  {included = included} {links = links}
  history parent parent∈ [] fresh noDup allIn
  bidirectional =
  let
    h₁ = subst
           (λ ys → ParentLinksDescribeInsertionOrder r included ys)
           (sym (++-identityʳ links))
           history
    h₁′ = subst
      (λ ys → ParentLinksDescribeInsertionOrder r ys (links ++ []))
      (sym (++-identityʳ included))
      h₁
    h₂ = subst
      (λ ls → ParentLinksDescribeInsertionOrder r
        (included ++ []) ls)
      (cong
        (λ zs → links ++ zs)
        (sym (parentLinksAlong-empty {G = G} {X = X}
          parent allIn bidirectional)))
      h₁′
  in h₂
appendInsertionHistory {G = G} {X = X} {r = r}
  {included = included} {links = links}
  history parent parent∈ (y ∷ ys) fresh
  (GC.noDup-cons y∉ys nd-ys)
  allIn
  (bidirectional-step forward backward rest) =
  let
    link : ParentLink X
    link = record
      { parent = parent
      ; child = y
      ; forward = forward
      ; backward = backward
      }

    history₁ :
      ParentLinksDescribeInsertionOrder r
        (included ++ y ∷ [])
        (links ++ link ∷ [])
    history₁ = append-child history parent∈
      (fresh here) link refl refl

    allIn₁ : AllIn {G = G} X (y ∷ ys)
    allIn₁ x x∈ = allIn x (there x∈)

    fresh₁ : FreshFor (included ++ y ∷ []) ys
    fresh₁ = freshAfterOne fresh (GC.noDup-cons y∉ys nd-ys)

    bidirectional₁ : BidirectionalConsecutiveEdges (y ∷ ys)
    bidirectional₁ = rest

    tailLinks : List (ParentLink X)
    tailLinks = parentLinksAlong {G = G} {X = X}
      y ys allIn₁ bidirectional₁

    tailHistory :
      ParentLinksDescribeInsertionOrder r
        ((included ++ y ∷ []) ++ ys)
        ((links ++ link ∷ []) ++ tailLinks)
    tailHistory = appendInsertionHistory
      {G = G} {X = X} {r = r}
      {included = included ++ y ∷ []}
      {links = links ++ link ∷ []}
      history₁ y
      (memberAttachmentInAppend included [])
      ys fresh₁ nd-ys allIn₁ bidirectional₁

    included-assoc :
      (included ++ y ∷ []) ++ ys ≡ included ++ (y ∷ ys)
    included-assoc = ++-assoc included (y ∷ []) ys

    links-assoc :
      (links ++ link ∷ []) ++ parentLinksAlong {G = G} {X = X}
        y ys allIn₁ bidirectional₁
        ≡ links ++ (link ∷ parentLinksAlong {G = G} {X = X}
          y ys allIn₁ bidirectional₁)
    links-assoc = ++-assoc links (link ∷ [])
      (parentLinksAlong {G = G} {X = X} y ys allIn₁ bidirectional₁)
  in subst
       (λ zs → ParentLinksDescribeInsertionOrder r zs
         (links ++ link ∷ parentLinksAlong {G = G} {X = X}
           y ys allIn₁ bidirectional₁))
       included-assoc
       (subst
         (λ ls → ParentLinksDescribeInsertionOrder r
           ((included ++ y ∷ []) ++ ys) ls)
         links-assoc
         tailHistory)

branchAllIn :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)}
  (T : PartialPathUnionTree {G = G} r X)
  (branch : FreshBranchAttachment G X
    (PartialPathUnionTree.included T)) →
  AllIn {G = G} X
    (FreshBranchAttachment.attachment branch ∷
     FreshBranchAttachment.suffix branch)
branchAllIn {G = G} {r = r} {X = X} T branch x here =
  PartialPathUnionTree.includedInCarrier T
    (FreshBranchAttachment.attachmentIncluded branch)
branchAllIn {G = G} {r = r} {X = X} T branch x (there x∈) =
  FreshBranchAttachment.suffixInCarrierProof {G = G} branch x x∈

appendCarrier :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)}
  (T : PartialPathUnionTree {G = G} r X)
  (branch : FreshBranchAttachment G X
    (PartialPathUnionTree.included T)) →
  ∀ {x} →
  x ∈ (PartialPathUnionTree.included T ++
       FreshBranchAttachment.suffix branch) →
  x ∈ X
appendCarrier {G = G} {r = r} {X = X} T branch {x} x∈ =
  appendCarrierCases x (appendMemberCases x x∈)
  where
    appendCarrierCases :
      (x : GC.Graph.Vertex G) →
      (x ∈ PartialPathUnionTree.included T ⊎
       x ∈ FreshBranchAttachment.suffix branch) →
      x ∈ X
    appendCarrierCases x (inj₁ x∈old) =
      PartialPathUnionTree.includedInCarrier T x∈old
    appendCarrierCases x (inj₂ x∈suffix) =
      FreshBranchAttachment.suffixInCarrierProof {G = G} branch x x∈suffix

attachFreshBranch :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)}
  (T : PartialPathUnionTree {G = G} r X) →
  FreshBranchAttachment G X
    (PartialPathUnionTree.included T) →
  PartialPathUnionTree r X
attachFreshBranch {G = G} {r = r} {X = X} T branch =
  let
    included′ = PartialPathUnionTree.included T ++
      FreshBranchAttachment.suffix branch
    links′ = PartialPathUnionTree.links T ++
      parentLinksAlong {G = G} {X = X}
        (FreshBranchAttachment.attachment branch)
        (FreshBranchAttachment.suffix branch)
        (branchAllIn T branch)
        (FreshBranchAttachment.bidirectionalEdges {G = G} branch)

    allInBranch : AllIn {G = G} X
      (FreshBranchAttachment.attachment branch ∷
       FreshBranchAttachment.suffix branch)
    allInBranch = branchAllIn T branch

    history′ = appendInsertionHistory
      (PartialPathUnionTree.history T)
      (FreshBranchAttachment.attachment branch)
      (FreshBranchAttachment.attachmentIncluded branch)
      (FreshBranchAttachment.suffix branch)
      (λ {x} x∈ →
        FreshBranchAttachment.suffixFresh branch x x∈)
      (FreshBranchAttachment.suffixNoDuplicates branch)
      allInBranch
      (FreshBranchAttachment.bidirectionalEdges {G = G} branch)

    noDup′ : NoDuplicates included′
    noDup′ = GC.++-noDup
      (PartialPathUnionTree.included T)
      (FreshBranchAttachment.suffix branch)
      (PartialPathUnionTree.includedNoDuplicates T)
      (FreshBranchAttachment.suffixNoDuplicates branch)
      (λ {x} x∈included x∈suffix →
        FreshBranchAttachment.suffixFresh branch x x∈suffix x∈included)

    inCarrier′ : ∀ {x} → x ∈ included′ → x ∈ X
    inCarrier′ = appendCarrier T branch

    root′ : r ∈ included′
    root′ = memberInAppendLeft
      (PartialPathUnionTree.included T)
      (FreshBranchAttachment.suffix branch)
      (PartialPathUnionTree.rootIncluded T)
  in record
  { included = included′
  ; links = links′
  ; includedNoDuplicates = noDup′
  ; includedInCarrier = inCarrier′
  ; rootIncluded = root′
  ; history = history′
  }

------------------------------------------------------------------------
-- The requested path endpoint is in the fresh suffix.  This is the
-- coverage fact needed by the carrier fold; it uses no adjacency
-- decision and no path minimisation.
------------------------------------------------------------------------

lastMember :
  {A : Set} {xs : List A} →
  (ne : NonEmpty xs) →
  last xs ne ∈ xs
lastMember {xs = x ∷ []} nonempty = here
lastMember {xs = x ∷ y ∷ xs} nonempty =
  there (lastMember {xs = y ∷ xs} nonempty)

appendNonEmpty :
  {A : Set} {xs ys : List A} →
  NonEmpty ys →
  NonEmpty (xs ++ ys)
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

lastRewrite :
  {A : Set} {xs ys : List A} →
  xs ≡ ys →
  (xs-ne : NonEmpty xs) →
  (ys-ne : NonEmpty ys) →
  last xs xs-ne ≡ last ys ys-ne
lastRewrite refl nonempty nonempty = refl

memberInAppend :
  {A : Set} (prefix ys : List A) {x : A} →
  x ∈ ys → x ∈ (prefix ++ ys)
memberInAppend [] ys x∈ = x∈
memberInAppend (z ∷ prefix) ys x∈ =
  there (memberInAppend prefix ys x∈)

headOrTail :
  {A : Set} (x y : A) (ys : List A) →
  x ∈ (y ∷ ys) → x ≡ y ⊎ x ∈ ys
headOrTail x y ys here = inj₁ refl
headOrTail x y ys (there x∈) = inj₂ x∈

lastNotInPrefixAppend :
  {A : Set} (prefix ys : List A) →
  (ys-ne : NonEmpty ys) →
  NoDuplicates (prefix ++ ys) →
  last ys ys-ne ∉ prefix
lastNotInPrefixAppend [] ys ys-ne noDup ()
lastNotInPrefixAppend (x ∷ prefix) ys ys-ne
  (GC.noDup-cons x∉rest restNoDup) =
  lastNotInPrefixHead x prefix ys ys-ne x∉rest restNoDup
  where
  lastNotInPrefixHead :
    {A : Set} (z : A) (prefix ys : List A) →
    (ys-ne : NonEmpty ys) →
    z ∉ (prefix ++ ys) →
    NoDuplicates (prefix ++ ys) →
    last ys ys-ne ∉ (z ∷ prefix)
  lastNotInPrefixHead z prefix ys ys-ne z∉rest restNoDup here =
    z∉rest
      (memberInAppend prefix ys
        (lastMember ys-ne))
  lastNotInPrefixHead z prefix ys ys-ne z∉rest restNoDup
    (there x∈) =
    lastNotInPrefixAppend prefix ys ys-ne restNoDup x∈

endpointInAfterOfLastMarkedSplit :
  {A : Set} {marked xs : List A} →
  (split : LastMarkedSplit marked xs) →
  (xs-ne : NonEmpty xs) →
  NoDuplicates xs →
  (x : A) →
  last xs xs-ne ≡ x →
  x ∉ marked →
  x ∈ (LastMarkedSplit.attachment split ∷
    LastMarkedSplit.after split)
endpointInAfterOfLastMarkedSplit {marked = marked} {xs = xs} split xs-ne noDup
  x last≡x x∉marked =
  let
    rest = LastMarkedSplit.attachment split ∷
      LastMarkedSplit.after split
    rest-ne : NonEmpty rest
    rest-ne = nonempty
    whole-last : last xs xs-ne ≡ last rest rest-ne
    whole-last = trans
      (lastRewrite
        (LastMarkedSplit.reconstruct split)
        xs-ne
        (appendNonEmpty rest-ne))
      (lastAppend
        (LastMarkedSplit.before split)
        rest
        rest-ne)
    x≡rest-last : x ≡ last rest rest-ne
    x≡rest-last = trans (sym last≡x) whole-last
    x∉before : x ∉ LastMarkedSplit.before split
    x∉before = λ x∈before →
      lastNotInPrefixAppend
        (LastMarkedSplit.before split) rest rest-ne
        (subst NoDuplicates
          (LastMarkedSplit.reconstruct split)
          noDup)
        (subst (λ z → z ∈ LastMarkedSplit.before split)
          x≡rest-last x∈before)
    x∈whole : x ∈ xs
    x∈whole =
      subst (λ z → z ∈ xs)
        last≡x
        (lastMember xs-ne)
  in
    caseAppend marked
      (LastMarkedSplit.before split)
      (LastMarkedSplit.after split)
      (LastMarkedSplit.attachment split)
      x
      (appendMemberCases x
        (subst (λ z → x ∈ z)
          (LastMarkedSplit.reconstruct split)
          x∈whole))
      x∉before
      x≡rest-last
      x∉marked
      (LastMarkedSplit.attachmentMarked split)
  where
  caseAppend :
    {A : Set} (marked before after : List A) (a x : A) →
    x ∈ before ⊎ x ∈ (a ∷ after) →
    x ∉ before →
    x ≡ last (a ∷ after) nonempty →
    x ∉ marked →
    a ∈ marked →
    x ∈ (a ∷ after)
  caseAppend marked before after a x
    (inj₁ x∈before) x∉before
    x≡last x∉marked a∈marked = ⊥-elim (x∉before x∈before)
  caseAppend marked before after a x
    (inj₂ x∈after) x∉before x≡last x∉marked a∈marked = x∈after

freshBranchEndpointIncluded :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)}
  (T : PartialPathUnionTree {G = G} r X) →
  (symmetry : CDFS.SkeletonAdjacencySymmetry {G = G} X) →
  (v : GC.Graph.Vertex G) →
  (v∉ : v ∉ PartialPathUnionTree.included T) →
  (p : SimplePathIn G X r v) →
  v ∈ PartialPathUnionTree.included
    (attachFreshBranch T
      (freshBranchFromSimplePath
        symmetry
        p
        (PartialPathUnionTree.rootIncluded T)
        (PathIn.insideX (SimplePathIn.pathIn p))
        (SimplePathIn.noDuplicateVertices p)))
freshBranchEndpointIncluded {G = G} {X = X} T symmetry v v∉ p =
  let
    split = splitSimplePathAfterLastIncluded p
      (PartialPathUnionTree.rootIncluded T)
    branch = freshBranchFromSimplePath
      symmetry
      p
      (PartialPathUnionTree.rootIncluded T)
      (PathIn.insideX (SimplePathIn.pathIn p))
      (SimplePathIn.noDuplicateVertices p)
    path-ne = Path.nonEmptyWitness
      (PathIn.path (SimplePathIn.pathIn p))
    endpoint-eq = Path.endsAt
      (PathIn.path (SimplePathIn.pathIn p))
    endpoint∉marked : v ∉ PartialPathUnionTree.included T
    endpoint∉marked = v∉
    endpoint∈suffix : v ∈ LastMarkedSplit.after split
    endpoint∈suffix =
      let
        endpointAfterOrAttachment =
          endpointInAfterOfLastMarkedSplit split path-ne
            (SimplePathIn.noDuplicateVertices p)
            v endpoint-eq endpoint∉marked
      in endpointAfter v split endpoint∉marked
        endpointAfterOrAttachment
    appendedAfter = memberInAppend
      (PartialPathUnionTree.included T)
      (LastMarkedSplit.after split)
      endpoint∈suffix
    branchSuffix : FreshBranchAttachment.suffix branch ≡
      LastMarkedSplit.after split
    branchSuffix = refl
  in subst
       (λ ys → v ∈ (PartialPathUnionTree.included T ++ ys))
       (sym branchSuffix)
       appendedAfter
  where
  endpointAfter :
    (v : GC.Graph.Vertex G) →
    (split : LastMarkedSplit
      (PartialPathUnionTree.included T)
      (vertices (PathIn.path (SimplePathIn.pathIn p)))) →
    v ∉ PartialPathUnionTree.included T →
    v ∈ (LastMarkedSplit.attachment split ∷
      LastMarkedSplit.after split) →
    v ∈ LastMarkedSplit.after split
  endpointAfter v split v∉marked proof with
    headOrTail v
      (LastMarkedSplit.attachment split)
      (LastMarkedSplit.after split)
      proof
  ... | inj₁ v≡attachment =
    ⊥-elim
      (v∉marked
        (subst (λ z → z ∈ PartialPathUnionTree.included T)
          (sym v≡attachment)
          (LastMarkedSplit.attachmentMarked split)))
  ... | inj₂ v∈after = v∈after

includedMonotoneAfterAttach :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)}
  (T : PartialPathUnionTree {G = G} r X) →
  (branch : FreshBranchAttachment G X
    (PartialPathUnionTree.included T)) →
  ∀ {x} → x ∈ PartialPathUnionTree.included T →
    x ∈ PartialPathUnionTree.included (attachFreshBranch T branch)
includedMonotoneAfterAttach T branch x∈ =
  memberInAppendLeft
    (PartialPathUnionTree.included T)
    (FreshBranchAttachment.suffix branch)
    x∈

------------------------------------------------------------------------
-- Carrier fold.  The result remembers that every processed carrier
-- vertex has entered the insertion-certified tree.
------------------------------------------------------------------------

record PathUnionFoldResult
  {G : GC.Graph}
  (r : GC.Graph.Vertex G)
  (X processed : List (GC.Graph.Vertex G)) : Set₁ where
  field
    tree : PartialPathUnionTree {G = G} r X
    processedCovered : ∀ {x} → x ∈ processed →
      x ∈ PartialPathUnionTree.included tree

open PathUnionFoldResult public

rootPartialTree :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  CDFS.RootedPathConnected G r X →
  PartialPathUnionTree {G = G} r X
rootPartialTree {r = r} paths = record
  { included = r ∷ []
  ; links = []
  ; includedNoDuplicates =
      GC.noDup-cons (λ ()) GC.noDup-nil
  ; includedInCarrier = λ { here →
      CDFS.RootedPathConnected.rootIn paths }
  ; rootIncluded = here
  ; history = root-only
  }

pathUnionFoldOver :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  (paths : CDFS.RootedPathConnected G r X) →
  (symmetry : CDFS.SkeletonAdjacencySymmetry {G = G} X) →
  (processed : List (GC.Graph.Vertex G)) →
  (processedInCarrier : ∀ {x} → x ∈ processed → x ∈ X) →
  PathUnionFoldResult {G = G} r X processed
pathUnionFoldOver paths symmetry [] processedInCarrier = record
  { tree = rootPartialTree paths
  ; processedCovered = λ { () }
  }
pathUnionFoldOver {G = G} {r = r} {X = X}
  paths symmetry (v ∷ processed) processedInCarrier
  with pathUnionFoldOver paths symmetry processed
    (λ {x} x∈ → processedInCarrier (there x∈))
... | previous with
  memberDec (GC.vertexEqDec {G}) v
    (PartialPathUnionTree.included (PathUnionFoldResult.tree previous))
... | yes v∈old = record
  { tree = PathUnionFoldResult.tree previous
  ; processedCovered = λ
      { here → v∈old
      ; (there x∈) →
          PathUnionFoldResult.processedCovered previous x∈ }
  }
... | no v∉old =
  let
    previousTree = PathUnionFoldResult.tree previous
    v∈X : v ∈ X
    v∈X = processedInCarrier here
    p = CDFS.RootedPathConnected.pathTo paths v v∈X
    branch = freshBranchFromSimplePath
      symmetry p
      (PartialPathUnionTree.rootIncluded previousTree)
      (PathIn.insideX (SimplePathIn.pathIn p))
      (SimplePathIn.noDuplicateVertices p)
    extended = attachFreshBranch previousTree branch
  in record
  { tree = extended
  ; processedCovered = λ
      { here →
          freshBranchEndpointIncluded previousTree symmetry v v∉old p
      ; (there x∈) →
          includedMonotoneAfterAttach previousTree branch
            (PathUnionFoldResult.processedCovered previous x∈) }
  }

pathUnionFold :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  CDFS.RootedPathConnected G r X →
  CDFS.SkeletonAdjacencySymmetry {G = G} X →
  PartialPathUnionTree {G = G} r X
pathUnionFold {G = G} {X = X} paths symmetry =
  PathUnionFoldResult.tree
    (pathUnionFoldOver paths symmetry X (λ x∈ → x∈))

pathUnionFoldCovers :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  (paths : CDFS.RootedPathConnected G r X) →
  (symmetry : CDFS.SkeletonAdjacencySymmetry {G = G} X) →
  ∀ {x} → x ∈ X →
    x ∈ PartialPathUnionTree.included (pathUnionFold paths symmetry)
pathUnionFoldCovers {G = G} {X = X} paths symmetry x∈ =
  PathUnionFoldResult.processedCovered
    (pathUnionFoldOver paths symmetry X (λ x∈ → x∈))
    x∈

pathUnionFoldRangeExact :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  (paths : CDFS.RootedPathConnected G r X) →
  (symmetry : CDFS.SkeletonAdjacencySymmetry {G = G} X) →
  SameVertexSet
    (PartialPathUnionTree.included (pathUnionFold paths symmetry))
    X
pathUnionFoldRangeExact paths symmetry =
  PartialPathUnionTree.includedInCarrier (pathUnionFold paths symmetry) ,
  pathUnionFoldCovers paths symmetry

------------------------------------------------------------------------
-- The carrier fold has now completed a tree.  Keep this projection small:
-- it contains exactly the finite carrier, ordered parent-edge history, and
-- its exact range.  Traversal data is deliberately not smuggled in here.
------------------------------------------------------------------------

record CompleteInsertionParentTree
  {G : GC.Graph}
  (r : GC.Graph.Vertex G)
  (X : List (GC.Graph.Vertex G)) : Set₁ where
  field
    included : List (GC.Graph.Vertex G)
    links : List (ParentLink {G = G} X)
    includedNoDuplicates : NoDuplicates included
    rangeExact : SameVertexSet included X
    rootIncluded : r ∈ included
    history : ParentLinksDescribeInsertionOrder r included links

open CompleteInsertionParentTree public

pathUnionFoldToCompleteInsertionTree :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  (paths : CDFS.RootedPathConnected G r X) →
  (symmetry : CDFS.SkeletonAdjacencySymmetry {G = G} X) →
  CompleteInsertionParentTree r X
pathUnionFoldToCompleteInsertionTree paths symmetry = record
  { included = PartialPathUnionTree.included final
  ; links = PartialPathUnionTree.links final
  ; includedNoDuplicates = PartialPathUnionTree.includedNoDuplicates final
  ; rangeExact = pathUnionFoldRangeExact paths symmetry
  ; rootIncluded = PartialPathUnionTree.rootIncluded final
  ; history = PartialPathUnionTree.history final
  }
  where
  final : PartialPathUnionTree _ _
  final = pathUnionFold paths symmetry

historyNonEmpty :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)} →
  ParentLinksDescribeInsertionOrder r included links →
  NonEmpty included
historyNonEmpty root-only = nonempty
historyNonEmpty (append-child history parent∈ child∉ link parent≡ child≡) =
  GC.appendSingle-nonEmpty (historyNonEmpty history)

-- Every append-child constructor adds one vertex and exactly one parent edge.
-- This is the structural edge-count identity used by the eventual Euler tour.
linksLength :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)} →
  ParentLinksDescribeInsertionOrder r included links →
  length links ≡ length included ∸ 1
linksLength root-only = refl
linksLength
  (append-child {included = included} {links = links} {child = child}
    history parent∈ child∉ link parent≡ child≡) =
  trans
    (GC.appendSingle-length links link)
    (trans
      (cong suc (linksLength history))
      (trans
        (sym (GC.nonEmpty-length-suc-pred (historyNonEmpty history)))
        (sym (cong (λ m → m ∸ 1)
          (GC.appendSingle-length included child)))))

-- A stored link never points outside the insertion carrier.  This is the
-- elementary history fact used to rule out an older link for a freshly
-- appended child.
historyLinkChildInIncluded :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)} →
  ParentLinksDescribeInsertionOrder r included links →
  {e : ParentLink {G = G} X} →
  e ∈ links → ParentLink.child e ∈ included
historyLinkChildInIncluded root-only ()
historyLinkChildInIncluded
  (append-child {included = included} {links = links} {child = child}
    history parent∈ child∉ link parent≡ child≡) {e} e∈
  with appendMemberCases e e∈
... | inj₁ e∈old =
  memberInAppendLeft included (child ∷ [])
    (historyLinkChildInIncluded history e∈old)
... | inj₂ here =
  subst
    (λ z → z ∈ (included ++ child ∷ []))
    (sym child≡)
    (memberAttachmentInAppend included [])

-- Every included non-root vertex was introduced by a concrete parent link.
-- This intentionally states existence only; the later child-partition proof
-- will establish the stronger uniqueness property needed by DFS recursion.
parentLinkExists :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)} →
  ParentLinksDescribeInsertionOrder r included links →
  (v : GC.Graph.Vertex G) →
  v ∈ included → v ≢ r →
  Σ (ParentLink {G = G} X) λ e →
    e ∈ links × ParentLink.child e ≡ v
parentLinkExists {r = r} root-only v v∈ v≢ =
  ⊥-elim (v≢ (memberSingletonCases {x = v} {y = r} v∈))
parentLinkExists {G = G} {X = X}
  (append-child {included = included} {links = links} {child = child}
    history parent∈ child∉ link parent≡ child≡)
  v v∈ v≢ with appendMemberCases v v∈
... | inj₁ v∈old =
  oldCase (parentLinkExists history v v∈old v≢)
  where
  oldCase :
    Σ (ParentLink {G = G} X) (λ e →
      e ∈ links × ParentLink.child e ≡ v) →
    Σ (ParentLink {G = G} X) (λ e →
      e ∈ (links ++ link ∷ []) × ParentLink.child e ≡ v)
  oldCase (e , e∈old , child≡v) =
    e , memberInAppendLeft links (link ∷ []) e∈old , child≡v
... | inj₂ v∈new =
  let v≡child = memberSingletonCases v∈new
  in link , memberAttachmentInAppend links [] ,
     trans child≡ (sym v≡child)

-- Freshness at an append step prevents an older link from naming the newly
-- introduced child.  This is the only exclusion fact needed for parent
-- uniqueness; equality of proof fields inside ParentLink is never required.
oldLinkChildNotNew :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {oldIncluded : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)}
  {child : GC.Graph.Vertex G} →
  (history : ParentLinksDescribeInsertionOrder r oldIncluded links) →
  child ∉ oldIncluded →
  {e : ParentLink {G = G} X} →
  e ∈ links → ParentLink.child e ≢ child
oldLinkChildNotNew {oldIncluded = oldIncluded} history child∉ e∈ child-eq =
  child∉
    (subst
      (λ z → z ∈ oldIncluded)
      child-eq
      (historyLinkChildInIncluded history e∈))

-- The insertion history determines a unique parent vertex for each child.
-- We intentionally prove uniqueness of parents, not equality of ParentLink
-- records, because their adjacency fields may carry distinct proof terms.
parentVertexUnique :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)} →
  ParentLinksDescribeInsertionOrder r included links →
  {e₁ e₂ : ParentLink {G = G} X} →
  e₁ ∈ links → e₂ ∈ links →
  ParentLink.child e₁ ≡ ParentLink.child e₂ →
  ParentLink.parent e₁ ≡ ParentLink.parent e₂
parentVertexUnique root-only ()
parentVertexUnique
  (append-child {included = included} {links = links} {child = child}
    history parent∈ child∉ link parent≡ child≡)
  {e₁} {e₂} e₁∈ e₂∈ childEq
  with appendMemberCases e₁ e₁∈ | appendMemberCases e₂ e₂∈
... | inj₁ e₁-old | inj₁ e₂-old =
  parentVertexUnique history e₁-old e₂-old childEq
... | inj₁ e₁-old | inj₂ here =
  ⊥-elim
    (oldLinkChildNotNew history child∉ e₁-old
      (trans childEq child≡))
... | inj₂ here | inj₁ e₂-old =
  ⊥-elim
    (oldLinkChildNotNew history child∉ e₂-old
      (trans (sym childEq) child≡))
... | inj₂ here | inj₂ here = refl

-- The child projection of an insertion history is duplicate-free.  This is
-- stronger than parent uniqueness: it says that an insertion step can never
-- introduce a vertex which was already introduced by an earlier step.  The
-- result is intentionally about proof-free vertices, so it is safe to reuse
-- when later comparing source-edge encodings.

mapList-append :
  {A B : Set} (f : A → B) (xs ys : List A) →
  mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
mapList-append f [] ys = refl
mapList-append f (x ∷ xs) ys =
  cong (λ zs → f x ∷ zs) (mapList-append f xs ys)

insertionChildrenNoDuplicates :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)} →
  ParentLinksDescribeInsertionOrder r included links →
  NoDuplicates (mapList ParentLink.child links)
insertionChildrenNoDuplicates root-only = noDup-nil
insertionChildrenNoDuplicates
  (append-child {included = included} {links = links} {child = child}
    history parent∈ child∉ link parent≡ child≡) =
  subst NoDuplicates (sym mapAppend)
    (++-noDup oldChildren (ParentLink.child link ∷ []) oldNoDup
      (noDup-cons (λ ()) noDup-nil) oldDisjoint)
  where
  oldChildren = mapList ParentLink.child links

  oldNoDup : NoDuplicates oldChildren
  oldNoDup = insertionChildrenNoDuplicates history

  mapAppend :
    mapList ParentLink.child (links ++ link ∷ []) ≡
    oldChildren ++ ParentLink.child link ∷ []
  mapAppend = mapList-append ParentLink.child links (link ∷ [])

  oldDisjoint : ∀ {z} → z ∈ oldChildren → z ∉ (ParentLink.child link ∷ [])
  oldDisjoint {z} z∈old z∈new =
    let z≡child = memberSingletonCases z∈new
        source = map-elem ParentLink.child links z∈old
        oldLink = proj₁ source
        childEq = proj₁ (proj₂ source)
        oldLink∈ = proj₂ (proj₂ source)
        oldChildIn : ParentLink.child oldLink ∈ included
        oldChildIn = historyLinkChildInIncluded history oldLink∈
        zEqLinkChild : z ≡ ParentLink.child link
        zEqLinkChild = memberSingletonCases z∈new
        zEqOldChild : z ≡ ParentLink.child oldLink
        zEqOldChild = childEq
        childEqOldChild : child ≡ ParentLink.child oldLink
        childEqOldChild =
          trans (sym child≡) (trans (sym zEqLinkChild) zEqOldChild)
        childIn : child ∈ included
        childIn = subst
          (λ w → w ∈ included)
          (sym childEqOldChild)
          oldChildIn
    in child∉ childIn

------------------------------------------------------------------------
-- Child lists are obtained by filtering the already-certified link list.
-- No decidable adjacency is required: only decidable equality of vertices.
------------------------------------------------------------------------

childrenLinksOf :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)} →
  (u : GC.Graph.Vertex G) →
  List (ParentLink {G = G} X) →
  List (ParentLink {G = G} X)
childrenLinksOf u [] = []
childrenLinksOf {G = G} u (e ∷ es)
  with GC.vertexEqDec {G} (ParentLink.parent e) u
... | yes parent≡ = e ∷ childrenLinksOf u es
... | no parent≢ = childrenLinksOf u es

childrenOf :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  CompleteInsertionParentTree {G = G} r X →
  GC.Graph.Vertex G → List (GC.Graph.Vertex G)
childrenOf T u =
  mapList ParentLink.child
    (childrenLinksOf u (CompleteInsertionParentTree.links T))

childLinkParent :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)} →
  (u : GC.Graph.Vertex G) →
  (es : List (ParentLink {G = G} X)) →
  {e : ParentLink {G = G} X} →
  e ∈ childrenLinksOf u es →
  ParentLink.parent e ≡ u
childLinkParent u [] ()
childLinkParent {G = G} u (e ∷ es) {e′} e′∈
  with GC.vertexEqDec {G} (ParentLink.parent e) u
... | yes parent≡ = yesCase e′∈
  where
  yesCase :
    e′ ∈ (e ∷ childrenLinksOf u es) →
    ParentLink.parent e′ ≡ u
  yesCase here = parent≡
  yesCase (there e′∈) = childLinkParent u es e′∈
... | no parent≢ = childLinkParent u es e′∈

childLinkInOriginal :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)} →
  (u : GC.Graph.Vertex G) →
  (es : List (ParentLink {G = G} X)) →
  {e : ParentLink {G = G} X} →
  e ∈ childrenLinksOf u es → e ∈ es
childLinkInOriginal u [] ()
childLinkInOriginal {G = G} u (e ∷ es) {e′} e′∈
  with GC.vertexEqDec {G} (ParentLink.parent e) u
... | yes parent≡ = yesCase e′∈
  where
  yesCase : e′ ∈ (e ∷ childrenLinksOf u es) → e′ ∈ (e ∷ es)
  yesCase here = here
  yesCase (there e′∈) = there (childLinkInOriginal u es e′∈)
... | no parent≢ = there (childLinkInOriginal u es e′∈)

childForward :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  (T : CompleteInsertionParentTree {G = G} r X) →
  (u v : GC.Graph.Vertex G) →
  v ∈ childrenOf T u → GC.Graph.Adj G u v
childForward {G = G} T u v v∈ with
  GC.map-elem ParentLink.child
    (childrenLinksOf u (CompleteInsertionParentTree.links T)) v∈
... | e , v≡child , e∈children =
  subst
    (λ z → GC.Graph.Adj G u z)
    (sym v≡child)
    (subst
      (λ z → GC.Graph.Adj G z (ParentLink.child e))
      (childLinkParent u (CompleteInsertionParentTree.links T) e∈children)
      (ParentLink.forward e))

childReturn :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  (T : CompleteInsertionParentTree {G = G} r X) →
  (u v : GC.Graph.Vertex G) →
  v ∈ childrenOf T u → GC.Graph.Adj G v u
childReturn {G = G} T u v v∈ with
  GC.map-elem ParentLink.child
    (childrenLinksOf u (CompleteInsertionParentTree.links T)) v∈
... | e , v≡child , e∈children =
  subst
    (λ z → GC.Graph.Adj G z u)
    (sym v≡child)
    (subst
      (λ z → GC.Graph.Adj G (ParentLink.child e) z)
      (childLinkParent u (CompleteInsertionParentTree.links T) e∈children)
      (ParentLink.backward e))

------------------------------------------------------------------------
-- Insertion order is the terminating measure for the forthcoming DFS.
-- Each stored parent is strictly earlier than its child, so following child
-- links strictly decreases the finite suffix remaining after a vertex.
------------------------------------------------------------------------

data AppearsBefore {A : Set} (x y : A) : List A → Set where
  before-head : ∀ {xs} → y ∈ xs → AppearsBefore x y (x ∷ xs)
  before-tail : ∀ {z xs} → AppearsBefore x y xs → AppearsBefore x y (z ∷ xs)

appearsBeforeAppendRight :
  {A : Set} {x y : A} {xs : List A} →
  AppearsBefore x y xs → (suffix : List A) →
  AppearsBefore x y (xs ++ suffix)
appearsBeforeAppendRight (before-head y∈) suffix =
  before-head (memberInAppendLeft _ suffix y∈)
appearsBeforeAppendRight (before-tail earlier) suffix =
  before-tail (appearsBeforeAppendRight earlier suffix)

memberBeforeAppendSingle :
  {A : Set} {x y : A} (xs : List A) →
  x ∈ xs → AppearsBefore x y (xs ++ y ∷ [])
memberBeforeAppendSingle [] ()
memberBeforeAppendSingle (z ∷ xs) here =
  before-head (memberAttachmentInAppend xs [])
memberBeforeAppendSingle (z ∷ xs) (there x∈) =
  before-tail (memberBeforeAppendSingle xs x∈)

appearsBeforeLeftMember :
  {A : Set} {x y : A} {xs : List A} →
  AppearsBefore x y xs → x ∈ xs
appearsBeforeLeftMember (before-head y∈) = here
appearsBeforeLeftMember (before-tail earlier) =
  there (appearsBeforeLeftMember earlier)

appearsBeforeRightMember :
  {A : Set} {x y : A} {xs : List A} →
  AppearsBefore x y xs → y ∈ xs
appearsBeforeRightMember (before-head y∈) = there y∈
appearsBeforeRightMember (before-tail earlier) =
  there (appearsBeforeRightMember earlier)

appearsBeforeEndsAtHeadRequiresTail :
  {A : Set} {x y : A} {xs : List A} →
  AppearsBefore y x (x ∷ xs) → x ∈ xs
appearsBeforeEndsAtHeadRequiresTail (before-head x∈) = x∈
appearsBeforeEndsAtHeadRequiresTail (before-tail earlier) =
  appearsBeforeRightMember earlier

-- Strict insertion order cannot run in both directions inside a
-- duplicate-free carrier.  This is the orientation-cycle exclusion used by
-- the cube-edge collapse: two links cannot select the same geometric edge
-- with opposite parent/child orientations.
appearsBeforeAsymmetric :
  {A : Set} {x y : A} {xs : List A} →
  NoDuplicates xs →
  AppearsBefore x y xs →
  AppearsBefore y x xs → ⊥
appearsBeforeAsymmetric noDup-nil () _
appearsBeforeAsymmetric
  (noDup-cons x∉xs noDup-xs) (before-head y∈) reverse =
  x∉xs (appearsBeforeEndsAtHeadRequiresTail reverse)
appearsBeforeAsymmetric
  (noDup-cons z∉xs noDup-xs) (before-tail earlier) (before-head x∈) =
  z∉xs (appearsBeforeRightMember earlier)
appearsBeforeAsymmetric
  (noDup-cons z∉xs noDup-xs) (before-tail earlier) (before-tail reverse) =
  appearsBeforeAsymmetric noDup-xs earlier reverse

historyParentBeforeChild :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)} →
  ParentLinksDescribeInsertionOrder r included links →
  {e : ParentLink {G = G} X} → e ∈ links →
  AppearsBefore (ParentLink.parent e) (ParentLink.child e) included
historyParentBeforeChild root-only ()
historyParentBeforeChild
  (append-child {included = included} {links = links}
    {parent = p} {child = child}
    history parent∈ child∉ link parent≡ child≡) {e} e∈
  with appendMemberCases e e∈
... | inj₁ e∈old =
  appearsBeforeAppendRight
    (historyParentBeforeChild history e∈old)
    (child ∷ [])
... | inj₂ here =
  subst
    (λ p → AppearsBefore p (ParentLink.child link)
      (included ++ child ∷ []))
    (sym parent≡)
    (subst
      (λ c → AppearsBefore p c (included ++ child ∷ []))
      (sym child≡)
      (memberBeforeAppendSingle included parent∈))

------------------------------------------------------------------------
-- Reify insertion history as eliminable tree data.  A parent occurrence is
-- carried explicitly while inserting, so this construction never needs a
-- separate parent map or well-founded child recursion.
------------------------------------------------------------------------

data TreeContains
  {G : GC.Graph} :
  {u : GC.Graph.Vertex G} →
  RootedTreeNode G u → GC.Graph.Vertex G → Set₁ where
  at-leaf :
    {u : GC.Graph.Vertex G} →
    TreeContains (CDFS.leaf u) u
  at-branch :
    {u : GC.Graph.Vertex G}
    {children : List (RootedTreeChild G u)} →
    TreeContains (CDFS.branch u children) u
  in-child :
    {u : GC.Graph.Vertex G}
    {children : List (RootedTreeChild G u)}
    {entry : RootedTreeChild G u}
    {x : GC.Graph.Vertex G} →
    entry ∈₁ children →
    TreeContains (CDFS.subtree entry) x →
    TreeContains (CDFS.branch u children) x

data ForestContains
  {G : GC.Graph} {u : GC.Graph.Vertex G}
  (children : List (RootedTreeChild G u))
  (x : GC.Graph.Vertex G) : Set₁ where
  in-forest :
    {entry : RootedTreeChild G u} →
    entry ∈₁ children →
    TreeContains (CDFS.subtree entry) x →
    ForestContains children x

mutual

  treeContainsToFlattenMember :
    {G : GC.Graph} {u x : GC.Graph.Vertex G}
    {T : RootedTreeNode G u} →
    TreeContains T x → x ∈ flattenTree T
  treeContainsToFlattenMember at-leaf = here
  treeContainsToFlattenMember at-branch = here
  treeContainsToFlattenMember (in-child {children = children} {entry = entry}
    entry∈ x∈) =
    there (forestContainsToFlattenMember children (in-forest entry∈ x∈))

  forestContainsToFlattenMember :
    {G : GC.Graph} {u x : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    ForestContains children x →
    x ∈ flattenForest children
  forestContainsToFlattenMember [] (in-forest () x∈tree)
  forestContainsToFlattenMember (entry ∷ children)
    (in-forest here₁ x∈tree) =
    memberInAppendLeft (flattenTree (CDFS.subtree entry))
      (flattenForest children) (treeContainsToFlattenMember x∈tree)
  forestContainsToFlattenMember (entry ∷ children)
    (in-forest (there₁ entry∈) x∈tree) =
    memberInPlainAppendRight (flattenTree (subtree entry))
      (flattenForest children)
      (forestContainsToFlattenMember children (in-forest entry∈ x∈tree))

mutual

  treeContainsFromFlattenMember :
    {G : GC.Graph} {u x : GC.Graph.Vertex G} →
    (T : RootedTreeNode G u) → x ∈ flattenTree T → TreeContains T x
  treeContainsFromFlattenMember (CDFS.leaf u) here = at-leaf
  treeContainsFromFlattenMember (CDFS.branch u children) here = at-branch
  treeContainsFromFlattenMember (CDFS.branch u children) (there x∈forest) =
    forestToTreeContains (forestContainsFromFlattenMember children x∈forest)

  forestToTreeContains :
    {G : GC.Graph} {u x : GC.Graph.Vertex G}
    {children : List (RootedTreeChild G u)} →
    ForestContains children x → TreeContains (CDFS.branch u children) x
  forestToTreeContains (in-forest entry∈ x∈) = in-child entry∈ x∈

  forestContainsFromFlattenMember :
    {G : GC.Graph} {u x : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    x ∈ flattenForest children →
    ForestContains children x
  forestContainsFromFlattenMember [] ()
  forestContainsFromFlattenMember {x = x} (entry ∷ children) x∈forest
    with appendMemberCases x x∈forest
  ... | inj₁ x∈entry =
    in-forest here₁
      (treeContainsFromFlattenMember (CDFS.subtree entry) x∈entry)
  ... | inj₂ x∈children
    with forestContainsFromFlattenMember children x∈children
  ... | in-forest entry∈ x∈subtree =
    in-forest (there₁ entry∈) x∈subtree

freshLeafChild :
  {G : GC.Graph} {u v : GC.Graph.Vertex G} →
  GC.Graph.Adj G u v → GC.Graph.Adj G v u →
  RootedTreeChild G u
freshLeafChild {v = v} fwd back = record
  { root = v
  ; forward = fwd
  ; backward = back
  ; subtree = CDFS.leaf v
  }

mutual

  insertFreshLeafUnder :
    {G : GC.Graph} {u parent child : GC.Graph.Vertex G} →
    (T : RootedTreeNode G u) →
    TreeContains T parent →
    GC.Graph.Adj G parent child →
    GC.Graph.Adj G child parent →
    RootedTreeNode G u
  insertFreshLeafUnder (CDFS.leaf u) at-leaf fwd back =
    CDFS.branch u (freshLeafChild fwd back ∷ [])
  insertFreshLeafUnder (CDFS.branch u children) at-branch fwd back =
    CDFS.branch u (freshLeafChild fwd back ∷ children)
  insertFreshLeafUnder (CDFS.branch u children)
    (in-child {entry = entry} entry∈ parent∈) fwd back =
    CDFS.branch u (insertFreshLeafInForest children entry∈ parent∈ fwd back)

  insertFreshLeafInForest :
    {G : GC.Graph} {u parent child : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    {entry : RootedTreeChild G u} →
    entry ∈₁ children →
    TreeContains (CDFS.subtree entry) parent →
    GC.Graph.Adj G parent child →
    GC.Graph.Adj G child parent →
    List (RootedTreeChild G u)
  insertFreshLeafInForest [] () parent∈ fwd back
  insertFreshLeafInForest (entry ∷ children) here₁ parent∈ fwd back =
    record
      { root = root entry
      ; forward = forward entry
      ; backward = backward entry
      ; subtree = insertFreshLeafUnder (subtree entry) parent∈ fwd back
      }
    ∷ children
  insertFreshLeafInForest (entry ∷ children) (there₁ entry∈)
    parent∈ fwd back =
    entry ∷ insertFreshLeafInForest children entry∈ parent∈ fwd back

mutual

  insertFreshLeafContainsChild :
    {G : GC.Graph} {u parent child : GC.Graph.Vertex G} →
    (T : RootedTreeNode G u) →
    (parent∈ : TreeContains T parent) →
    (fwd : GC.Graph.Adj G parent child) →
    (back : GC.Graph.Adj G child parent) →
    TreeContains (insertFreshLeafUnder T parent∈ fwd back) child
  insertFreshLeafContainsChild (CDFS.leaf u) at-leaf fwd back =
    in-child here₁ at-leaf
  insertFreshLeafContainsChild (CDFS.branch u children) at-branch fwd back =
    in-child here₁ at-leaf
  insertFreshLeafContainsChild (CDFS.branch u children)
    (in-child {entry = entry} entry∈ parent∈) fwd back =
    forestToTreeContains
      (forestInsertContainsChild children entry∈ parent∈ fwd back)

  forestInsertContainsChild :
    {G : GC.Graph} {u parent child : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    {entry : RootedTreeChild G u} →
    (entry∈ : entry ∈₁ children) →
    (parent∈ : TreeContains (subtree entry) parent) →
    (fwd : GC.Graph.Adj G parent child) →
    (back : GC.Graph.Adj G child parent) →
    ForestContains
      (insertFreshLeafInForest children entry∈ parent∈ fwd back)
      child
  forestInsertContainsChild [] () parent∈ fwd back
  forestInsertContainsChild (entry ∷ children) here₁ parent∈ fwd back =
    in-forest here₁
      (insertFreshLeafContainsChild (subtree entry) parent∈ fwd back)
  forestInsertContainsChild (entry ∷ children) (there₁ entry∈)
    parent∈ fwd back =
    let childInTail = forestInsertContainsChild children entry∈ parent∈ fwd back
    in forestShiftRight entry childInTail

  forestShiftRight :
    {G : GC.Graph} {u child : GC.Graph.Vertex G}
    (entry : RootedTreeChild G u) {children : List (RootedTreeChild G u)} →
    ForestContains children child → ForestContains (entry ∷ children) child
  forestShiftRight entry (in-forest entry∈ child∈) =
    in-forest (there₁ entry∈) child∈

------------------------------------------------------------------------
-- Insertion preserves every pre-existing tree member.  This is kept at
-- the `TreeContains` level, rather than by comparing dependent child
-- entries for equality: the latter would unnecessarily expose proof
-- fields of `RootedTreeChild`.
------------------------------------------------------------------------

mutual

  insertFreshLeafPreservesContains :
    {G : GC.Graph} {u parent child x : GC.Graph.Vertex G} →
    (T : RootedTreeNode G u) →
    (parent∈ : TreeContains T parent) →
    (fwd : GC.Graph.Adj G parent child) →
    (back : GC.Graph.Adj G child parent) →
    TreeContains T x →
    TreeContains (insertFreshLeafUnder T parent∈ fwd back) x
  insertFreshLeafPreservesContains (CDFS.leaf u) at-leaf fwd back at-leaf =
    at-branch
  insertFreshLeafPreservesContains (CDFS.branch u children) at-branch fwd back
    at-branch = at-branch
  insertFreshLeafPreservesContains (CDFS.branch u children) at-branch fwd back
    (in-child entry∈ x∈) =
    forestToTreeContains
      (forestContainsShiftRight (freshLeafChild fwd back)
        (in-forest entry∈ x∈))
  insertFreshLeafPreservesContains (CDFS.branch u children)
    (in-child {entry = entry} entry∈ parent∈) fwd back at-branch =
    at-branch
  insertFreshLeafPreservesContains (CDFS.branch u children)
    (in-child {entry = entry} entry∈ parent∈) fwd back
    (in-child oldEntry∈ x∈) =
    forestToTreeContains
      (forestInsertPreservesContains children entry∈ parent∈ fwd back
        (in-forest oldEntry∈ x∈))

  forestContainsShiftRight :
    {G : GC.Graph} {u x : GC.Graph.Vertex G} →
    (entry : RootedTreeChild G u) →
    {children : List (RootedTreeChild G u)} →
    ForestContains children x → ForestContains (entry ∷ children) x
  forestContainsShiftRight entry (in-forest entry∈ x∈) =
    in-forest (there₁ entry∈) x∈

  forestInsertPreservesContains :
    {G : GC.Graph} {u parent child x : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    {entry : RootedTreeChild G u} →
    (entry∈ : entry ∈₁ children) →
    (parent∈ : TreeContains (subtree entry) parent) →
    (fwd : GC.Graph.Adj G parent child) →
    (back : GC.Graph.Adj G child parent) →
    ForestContains children x →
    ForestContains
      (insertFreshLeafInForest children entry∈ parent∈ fwd back) x
  forestInsertPreservesContains [] () parent∈ fwd back old∈
  forestInsertPreservesContains (entry ∷ children) here₁ parent∈ fwd back
    (in-forest here₁ x∈) =
    in-forest here₁
      (insertFreshLeafPreservesContains (subtree entry) parent∈ fwd back x∈)
  forestInsertPreservesContains (entry ∷ children) here₁ parent∈ fwd back
    (in-forest (there₁ oldEntry∈) x∈) =
    forestContainsShiftRight
      (record
        { root = root entry
        ; forward = forward entry
        ; backward = backward entry
        ; subtree = insertFreshLeafUnder (subtree entry) parent∈ fwd back
        })
      (in-forest oldEntry∈ x∈)
  forestInsertPreservesContains (entry ∷ children) (there₁ entry∈)
    parent∈ fwd back (in-forest here₁ x∈) =
    in-forest here₁ x∈
  forestInsertPreservesContains (entry ∷ children) (there₁ entry∈)
    parent∈ fwd back (in-forest (there₁ oldEntry∈) x∈) =
    forestContainsShiftRight entry
      (forestInsertPreservesContains children entry∈ parent∈ fwd back
        (in-forest oldEntry∈ x∈))

insertFreshLeafPreservesFlattenMember :
  {G : GC.Graph} {u parent child x : GC.Graph.Vertex G} →
  (T : RootedTreeNode G u) →
  (parent∈ : TreeContains T parent) →
  (fwd : GC.Graph.Adj G parent child) →
  (back : GC.Graph.Adj G child parent) →
  x ∈ flattenTree T →
  x ∈ flattenTree (insertFreshLeafUnder T parent∈ fwd back)
insertFreshLeafPreservesFlattenMember T parent∈ fwd back x∈ =
  treeContainsToFlattenMember
    (insertFreshLeafPreservesContains T parent∈ fwd back
      (treeContainsFromFlattenMember T x∈))

------------------------------------------------------------------------
-- Conversely, insertion has exactly one possible new member.  The
-- statement is intentionally a disjunction rather than equality of the
-- dependent child lists: it is the range fact required by history
-- reification and keeps all edge-proof fields opaque.
------------------------------------------------------------------------

mutual

  insertFreshLeafContainsCases :
    {G : GC.Graph} {u parent child x : GC.Graph.Vertex G} →
    (T : RootedTreeNode G u) →
    (parent∈ : TreeContains T parent) →
    (fwd : GC.Graph.Adj G parent child) →
    (back : GC.Graph.Adj G child parent) →
    TreeContains (insertFreshLeafUnder T parent∈ fwd back) x →
    TreeContains T x ⊎ x ≡ child
  insertFreshLeafContainsCases (CDFS.leaf u) at-leaf fwd back at-branch =
    inj₁ at-leaf
  insertFreshLeafContainsCases (CDFS.leaf u) at-leaf fwd back
    (in-child here₁ at-leaf) = inj₂ refl
  insertFreshLeafContainsCases (CDFS.leaf u) at-leaf fwd back
    (in-child (there₁ ()) x∈)
  insertFreshLeafContainsCases (CDFS.branch u children) at-branch fwd back
    at-branch = inj₁ at-branch
  insertFreshLeafContainsCases (CDFS.branch u children) at-branch fwd back
    (in-child here₁ at-leaf) = inj₂ refl
  insertFreshLeafContainsCases (CDFS.branch u children) at-branch fwd back
    (in-child (there₁ entry∈) x∈) =
    inj₁ (in-child entry∈ x∈)
  insertFreshLeafContainsCases (CDFS.branch u children)
    (in-child {entry = entry} entry∈ parent∈) fwd back at-branch =
    inj₁ at-branch
  insertFreshLeafContainsCases {child = c} (CDFS.branch u children)
    (in-child {entry = entry} entry∈ parent∈) fwd back
    (in-child {x = x} updatedEntry∈ x∈) =
    liftForestCases
      (forestInsertContainsCases children entry∈ parent∈ fwd back
        (in-forest updatedEntry∈ x∈))
    where
    liftForestCases :
      ForestContains children x ⊎ x ≡ c →
      TreeContains (CDFS.branch u children) x ⊎ x ≡ c
    liftForestCases (inj₁ old∈) = inj₁ (forestToTreeContains old∈)
    liftForestCases (inj₂ x≡) = inj₂ x≡

  forestInsertContainsCases :
    {G : GC.Graph} {u parent child x : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    {entry : RootedTreeChild G u} →
    (entry∈ : entry ∈₁ children) →
    (parent∈ : TreeContains (subtree entry) parent) →
    (fwd : GC.Graph.Adj G parent child) →
    (back : GC.Graph.Adj G child parent) →
    ForestContains
      (insertFreshLeafInForest children entry∈ parent∈ fwd back) x →
    ForestContains children x ⊎ x ≡ child
  forestInsertContainsCases [] () parent∈ fwd back x∈
  forestInsertContainsCases (entry ∷ children) here₁ parent∈ fwd back
    (in-forest here₁ x∈) with
      insertFreshLeafContainsCases (subtree entry) parent∈ fwd back x∈
  ... | inj₁ old∈ = inj₁ (in-forest here₁ old∈)
  ... | inj₂ x≡ = inj₂ x≡
  forestInsertContainsCases (entry ∷ children) here₁ parent∈ fwd back
    (in-forest (there₁ updatedEntry∈) x∈) =
    inj₁ (in-forest (there₁ updatedEntry∈) x∈)
  forestInsertContainsCases (entry ∷ children) (there₁ entry∈)
    parent∈ fwd back (in-forest here₁ x∈) =
    inj₁ (in-forest here₁ x∈)
  forestInsertContainsCases (entry ∷ children) (there₁ entry∈)
    parent∈ fwd back (in-forest (there₁ updatedEntry∈) x∈) with
      forestInsertContainsCases children entry∈ parent∈ fwd back
        (in-forest updatedEntry∈ x∈)
  ... | inj₁ old∈ = inj₁ (forestContainsShiftRight entry old∈)
  ... | inj₂ x≡ = inj₂ x≡

insertFreshLeafFlattenCases :
  {G : GC.Graph} {u parent child x : GC.Graph.Vertex G} →
  (T : RootedTreeNode G u) →
  (parent∈ : TreeContains T parent) →
  (fwd : GC.Graph.Adj G parent child) →
  (back : GC.Graph.Adj G child parent) →
  x ∈ flattenTree (insertFreshLeafUnder T parent∈ fwd back) →
  x ∈ flattenTree T ⊎ x ≡ child
insertFreshLeafFlattenCases T parent∈ fwd back x∈ with
  insertFreshLeafContainsCases T parent∈ fwd back
    (treeContainsFromFlattenMember
      (insertFreshLeafUnder T parent∈ fwd back) x∈)
... | inj₁ old∈ = inj₁ (treeContainsToFlattenMember old∈)
... | inj₂ x≡ = inj₂ x≡

insertFreshLeafFlattenRange :
  {G : GC.Graph} {u parent child : GC.Graph.Vertex G} →
  (T : RootedTreeNode G u) →
  (parent∈ : TreeContains T parent) →
  (fwd : GC.Graph.Adj G parent child) →
  (back : GC.Graph.Adj G child parent) →
  SameVertexSet
    (flattenTree (insertFreshLeafUnder T parent∈ fwd back))
    (flattenTree T ++ child ∷ [])
insertFreshLeafFlattenRange {child = c} T parent∈ fwd back =
  updated⊆old-plus-child , old-plus-child⊆updated
  where
  updated⊆old-plus-child :
    ∀ {x} →
    x ∈ flattenTree (insertFreshLeafUnder T parent∈ fwd back) →
    x ∈ (flattenTree T ++ c ∷ [])
  updated⊆old-plus-child {x} x∈ with
    insertFreshLeafFlattenCases T parent∈ fwd back x∈
  ... | inj₁ old∈ = memberInAppendLeft (flattenTree T) (c ∷ []) old∈
  ... | inj₂ x≡ =
    subst (λ z → z ∈ (flattenTree T ++ c ∷ [])) (sym x≡)
      (memberAttachmentInAppend (flattenTree T) [])

  old-plus-child⊆updated :
    ∀ {x} →
    x ∈ (flattenTree T ++ c ∷ []) →
    x ∈ flattenTree (insertFreshLeafUnder T parent∈ fwd back)
  old-plus-child⊆updated {x} x∈ with appendMemberCases x x∈
  ... | inj₁ old∈ =
    insertFreshLeafPreservesFlattenMember T parent∈ fwd back old∈
  ... | inj₂ child∈ =
    subst
      (λ z → z ∈ flattenTree (insertFreshLeafUnder T parent∈ fwd back))
      (sym (memberSingletonCases child∈))
      (treeContainsToFlattenMember
        (insertFreshLeafContainsChild T parent∈ fwd back))

------------------------------------------------------------------------
-- Duplicate-freeness is preserved structurally.  The range theorem above
-- controls the one new vertex, but cannot by itself rule out repetition;
-- the mutually recursive proof below follows the actual updated subtree.
------------------------------------------------------------------------

noDupAppendPrefix :
  {A : Set} (xs ys : List A) →
  NoDuplicates (xs ++ ys) → NoDuplicates xs
noDupAppendPrefix [] ys noDup = GC.noDup-nil
noDupAppendPrefix (x ∷ xs) ys (GC.noDup-cons x∉rest noDup-rest) =
  GC.noDup-cons x∉xs
    (noDupAppendPrefix xs ys noDup-rest)
  where
  x∉xs : x ∉ xs
  x∉xs x∈xs =
    x∉rest (memberInAppendLeft xs ys x∈xs)

noDupAppendDisjoint :
  {A : Set} {xs ys : List A} →
  NoDuplicates (xs ++ ys) →
  ∀ {x} → x ∈ xs → x ∉ ys
noDupAppendDisjoint {xs = []} noDup ()
noDupAppendDisjoint {xs = x ∷ xs} {ys = ys}
  (GC.noDup-cons x∉rest noDup-rest) here y∈ =
  x∉rest (memberInPlainAppendRight xs ys y∈)
noDupAppendDisjoint {xs = x ∷ xs} {ys = ys}
  (GC.noDup-cons x∉rest noDup-rest) (there x∈) y∈ =
  noDupAppendDisjoint noDup-rest x∈ y∈

mutual

  forestInsertFreshLeafFlattenCases :
    {G : GC.Graph} {u parent child x : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    {entry : RootedTreeChild G u} →
    (entry∈ : entry ∈₁ children) →
    (parent∈ : TreeContains (subtree entry) parent) →
    (fwd : GC.Graph.Adj G parent child) →
    (back : GC.Graph.Adj G child parent) →
    x ∈ flattenForest (insertFreshLeafInForest children entry∈ parent∈ fwd back) →
    x ∈ flattenForest children ⊎ x ≡ child
  forestInsertFreshLeafFlattenCases children entry∈ parent∈ fwd back x∈ with
    forestInsertContainsCases children entry∈ parent∈ fwd back
      (forestContainsFromFlattenMember
        (insertFreshLeafInForest children entry∈ parent∈ fwd back) x∈)
  ... | inj₁ old∈ = inj₁ (forestContainsToFlattenMember children old∈)
  ... | inj₂ x≡ = inj₂ x≡

  insertFreshLeafNoDuplicates :
    {G : GC.Graph} {u parent child : GC.Graph.Vertex G} →
    (T : RootedTreeNode G u) →
    (parent∈ : TreeContains T parent) →
    (fwd : GC.Graph.Adj G parent child) →
    (back : GC.Graph.Adj G child parent) →
    child ∉ flattenTree T →
    NoDuplicates (flattenTree T) →
    NoDuplicates (flattenTree (insertFreshLeafUnder T parent∈ fwd back))
  insertFreshLeafNoDuplicates {child = c} (CDFS.leaf u) at-leaf fwd back childFresh
    (GC.noDup-cons u∉[] GC.noDup-nil) =
    GC.noDup-cons u∉child
      (GC.noDup-cons (λ ()) GC.noDup-nil)
    where
    u∉child : u ∉ (c ∷ [])
    u∉child here = childFresh here
    u∉child (there ())
  insertFreshLeafNoDuplicates {child = c} (CDFS.branch u children) at-branch fwd back
    childFresh (GC.noDup-cons u∉forest noDupForest) =
    GC.noDup-cons u∉newForest
      (GC.noDup-cons child∉oldForest noDupForest)
    where
    child∉oldForest : c ∉ flattenForest children
    child∉oldForest child∈ = childFresh (there child∈)

    u∉child : u ∉ (c ∷ [])
    u∉child here = childFresh here
    u∉child (there ())

    u∉newForest : u ∉ (c ∷ flattenForest children)
    u∉newForest here = u∉child here
    u∉newForest (there u∈forest) = u∉forest u∈forest
  insertFreshLeafNoDuplicates {child = c} (CDFS.branch u children)
    (in-child {entry = entry} entry∈ parent∈) fwd back childFresh
    (GC.noDup-cons u∉forest noDupForest) =
    GC.noDup-cons u∉updatedForest updatedForestNoDup
    where
    updatedForest =
      insertFreshLeafInForest children entry∈ parent∈ fwd back

    child∉forest : c ∉ flattenForest children
    child∉forest child∈ = childFresh (there child∈)

    updatedForestNoDup : NoDuplicates (flattenForest updatedForest)
    updatedForestNoDup =
      forestInsertFreshLeafNoDuplicates children entry∈ parent∈ fwd back
        child∉forest noDupForest

    u∉updatedForest : u ∉ flattenForest updatedForest
    u∉updatedForest u∈ with
      forestInsertFreshLeafFlattenCases children entry∈ parent∈ fwd back u∈
    ... | inj₁ old∈ = u∉forest old∈
    ... | inj₂ u≡ =
      childFresh (subst (λ z → z ∈ (u ∷ flattenForest children)) u≡ here)

  forestInsertFreshLeafNoDuplicates :
    {G : GC.Graph} {u parent child : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    {entry : RootedTreeChild G u} →
    (entry∈ : entry ∈₁ children) →
    (parent∈ : TreeContains (subtree entry) parent) →
    (fwd : GC.Graph.Adj G parent child) →
    (back : GC.Graph.Adj G child parent) →
    child ∉ flattenForest children →
    NoDuplicates (flattenForest children) →
    NoDuplicates
      (flattenForest (insertFreshLeafInForest children entry∈ parent∈ fwd back))
  forestInsertFreshLeafNoDuplicates [] () parent∈ fwd back childFresh noDup
  forestInsertFreshLeafNoDuplicates {child = c} (entry ∷ children) here₁ parent∈ fwd back
    childFresh noDup =
    GC.++-noDup updatedPrefix (flattenForest children)
      updatedPrefixNoDup tailNoDup updatedPrefixDisjoint
    where
    oldPrefix = flattenTree (subtree entry)
    oldForest = oldPrefix ++ flattenForest children
    updatedPrefix =
      flattenTree (insertFreshLeafUnder (subtree entry) parent∈ fwd back)

    oldPrefixNoDup : NoDuplicates oldPrefix
    oldPrefixNoDup = noDupAppendPrefix oldPrefix (flattenForest children) noDup

    tailNoDup : NoDuplicates (flattenForest children)
    tailNoDup = dropPrefixNoDuplicates oldPrefix (flattenForest children) noDup

    childFreshPrefix : c ∉ oldPrefix
    childFreshPrefix child∈ =
      childFresh (memberInAppendLeft oldPrefix (flattenForest children) child∈)

    updatedPrefixNoDup : NoDuplicates updatedPrefix
    updatedPrefixNoDup =
      insertFreshLeafNoDuplicates (subtree entry) parent∈ fwd back
        childFreshPrefix oldPrefixNoDup

    updatedPrefixDisjoint :
      ∀ {x} → x ∈ updatedPrefix → x ∉ flattenForest children
    updatedPrefixDisjoint {x} x∈ with
      insertFreshLeafFlattenCases (subtree entry) parent∈ fwd back x∈
    ... | inj₁ old∈ = noDupAppendDisjoint noDup old∈
    ... | inj₂ x≡ =
      subst (λ z → z ∉ flattenForest children) (sym x≡)
        (λ child∈ →
          childFresh
            (memberInPlainAppendRight oldPrefix (flattenForest children) child∈))
  forestInsertFreshLeafNoDuplicates {child = c} (entry ∷ children) (there₁ entry∈)
    parent∈ fwd back childFresh noDup =
    GC.++-noDup oldPrefix updatedTail
      oldPrefixNoDup updatedTailNoDup oldPrefixDisjoint
    where
    oldPrefix = flattenTree (subtree entry)
    oldTail = flattenForest children
    updatedTail =
      flattenForest (insertFreshLeafInForest children entry∈ parent∈ fwd back)

    oldPrefixNoDup : NoDuplicates oldPrefix
    oldPrefixNoDup = noDupAppendPrefix oldPrefix oldTail noDup

    oldTailNoDup : NoDuplicates oldTail
    oldTailNoDup = dropPrefixNoDuplicates oldPrefix oldTail noDup

    childFreshTail : c ∉ oldTail
    childFreshTail child∈ =
      childFresh (memberInPlainAppendRight oldPrefix oldTail child∈)

    updatedTailNoDup : NoDuplicates updatedTail
    updatedTailNoDup =
      forestInsertFreshLeafNoDuplicates children entry∈ parent∈ fwd back
        childFreshTail oldTailNoDup

    oldPrefixDisjoint : ∀ {x} → x ∈ oldPrefix → x ∉ updatedTail
    oldPrefixDisjoint {x} x∈prefix x∈tail with
      forestInsertFreshLeafFlattenCases children entry∈ parent∈ fwd back x∈tail
    ... | inj₁ x∈oldTail = noDupAppendDisjoint noDup x∈prefix x∈oldTail
    ... | inj₂ x≡ =
      childFresh
        (subst (λ z → z ∈ (oldPrefix ++ oldTail)) x≡
          (memberInAppendLeft oldPrefix oldTail x∈prefix))

------------------------------------------------------------------------
-- Reification of insertion history, first at the exact range level.  The
-- flattening no-duplicates invariant is deliberately kept separate below:
-- it is a structural strengthening, while range and witnessed membership
-- are already enough to remove the abstract/history-versus-tree gap.
------------------------------------------------------------------------

sameVertexSetAppendSingle :
  {A : Set} {xs ys : List A} {a : A} →
  SameVertexSet xs ys →
  SameVertexSet (xs ++ a ∷ []) (ys ++ a ∷ [])
sameVertexSetAppendSingle {xs = xs} {ys = ys} {a = a} (xs⊆ys , ys⊆xs) =
  left-to-right , right-to-left
  where
  left-to-right : ∀ {x} → x ∈ (xs ++ a ∷ []) → x ∈ (ys ++ a ∷ [])
  left-to-right {x} x∈ with appendMemberCases x x∈
  ... | inj₁ x∈xs = memberInAppendLeft ys (a ∷ []) (xs⊆ys x∈xs)
  ... | inj₂ x∈a =
    subst (λ z → z ∈ (ys ++ a ∷ [])) (sym (memberSingletonCases x∈a))
      (memberAttachmentInAppend ys [])

  right-to-left : ∀ {x} → x ∈ (ys ++ a ∷ []) → x ∈ (xs ++ a ∷ [])
  right-to-left {x} x∈ with appendMemberCases x x∈
  ... | inj₁ x∈ys = memberInAppendLeft xs (a ∷ []) (ys⊆xs x∈ys)
  ... | inj₂ x∈a =
    subst (λ z → z ∈ (xs ++ a ∷ [])) (sym (memberSingletonCases x∈a))
      (memberAttachmentInAppend xs [])

sameVertexSet-trans :
  {A : Set} {xs ys zs : List A} →
  SameVertexSet xs ys → SameVertexSet ys zs → SameVertexSet xs zs
sameVertexSet-trans (xs⊆ys , ys⊆xs) (ys⊆zs , zs⊆ys) =
  (λ x∈ → ys⊆zs (xs⊆ys x∈)) ,
  (λ x∈ → ys⊆xs (zs⊆ys x∈))

record TreeRangeRealisesInsertionHistory
  {G : GC.Graph}
  {X : List (GC.Graph.Vertex G)}
  (r : GC.Graph.Vertex G)
  (included : List (GC.Graph.Vertex G))
  (links : List (ParentLink {G = G} X)) : Set₁ where
  field
    tree : RootedTreeNode G r
    rangeExact : SameVertexSet (flattenTree tree) included
    includedPresent : ∀ {v} → v ∈ included → TreeContains tree v

open TreeRangeRealisesInsertionHistory public

insertionHistoryToTreeRange :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)} →
  ParentLinksDescribeInsertionOrder r included links →
  TreeRangeRealisesInsertionHistory r included links
insertionHistoryToTreeRange root-only = record
  { tree = CDFS.leaf _
  ; rangeExact = (λ x∈ → x∈) , (λ x∈ → x∈)
  ; includedPresent = λ { here → at-leaf }
  }
insertionHistoryToTreeRange {G = G} {X = X} {r = r}
  (append-child {included = included} {links = links}
    {parent = parent} {child = child}
    history parent∈ child∉ link parent≡ child≡) =
  record
    { tree = newTree
    ; rangeExact = newRange
    ; includedPresent = newPresent
    }
  where
  previous : TreeRangeRealisesInsertionHistory {G = G} {X = X} r included links
  previous = insertionHistoryToTreeRange history

  oldTree : RootedTreeNode G r
  oldTree = tree previous

  linkForward : GC.Graph.Adj G parent child
  linkForward =
    subst (λ q → GC.Graph.Adj G parent q) child≡
      (subst (λ p → GC.Graph.Adj G p (ParentLink.child link)) parent≡
        (ParentLink.forward link))

  linkBackward : GC.Graph.Adj G child parent
  linkBackward =
    subst (λ p → GC.Graph.Adj G child p) parent≡
      (subst (λ q → GC.Graph.Adj G q (ParentLink.parent link)) child≡
        (ParentLink.backward link))

  parentInOldTree : TreeContains oldTree parent
  parentInOldTree =
    treeContainsFromFlattenMember oldTree
      (proj₂ (rangeExact previous) parent∈)

  childFreshInOldTree : child ∉ flattenTree oldTree
  childFreshInOldTree childInOld =
    child∉ (proj₁ (rangeExact previous) childInOld)

  newTree : RootedTreeNode G r
  newTree =
    insertFreshLeafUnder oldTree parentInOldTree linkForward linkBackward

  newRange : SameVertexSet (flattenTree newTree) (included ++ child ∷ [])
  newRange =
    sameVertexSet-trans
      (insertFreshLeafFlattenRange oldTree parentInOldTree
        linkForward linkBackward)
      (sameVertexSetAppendSingle (rangeExact previous))

  newPresent : ∀ {v} → v ∈ (included ++ child ∷ []) → TreeContains newTree v
  newPresent {v} v∈ with appendMemberCases v v∈
  ... | inj₁ old∈ =
    insertFreshLeafPreservesContains oldTree parentInOldTree
      linkForward linkBackward
      (includedPresent previous old∈)
  ... | inj₂ new∈ =
    subst (λ z → TreeContains newTree z)
      (sym (memberSingletonCases new∈))
      (insertFreshLeafContainsChild oldTree parentInOldTree
        linkForward linkBackward)

------------------------------------------------------------------------
-- The range reification above is strengthened here with the structural
-- no-duplicates invariant.  Keeping the two records separate makes the
-- extensional range theorem reusable while ensuring this stronger result is
-- obtained only from the actual leaf-insertion construction.
------------------------------------------------------------------------

{-
-- Structural edge preservation for fresh-leaf insertion.  This is expressed
-- in the proof-relevant tree-edge relation from the DFS module, rather than
-- as equality of dependent child records.

childOccursFromMember :
  {G : GC.Graph} {u : GC.Graph.Vertex G}
  {child : RootedTreeChild G u} {children : List (RootedTreeChild G u)} →
  child ∈₁ children → CDFS.ChildOccurs child children
childOccursFromMember here₁ = CDFS.child-here
childOccursFromMember (there₁ child∈) =
  CDFS.child-there (childOccursFromMember child∈)

mutual

  insertFreshLeafIntroducesTreeEdge :
    {G : GC.Graph} {u parent fresh : GC.Graph.Vertex G} →
    (T : RootedTreeNode G u) →
    (parent∈ : TreeContains T parent) →
    (fwd : GC.Graph.Adj G parent fresh) →
    (back : GC.Graph.Adj G fresh parent) →
    CDFS.TreeEdgeOccurs
      {tree = insertFreshLeafUnder T parent∈ fwd back}
      parent fresh
  insertFreshLeafIntroducesTreeEdge (CDFS.leaf u) at-leaf fwd back =
    CDFS.direct-tree-edge CDFS.child-here
  insertFreshLeafIntroducesTreeEdge (CDFS.branch u children) at-branch fwd back =
    CDFS.direct-tree-edge CDFS.child-here
  insertFreshLeafIntroducesTreeEdge (CDFS.branch u children)
    (in-child {entry = entry} entry∈ parent∈) fwd back =
    insertFreshLeafInForestIntroducesTreeEdge
      children entry∈ parent∈ fwd back

  insertFreshLeafInForestIntroducesTreeEdge :
    {G : GC.Graph} {u parent fresh : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    {entry : RootedTreeChild G u} →
    (entry∈ : entry ∈₁ children) →
    (parent∈ : TreeContains (subtree entry) parent) →
    (fwd : GC.Graph.Adj G parent fresh) →
    (back : GC.Graph.Adj G fresh parent) →
    CDFS.TreeEdgeOccurs
      {tree = CDFS.branch u
        (insertFreshLeafInForest children entry∈ parent∈ fwd back)}
      parent fresh
  insertFreshLeafInForestIntroducesTreeEdge (entry ∷ children) here₁
    parent∈ fwd back =
    CDFS.below-tree-edge CDFS.child-here
      (insertFreshLeafIntroducesTreeEdge
        (subtree entry) parent∈ fwd back)
  insertFreshLeafInForestIntroducesTreeEdge (head ∷ children) (there₁ entry∈)
    parent∈ fwd back =
    CDFS.below-tree-edge CDFS.child-there
      (insertFreshLeafInForestIntroducesTreeEdge
        children entry∈ parent∈ fwd back)

  insertFreshLeafPreservesTreeEdge :
    {G : GC.Graph} {u parent fresh p q : GC.Graph.Vertex G} →
    (T : RootedTreeNode G u) →
    (parent∈ : TreeContains T parent) →
    (fwd : GC.Graph.Adj G parent fresh) →
    (back : GC.Graph.Adj G fresh parent) →
    CDFS.TreeEdgeOccurs {tree = T} p q →
    CDFS.TreeEdgeOccurs
      {tree = insertFreshLeafUnder T parent∈ fwd back} p q
  insertFreshLeafPreservesTreeEdge (CDFS.leaf u) at-leaf fwd back ()
  insertFreshLeafPreservesTreeEdge (CDFS.branch u children) at-branch fwd back
    (CDFS.direct-tree-edge child∈) =
    CDFS.direct-tree-edge (CDFS.child-there child∈)
  insertFreshLeafPreservesTreeEdge (CDFS.branch u children) at-branch fwd back
    (CDFS.below-tree-edge child∈ edge∈) =
    CDFS.below-tree-edge (CDFS.child-there child∈) edge∈
  insertFreshLeafPreservesTreeEdge (CDFS.branch u children)
    (in-child {entry = entry} entry∈ parent∈) fwd back edge∈ =
    insertFreshLeafInForestPreservesTreeEdge
      children entry∈ parent∈ fwd back edge∈

  insertFreshLeafInForestPreservesTreeEdge :
    {G : GC.Graph} {u parent fresh p q : GC.Graph.Vertex G} →
    (children : List (RootedTreeChild G u)) →
    {entry : RootedTreeChild G u} →
    (entry∈ : entry ∈₁ children) →
    (parent∈ : TreeContains (subtree entry) parent) →
    (fwd : GC.Graph.Adj G parent fresh) →
    (back : GC.Graph.Adj G fresh parent) →
    CDFS.TreeEdgeOccurs {tree = CDFS.branch u children} p q →
    CDFS.TreeEdgeOccurs
      {tree = CDFS.branch u
        (insertFreshLeafInForest children entry∈ parent∈ fwd back)} p q
  insertFreshLeafInForestPreservesTreeEdge [] () parent∈ fwd back edge∈
  insertFreshLeafInForestPreservesTreeEdge (entry ∷ children) here₁ parent∈ fwd back
    (CDFS.direct-tree-edge CDFS.child-here) =
    CDFS.direct-tree-edge CDFS.child-here
  insertFreshLeafInForestPreservesTreeEdge (entry ∷ children) here₁ parent∈ fwd back
    (CDFS.direct-tree-edge (CDFS.child-there child∈)) =
    CDFS.direct-tree-edge (CDFS.child-there child∈)
  insertFreshLeafInForestPreservesTreeEdge (entry ∷ children) here₁ parent∈ fwd back
    (CDFS.below-tree-edge CDFS.child-here edge∈) =
    CDFS.below-tree-edge CDFS.child-here
      (insertFreshLeafPreservesTreeEdge
        (subtree entry) parent∈ fwd back edge∈)
  insertFreshLeafInForestPreservesTreeEdge (entry ∷ children) here₁ parent∈ fwd back
    (CDFS.below-tree-edge (CDFS.child-there child∈) edge∈) =
    CDFS.below-tree-edge (CDFS.child-there child∈) edge∈
  insertFreshLeafInForestPreservesTreeEdge (head ∷ children) (there₁ entry∈)
    parent∈ fwd back (CDFS.direct-tree-edge CDFS.child-here) =
    CDFS.direct-tree-edge CDFS.child-here
  insertFreshLeafInForestPreservesTreeEdge (head ∷ children) (there₁ entry∈)
    parent∈ fwd back (CDFS.direct-tree-edge (CDFS.child-there child∈)) =
    insertFreshLeafInForestPreservesTreeEdge children entry∈ parent∈ fwd back
      (CDFS.direct-tree-edge child∈)
  insertFreshLeafInForestPreservesTreeEdge (head ∷ children) (there₁ entry∈)
    parent∈ fwd back (CDFS.below-tree-edge CDFS.child-here edge∈) =
    CDFS.below-tree-edge CDFS.child-here edge∈
  insertFreshLeafInForestPreservesTreeEdge (head ∷ children) (there₁ entry∈)
    parent∈ fwd back (CDFS.below-tree-edge (CDFS.child-there child∈) edge∈) =
    insertFreshLeafInForestPreservesTreeEdge children entry∈ parent∈ fwd back
      (CDFS.below-tree-edge child∈ edge∈)
-}


record TreeRealisesInsertionHistory
  {G : GC.Graph}
  {X : List (GC.Graph.Vertex G)}
  (r : GC.Graph.Vertex G)
  (included : List (GC.Graph.Vertex G))
  (links : List (ParentLink {G = G} X)) : Set₁ where
  field
    tree : RootedTreeNode G r
    rangeExact : SameVertexSet (flattenTree tree) included
    flattenedNoDuplicates : NoDuplicates (flattenTree tree)
    includedPresent : ∀ {v} → v ∈ included → TreeContains tree v

open TreeRealisesInsertionHistory public

insertionHistoryToRootedTree :
  {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  {r : GC.Graph.Vertex G}
  {included : List (GC.Graph.Vertex G)}
  {links : List (ParentLink {G = G} X)} →
  ParentLinksDescribeInsertionOrder r included links →
  TreeRealisesInsertionHistory r included links
insertionHistoryToRootedTree root-only = record
  { tree = CDFS.leaf _
  ; rangeExact = (λ x∈ → x∈) , (λ x∈ → x∈)
  ; flattenedNoDuplicates = GC.noDup-cons (λ ()) GC.noDup-nil
  ; includedPresent = λ { here → at-leaf }
  }
insertionHistoryToRootedTree {G = G} {X = X} {r = r}
  (append-child {included = included} {links = links}
    {parent = parent} {child = child}
    history parent∈ child∉ link parent≡ child≡) =
  record
    { tree = newTree
    ; rangeExact = newRange
    ; flattenedNoDuplicates = newNoDuplicates
    ; includedPresent = newPresent
    }
  where
  previous : TreeRealisesInsertionHistory {G = G} {X = X} r included links
  previous = insertionHistoryToRootedTree history

  oldTree : RootedTreeNode G r
  oldTree = tree previous

  linkForward : GC.Graph.Adj G parent child
  linkForward =
    subst (λ q → GC.Graph.Adj G parent q) child≡
      (subst (λ p → GC.Graph.Adj G p (ParentLink.child link)) parent≡
        (ParentLink.forward link))

  linkBackward : GC.Graph.Adj G child parent
  linkBackward =
    subst (λ p → GC.Graph.Adj G child p) parent≡
      (subst (λ q → GC.Graph.Adj G q (ParentLink.parent link)) child≡
        (ParentLink.backward link))

  parentInOldTree : TreeContains oldTree parent
  parentInOldTree =
    treeContainsFromFlattenMember oldTree
      (proj₂ (rangeExact previous) parent∈)

  childFreshInOldTree : child ∉ flattenTree oldTree
  childFreshInOldTree childInOld =
    child∉ (proj₁ (rangeExact previous) childInOld)

  newTree : RootedTreeNode G r
  newTree =
    insertFreshLeafUnder oldTree parentInOldTree linkForward linkBackward

  newRange : SameVertexSet (flattenTree newTree) (included ++ child ∷ [])
  newRange =
    sameVertexSet-trans
      (insertFreshLeafFlattenRange oldTree parentInOldTree
        linkForward linkBackward)
      (sameVertexSetAppendSingle (rangeExact previous))

  newNoDuplicates : NoDuplicates (flattenTree newTree)
  newNoDuplicates =
    insertFreshLeafNoDuplicates oldTree parentInOldTree
      linkForward linkBackward childFreshInOldTree
      (flattenedNoDuplicates previous)

  newPresent : ∀ {v} → v ∈ (included ++ child ∷ []) → TreeContains newTree v
  newPresent {v} v∈ with appendMemberCases v v∈
  ... | inj₁ old∈ =
    insertFreshLeafPreservesContains oldTree parentInOldTree
      linkForward linkBackward
      (includedPresent previous old∈)
  ... | inj₂ new∈ =
    subst (λ z → TreeContains newTree z)
      (sym (memberSingletonCases new∈))
      (insertFreshLeafContainsChild oldTree parentInOldTree
        linkForward linkBackward)

------------------------------------------------------------------------
-- The reified tree can now be projected into the existing constructive
-- spanning-tree interface.  Carrier duplicate-freeness is intentionally
-- explicit: a partial path-union tree never needs it, but exact cardinality
-- does.
------------------------------------------------------------------------

completeInsertionTreeToConstructiveRootedSpanningTree :
  {G : GC.Graph} {r : GC.Graph.Vertex G}
  {X : List (GC.Graph.Vertex G)} →
  (T : CompleteInsertionParentTree r X) →
  NoDuplicates X →
  ConstructiveRootedSpanningTree G r X
completeInsertionTreeToConstructiveRootedSpanningTree {G = G} {r = r} {X = X}
  T noDup-X = record
  { tree = reifiedTree
  ; flattenedVertices = flattenTree reifiedTree
  ; flattenCorrect = refl
  ; noDuplicateVertices = flattenedNoDuplicates reified
  ; covers = proj₂ completeRange
  ; containsOnlyX = proj₁ completeRange
  ; rootIsRoot = proj₁ (CompleteInsertionParentTree.rangeExact T)
      (CompleteInsertionParentTree.rootIncluded T)
  ; flattenSize = sameVertexSetNoDuplicatesLength
      (flattenedNoDuplicates reified)
      noDup-X
      completeRange
  }
  where
  reified : TreeRealisesInsertionHistory r
    (CompleteInsertionParentTree.included T)
    (CompleteInsertionParentTree.links T)
  reified = insertionHistoryToRootedTree
    (CompleteInsertionParentTree.history T)

  reifiedTree : RootedTreeNode G r
  reifiedTree = tree reified

  completeRange : SameVertexSet (flattenTree reifiedTree) X
  completeRange = sameVertexSet-trans
    (rangeExact reified)
    (CompleteInsertionParentTree.rangeExact T)

------------------------------------------------------------------------
-- The path-union construction now owns the previously external DFS input.
-- Connectedness supplies paths inside the skeleton carrier; branch folding
-- reifies those paths into an eliminable tree, whose structural Euler tour
-- is exported by the constructive DFS module.
------------------------------------------------------------------------

pathUnionCanonicalSkeletonExactDFS :
  {G : GC.Graph} {r : GC.Graph.Vertex G} {n : ℕ} →
  (obj : GC.CanonicalSkeletonObject G r n) →
  CDFS.SkeletonAdjacencySymmetry
    (GC.CanonicalSkeletonObject.skelVertices obj) →
  CDFS.CanonicalSkeletonExactDFS obj
pathUnionCanonicalSkeletonExactDFS {G = G} {r = r} {n = n} obj symmetry =
  CDFS.canonicalSkeletonExactDFSFromConstructiveTree
    obj
    (completeInsertionTreeToConstructiveRootedSpanningTree
      complete
      (GC.CanonicalSkeletonObject.noDup obj))
  where
  X : List (GC.Graph.Vertex G)
  X = GC.CanonicalSkeletonObject.skelVertices obj

  paths : CDFS.RootedPathConnected G r X
  paths = CDFS.rootedConnectedSkeletonToRootedPathConnected
    (GC.CanonicalSkeletonObject.connected obj)

  complete : CompleteInsertionParentTree r X
  complete = pathUnionFoldToCompleteInsertionTree paths symmetry
