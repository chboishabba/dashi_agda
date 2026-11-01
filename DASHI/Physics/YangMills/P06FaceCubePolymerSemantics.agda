module DASHI.Physics.YangMills.P06FaceCubePolymerSemantics where

------------------------------------------------------------------------
-- Source-faithful P06 adapter for Bałaban's base M-cube carrier.
--
-- CMP 116 fixes the ambient graph as face-sharing M-cubes.  This module
-- deliberately does not redefine the generic abstract counts: it records
-- their intended interpretation by the concrete finite enumerations used
-- in P06, then applies the owned exact-DFS theorem at degree eight.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (ℕ; NonZero; suc; _∸_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)
open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; _∈_; _⊆_; here; there
        ; countNeighbors
        ; countSkeletons
        ; countWalks
        ; FiniteBallEnumeration
        ; ExplicitSkeletonCandidateEnumeration
        ; CanonicalBoundedNeighbourEnumeration
        ; BoundedNeighbourEnumeration
        ; Connected
        ; Ball
        ; Path
        ; ConsecutiveEdges
        ; edges-single; edges-step
        ; NonEmpty; nonempty; head
        ; ConnectedIffPathsInsideSubset
        ; pathSimplifyInsideSubset
        ; simplePathInsideSkeletonLengthBound
        ; pathBoundGivesBallMembership
        ; SkeletonCandidate
        ; chooseN
        ; candidateFromConnectedDecision
        ; filterMapListWithMembership
        ; filterMapListWithMembership-yes
        ; filterMapListWithMembership-projection-noDup
        ; in-map
        ; mapList
        ; NoDuplicates
        ; chooseN-noDup
        ; canonicalSkeletonCandidatesFromBall
        ; finiteBallEnumerationFromNeighbours
        ; memberDec
        ; noDupSubsetLength≤
        ; generatedWalkVertexLists
        )
open import Relation.Nullary using (Dec; yes; no)
open import DASHI.Physics.YangMills.P06ConcreteEnumerationEndpoint
  using ( CanonicalBoundedNeighbourEnumerationWithDegree )
open import DASHI.Physics.YangMills.P06ConstructiveSpanningTreeDFS
  using (p06DFSWalkLength)
open import DASHI.Physics.YangMills.P06ExactEnumerationEndpoint
  using ( P06ConcreteCountSemantics
        ; P06ConcreteEnumerationTheoremOwned
        )
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry

------------------------------------------------------------------------
-- The sole local refinement still required by the generic graph API.
-- `countNeighbors` is abstract in GraphCombinatorics, so this equality is
-- explicitly a model semantics statement rather than a fabricated proof.
------------------------------------------------------------------------

faceCubeCanonicalBoundedNeighbourEnumerationWithDegree :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (neighbourCountAgreement :
    ∀ x →
    countNeighbors (faceCubeGraph {N}) x ≡ length (faceNeighbours x)) →
  CanonicalBoundedNeighbourEnumerationWithDegree
    (faceCubeGraph {N}) faceCubeDegreeBound
faceCubeCanonicalBoundedNeighbourEnumerationWithDegree agreement = record
  { enumeration = faceCubeCanonicalBoundedNeighbourEnumeration
  ; countNeighborsAgrees = agreement
  }

faceCubePositiveDegree : 1 ≤ faceCubeDegreeBound
faceCubePositiveDegree = s≤s z≤n

------------------------------------------------------------------------
-- Exact finite balls are constructive already: rawBallApprox performs the
-- breadth expansion from the canonical face-neighbour list, and the generic
-- theorem proves both directions against the Path-based Ball predicate.
------------------------------------------------------------------------

faceCubeFiniteBallEnumeration :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (r : Cube4 N) (n : ℕ) →
  FiniteBallEnumeration (faceCubeGraph {N}) r (n ∸ 1)
faceCubeFiniteBallEnumeration r n =
  finiteBallEnumerationFromNeighbours
    faceCubeBoundedNeighbourEnumeration r (n ∸ 1)

------------------------------------------------------------------------
-- Finite reachability inside a proposed support.  The induced support
-- graph retains the ambient cube carrier but permits an edge u → v only
-- when v belongs to the support.  Starting from a support member, every
-- path in this graph remains in that support.  Its bounded-neighbour and
-- finite-ball instances are fully constructive.
------------------------------------------------------------------------

supportFaceGraph :
  ∀ {N : ℕ} {{_ : NonZero N}} → List (Cube4 N) → Graph
supportFaceGraph {N} X = record
  { Vertex = Cube4 N
  ; Edge = Cube4 N × Cube4 N
  ; Adj = λ u v → FaceCubeAdj u v × v ∈ X
  }

filterSupportMembers :
  ∀ {N : ℕ} → List (Cube4 N) → List (Cube4 N) → List (Cube4 N)
filterSupportMembers X [] = []
filterSupportMembers X (v ∷ vs)
  with memberDec cube4Eq? v X
... | yes _ = v ∷ filterSupportMembers X vs
... | no _ = filterSupportMembers X vs

filterSupportMembersSound :
  ∀ {N : ℕ} {X ws : List (Cube4 N)} {v : Cube4 N} →
  v ∈ filterSupportMembers X ws → v ∈ ws × v ∈ X
filterSupportMembersSound {X = X} {ws = []} ()
filterSupportMembersSound {X = X} {ws = w ∷ ws} {v} v∈
  with memberDec cube4Eq? w X | v∈
... | yes w∈X | here = here , w∈X
... | yes w∈X | there v∈tail =
  let result = filterSupportMembersSound v∈tail
  in there (proj₁ result) , proj₂ result
... | no w∉X | v∈tail =
  let result = filterSupportMembersSound v∈tail
  in there (proj₁ result) , proj₂ result

filterSupportMembersComplete :
  ∀ {N : ℕ} {X ws : List (Cube4 N)} {v : Cube4 N} →
  v ∈ ws → v ∈ X → v ∈ filterSupportMembers X ws
filterSupportMembersComplete {X = X} {ws = []} () v∈X
filterSupportMembersComplete {X = X} {ws = w ∷ ws} {v} v∈ws v∈X
  with memberDec cube4Eq? w X | v∈ws
... | yes w∈X | here = here
... | yes w∈X | there v∈tail = there (filterSupportMembersComplete v∈tail v∈X)
... | no w∉X | here = ⊥-elim (w∉X v∈X)
... | no w∉X | there v∈tail = filterSupportMembersComplete v∈tail v∈X

filterSupportMembersLength≤ :
  ∀ {N : ℕ} (X ws : List (Cube4 N)) →
  length (filterSupportMembers X ws) ≤ length ws
filterSupportMembersLength≤ X [] = z≤n
filterSupportMembersLength≤ X (v ∷ vs) with memberDec cube4Eq? v X
... | yes _ = s≤s (filterSupportMembersLength≤ X vs)
... | no _ = ≤-step-right (filterSupportMembersLength≤ X vs)
  where
  ≤-step-right : ∀ {m n : ℕ} → m ≤ n → m ≤ suc n
  ≤-step-right {m} {n} m≤n = ≤-trans m≤n (n≤1+n n)

faceNeighboursWithin :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  List (Cube4 N) → Cube4 N → List (Cube4 N)
faceNeighboursWithin X u = filterSupportMembers X (faceNeighbours u)

faceNeighboursWithinSound :
  ∀ {N : ℕ} {{_ : NonZero N}} {X : List (Cube4 N)} {u v : Cube4 N} →
  v ∈ faceNeighboursWithin X u →
  FaceCubeAdj u v × v ∈ X
faceNeighboursWithinSound {X = X} {u} v∈ =
  let result = filterSupportMembersSound v∈
  in faceNeighboursSound (proj₁ result) , proj₂ result

faceNeighboursWithinComplete :
  ∀ {N : ℕ} {{_ : NonZero N}} {X : List (Cube4 N)} {u v : Cube4 N} →
  FaceCubeAdj u v → v ∈ X →
  v ∈ faceNeighboursWithin X u
faceNeighboursWithinComplete {X = X} {u} {v} uv v∈X =
  filterSupportMembersComplete (faceNeighboursComplete uv) v∈X

supportFaceBoundedNeighbourEnumeration :
  ∀ {N : ℕ} {{_ : NonZero N}} (X : List (Cube4 N)) →
  BoundedNeighbourEnumeration (supportFaceGraph X) faceCubeDegreeBound
supportFaceBoundedNeighbourEnumeration X = record
  { neighbours = faceNeighboursWithin X
  ; neighbourSound = faceNeighboursWithinSound
  ; neighbourComplete = λ {u} {v} uv →
      faceNeighboursWithinComplete (proj₁ uv) (proj₂ uv)
  ; neighbourBound = λ u →
      ≤-trans
        (filterSupportMembersLength≤ X (faceNeighbours u))
        (faceNeighboursLength≤8 u)
  }

supportFaceFiniteBallEnumeration :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (X : List (Cube4 N)) (r : Cube4 N) (k : ℕ) →
  FiniteBallEnumeration (supportFaceGraph X) r k
supportFaceFiniteBallEnumeration X r k =
  finiteBallEnumerationFromNeighbours
    (supportFaceBoundedNeighbourEnumeration X) r k

------------------------------------------------------------------------
-- Decidable pairwise reachability in the finite induced support graph.
-- The recursive decision is over finite lists only; no global graph
-- finiteness or classical choice is used.
------------------------------------------------------------------------

data All {A : Set} (P : A → Set) : List A → Set where
  all[] : All P []
  all∷  : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

allDec :
  ∀ {A : Set} {P : A → Set} →
  (∀ x → Dec (P x)) → (xs : List A) → Dec (All P xs)
allDec decide [] = yes all[]
allDec decide (x ∷ xs) with decide x | allDec decide xs
... | yes px | yes pxs = yes (all∷ px pxs)
... | no ¬px | _ = no (λ { (all∷ px _) → ¬px px })
... | yes _ | no ¬pxs = no (λ { (all∷ _ pxs) → ¬pxs pxs })

allLookup :
  ∀ {A : Set} {P : A → Set} {xs : List A} {x : A} →
  All P xs → x ∈ xs → P x
allLookup (all∷ px pxs) here = px
allLookup (all∷ px pxs) (there x∈) = allLookup pxs x∈

supportTargetReachable? :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (X : List (Cube4 N)) (x : Cube4 N) (k : ℕ) (y : Cube4 N) →
  Dec (y ∈ FiniteBallEnumeration.ballList
           (supportFaceFiniteBallEnumeration X x k))
supportTargetReachable? X x k y =
  memberDec cube4Eq? y
    (FiniteBallEnumeration.ballList
      (supportFaceFiniteBallEnumeration X x k))

record SupportPairBalls
  {N : ℕ} {{_ : NonZero N}}
  (X : List (Cube4 N)) (k : ℕ) : Set where
  field
    ball :
      ∀ {x y} → x ∈ X → y ∈ X → Ball (supportFaceGraph X) x k y

supportPairBalls? :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (X : List (Cube4 N)) (k : ℕ) → Dec (SupportPairBalls X k)
supportPairBalls? {N} X k with
  allDec
    (λ x →
      allDec
        (λ y → supportTargetReachable? X x k y)
        X)
    X
... | yes allPairs = yes (record
  { ball = λ {x} {y} x∈X y∈X →
      FiniteBallEnumeration.ballSoundList
        (supportFaceFiniteBallEnumeration X x k)
        y
        (allLookup
          (allLookup allPairs x∈X)
          y∈X)
  })
... | no ¬allPairs = no (λ pairBalls →
  ¬allPairs
    (allPairsFrom pairBalls X (λ {x} x∈X → x∈X)))
  where
  allPairsFrom :
    (balls : SupportPairBalls X k) →
    (xs : List (Cube4 N)) → xs ⊆ X →
    All
      (λ x → All
        (λ y → y ∈ FiniteBallEnumeration.ballList
          (supportFaceFiniteBallEnumeration X x k)) X)
      xs
  allPairsFrom balls [] xs⊆X = all[]
  allPairsFrom balls (x ∷ xs) xs⊆X =
    all∷ (targets x (xs⊆X here) X (λ {y} y∈X → y∈X))
      (allPairsFrom balls xs (λ {y} y∈xs → xs⊆X (there y∈xs)))
    where
    targets : (u : Cube4 N) → u ∈ X →
      (ys : List (Cube4 N)) → ys ⊆ X →
      All
        (λ y → y ∈ FiniteBallEnumeration.ballList
          (supportFaceFiniteBallEnumeration X u k)) ys
    targets u u∈X [] ys⊆X = all[]
    targets u u∈X (y ∷ ys) ys⊆X =
      all∷
        (FiniteBallEnumeration.ballCompleteList
          (supportFaceFiniteBallEnumeration X u k)
          y
          (SupportPairBalls.ball balls u∈X (ys⊆X here)))
        (targets u u∈X ys (λ {z} z∈ys → ys⊆X (there z∈ys)))

------------------------------------------------------------------------
-- The induced support graph and the ambient face graph have the same paths
-- whenever all vertices of the path are in X.  These two translations turn
-- the decidable finite-ball test above into a decision procedure for the
-- generic Connected predicate without changing GraphCombinatorics.
------------------------------------------------------------------------

forgetSupportEdges :
  ∀ {N : ℕ} {{_ : NonZero N}} {X : List (Cube4 N)} {xs : List (Cube4 N)} →
  ConsecutiveEdges (supportFaceGraph X) xs →
  ConsecutiveEdges (faceCubeGraph {N}) xs
forgetSupportEdges edges-single = edges-single
forgetSupportEdges (edges-step uv rest) =
  edges-step (proj₁ uv) (forgetSupportEdges rest)

supportEdgesInside :
  ∀ {N : ℕ} {{_ : NonZero N}} {X : List (Cube4 N)}
  {x : Cube4 N} {xs : List (Cube4 N)} →
  ConsecutiveEdges (supportFaceGraph X) (x ∷ xs) → x ∈ X →
  (x ∷ xs) ⊆ X
supportEdgesInside edges-single x∈X here = x∈X
supportEdgesInside (edges-step uv rest) x∈X here = x∈X
supportEdgesInside (edges-step uv rest) x∈X (there here) = proj₂ uv
supportEdgesInside (edges-step uv rest) x∈X (there (there z∈)) =
  supportEdgesInside rest (proj₂ uv) (there z∈)

supportEdgesInsideFromStart :
  ∀ {N : ℕ} {{_ : NonZero N}} {X : List (Cube4 N)}
  (vs : List (Cube4 N)) (vsNonEmpty : NonEmpty vs) →
  head vs vsNonEmpty ∈ X →
  ConsecutiveEdges (supportFaceGraph X) vs → vs ⊆ X
supportEdgesInsideFromStart (x ∷ []) nonempty x∈X edges-single here = x∈X
supportEdgesInsideFromStart (x ∷ y ∷ xs) nonempty x∈X (edges-step uv rest) here = x∈X
supportEdgesInsideFromStart (x ∷ y ∷ xs) nonempty x∈X (edges-step uv rest) (there here) =
  proj₂ uv
supportEdgesInsideFromStart (x ∷ y ∷ xs) nonempty x∈X (edges-step uv rest)
  (there (there z∈)) =
  supportEdgesInsideFromStart (y ∷ xs) nonempty (proj₂ uv) rest (there z∈)

forgetSupportPath :
  ∀ {N : ℕ} {{_ : NonZero N}} {X : List (Cube4 N)} {a b : Cube4 N} →
  Path (supportFaceGraph X) a b → Path (faceCubeGraph {N}) a b
forgetSupportPath p = record
  { vertices = GC.Path.vertices p
  ; nonEmptyWitness = GC.Path.nonEmptyWitness p
  ; startsAt = GC.Path.startsAt p
  ; endsAt = GC.Path.endsAt p
  ; adjacent = forgetSupportEdges (GC.Path.adjacent p)
  }

supportPathInside :
  ∀ {N : ℕ} {{_ : NonZero N}} {X : List (Cube4 N)} {a b : Cube4 N} →
  (p : Path (supportFaceGraph X) a b) → a ∈ X →
  GC.vertices (forgetSupportPath p) ⊆ X
supportPathInside {X = X} {a = a} p a∈X =
  supportEdgesInsideFromStart
    (GC.Path.vertices p)
    (GC.Path.nonEmptyWitness p)
    (subst
      (λ z → z ∈ X)
      (sym (GC.Path.startsAt p))
      a∈X)
    (GC.Path.adjacent p)

liftFaceEdges :
  ∀ {N : ℕ} {{_ : NonZero N}} {X : List (Cube4 N)} {xs : List (Cube4 N)} →
  ConsecutiveEdges (faceCubeGraph {N}) xs → xs ⊆ X →
  ConsecutiveEdges (supportFaceGraph X) xs
liftFaceEdges edges-single inside = edges-single
liftFaceEdges (edges-step uv rest) inside =
  edges-step (uv , inside (there here))
    (liftFaceEdges rest (λ {z} z∈rest → inside (there z∈rest)))

liftFacePath :
  ∀ {N : ℕ} {{_ : NonZero N}} {X : List (Cube4 N)} {a b : Cube4 N} →
  (p : Path (faceCubeGraph {N}) a b) → GC.vertices p ⊆ X →
  Path (supportFaceGraph X) a b
liftFacePath p inside = record
  { vertices = GC.Path.vertices p
  ; nonEmptyWitness = GC.Path.nonEmptyWitness p
  ; startsAt = GC.Path.startsAt p
  ; endsAt = GC.Path.endsAt p
  ; adjacent = liftFaceEdges (GC.Path.adjacent p) inside
  }

supportPairBallsToFaceConnected :
  ∀ {N : ℕ} {{_ : NonZero N}} (X : List (Cube4 N)) (k : ℕ) →
  SupportPairBalls X k → Connected (faceCubeGraph {N}) X
supportPairBallsToFaceConnected X k pairs =
  proj₂ (ConnectedIffPathsInsideSubset X)
    (λ x y x∈X y∈X →
      let b = SupportPairBalls.ball pairs x∈X y∈X
          p = GC.BallMembership.witnessPath b
      in forgetSupportPath p , supportPathInside p x∈X)

faceConnectedToSupportPairBalls :
  ∀ {N : ℕ} {{_ : NonZero N}} (X : List (Cube4 N)) →
  Connected (faceCubeGraph {N}) X →
  SupportPairBalls X (length X ∸ 1)
faceConnectedToSupportPairBalls X connected = record
  { ball = λ {x} {y} x∈X y∈X →
      let pathData = proj₁ (ConnectedIffPathsInsideSubset X) connected x y x∈X y∈X
          p = proj₁ pathData
          pInside = proj₂ pathData
          simple = pathSimplifyInsideSubset p pInside
          simplePath = GC.PathIn.path (GC.SimplePathIn.pathIn simple)
          q = liftFacePath simplePath (GC.PathIn.insideX (GC.SimplePathIn.pathIn simple))
      in pathBoundGivesBallMembership q (simplePathInsideSkeletonLengthBound simple)
  }

faceCubeConnected? :
  ∀ {N : ℕ} {{_ : NonZero N}} (X : List (Cube4 N)) →
  Dec (Connected (faceCubeGraph {N}) X)
faceCubeConnected? X with supportPairBalls? X (length X ∸ 1)
... | yes pairs = yes (supportPairBallsToFaceConnected X (length X ∸ 1) pairs)
... | no ¬pairs = no (λ connected →
  ¬pairs (faceConnectedToSupportPairBalls X connected))

------------------------------------------------------------------------
-- The candidate *list* is concrete once connectedness is decidable.  It is
-- the canonical filter of choose-n subsets of the exact ball above.  The
-- generic Graph API currently declares Connected postulated, so the decision
-- procedure itself cannot be manufactured by this module without first
-- replacing that opaque predicate by an eliminable path-connectedness
-- definition (or supplying a proved equivalence and finite search theorem).
------------------------------------------------------------------------

faceCubeSkeletonCandidates :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (r : Cube4 N) (n : ℕ) →
  ((ys : List (Cube4 N)) → Dec (Connected (faceCubeGraph {N}) ys)) →
  List
    (SkeletonCandidate
      (faceCubeGraph {N}) r n
      (faceCubeFiniteBallEnumeration r n))
faceCubeSkeletonCandidates r n connectedDecider =
  canonicalSkeletonCandidatesFromBall
    (faceCubeFiniteBallEnumeration r n)
    connectedDecider

-- The candidate list no longer needs an externally supplied connectedness
-- decision: faceCubeConnected? is the finite decision procedure above.
concreteFaceCubeSkeletonCandidates :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (r : Cube4 N) (n : ℕ) →
  List
    (SkeletonCandidate
      (faceCubeGraph {N}) r n
      (faceCubeFiniteBallEnumeration r n))
concreteFaceCubeSkeletonCandidates r n =
  faceCubeSkeletonCandidates r n faceCubeConnected?

faceCubeSkeletonCandidatesComplete :
  ∀ {N : ℕ} {{_ : NonZero N}}
  (r : Cube4 N) (n : ℕ)
  {ys : List (Cube4 N)} →
  ys ∈ chooseN
    (FiniteBallEnumeration.ballList (faceCubeFiniteBallEnumeration r n)) n →
  r ∈ ys →
  Connected (faceCubeGraph {N}) ys →
  Σ
    (SkeletonCandidate
      (faceCubeGraph {N}) r n
      (faceCubeFiniteBallEnumeration r n))
    (λ c →
      c ∈ concreteFaceCubeSkeletonCandidates r n ×
      GC.SkeletonCandidate.candVertices c ≡ ys)
faceCubeSkeletonCandidatesComplete {N} r n {ys} ys∈ root∈ connected
  with candidateFromConnectedDecision faceCubeConnected? {ys = ys} ys∈ in decisionEq
... | yes (c , verticesEq) =
  c ,
  ( in-map
      (λ p → proj₁ (proj₂ p))
      (filterMapListWithMembership-yes
        (chooseN
          (FiniteBallEnumeration.ballList (faceCubeFiniteBallEnumeration r n)) n)
        (λ zs zs∈ →
          candidateFromConnectedDecision faceCubeConnected? {ys = zs} zs∈)
        ys∈
        decisionEq)
  , verticesEq)
... | no noCandidate =
  ⊥-elim
    (noCandidate
      (record
        { candVertices = ys
        ; inChooseN = ys∈
        ; rootIn = root∈
        ; connected = connected
        }
      , refl))

-- The dependent connectedness filter preserves the underlying choose-n
-- support list.  The generic provenance theorem deliberately proves this
-- after projecting away proof fields, so no proof-irrelevance principle is
-- needed for SkeletonCandidate records.
faceCubeSkeletonCandidateVerticesNoDuplicates :
  ∀ {N : ℕ} {{_ : NonZero N}}
  (r : Cube4 N) (n : ℕ) →
  NoDuplicates
    (mapList GC.SkeletonCandidate.candVertices
      (concreteFaceCubeSkeletonCandidates r n))
faceCubeSkeletonCandidateVerticesNoDuplicates r n =
  filterMapListWithMembership-projection-noDup
    (chooseN
      (FiniteBallEnumeration.ballList (faceCubeFiniteBallEnumeration r n)) n)
    (λ ys ys∈ → candidateFromConnectedDecision faceCubeConnected? {ys = ys} ys∈)
    (λ p → GC.SkeletonCandidate.candVertices (proj₁ (proj₂ p)))
    (λ ys → ys)
    (λ ys ys∈ candidateAndVertices → proj₂ candidateAndVertices)
    (chooseN-noDup
      (FiniteBallEnumeration.ballNoDup (faceCubeFiniteBallEnumeration r n)))

-- The generic countSkeletons symbol remains intentionally abstract.  This
-- constructor is therefore parameterized only by its explicit interpretation
-- as the concrete candidate-list length; all geometric fields are owned.
faceCubeExplicitSkeletonCandidateEnumeration :
  ∀ {N : ℕ} {{_ : NonZero N}}
  (r : Cube4 N) (n : ℕ) →
  countSkeletons (faceCubeGraph {N}) r n ≡
    length (concreteFaceCubeSkeletonCandidates r n) →
  ExplicitSkeletonCandidateEnumeration
    (faceCubeGraph {N}) r n
    (faceCubeFiniteBallEnumeration r n)
faceCubeExplicitSkeletonCandidateEnumeration r n countAgreement = record
  { candidates = concreteFaceCubeSkeletonCandidates r n
  ; complete = faceCubeSkeletonCandidatesComplete r n
  ; uniqueVertexLists = faceCubeSkeletonCandidateVerticesNoDuplicates r n
  ; countAgrees = countAgreement
  }

------------------------------------------------------------------------
-- Fully concrete list cardinalities.  These are the count functions of
-- the face-cube model itself; the abstract GraphCombinatorics counts are
-- related to them only through the explicit semantic bridges above.
------------------------------------------------------------------------

countFaceCubeNeighbours :
  ∀ {N : ℕ} {{_ : NonZero N}} → Cube4 N → ℕ
countFaceCubeNeighbours x = length (faceNeighbours x)

countFaceCubeNeighbours≤8 :
  ∀ {N : ℕ} {{_ : NonZero N}} (x : Cube4 N) →
  countFaceCubeNeighbours x ≤ faceCubeDegreeBound
countFaceCubeNeighbours≤8 = faceNeighboursLength≤8

faceCubeGeneratedWalkVertexLists :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (r : Cube4 N) (L : ℕ) → List (List (Cube4 N))
faceCubeGeneratedWalkVertexLists r L =
  generatedWalkVertexLists {r = r} {L = L}
    faceCubeBoundedNeighbourEnumeration

countFaceCubeWalks :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (r : Cube4 N) (L : ℕ) → ℕ
countFaceCubeWalks r L = length (faceCubeGeneratedWalkVertexLists r L)

countFaceCubeRootedCandidates :
  ∀ {N : ℕ} {{_ : NonZero N}} →
  (r : Cube4 N) (n : ℕ) → ℕ
countFaceCubeRootedCandidates r n =
  length (concreteFaceCubeSkeletonCandidates r n)

------------------------------------------------------------------------
-- Concrete P06 count meanings for a fixed root and skeleton size.
--
-- The skeleton equality is already a field of the explicit candidate
-- enumeration.  The remaining two equations are kept visible here because
-- the generic counts are intentionally abstract elsewhere in DASHI.
------------------------------------------------------------------------

record FaceCubeP06CountSemantics
  {N : ℕ} {{_ : NonZero N}}
  (r : Cube4 N) (n : ℕ)
  (FBE : FiniteBallEnumeration (faceCubeGraph {N}) r (n ∸ 1))
  (skelEnum : ExplicitSkeletonCandidateEnumeration
                (faceCubeGraph {N}) r n FBE)
  : Set₁ where
  field
    neighbourCountAgreement :
      ∀ x →
      countNeighbors (faceCubeGraph {N}) x ≡ length (faceNeighbours x)

    walkCountAgreement :
      countWalks (faceCubeGraph {N}) r (p06DFSWalkLength n) ≡
      length
        (generatedWalkVertexLists
          {r = r} {L = p06DFSWalkLength n}
          (CanonicalBoundedNeighbourEnumeration.bounded
            faceCubeCanonicalBoundedNeighbourEnumeration))

open FaceCubeP06CountSemantics public

faceCubeCBNED :
  ∀ {N : ℕ} {{_ : NonZero N}} {r : Cube4 N} {n : ℕ}
  {FBE : FiniteBallEnumeration (faceCubeGraph {N}) r (n ∸ 1)}
  {skelEnum : ExplicitSkeletonCandidateEnumeration
                (faceCubeGraph {N}) r n FBE} →
  FaceCubeP06CountSemantics r n FBE skelEnum →
  CanonicalBoundedNeighbourEnumerationWithDegree
    (faceCubeGraph {N}) faceCubeDegreeBound
faceCubeCBNED semantics =
  faceCubeCanonicalBoundedNeighbourEnumerationWithDegree
    (neighbourCountAgreement semantics)

faceCubeConcreteCountSemantics :
  ∀ {N : ℕ} {{_ : NonZero N}} {r : Cube4 N} {n : ℕ}
  {FBE : FiniteBallEnumeration (faceCubeGraph {N}) r (n ∸ 1)}
  {skelEnum : ExplicitSkeletonCandidateEnumeration
                (faceCubeGraph {N}) r n FBE} →
  (semantics : FaceCubeP06CountSemantics r n FBE skelEnum) →
  P06ConcreteCountSemantics FBE (faceCubeCBNED semantics) skelEnum
faceCubeConcreteCountSemantics {skelEnum = skelEnum} semantics = record
  { skeletonCountAgreement =
      ExplicitSkeletonCandidateEnumeration.countAgrees skelEnum
  ; walkCountAgreement = walkCountAgreement semantics
  }

------------------------------------------------------------------------
-- Direct source-faithful rooted face-animal bound.  The finite ball and
-- candidate enumeration are arguments on purpose: constructing them is the
-- remaining finite-enumeration task, while this theorem supplies the exact
-- model-to-P06 bridge once they are available.
------------------------------------------------------------------------

balabanFaceCubeRootedAnimalBound :
  ∀ {N : ℕ} {{_ : NonZero N}} {r : Cube4 N} {n : ℕ}
  (FBE : FiniteBallEnumeration (faceCubeGraph {N}) r (n ∸ 1))
  (skelEnum : ExplicitSkeletonCandidateEnumeration
                (faceCubeGraph {N}) r n FBE)
  (semantics : FaceCubeP06CountSemantics r n FBE skelEnum) →
  countSkeletons (faceCubeGraph {N}) r n ≤
    pow (faceCubeDegreeBound * faceCubeDegreeBound) n
balabanFaceCubeRootedAnimalBound FBE skelEnum semantics =
  P06ConcreteEnumerationTheoremOwned
    FBE
    faceCubeUndirected
    faceCubePositiveDegree
    (faceCubeCBNED semantics)
    skelEnum
    (faceCubeConcreteCountSemantics semantics)

-- Concrete list-cardinality form of the source-faithful rooted animal bound.
-- The only parameters are the three explicit bridges to the legacy abstract
-- GraphCombinatorics counts; the ball, connected-support filter, candidate
-- enumeration, and degree-eight geometry are constructed above.
faceCubeRootedCandidateListBound :
  ∀ {N : ℕ} {{_ : NonZero N}}
  (r : Cube4 N) (n : ℕ)
  (skeletonCountAgreement :
    countSkeletons (faceCubeGraph {N}) r n ≡
      countFaceCubeRootedCandidates r n)
  (neighbourCountAgreement :
    ∀ x →
    countNeighbors (faceCubeGraph {N}) x ≡ length (faceNeighbours x))
  (walkCountAgreement :
    countWalks (faceCubeGraph {N}) r (p06DFSWalkLength n) ≡
    countFaceCubeWalks r (p06DFSWalkLength n)) →
  countFaceCubeRootedCandidates r n ≤
    pow (faceCubeDegreeBound * faceCubeDegreeBound) n
faceCubeRootedCandidateListBound r n skeletonAgreement neighbourAgreement walkAgreement =
  subst
    (λ q → q ≤ pow (faceCubeDegreeBound * faceCubeDegreeBound) n)
    (sym skeletonAgreement)
    (balabanFaceCubeRootedAnimalBound
      (faceCubeFiniteBallEnumeration r n)
      (faceCubeExplicitSkeletonCandidateEnumeration r n skeletonAgreement)
      (record
        { neighbourCountAgreement = neighbourAgreement
        ; walkCountAgreement = walkAgreement
        }))
