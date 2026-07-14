module DASHI.Physics.YangMills.P06ConcreteEnumerationEndpoint where

------------------------------------------------------------------------
-- Additive P06 endpoint.
--
-- The walk semantic input is deliberately membership-indexed.  A DFS
-- sequence is required to be a member of the finite valid-walk list before
-- its Fin index is requested; this module never constructs the legacy total
-- `CountWalksSemantics` record.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; length)
open import Data.Nat.Base using (ℕ; _+_; _*_; _∸_; _≤_)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans; sym)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; BoundedDegree
        ; BoundedNeighbourEnumeration
        ; CanonicalBoundedNeighbourEnumeration
        ; countSkeletons
        ; countWalks
        ; countNeighbors
        ; FiniteBallEnumeration
        ; ExplicitSkeletonCandidateEnumeration
        ; ConcreteCountSkeletonsSemantics
        ; concreteCountSkeletonsSemanticsToCountSkeletonsSemantics
        ; CountSkeletonsSemantics
        ; CountWalksMembershipSemantics
        ; MembershipIndexedCanonicalWalkObjectList
        ; ConcreteWalkCountAgreement
        ; explicitSkeletonCandidateEnumerationToCandidateFilterWitness
        ; countSkeletonsSemanticsToEnumeration
        ; generatedWalksToMembershipIndexedCanonicalWalkObjectList
        ; walkObjectsFromNeighbourCodes
        ; walkObjectVertices
        ; listMapLength
        ; _∈_
        ; ActualSkeletonEncodingData
        ; SameVertexSet
        ; CanonicalSkeletonEnumeration
        ; CanonicalSkeletonObject
        ; actualSkeletonCountBound
        ; RootedReducedSkeleton
        ; RootedConnectedSkeleton
        ; SkeletonEnumeration
        )

------------------------------------------------------------------------
-- Direct bridges used by the concrete theorem.
------------------------------------------------------------------------

explicitSkeletonEnumerationToCanonicalEnumeration :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (skelEnum : ExplicitSkeletonCandidateEnumeration G r n FBE) →
  countSkeletons G r n ≡
    length (ExplicitSkeletonCandidateEnumeration.candidates skelEnum) →
  CanonicalSkeletonEnumeration G r n
explicitSkeletonEnumerationToCanonicalEnumeration skelEnum skelCount =
  countSkeletonsSemanticsToEnumeration
    (record
      { witness =
          explicitSkeletonCandidateEnumerationToCandidateFilterWitness skelEnum
      ; countAgrees = skelCount
      })

generatedWalksToMembershipIndexedWalkList :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {L : ℕ} →
  (CBNE : CanonicalBoundedNeighbourEnumeration G Δ) →
  countWalks G r L ≡
    length
      (GC.generatedWalkVertexLists
        {r = r} {L = L}
        (CanonicalBoundedNeighbourEnumeration.bounded CBNE)) →
  MembershipIndexedCanonicalWalkObjectList G r L
generatedWalksToMembershipIndexedWalkList {r = r} {L = L} CBNE walkCount =
  generatedWalksToMembershipIndexedCanonicalWalkObjectList
    (CanonicalBoundedNeighbourEnumeration.bounded CBNE)
    (record
      { countAgrees =
          trans walkCount
            (listMapLength
              walkObjectVertices
              (walkObjectsFromNeighbourCodes
                (CanonicalBoundedNeighbourEnumeration.bounded CBNE)
                r L))
      })

------------------------------------------------------------------------
-- A valid, membership-indexed DFS map.
------------------------------------------------------------------------

-- The existing neighbour enumeration deliberately does not identify the
-- abstract `countNeighbors` function with the concrete neighbour list.  Keep
-- that identification as a small refinement rather than changing the
-- already-used CBNE record and breaking its callers.
record CanonicalBoundedNeighbourEnumerationWithDegree
  (G : Graph) (Δ : ℕ) : Set₁ where
  field
    enumeration : CanonicalBoundedNeighbourEnumeration G Δ
    countNeighborsAgrees :
      ∀ u →
      countNeighbors G u ≡
        length
          (BoundedNeighbourEnumeration.neighbours
            (CanonicalBoundedNeighbourEnumeration.bounded enumeration) u)

boundedDegreeFromCanonicalNeighbourEnumeration :
  {G : Graph} {Δ : ℕ} →
  CanonicalBoundedNeighbourEnumerationWithDegree G Δ →
  BoundedDegree G Δ
boundedDegreeFromCanonicalNeighbourEnumeration package u =
  subst
    (λ k → k ≤ _)
    (sym
      (CanonicalBoundedNeighbourEnumerationWithDegree.countNeighborsAgrees
        package u))
    (BoundedNeighbourEnumeration.neighbourBound
      (CanonicalBoundedNeighbourEnumeration.bounded
        (CanonicalBoundedNeighbourEnumerationWithDegree.enumeration package))
      u)

record MembershipIndexedDFSMap
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  (CE : CanonicalSkeletonEnumeration G r n)
  (WE : CountWalksMembershipSemantics G r (n + n)) : Set₁ where
  field
    dfsWalkOfSkeleton :
      Fin (countSkeletons G r n) → List (Graph.Vertex G)

    dfsWalkMember :
      ∀ s →
      dfsWalkOfSkeleton s ∈
        MembershipIndexedCanonicalWalkObjectList.walks WE

    dfsWalkSound :
      ∀ s →
      SameVertexSet
        (dfsWalkOfSkeleton s)
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s))

    dfsWalkInjective :
      ∀ {s₁ s₂} →
      dfsWalkOfSkeleton s₁ ≡ dfsWalkOfSkeleton s₂ →
      s₁ ≡ s₂

------------------------------------------------------------------------
-- The membership-aware DFS map yields the old concrete encoding record.
-- This is a genuine construction: the only index operation is applied to
-- a list together with its membership proof.
------------------------------------------------------------------------

membershipIndexedDFSMapToEncodingData :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {CE : CanonicalSkeletonEnumeration G r n}
  {WE : CountWalksMembershipSemantics G r (n + n)} →
  MembershipIndexedDFSMap CE WE →
  ActualSkeletonEncodingData G r n
membershipIndexedDFSMapToEncodingData {CE = CE} {WE = WE} map = record
  { skeletonOf = λ s →
      let o = CanonicalSkeletonEnumeration.objectOf CE s
      in ( CanonicalSkeletonObject.skelVertices o
         , CanonicalSkeletonObject.reduced o
         , CanonicalSkeletonObject.connected o
         , CanonicalSkeletonObject.size o )

  ; walkRange =
      MembershipIndexedCanonicalWalkObjectList.walkOfFin WE

  ; encode = λ s →
      MembershipIndexedCanonicalWalkObjectList.walkIndex WE
        (MembershipIndexedDFSMap.dfsWalkOfSkeleton map s)
        (MembershipIndexedDFSMap.dfsWalkMember map s)

  ; encodeSound = λ s →
      let w = MembershipIndexedDFSMap.dfsWalkOfSkeleton map s
          i = MembershipIndexedCanonicalWalkObjectList.walkIndex WE w
                (MembershipIndexedDFSMap.dfsWalkMember map s)
          rw≡w :
            MembershipIndexedCanonicalWalkObjectList.walkOfFin WE i ≡ w
          rw≡w = MembershipIndexedCanonicalWalkObjectList.walkIndexOf WE
                   (MembershipIndexedDFSMap.dfsWalkMember map s)
          sound = MembershipIndexedDFSMap.dfsWalkSound map s
      in subst
           (λ ws →
             SameVertexSet ws
               (CanonicalSkeletonObject.skelVertices
                 (CanonicalSkeletonEnumeration.objectOf CE s)))
           (sym rw≡w)
           sound

  ; encodeInjective = λ {s₁} {s₂} eq →
      let w₁ = MembershipIndexedDFSMap.dfsWalkOfSkeleton map s₁
          w₂ = MembershipIndexedDFSMap.dfsWalkOfSkeleton map s₂
          i₁ = MembershipIndexedCanonicalWalkObjectList.walkIndex WE w₁
                 (MembershipIndexedDFSMap.dfsWalkMember map s₁)
          i₂ = MembershipIndexedCanonicalWalkObjectList.walkIndex WE w₂
                 (MembershipIndexedDFSMap.dfsWalkMember map s₂)
          w₁≡w₂ : w₁ ≡ w₂
          w₁≡w₂ = trans
            (sym (MembershipIndexedCanonicalWalkObjectList.walkIndexOf WE
                   (MembershipIndexedDFSMap.dfsWalkMember map s₁)))
            (trans
              (cong (MembershipIndexedCanonicalWalkObjectList.walkOfFin WE) eq)
              (MembershipIndexedCanonicalWalkObjectList.walkIndexOf WE
                (MembershipIndexedDFSMap.dfsWalkMember map s₂)))
      in MembershipIndexedDFSMap.dfsWalkInjective map w₁≡w₂
  }

------------------------------------------------------------------------
-- Combined concrete endpoint.  Skeleton semantics is normalized through
-- the existing concrete bridge; walk semantics stays membership-indexed.
------------------------------------------------------------------------

record P06ConcreteEnumerationEndpoint
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    skeletonSemantics : ConcreteCountSkeletonsSemantics G r n FBE
    walkSemantics : CountWalksMembershipSemantics G r (n + n)
    dfsMap :
      MembershipIndexedDFSMap
        (GC.countSkeletonsSemanticsToEnumeration
          (concreteCountSkeletonsSemanticsToCountSkeletonsSemantics
            skeletonSemantics))
        walkSemantics
    encodingData : ActualSkeletonEncodingData G r n
    encodingDataIsDerived :
      encodingData ≡
      membershipIndexedDFSMapToEncodingData dfsMap
    countBound :
      countSkeletons G r n ≤ pow (Δ * Δ) n

p06ConcreteEnumerationEndpoint :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  BoundedDegree G Δ →
  (skeletonSemantics : ConcreteCountSkeletonsSemantics G r n FBE) →
  (walkSemantics : CountWalksMembershipSemantics G r (n + n)) →
  (dfsMap :
    MembershipIndexedDFSMap
      (GC.countSkeletonsSemanticsToEnumeration
        (concreteCountSkeletonsSemanticsToCountSkeletonsSemantics
          skeletonSemantics))
      walkSemantics) →
  P06ConcreteEnumerationEndpoint {Δ = Δ} FBE
p06ConcreteEnumerationEndpoint bd skelSem walkSem dfsMap =
  let CE = GC.countSkeletonsSemanticsToEnumeration
             (concreteCountSkeletonsSemanticsToCountSkeletonsSemantics
               skelSem)
      encoding = membershipIndexedDFSMapToEncodingData
                   {CE = CE} {WE = walkSem} dfsMap
  in record
    { skeletonSemantics = skelSem
    ; walkSemantics = walkSem
    ; dfsMap = dfsMap
    ; encodingData = encoding
    ; encodingDataIsDerived = refl
    ; countBound = actualSkeletonCountBound bd encoding
    }

------------------------------------------------------------------------
-- Convenience projections for downstream additive consumers.
------------------------------------------------------------------------

p06ConcreteEnumerationEncodingData :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  BoundedDegree G Δ →
  (skeletonSemantics : ConcreteCountSkeletonsSemantics G r n FBE) →
  (walkSemantics : CountWalksMembershipSemantics G r (n + n)) →
  (dfsMap :
    MembershipIndexedDFSMap
      (GC.countSkeletonsSemanticsToEnumeration
        (concreteCountSkeletonsSemanticsToCountSkeletonsSemantics
          skeletonSemantics))
      walkSemantics) →
  ActualSkeletonEncodingData G r n
p06ConcreteEnumerationEncodingData {Δ = Δ} bd skelSem walkSem dfsMap =
  P06ConcreteEnumerationEndpoint.encodingData
    (p06ConcreteEnumerationEndpoint {Δ = Δ} bd skelSem walkSem dfsMap)

p06ConcreteEnumerationCountBound :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  BoundedDegree G Δ →
  (skeletonSemantics : ConcreteCountSkeletonsSemantics G r n FBE) →
  (walkSemantics : CountWalksMembershipSemantics G r (n + n)) →
  (dfsMap :
    MembershipIndexedDFSMap
      (GC.countSkeletonsSemanticsToEnumeration
        (concreteCountSkeletonsSemanticsToCountSkeletonsSemantics
          skeletonSemantics))
      walkSemantics) →
  countSkeletons G r n ≤ pow (Δ * Δ) n
p06ConcreteEnumerationCountBound {Δ = Δ} bd skelSem walkSem dfsMap =
  P06ConcreteEnumerationEndpoint.countBound
    (p06ConcreteEnumerationEndpoint {Δ = Δ} bd skelSem walkSem dfsMap)

------------------------------------------------------------------------
-- The concrete P06 endpoint.
--
-- `dfsMap` is intentionally explicit: the two count equalities identify
-- finite list lengths, while this witness supplies the skeleton-to-valid-
-- walk injection needed by `actualSkeletonCountBound`.
------------------------------------------------------------------------

P06ConcreteEnumerationTheorem :
  ∀ {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1))
  (CBNE : CanonicalBoundedNeighbourEnumeration G Δ)
  (bd : BoundedDegree G Δ)
  (skelEnum : ExplicitSkeletonCandidateEnumeration G r n FBE)
  (skelCount :
    countSkeletons G r n ≡
      length
        (ExplicitSkeletonCandidateEnumeration.candidates skelEnum))
  (walkCount :
    countWalks G r (n + n) ≡
      length
        (GC.generatedWalkVertexLists
          {r = r} {L = n + n}
          (CanonicalBoundedNeighbourEnumeration.bounded CBNE)))
  (dfsMap :
    MembershipIndexedDFSMap
      (explicitSkeletonEnumerationToCanonicalEnumeration skelEnum skelCount)
      (generatedWalksToMembershipIndexedWalkList CBNE walkCount)) →
  countSkeletons G r n ≤ pow (Δ * Δ) n
P06ConcreteEnumerationTheorem FBE CBNE bd skelEnum skelCount walkCount dfsMap =
  actualSkeletonCountBound bd
    (membershipIndexedDFSMapToEncodingData dfsMap)

------------------------------------------------------------------------
-- Closed numerical endpoint once neighbour-list degree agreement is owned.
-- The DFS map remains explicit: this refinement closes only the separate
-- `BoundedDegree` dependency.
------------------------------------------------------------------------

P06ConcreteEnumerationTheoremClosed :
  ∀ {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1))
  (CBNE : CanonicalBoundedNeighbourEnumerationWithDegree G Δ)
  (skelEnum : ExplicitSkeletonCandidateEnumeration G r n FBE)
  (skelCount :
    countSkeletons G r n ≡
      length
        (ExplicitSkeletonCandidateEnumeration.candidates skelEnum))
  (walkCount :
    countWalks G r (n + n) ≡
      length
        (GC.generatedWalkVertexLists
          {r = r} {L = n + n}
          (CanonicalBoundedNeighbourEnumeration.bounded
            (CanonicalBoundedNeighbourEnumerationWithDegree.enumeration CBNE))))
  (dfsMap :
    MembershipIndexedDFSMap
      (explicitSkeletonEnumerationToCanonicalEnumeration skelEnum skelCount)
      (generatedWalksToMembershipIndexedWalkList
        (CanonicalBoundedNeighbourEnumerationWithDegree.enumeration CBNE)
        walkCount)) →
  countSkeletons G r n ≤ pow (Δ * Δ) n
P06ConcreteEnumerationTheoremClosed FBE CBNE skelEnum skelCount walkCount dfsMap =
  P06ConcreteEnumerationTheorem
    FBE
    (CanonicalBoundedNeighbourEnumerationWithDegree.enumeration CBNE)
    (boundedDegreeFromCanonicalNeighbourEnumeration CBNE)
    skelEnum skelCount walkCount dfsMap
