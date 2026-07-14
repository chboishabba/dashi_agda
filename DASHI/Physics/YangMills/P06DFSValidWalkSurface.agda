module DASHI.Physics.YangMills.P06DFSValidWalkSurface where

------------------------------------------------------------------------
-- P06: the smallest honest DFS-valid-walk surface.
--
-- `DFSCover.w`/`dfsWalkRange` are coverage data only.  In particular, they
-- do not prove that the range starts at r, has consecutive graph edges, or
-- has the path length required by WalkObject.  This module therefore asks
-- for exactly one additional object: a genuine WalkObject together with its
-- vertex-list equality to the DFS range.  No postulate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; _+_; _*_; _≤_; zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using ( +-suc; ≤-trans; ≤-refl
                                    ; *-mono-≤; *-identityˡ )
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; CanonicalSkeletonEnumeration
        ; CanonicalSkeletonObject
        ; CountWalksMembershipSemantics
        ; DFSCover
        ; BoundedNeighbourEnumeration
        ; WalkObject
        ; walkObjectVertices
        ; dfsWalkRange
        ; canonicalDFSObjectSound
        ; dfsWalkRangeMemberFromWalkObject
        ; generatedWalkVertexLists
        ; generatedWalkVertexListComplete
        ; MembershipIndexedCanonicalWalkObjectList
        ; SameVertexSet
        ; _∈_
        ; BoundedDegree
        ; P06a2dBoundedDegreeWalkCount-pow
        ; ≤-succ
        )
open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)
open import DASHI.Physics.ClaySupportingPolymerCounting using (inj⇒≤)

open import DASHI.Physics.YangMills.P06ConcreteEnumerationEndpoint
         using (MembershipIndexedDFSMap)
open import DASHI.Physics.YangMills.P06ConstructiveSpanningTreeDFS as CDFS
  using ( p06DFSWalkLength
        ; CanonicalSkeletonExactDFS
        ; UndirectedGraphStructure
        ; undirectedGraphGivesSkeletonSymmetry
        ; BidirectionalCanonicalDFSInput
        ; bidirectionalCanonicalDFSInputToExactDFS
        ; dfsTour
        ; dfsTourPath
        )
open import DASHI.Physics.YangMills.P06PathUnionSpanningTreeClosure
  using (pathUnionCanonicalSkeletonExactDFS)

------------------------------------------------------------------------
-- A valid walk witnessing one DFS range.
------------------------------------------------------------------------

record DFSValidWalkWitness
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  (obj : CanonicalSkeletonObject G r n) : Set₁ where
  field
    walk : WalkObject G r (n + n)

    -- The WalkObject carries the actual nonempty/rooted/consecutive/length
    -- evidence through its Path.  This equality identifies its vertex
    -- sequence with the current DFS range; it does not treat DFSCover.w as a
    -- path.
    vertices-is-dfsRange :
      walkObjectVertices walk ≡ dfsWalkRange obj

------------------------------------------------------------------------
-- Exact-length replacement.  Unlike the compatibility witness above this
-- does not identify a path with the legacy `dfsWalkRange`, whose only
-- available construction is still the opaque TreeDFSWalk traversal.
------------------------------------------------------------------------

record DFSValidWalkWitnessAtLength
  {G : Graph} {r : Graph.Vertex G} {n L : ℕ}
  (obj : CanonicalSkeletonObject G r n) : Set₁ where
  field
    walk : WalkObject G r L
    range-is-skeleton :
      SameVertexSet
        (walkObjectVertices walk)
        (CanonicalSkeletonObject.skelVertices obj)

sameVertexSetFromListEquality
  : {A : Set} {xs ys : List A}
  → xs ≡ ys
  → SameVertexSet xs ys
sameVertexSetFromListEquality refl =
  (λ x∈ → x∈) , (λ x∈ → x∈)

sameVertexSetSym
  : {A : Set} {xs ys : List A}
  → SameVertexSet xs ys
  → SameVertexSet ys xs
sameVertexSetSym sv = proj₂ sv , proj₁ sv

sameVertexSetTrans
  : {A : Set} {xs ys zs : List A}
  → SameVertexSet xs ys
  → SameVertexSet ys zs
  → SameVertexSet xs zs
sameVertexSetTrans sv₁ sv₂ =
  (λ x∈ → proj₁ sv₂ (proj₁ sv₁ x∈)) ,
  (λ z∈ → proj₂ sv₁ (proj₂ sv₂ z∈))

canonicalSkeletonExactDFSToValidWalk :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {obj : CanonicalSkeletonObject G r n} →
  CDFS.CanonicalSkeletonExactDFS obj →
  DFSValidWalkWitnessAtLength {L = p06DFSWalkLength n} obj
canonicalSkeletonExactDFSToValidWalk {obj = obj} exact = record
  { walk = record
      { endpoint = _
      ; path = dfsTourPath
          (CDFS.CanonicalSkeletonExactDFS.tourInvariant exact)
      ; length-is = CDFS.CanonicalSkeletonExactDFS.tourLength exact
      }
  ; range-is-skeleton = CDFS.CanonicalSkeletonExactDFS.tourRange exact
  }

------------------------------------------------------------------------
-- Exact-length generated membership and injection.  These are separate
-- from the legacy n+n map below: a 2(n-1)-edge Euler tour cannot be fed to
-- an exact-length n+n walk object without an invalid padding argument.
------------------------------------------------------------------------

dfsValidWalkAtLengthGeneratedMember
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n L : ℕ}
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (obj : CanonicalSkeletonObject G r n)
  → (dw : DFSValidWalkWitnessAtLength {L = L} obj)
  → walkObjectVertices (DFSValidWalkWitnessAtLength.walk dw)
      ∈ generatedWalkVertexLists {r = r} {L = L} BNE
dfsValidWalkAtLengthGeneratedMember BNE obj dw
  with generatedWalkVertexListComplete
         BNE
         (DFSValidWalkWitnessAtLength.walk dw)
... | vs , vs∈ , vs≡ =
  subst
    (λ xs → xs ∈ generatedWalkVertexLists {r = _} {L = _} BNE)
    vs≡
    vs∈

dfsWalkVerticesInjectiveAtLength
  : {G : Graph} {r : Graph.Vertex G} {n L : ℕ}
  → (CE : CanonicalSkeletonEnumeration G r n)
  → (walkWitness :
      (s : Fin (GC.countSkeletons G r n)) →
      DFSValidWalkWitnessAtLength {L = L}
        (CanonicalSkeletonEnumeration.objectOf CE s))
  → ∀ {s₁ s₂}
  → walkObjectVertices
      (DFSValidWalkWitnessAtLength.walk (walkWitness s₁))
      ≡
    walkObjectVertices
      (DFSValidWalkWitnessAtLength.walk (walkWitness s₂))
  → s₁ ≡ s₂
dfsWalkVerticesInjectiveAtLength CE walkWitness {s₁} {s₂} walkEq =
  GC.canonicalSameVertexSetImpliesSameIndex CE skelSVS
  where
    walkSVS = sameVertexSetFromListEquality walkEq

    sound₁ = DFSValidWalkWitnessAtLength.range-is-skeleton (walkWitness s₁)
    sound₂ = DFSValidWalkWitnessAtLength.range-is-skeleton (walkWitness s₂)

    skelSVS =
      sameVertexSetTrans
        (sameVertexSetSym sound₁)
        (sameVertexSetTrans walkSVS sound₂)

------------------------------------------------------------------------
-- Constructive consequences of the witness.
------------------------------------------------------------------------

dfsValidWalkWitnessMember
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (obj : CanonicalSkeletonObject G r n)
  → DFSValidWalkWitness obj
  → dfsWalkRange obj ∈
      generatedWalkVertexLists {r = r} {L = n + n} BNE
dfsValidWalkWitnessMember BNE obj witness =
  dfsWalkRangeMemberFromWalkObject
    BNE obj
    (DFSValidWalkWitness.walk witness)
    (DFSValidWalkWitness.vertices-is-dfsRange witness)

dfsValidWalkWitnessSound
  : {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  → (obj : CanonicalSkeletonObject G r n)
  → (witness : DFSValidWalkWitness obj)
  → SameVertexSet
      (walkObjectVertices (DFSValidWalkWitness.walk witness))
      (CanonicalSkeletonObject.skelVertices obj)
dfsValidWalkWitnessSound obj witness =
  subst
    (λ xs → SameVertexSet xs
      (CanonicalSkeletonObject.skelVertices obj))
    (sym (DFSValidWalkWitness.vertices-is-dfsRange witness))
    (canonicalDFSObjectSound obj)

------------------------------------------------------------------------
-- Generated-list membership and canonical injectivity.
------------------------------------------------------------------------

dfsValidWalkGeneratedMember
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (obj : CanonicalSkeletonObject G r n)
  → (dw : DFSValidWalkWitness obj)
  → walkObjectVertices (DFSValidWalkWitness.walk dw)
      ∈ generatedWalkVertexLists {r = r} {L = n + n} BNE
dfsValidWalkGeneratedMember BNE obj dw
  with generatedWalkVertexListComplete
         BNE
         (DFSValidWalkWitness.walk dw)
... | vs , vs∈ , vs≡ =
  subst
    (λ xs → xs ∈ generatedWalkVertexLists {r = _} {L = _} BNE)
    vs≡
    vs∈

dfsWalkVerticesInjective
  : {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  → (CE : CanonicalSkeletonEnumeration G r n)
  → (walkWitness :
      (s : Fin (GC.countSkeletons G r n)) →
      DFSValidWalkWitness
        (CanonicalSkeletonEnumeration.objectOf CE s))
  → ∀ {s₁ s₂}
  → walkObjectVertices
      (DFSValidWalkWitness.walk (walkWitness s₁))
      ≡
    walkObjectVertices
      (DFSValidWalkWitness.walk (walkWitness s₂))
  → s₁ ≡ s₂
dfsWalkVerticesInjective CE walkWitness {s₁} {s₂} walkEq =
  GC.canonicalSameVertexSetImpliesSameIndex CE skelSVS
  where
    walkSVS :
      SameVertexSet
        (walkObjectVertices
          (DFSValidWalkWitness.walk (walkWitness s₁)))
        (walkObjectVertices
          (DFSValidWalkWitness.walk (walkWitness s₂)))
    walkSVS = sameVertexSetFromListEquality walkEq

    sound₁ :
      SameVertexSet
        (walkObjectVertices
          (DFSValidWalkWitness.walk (walkWitness s₁)))
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s₁))
    sound₁ = dfsValidWalkWitnessSound _ (walkWitness s₁)

    sound₂ :
      SameVertexSet
        (walkObjectVertices
          (DFSValidWalkWitness.walk (walkWitness s₂)))
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s₂))
    sound₂ = dfsValidWalkWitnessSound _ (walkWitness s₂)

    skelSVS :
      SameVertexSet
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s₁))
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s₂))
    skelSVS =
      sameVertexSetTrans
        (sameVertexSetSym sound₁)
        (sameVertexSetTrans walkSVS sound₂)

------------------------------------------------------------------------
-- Compatibility between a membership-indexed semantic list and the
-- constructive generated list.  For the generated semantic constructor this
-- is normally `refl`; keeping it as a field prevents an accidental claim that
-- arbitrary CountWalksMembershipSemantics uses the generated list.
------------------------------------------------------------------------

record GeneratedWalkSemanticsCompatibility
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {L : ℕ}
  (BNE : BoundedNeighbourEnumeration G Δ)
  (WE : CountWalksMembershipSemantics G r L) : Set₁ where
  field
    walks-is-generated :
      MembershipIndexedCanonicalWalkObjectList.walks WE
        ≡ generatedWalkVertexLists {r = r} {L = L} BNE

generatedMemberToSemanticsMember
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {L : ℕ}
  → {BNE : BoundedNeighbourEnumeration G Δ}
  → {WE : CountWalksMembershipSemantics G r L}
  → GeneratedWalkSemanticsCompatibility BNE WE
  → (w : List (Graph.Vertex G))
  → w ∈ generatedWalkVertexLists {r = r} {L = L} BNE
  → w ∈ MembershipIndexedCanonicalWalkObjectList.walks WE
generatedMemberToSemanticsMember compatibility w member =
  subst
    (λ xs → w ∈ xs)
    (sym (GeneratedWalkSemanticsCompatibility.walks-is-generated compatibility))
    member

------------------------------------------------------------------------
-- The exact Euler-tour analogue of DFSValidWalkMapWitness.  It deliberately
-- has an arbitrary length parameter, so the P06 numerical endpoint can use
-- 2(n-1) without pretending that a tour has n+n graph edges.
------------------------------------------------------------------------

record DFSValidWalkMapWitnessAtLength
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n L : ℕ}
  (CE : CanonicalSkeletonEnumeration G r n)
  (BNE : BoundedNeighbourEnumeration G Δ)
  (WE : CountWalksMembershipSemantics G r L) : Set₁ where
  field
    walkWitness :
      (s : Fin (GC.countSkeletons G r n)) →
      DFSValidWalkWitnessAtLength {L = L}
        (CanonicalSkeletonEnumeration.objectOf CE s)

    semanticsCompatibility : GeneratedWalkSemanticsCompatibility BNE WE

    walkInjective :
      ∀ {s₁ s₂} →
      walkObjectVertices
        (DFSValidWalkWitnessAtLength.walk (walkWitness s₁))
        ≡
      walkObjectVertices
        (DFSValidWalkWitnessAtLength.walk (walkWitness s₂)) →
      s₁ ≡ s₂

canonicalSkeletonEnumerationToOwnedDFSValidWalkMapAtLength
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → (CE : CanonicalSkeletonEnumeration G r n)
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (WE : CountWalksMembershipSemantics G r (p06DFSWalkLength n))
  → GeneratedWalkSemanticsCompatibility BNE WE
  → (input :
      (s : Fin (GC.countSkeletons G r n)) →
      BidirectionalCanonicalDFSInput
        (CanonicalSkeletonEnumeration.objectOf CE s))
  → DFSValidWalkMapWitnessAtLength CE BNE WE
canonicalSkeletonEnumerationToOwnedDFSValidWalkMapAtLength
  CE BNE WE compat input =
  record
    { walkWitness = λ s →
        canonicalSkeletonExactDFSToValidWalk
          (bidirectionalCanonicalDFSInputToExactDFS (input s))
    ; semanticsCompatibility = compat
    ; walkInjective =
        dfsWalkVerticesInjectiveAtLength CE
          (λ s →
            canonicalSkeletonExactDFSToValidWalk
              (bidirectionalCanonicalDFSInputToExactDFS (input s)))
    }

------------------------------------------------------------------------
-- The path-union spanning-tree construction removes the legacy
-- `BidirectionalCanonicalDFSInput` assumption: connected canonical
-- skeletons are reified internally, while graph-wide undirectedness is
-- restricted to the skeleton carrier at each use.
------------------------------------------------------------------------

canonicalSkeletonEnumerationToPathUnionDFSValidWalkMapAtLength
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → (CE : CanonicalSkeletonEnumeration G r n)
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (WE : CountWalksMembershipSemantics G r (p06DFSWalkLength n))
  → GeneratedWalkSemanticsCompatibility BNE WE
  → UndirectedGraphStructure G
  → DFSValidWalkMapWitnessAtLength CE BNE WE
canonicalSkeletonEnumerationToPathUnionDFSValidWalkMapAtLength
  {G = G} {r = r} {n = n} CE BNE WE compat undirected =
  record
    { walkWitness = walkWitness
    ; semanticsCompatibility = compat
    ; walkInjective = dfsWalkVerticesInjectiveAtLength CE walkWitness
    }
  where
  walkWitness :
    (s : Fin (GC.countSkeletons G r n)) →
    DFSValidWalkWitnessAtLength {L = p06DFSWalkLength n}
      (CanonicalSkeletonEnumeration.objectOf CE s)
  walkWitness s =
    canonicalSkeletonExactDFSToValidWalk
      (pathUnionCanonicalSkeletonExactDFS
        (CanonicalSkeletonEnumeration.objectOf CE s)
        (undirectedGraphGivesSkeletonSymmetry undirected))

------------------------------------------------------------------------
-- Length-parametric counting bridge.  This is the numerical consequence
-- of the exact DFS injection before the final comparison
-- 2 (n ∸ 1) ≤ 2 n.  Keeping it here avoids pretending that the Euler tour
-- inhabits the legacy exact-length `n + n` walk semantics.
------------------------------------------------------------------------

dfsValidWalkMapAtLengthCountBound
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n L : ℕ}
  → {CE : CanonicalSkeletonEnumeration G r n}
  → {BNE : BoundedNeighbourEnumeration G Δ}
  → {WE : CountWalksMembershipSemantics G r L}
  → BoundedDegree G Δ
  → DFSValidWalkMapWitnessAtLength CE BNE WE
  → GC.countSkeletons G r n ≤ pow Δ L
dfsValidWalkMapAtLengthCountBound
  {G = G} {Δ = Δ} {r = r} {L = L} {CE = CE} {BNE = BNE} {WE = WE}
  degree witness =
  ≤-trans skeletonLeWalks
    (P06a2dBoundedDegreeWalkCount-pow degree r L)
  where
  encode : Fin (GC.countSkeletons G r _) → Fin (GC.countWalks G r L)
  encode s =
    MembershipIndexedCanonicalWalkObjectList.walkIndex WE
      (walkObjectVertices
        (DFSValidWalkWitnessAtLength.walk
          (DFSValidWalkMapWitnessAtLength.walkWitness witness s)))
      (generatedMemberToSemanticsMember
        (DFSValidWalkMapWitnessAtLength.semanticsCompatibility witness)
        (walkObjectVertices
          (DFSValidWalkWitnessAtLength.walk
            (DFSValidWalkMapWitnessAtLength.walkWitness witness s)))
        (dfsValidWalkAtLengthGeneratedMember
          BNE
          (CanonicalSkeletonEnumeration.objectOf CE s)
          (DFSValidWalkMapWitnessAtLength.walkWitness witness s)))

  encodeInjective :
    ∀ {s₁ s₂} → encode s₁ ≡ encode s₂ → s₁ ≡ s₂
  encodeInjective {s₁} {s₂} equalIndices =
    DFSValidWalkMapWitnessAtLength.walkInjective witness
      (trans
        (sym
          (MembershipIndexedCanonicalWalkObjectList.walkIndexOf WE
            (generatedMemberToSemanticsMember
              (DFSValidWalkMapWitnessAtLength.semanticsCompatibility witness)
              (walkObjectVertices
                (DFSValidWalkWitnessAtLength.walk
                  (DFSValidWalkMapWitnessAtLength.walkWitness witness s₁)))
              (dfsValidWalkAtLengthGeneratedMember
                BNE
                (CanonicalSkeletonEnumeration.objectOf CE s₁)
                (DFSValidWalkMapWitnessAtLength.walkWitness witness s₁)))))
        (trans
          (cong
            (MembershipIndexedCanonicalWalkObjectList.walkOfFin WE)
            equalIndices)
          (MembershipIndexedCanonicalWalkObjectList.walkIndexOf WE
            (generatedMemberToSemanticsMember
              (DFSValidWalkMapWitnessAtLength.semanticsCompatibility witness)
              (walkObjectVertices
                (DFSValidWalkWitnessAtLength.walk
                  (DFSValidWalkMapWitnessAtLength.walkWitness witness s₂)))
              (dfsValidWalkAtLengthGeneratedMember
                BNE
                (CanonicalSkeletonEnumeration.objectOf CE s₂)
                (DFSValidWalkMapWitnessAtLength.walkWitness witness s₂))))))

  skeletonLeWalks : GC.countSkeletons G r _ ≤ GC.countWalks G r L
  skeletonLeWalks = inj⇒≤ {encode = encode} encodeInjective

------------------------------------------------------------------------
-- The final exponent comparison for the natural 2(n-1)-edge Euler tour.
-- It is kept separate from the graph argument: Δ ≥ 1 is exactly the
-- hypothesis needed for monotonicity in the exponent.
------------------------------------------------------------------------

p06DFSWalkLength≤double : (n : ℕ) →
  p06DFSWalkLength n ≤ n + n
p06DFSWalkLength≤double zero = z≤n
p06DFSWalkLength≤double (suc n) =
  subst
    (λ z → n + n ≤ suc z)
    (sym (+-suc n n))
    (≤-trans (GC.≤-succ (n + n)) (GC.≤-succ (suc (n + n))))

powAtLeastOne :
  (b : ℕ) → 1 ≤ b → (k : ℕ) → 1 ≤ pow b k
powAtLeastOne b one≤b zero = ≤-refl
powAtLeastOne b one≤b (suc k) =
  ≤-trans
    (subst (λ z → z ≤ b * pow b k) (*-identityˡ 1)
      (*-mono-≤ one≤b (powAtLeastOne b one≤b k)))
    ≤-refl

powExponentMonotoneFromOne :
  (b : ℕ) → 1 ≤ b → {a c : ℕ} → a ≤ c → pow b a ≤ pow b c
powExponentMonotoneFromOne b one≤b {zero} {c} z≤n =
  powAtLeastOne b one≤b c
powExponentMonotoneFromOne b one≤b {suc a} {suc c} (s≤s a≤c) =
  *-mono-≤ (≤-refl {b}) (powExponentMonotoneFromOne b one≤b a≤c)

p06DFSWalkPowerBound :
  {Δ n : ℕ} → 1 ≤ Δ →
  pow Δ (p06DFSWalkLength n) ≤ pow (Δ * Δ) n
p06DFSWalkPowerBound {Δ} {n} one≤Δ =
  ≤-trans
    (powExponentMonotoneFromOne Δ one≤Δ (p06DFSWalkLength≤double n))
    (subst (pow Δ (n + n) ≤_) (GC.pow-double Δ n) ≤-refl)

------------------------------------------------------------------------
-- Owned P06 graph-theoretic closure at the natural Euler-tour length.
-- The only remaining inputs are finite enumeration semantics (CE/WE),
-- a bounded-degree witness, and the local undirectedness condition.
------------------------------------------------------------------------

pathUnionConcreteEnumerationBound :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → (CE : CanonicalSkeletonEnumeration G r n)
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (WE : CountWalksMembershipSemantics G r (p06DFSWalkLength n))
  → GeneratedWalkSemanticsCompatibility BNE WE
  → UndirectedGraphStructure G
  → BoundedDegree G Δ
  → 1 ≤ Δ
  → GC.countSkeletons G r n ≤ pow (Δ * Δ) n
pathUnionConcreteEnumerationBound
  {n = n} CE BNE WE compat undirected degree one≤Δ =
  ≤-trans
    (dfsValidWalkMapAtLengthCountBound degree ownedMap)
    (p06DFSWalkPowerBound {n = n} one≤Δ)
  where
  ownedMap : DFSValidWalkMapWitnessAtLength CE BNE WE
  ownedMap = canonicalSkeletonEnumerationToPathUnionDFSValidWalkMapAtLength
    CE BNE WE compat undirected

------------------------------------------------------------------------
-- A map-level witness.  The only obligations not derivable from a valid
-- WalkObject are semantic-list compatibility and index injectivity.  They
-- remain explicit instead of being smuggled in through DFSCover.
------------------------------------------------------------------------

record DFSValidWalkMapWitness
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (CE : CanonicalSkeletonEnumeration G r n)
  (BNE : BoundedNeighbourEnumeration G Δ)
  (WE : CountWalksMembershipSemantics G r (n + n)) : Set₁ where
  field
    walkWitness :
      (s : Fin (GC.countSkeletons G r n))
      → DFSValidWalkWitness
          (CanonicalSkeletonEnumeration.objectOf CE s)

    semanticsCompatibility :
      GeneratedWalkSemanticsCompatibility BNE WE

    walkInjective :
      ∀ {s₁ s₂}
      → walkObjectVertices (DFSValidWalkWitness.walk
          (walkWitness s₁))
          ≡
        walkObjectVertices (DFSValidWalkWitness.walk
          (walkWitness s₂))
      → s₁ ≡ s₂

------------------------------------------------------------------------
-- Constructive adapter to the endpoint's MembershipIndexedDFSMap.
------------------------------------------------------------------------

dfsValidWalkMapToMembershipIndexedDFSMap
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → {CE : CanonicalSkeletonEnumeration G r n}
  → {BNE : BoundedNeighbourEnumeration G Δ}
  → {WE : CountWalksMembershipSemantics G r (n + n)}
  → DFSValidWalkMapWitness CE BNE WE
  → MembershipIndexedDFSMap CE WE
dfsValidWalkMapToMembershipIndexedDFSMap {CE = CE} {BNE = BNE} {WE = WE} witness =
  record
  { dfsWalkOfSkeleton = λ s →
      walkObjectVertices
        (DFSValidWalkWitness.walk
          (DFSValidWalkMapWitness.walkWitness witness s))

  ; dfsWalkMember = λ s →
      subst
        (λ xs → xs ∈ MembershipIndexedCanonicalWalkObjectList.walks WE)
        (sym (DFSValidWalkWitness.vertices-is-dfsRange
          (DFSValidWalkMapWitness.walkWitness witness s)))
        (generatedMemberToSemanticsMember
          (DFSValidWalkMapWitness.semanticsCompatibility witness)
          (dfsWalkRange
            (CanonicalSkeletonEnumeration.objectOf CE s))
          (dfsValidWalkWitnessMember
            BNE
            (CanonicalSkeletonEnumeration.objectOf CE s)
            (DFSValidWalkMapWitness.walkWitness witness s)))

  ; dfsWalkSound = λ s →
      dfsValidWalkWitnessSound
        (CanonicalSkeletonEnumeration.objectOf CE s)
        (DFSValidWalkMapWitness.walkWitness witness s)

  ; dfsWalkInjective =
      DFSValidWalkMapWitness.walkInjective witness
  }

------------------------------------------------------------------------
-- Integrated packaging once the genuine WalkObject construction is owned.
-- The remaining input is deliberately only the per-skeleton valid-walk
-- constructor; membership and injectivity are derived here.
------------------------------------------------------------------------

canonicalSkeletonEnumerationToDFSValidWalkMapWitnessFromWalks
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → (CE : CanonicalSkeletonEnumeration G r n)
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (WE : CountWalksMembershipSemantics G r (n + n))
  → GeneratedWalkSemanticsCompatibility BNE WE
  → (walkWitness :
      (s : Fin (GC.countSkeletons G r n)) →
      DFSValidWalkWitness
        (CanonicalSkeletonEnumeration.objectOf CE s))
  → DFSValidWalkMapWitness CE BNE WE
canonicalSkeletonEnumerationToDFSValidWalkMapWitnessFromWalks
  CE BNE WE compat walkWitness =
  record
  { walkWitness = walkWitness
  ; semanticsCompatibility = compat
  ; walkInjective = dfsWalkVerticesInjective CE walkWitness
  }

------------------------------------------------------------------------
-- Direct range-membership adapter, useful before a full semantic WE exists.
------------------------------------------------------------------------

record DFSRangeMembershipWitness
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (BNE : BoundedNeighbourEnumeration G Δ)
  (obj : CanonicalSkeletonObject G r n) : Set₁ where
  field
    validWalk : DFSValidWalkWitness obj

dfsRangeMembershipWitnessMember
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → {BNE : BoundedNeighbourEnumeration G Δ}
  → {obj : CanonicalSkeletonObject G r n}
  → DFSRangeMembershipWitness BNE obj
  → dfsWalkRange obj ∈
      generatedWalkVertexLists {r = r} {L = n + n} BNE
dfsRangeMembershipWitnessMember {BNE = BNE} {obj = obj} witness =
  dfsValidWalkWitnessMember
    BNE obj
    (DFSRangeMembershipWitness.validWalk witness)

------------------------------------------------------------------------
-- DFSCover remains an explicitly named coverage input.  No conversion is
-- supplied: its length/coverage fields are insufficient for a WalkObject.
------------------------------------------------------------------------

DFSCoverRange
  : {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} {m : ℕ}
  → DFSCover G r X m
  → List (Graph.Vertex G)
DFSCoverRange = DFSCover.w
