module DASHI.Physics.Moonshine.PrimeLaneVOAEquivalenceReceiptSurface where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Prime-lane VOA equivalence candidate receipt surface.
--
-- This module records the candidate bridge requested for composition by a
-- later LaneDimension theorem surface:
--
--   G2 + G4 + Ogg genus-zero/no-ghost compatibility identify the DASHI
--   prime-lane algebra with the Monster VOA orbifold V^natural/<g_p>.
--
-- It is deliberately a candidate/receipt surface only.  It does not construct
-- a VOA, construct the Monster action, prove the no-ghost theorem, prove Ogg
-- genus-zero Moonshine, prove G2 or G4, or promote a lane-dimension theorem.

data PrimeLaneVOAEquivalenceStatus : Set where
  candidateReceiptOnlyNoTheoremPromotion :
    PrimeLaneVOAEquivalenceStatus

data PrimeLaneVOAEquivalenceIntegrationLane : Set where
  p2BDASHIPrimeLaneEquivInternalGap :
    PrimeLaneVOAEquivalenceIntegrationLane

data PrimeLaneVOAEquivalencePromotionAuthorityToken : Set where

data PrimeLaneVOAEquivalenceBoundary : Set where
  boundaryNoVOAConstruction :
    PrimeLaneVOAEquivalenceBoundary

  boundaryNoMonsterActionConstruction :
    PrimeLaneVOAEquivalenceBoundary

  boundaryG2CompatibilityIsInput :
    PrimeLaneVOAEquivalenceBoundary

  boundaryG4CompatibilityIsInput :
    PrimeLaneVOAEquivalenceBoundary

  boundaryOggNoGhostCompatibilityIsInput :
    PrimeLaneVOAEquivalenceBoundary

  boundaryNoLaneDimensionPromotion :
    PrimeLaneVOAEquivalenceBoundary

canonicalPrimeLaneVOAEquivalenceBoundaries :
  List PrimeLaneVOAEquivalenceBoundary
canonicalPrimeLaneVOAEquivalenceBoundaries =
  boundaryNoVOAConstruction
  ∷ boundaryNoMonsterActionConstruction
  ∷ boundaryG2CompatibilityIsInput
  ∷ boundaryG4CompatibilityIsInput
  ∷ boundaryOggNoGhostCompatibilityIsInput
  ∷ boundaryNoLaneDimensionPromotion
  ∷ []

data G2PrimeLaneCompatibilityReceipt : Lane.MonsterPrimeLane → Set where
  g2PrimeLaneCompatibilityCandidate :
    (p : Lane.MonsterPrimeLane) →
    G2PrimeLaneCompatibilityReceipt p

data G4PrimeLaneIndependenceCompatibilityReceipt :
  Lane.MonsterPrimeLane →
  Set where
  g4PrimeLaneIndependenceCompatibilityCandidate :
    (p : Lane.MonsterPrimeLane) →
    G4PrimeLaneIndependenceCompatibilityReceipt p

data OggGenusZeroNoGhostCompatibilityReceipt :
  Lane.MonsterPrimeLane →
  Set where
  oggGenusZeroNoGhostCompatibilityCandidate :
    (p : Lane.MonsterPrimeLane) →
    OggGenusZeroNoGhostCompatibilityReceipt p

data DASHIPrimeLaneAlgebra : Lane.MonsterPrimeLane → Set where
  dashiPrimeLaneAlgebraCandidate :
    (p : Lane.MonsterPrimeLane) →
    DASHIPrimeLaneAlgebra p

data MonsterVOAOrbifold : Lane.MonsterPrimeLane → Set where
  vNaturalOrbifoldBy-gp :
    (p : Lane.MonsterPrimeLane) →
    MonsterVOAOrbifold p

record CandidateEquivalence (A B : Set) : Set where
  constructor candidateEquivalence
  field
    to :
      A →
      B

    from :
      B →
      A

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promotedTheorem :
      Bool

    promotedTheoremIsFalse :
      promotedTheorem ≡ false

open CandidateEquivalence public

dashiPrimeLaneToMonsterVOAOrbifold :
  (p : Lane.MonsterPrimeLane) →
  DASHIPrimeLaneAlgebra p →
  MonsterVOAOrbifold p
dashiPrimeLaneToMonsterVOAOrbifold p _ =
  vNaturalOrbifoldBy-gp p

monsterVOAOrbifoldToDASHIPrimeLane :
  (p : Lane.MonsterPrimeLane) →
  MonsterVOAOrbifold p →
  DASHIPrimeLaneAlgebra p
monsterVOAOrbifoldToDASHIPrimeLane p _ =
  dashiPrimeLaneAlgebraCandidate p

candidateDASHIPrimeLaneAlgebraMonsterVOAOrbifoldEquiv :
  (p : Lane.MonsterPrimeLane) →
  CandidateEquivalence
    (DASHIPrimeLaneAlgebra p)
    (MonsterVOAOrbifold p)
candidateDASHIPrimeLaneAlgebraMonsterVOAOrbifoldEquiv p =
  candidateEquivalence
    (dashiPrimeLaneToMonsterVOAOrbifold p)
    (monsterVOAOrbifoldToDASHIPrimeLane p)
    true
    refl
    false
    refl

record DASHIPrimeLaneEquiv (p : Lane.MonsterPrimeLane) : Setω where
  field
    status :
      PrimeLaneVOAEquivalenceStatus

    lane :
      Lane.MonsterPrimeLane

    laneIsInput :
      lane ≡ p

    primeValue :
      Nat

    primeValueIsLaneValue :
      primeValue ≡ Lane.monsterPrimeLaneToNat p

    dashiPrimeLaneAlgebra :
      DASHIPrimeLaneAlgebra p

    monsterVOAOrbifold :
      MonsterVOAOrbifold p

    g2Compatibility :
      G2PrimeLaneCompatibilityReceipt p

    g4Compatibility :
      G4PrimeLaneIndependenceCompatibilityReceipt p

    oggGenusZeroNoGhostCompatibility :
      OggGenusZeroNoGhostCompatibilityReceipt p

    algebraOrbifoldCandidateEquivalence :
      CandidateEquivalence
        (DASHIPrimeLaneAlgebra p)
        (MonsterVOAOrbifold p)

    candidateBridgeName :
      String

    candidateBridgeNameIsDASHIPrimeLaneEquiv :
      candidateBridgeName ≡ "DASHIPrimeLaneEquiv"

    identifiesDASHIPrimeLaneAlgebraWithVNaturalOrbifold :
      Bool

    identifiesDASHIPrimeLaneAlgebraWithVNaturalOrbifoldIsTrue :
      identifiesDASHIPrimeLaneAlgebraWithVNaturalOrbifold ≡ true

    p2BIntegrationLane :
      PrimeLaneVOAEquivalenceIntegrationLane

    internalMathGap :
      Bool

    internalMathGapIsTrue :
      internalMathGap ≡ true

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    laneDimensionReusableInput :
      Bool

    laneDimensionReusableInputIsTrue :
      laneDimensionReusableInput ≡ true

    boundaries :
      List PrimeLaneVOAEquivalenceBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalPrimeLaneVOAEquivalenceBoundaries

    noPromotionWithoutAuthority :
      PrimeLaneVOAEquivalencePromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open DASHIPrimeLaneEquiv public

canonicalDASHIPrimeLaneEquiv :
  (p : Lane.MonsterPrimeLane) →
  DASHIPrimeLaneEquiv p
canonicalDASHIPrimeLaneEquiv p =
  record
    { status =
        candidateReceiptOnlyNoTheoremPromotion
    ; lane =
        p
    ; laneIsInput =
        refl
    ; primeValue =
        Lane.monsterPrimeLaneToNat p
    ; primeValueIsLaneValue =
        refl
    ; dashiPrimeLaneAlgebra =
        dashiPrimeLaneAlgebraCandidate p
    ; monsterVOAOrbifold =
        vNaturalOrbifoldBy-gp p
    ; g2Compatibility =
        g2PrimeLaneCompatibilityCandidate p
    ; g4Compatibility =
        g4PrimeLaneIndependenceCompatibilityCandidate p
    ; oggGenusZeroNoGhostCompatibility =
        oggGenusZeroNoGhostCompatibilityCandidate p
    ; algebraOrbifoldCandidateEquivalence =
        candidateDASHIPrimeLaneAlgebraMonsterVOAOrbifoldEquiv p
    ; candidateBridgeName =
        "DASHIPrimeLaneEquiv"
    ; candidateBridgeNameIsDASHIPrimeLaneEquiv =
        refl
    ; identifiesDASHIPrimeLaneAlgebraWithVNaturalOrbifold =
        true
    ; identifiesDASHIPrimeLaneAlgebraWithVNaturalOrbifoldIsTrue =
        refl
    ; p2BIntegrationLane =
        p2BDASHIPrimeLaneEquivInternalGap
    ; internalMathGap =
        true
    ; internalMathGapIsTrue =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; laneDimensionReusableInput =
        true
    ; laneDimensionReusableInputIsTrue =
        refl
    ; boundaries =
        canonicalPrimeLaneVOAEquivalenceBoundaries
    ; boundariesAreCanonical =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "DASHIPrimeLaneEquiv is a candidate receipt bridge, not a promoted equivalence theorem"
        ∷ "The bridge identifies the DASHI prime-lane algebra target with V^natural/<g_p> only under explicit G2, G4, and Ogg genus-zero/no-ghost compatibility inputs"
        ∷ "G2 compatibility is consumed as a receipt-shaped candidate input; it is not proved in this module"
        ∷ "G4 prime-lane independence compatibility is consumed as a receipt-shaped candidate input; it is not proved in this module"
        ∷ "Ogg genus-zero/no-ghost compatibility is consumed as a receipt-shaped candidate input; no Moonshine theorem or no-ghost theorem is proved here"
        ∷ "P2-B exports DASHIPrimeLaneEquiv as an internal math-gap bridge until the P2-A DLM authority and downstream composition surface consume it"
        ∷ "The exported bridge is intended as reusable input for a later LaneDimension theorem surface"
        ∷ "No VOA construction, Monster action construction, orbifold theorem, DHR sector computation, or lane-dimension promotion follows from this receipt"
        ∷ []
    }

DASHIPrimeLaneEquivForLane :
  Lane.MonsterPrimeLane →
  Setω
DASHIPrimeLaneEquivForLane =
  DASHIPrimeLaneEquiv

dashiPrimeLaneEquivForLane :
  (p : Lane.MonsterPrimeLane) →
  DASHIPrimeLaneEquivForLane p
dashiPrimeLaneEquivForLane =
  canonicalDASHIPrimeLaneEquiv

dashiPrimeLaneEquivLaneDimensionInput :
  (p : Lane.MonsterPrimeLane) →
  Bool
dashiPrimeLaneEquivLaneDimensionInput p =
  DASHIPrimeLaneEquiv.laneDimensionReusableInput
    (canonicalDASHIPrimeLaneEquiv p)

dashiPrimeLaneEquivInternalMathGap :
  (p : Lane.MonsterPrimeLane) →
  Bool
dashiPrimeLaneEquivInternalMathGap p =
  DASHIPrimeLaneEquiv.internalMathGap
    (canonicalDASHIPrimeLaneEquiv p)

dashiPrimeLaneEquivInternalMathGapIsTrue :
  (p : Lane.MonsterPrimeLane) →
  dashiPrimeLaneEquivInternalMathGap p ≡ true
dashiPrimeLaneEquivInternalMathGapIsTrue p =
  refl

dashiPrimeLaneEquivTheoremPromoted :
  (p : Lane.MonsterPrimeLane) →
  Bool
dashiPrimeLaneEquivTheoremPromoted p =
  DASHIPrimeLaneEquiv.theoremPromoted
    (canonicalDASHIPrimeLaneEquiv p)

dashiPrimeLaneEquivTheoremPromotedIsFalse :
  (p : Lane.MonsterPrimeLane) →
  dashiPrimeLaneEquivTheoremPromoted p ≡ false
dashiPrimeLaneEquivTheoremPromotedIsFalse p =
  refl

record DASHIPrimeLaneEquivReceiptSurface : Setω where
  field
    status :
      PrimeLaneVOAEquivalenceStatus

    sourcePrimeLaneReceipt :
      Lane.MoonshinePrimeLaneReceiptSurface

    trackedPrimeLane :
      List Lane.MonsterPrimeLane

    trackedPrimeLaneIsCanonical :
      trackedPrimeLane ≡ Lane.canonicalMonsterPrimeLane

    bridgeAt :
      (p : Lane.MonsterPrimeLane) →
      DASHIPrimeLaneEquiv p

    bridgeName :
      String

    bridgeNameIsDASHIPrimeLaneEquiv :
      bridgeName ≡ "DASHIPrimeLaneEquiv"

    p2BIntegrationLane :
      PrimeLaneVOAEquivalenceIntegrationLane

    internalMathGap :
      Bool

    internalMathGapIsTrue :
      internalMathGap ≡ true

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    laneDimensionReusableSurface :
      Bool

    laneDimensionReusableSurfaceIsTrue :
      laneDimensionReusableSurface ≡ true

    boundaries :
      List PrimeLaneVOAEquivalenceBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalPrimeLaneVOAEquivalenceBoundaries

    noPromotionWithoutAuthority :
      PrimeLaneVOAEquivalencePromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open DASHIPrimeLaneEquivReceiptSurface public

canonicalDASHIPrimeLaneEquivReceiptSurface :
  DASHIPrimeLaneEquivReceiptSurface
canonicalDASHIPrimeLaneEquivReceiptSurface =
  record
    { status =
        candidateReceiptOnlyNoTheoremPromotion
    ; sourcePrimeLaneReceipt =
        Lane.canonicalMoonshinePrimeLaneReceiptSurface
    ; trackedPrimeLane =
        Lane.canonicalMonsterPrimeLane
    ; trackedPrimeLaneIsCanonical =
        refl
    ; bridgeAt =
        canonicalDASHIPrimeLaneEquiv
    ; bridgeName =
        "DASHIPrimeLaneEquiv"
    ; bridgeNameIsDASHIPrimeLaneEquiv =
        refl
    ; p2BIntegrationLane =
        p2BDASHIPrimeLaneEquivInternalGap
    ; internalMathGap =
        true
    ; internalMathGapIsTrue =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; laneDimensionReusableSurface =
        true
    ; laneDimensionReusableSurfaceIsTrue =
        refl
    ; boundaries =
        canonicalPrimeLaneVOAEquivalenceBoundaries
    ; boundariesAreCanonical =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "Whole-surface receipt for the per-lane DASHIPrimeLaneEquiv candidate bridge"
        ∷ "Every tracked Monster prime lane receives the same candidate bridge shape"
        ∷ "P2-B remains the internal math gap exported for P2-A/P2-B lane-dimension composition"
        ∷ "This surface is reusable by a LaneDimension theorem surface but does not prove lane dimensions"
        ∷ "Promotion remains blocked without a future authority token and concrete G2, G4, Ogg genus-zero/no-ghost, VOA, orbifold, and DHR receipts"
        ∷ []
    }
