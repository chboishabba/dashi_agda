module DASHI.Physics.QFT.DHRHexagonObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; _++_; [])
open import Data.Nat.Base using (_<_)

import DASHI.TrackedPrimes as TP
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as PrimeLane
import DASHI.Physics.Closure.CarrierToPhysicsInterpretationFunctor as CarrierFunctor
import DASHI.Physics.Closure.G6CrossLaneCommutingTheorem as G6
import DASHI.Physics.Moonshine.LaneDimensionTheoremReceiptSurface as LaneDimension
import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT
import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as AQFTColim
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR
import DASHI.Physics.QFT.ModularTheoryReceiptSurface as Modular
import DASHI.Quantum.Stone as Stone

------------------------------------------------------------------------
-- DHR fusion and symmetric-monoidal hexagon obligation surface.
--
-- This module is a non-promoting obligation surface.  It records the next
-- Paper 2 target needed before DHR fusion rules can be read from the
-- lane-dimension table: the DHR tensor product, associator, braiding, and
-- symmetric hexagon coherence laws must be supplied over the existing
-- Doplicher-Roberts and laneDimension inputs.
--
-- It does not prove the hexagon, compute fusion coefficients, reconstruct a
-- Standard Model gauge assignment, or promote the DR classification theorem.

data DHRHexagonObligationStatus : Set where
  dhrHexagonObligationOnlyNoPromotion :
    DHRHexagonObligationStatus

data DHRHexagonOpenObligation : Set where
  missingDHRObjectToTrackedLaneMap :
    DHRHexagonOpenObligation

  missingDHRLocalisedEndomorphismCarrierSemantics :
    DHRHexagonOpenObligation

  missingDHRSectorRepresentationData :
    DHRHexagonOpenObligation

  missingDHRCrossLaneInvisibilityEvidence :
    DHRHexagonOpenObligation

  missingDHRSectorLaneClassifierEvidence :
    DHRHexagonOpenObligation

  missingDHRIntertwinerTrackedCarrierSemantics :
    DHRHexagonOpenObligation

  missingDHRIntertwinerTrackedCarrierAction :
    DHRHexagonOpenObligation

  missingDHRFusionProduct :
    DHRHexagonOpenObligation

  missingDHRFusionMultiplicityLaw :
    DHRHexagonOpenObligation

  missingDHRUnitCoherence :
    DHRHexagonOpenObligation

  missingDHRPentagonCoherence :
    DHRHexagonOpenObligation

  missingDHRBraidingNaturality :
    DHRHexagonOpenObligation

  missingDHRSymmetricHexagon :
    DHRHexagonOpenObligation

  missingLaneDimensionFusionRuleComparison :
    DHRHexagonOpenObligation

  missingDRClassificationPromotionAuthority :
    DHRHexagonOpenObligation

canonicalDHRHexagonOpenObligations :
  List DHRHexagonOpenObligation
canonicalDHRHexagonOpenObligations =
  missingDHRObjectToTrackedLaneMap
  ∷ missingDHRLocalisedEndomorphismCarrierSemantics
  ∷ missingDHRSectorRepresentationData
  ∷ missingDHRCrossLaneInvisibilityEvidence
  ∷ missingDHRSectorLaneClassifierEvidence
  ∷ missingDHRIntertwinerTrackedCarrierSemantics
  ∷ missingDHRIntertwinerTrackedCarrierAction
  ∷ missingDHRFusionProduct
  ∷ missingDHRFusionMultiplicityLaw
  ∷ missingDHRUnitCoherence
  ∷ missingDHRPentagonCoherence
  ∷ missingDHRBraidingNaturality
  ∷ missingDHRSymmetricHexagon
  ∷ missingLaneDimensionFusionRuleComparison
  ∷ missingDRClassificationPromotionAuthority
  ∷ []

data DHRHexagonPromotionAuthorityToken : Set where

data DHRHexagonDependency : Set where
  dependsOnDHRCategoryPrimitiveSurface :
    DHRHexagonDependency

  dependsOnDoplicherRobertsHypothesesForDASHI :
    DHRHexagonDependency

  dependsOnLaneDimensionTheoremReceiptSurface :
    DHRHexagonDependency

  dependsOnMoonshinePrimeLaneReceiptSurface :
    DHRHexagonDependency

canonicalDHRHexagonDependencies :
  List DHRHexagonDependency
canonicalDHRHexagonDependencies =
  dependsOnDHRCategoryPrimitiveSurface
  ∷ dependsOnDoplicherRobertsHypothesesForDASHI
  ∷ dependsOnLaneDimensionTheoremReceiptSurface
  ∷ dependsOnMoonshinePrimeLaneReceiptSurface
  ∷ []

data DHRHexagonClosureStatus : Set where
  dhrHexagonFailClosedReceiptOnly :
    DHRHexagonClosureStatus

data DHRHexagonClosureBlocker : Set where
  blockedByMissingDHRObjectToTrackedLaneMap :
    DHRHexagonClosureBlocker

  blockedByMissingDHRLocalisedEndomorphismCarrierSemantics :
    DHRHexagonClosureBlocker

  blockedByMissingDHRSectorRepresentationData :
    DHRHexagonClosureBlocker

  blockedByMissingDHRCrossLaneInvisibilityEvidence :
    DHRHexagonClosureBlocker

  blockedByMissingDHRSectorLaneClassifierEvidence :
    DHRHexagonClosureBlocker

  blockedByMissingDHRIntertwinerTrackedCarrierSemantics :
    DHRHexagonClosureBlocker

  blockedByMissingDHRIntertwinerTrackedCarrierAction :
    DHRHexagonClosureBlocker

  blockedByAbstractFusionProduct :
    DHRHexagonClosureBlocker

  blockedByAbstractTensorUnit :
    DHRHexagonClosureBlocker

  blockedByAbstractStatisticsBraiding :
    DHRHexagonClosureBlocker

  blockedByMissingNaturalitySquare :
    DHRHexagonClosureBlocker

  blockedByMissingLeftRightHexagonProofs :
    DHRHexagonClosureBlocker

canonicalDHRHexagonClosureBlockers :
  List DHRHexagonClosureBlocker
canonicalDHRHexagonClosureBlockers =
  blockedByMissingDHRObjectToTrackedLaneMap
  ∷ blockedByMissingDHRLocalisedEndomorphismCarrierSemantics
  ∷ blockedByMissingDHRSectorRepresentationData
  ∷ blockedByMissingDHRCrossLaneInvisibilityEvidence
  ∷ blockedByMissingDHRSectorLaneClassifierEvidence
  ∷ blockedByMissingDHRIntertwinerTrackedCarrierSemantics
  ∷ blockedByMissingDHRIntertwinerTrackedCarrierAction
  ∷ blockedByAbstractFusionProduct
  ∷ blockedByAbstractTensorUnit
  ∷ blockedByAbstractStatisticsBraiding
  ∷ blockedByMissingNaturalitySquare
  ∷ blockedByMissingLeftRightHexagonProofs
  ∷ []

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record LocalisedEndomorphismCarrierSemantics
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane) :
  Set where
  field
    semanticSector :
      DHR.SuperselectionSector

    semanticSectorMatchesLocalisedSector :
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      semanticSector

    carrierPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    assignedLaneActionPreservesCarrier :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      carrierPredicate x ≡ true →
      carrierPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      true

    crossLaneActionInvisibleOnCarrier :
      (otherLane : G6.Lane) →
      lane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      carrierPredicate x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    carrierSemanticsBoundary :
      List String

open LocalisedEndomorphismCarrierSemantics public

degenerateEmptyLocalisedEndomorphismCarrierSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  LocalisedEndomorphismCarrierSemantics operator ρ lane
degenerateEmptyLocalisedEndomorphismCarrierSemantics operator ρ lane =
  record
    { semanticSector =
        DHR.LocalisedEndomorphism.localisedSector ρ
    ; semanticSectorMatchesLocalisedSector =
        refl
    ; carrierPredicate =
        λ _ → false
    ; assignedLaneActionPreservesCarrier =
        λ _ ()
    ; crossLaneActionInvisibleOnCarrier =
        λ _ _ _ ()
    ; carrierSemanticsBoundary =
        "Degenerate empty carrier predicate: no tracked-carrier point is selected"
        ∷ "Assigned-lane preservation and foreign-lane action identity are vacuous because false = true has no inhabitant"
        ∷ "This inhabits only the bare LocalisedEndomorphismCarrierSemantics record and does not supply a nonempty carrier predicate"
        ∷ "No tracked intertwiner action, DHR bridge closure, DR classification, gauge assignment, or hexagon closure is promoted"
        ∷ []
    }

record DegenerateLocalisedEndomorphismCarrierSemanticsReceipt
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane) :
  Setω where
  field
    degenerateCarrierSemantics :
      LocalisedEndomorphismCarrierSemantics operator ρ lane

    degenerateCarrierPredicateIsEmpty :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      LocalisedEndomorphismCarrierSemantics.carrierPredicate
        degenerateCarrierSemantics
        x
      ≡
      false

    degenerateCarrierSemanticsConstructed :
      Bool

    degenerateCarrierSemanticsConstructedIsTrue :
      degenerateCarrierSemanticsConstructed ≡ true

    nondegenerateCarrierPredicateConstructed :
      Bool

    nondegenerateCarrierPredicateConstructedIsFalse :
      nondegenerateCarrierPredicateConstructed ≡ false

    globalForeignLaneActionIdentityConstructed :
      Bool

    globalForeignLaneActionIdentityConstructedIsFalse :
      globalForeignLaneActionIdentityConstructed ≡ false

    trackedIntertwinerCarrierActionConstructed :
      Bool

    trackedIntertwinerCarrierActionConstructedIsFalse :
      trackedIntertwinerCarrierActionConstructed ≡ false

    dhrBridgeClosed :
      Bool

    dhrBridgeClosedIsFalse :
      dhrBridgeClosed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    degenerateReceiptBoundary :
      List String

open DegenerateLocalisedEndomorphismCarrierSemanticsReceipt public

degenerateLocalisedEndomorphismCarrierSemanticsReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  DegenerateLocalisedEndomorphismCarrierSemanticsReceipt operator ρ lane
degenerateLocalisedEndomorphismCarrierSemanticsReceipt operator ρ lane =
  record
    { degenerateCarrierSemantics =
        degenerateEmptyLocalisedEndomorphismCarrierSemantics
          operator
          ρ
          lane
    ; degenerateCarrierPredicateIsEmpty =
        λ _ → refl
    ; degenerateCarrierSemanticsConstructed =
        true
    ; degenerateCarrierSemanticsConstructedIsTrue =
        refl
    ; nondegenerateCarrierPredicateConstructed =
        false
    ; nondegenerateCarrierPredicateConstructedIsFalse =
        refl
    ; globalForeignLaneActionIdentityConstructed =
        false
    ; globalForeignLaneActionIdentityConstructedIsFalse =
        refl
    ; trackedIntertwinerCarrierActionConstructed =
        false
    ; trackedIntertwinerCarrierActionConstructedIsFalse =
        refl
    ; dhrBridgeClosed =
        false
    ; dhrBridgeClosedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; degenerateReceiptBoundary =
        "The only constructed carrier semantics here is the empty predicate witness"
        ∷ "It is mathematically honest as a vacuous selected subset, but it carries no nonempty DHR sector realisation"
        ∷ "A nondegenerate selected fixed-point carrier still needs an explicit predicate plus foreign-lane identity evidence"
        ∷ "Intertwiner semantics still needs a tracked carrier action and preservation/invisibility evidence"
        ∷ []
    }

record IntertwinerTrackedCarrierSemantics
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ σ : DHR.LocalisedEndomorphism)
  (f : DHR.Intertwiner ρ σ)
  (ρLane σLane : G6.Lane)
  (ρSemantics :
    LocalisedEndomorphismCarrierSemantics operator ρ ρLane)
  (σSemantics :
    LocalisedEndomorphismCarrierSemantics operator σ σLane) :
  Set where
  field
    trackedCarrierAction :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    trackedCarrierActionPreservesSemantics :
      (x y : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      LocalisedEndomorphismCarrierSemantics.carrierPredicate ρSemantics x
      ≡
      true →
      trackedCarrierAction x y ≡ true →
      LocalisedEndomorphismCarrierSemantics.carrierPredicate σSemantics y
      ≡
      true

    trackedCarrierActionSeesNoForeignLane :
      (otherLane : G6.Lane) →
      ρLane ≢ otherLane →
      σLane ≢ otherLane →
      Bool

    trackedCarrierSemanticsBoundary :
      List String

open IntertwinerTrackedCarrierSemantics public

data DHRLocalCarrierSemanticsMissingPiece : Set where
  carrierPredicateMissing :
    DHRLocalCarrierSemanticsMissingPiece

  assignedLanePreservationBlockedByMissingPredicate :
    DHRLocalCarrierSemanticsMissingPiece

  crossLaneGlobalActionIdentityMissing :
    DHRLocalCarrierSemanticsMissingPiece

data DHRIntertwinerCarrierSemanticsMissingPiece : Set where
  trackedCarrierActionMissing :
    DHRIntertwinerCarrierSemanticsMissingPiece

  trackedPreservationBlockedByMissingAction :
    DHRIntertwinerCarrierSemanticsMissingPiece

  foreignLaneInvisibilityWitnessMissing :
    DHRIntertwinerCarrierSemanticsMissingPiece

record DHRCarrierSemanticsAbsenceLedger
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    localisedSectorFieldUsable :
      (ρ : DHR.LocalisedEndomorphism) →
      DHR.SuperselectionSector

    localisedSectorFieldMatches :
      (ρ : DHR.LocalisedEndomorphism) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      localisedSectorFieldUsable ρ

    endomorphismActionFieldUsable :
      Bool

    endomorphismActionFieldUsableIsFalse :
      endomorphismActionFieldUsable ≡ false

    g6TrackedCrossLaneCommutationAvailable :
      G6.G6TrackedCrossLaneCommutationTheorem operator

    g6AssignedLaneTrackedPrimeBumpAvailable :
      (lane : G6.Lane) →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      G6.NontrivialTrackedLaneOperator.trackedValuationAt operator
        (G6.NontrivialTrackedLaneOperator.laneActionPrime operator lane)
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      suc
        (G6.NontrivialTrackedLaneOperator.trackedValuationAt operator
          (G6.NontrivialTrackedLaneOperator.laneActionPrime operator lane)
          x)

    g6ForeignTrackedPrimeLocalityAvailable :
      (lane : G6.Lane) →
      (q : TP.SSP) →
      G6.NontrivialTrackedLaneOperator.laneActionPrime operator lane ≢ q →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      G6.NontrivialTrackedLaneOperator.trackedValuationAt operator q
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      G6.NontrivialTrackedLaneOperator.trackedValuationAt operator q x

    g6OutsideBasisCoordinateIdentityAvailable :
      (p : Nat) →
      (lane : G6.Lane) →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      71 < p →
      G6.NontrivialTrackedLaneOperator.outsideBasisValuationAt operator p
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      G6.NontrivialTrackedLaneOperator.outsideBasisValuationAt operator p x

    carrierPredicateSuppliedByDHRFields :
      Bool

    carrierPredicateSuppliedByDHRFieldsIsFalse :
      carrierPredicateSuppliedByDHRFields ≡ false

    assignedLanePredicatePreservationSupplied :
      Bool

    assignedLanePredicatePreservationSuppliedIsFalse :
      assignedLanePredicatePreservationSupplied ≡ false

    foreignLaneGlobalActionIdentitySupplied :
      Bool

    foreignLaneGlobalActionIdentitySuppliedIsFalse :
      foreignLaneGlobalActionIdentitySupplied ≡ false

    localCarrierSemanticsFirstMissingPiece :
      DHRLocalCarrierSemanticsMissingPiece

    localCarrierSemanticsFirstMissingPieceIsCarrierPredicate :
      localCarrierSemanticsFirstMissingPiece
      ≡
      carrierPredicateMissing

    residualLocalCarrierSemanticsMissingPieces :
      List DHRLocalCarrierSemanticsMissingPiece

    arrowCarrierFieldUsable :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      DHR.LocalObservableAlgebra
        (DHR.Intertwiner.supportRegion f)

    unitaryTransportTargetFieldUsable :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      Set

    trackedCarrierActionSuppliedByIntertwinerFields :
      Bool

    trackedCarrierActionSuppliedByIntertwinerFieldsIsFalse :
      trackedCarrierActionSuppliedByIntertwinerFields ≡ false

    trackedPreservationSuppliedByIntertwinerFields :
      Bool

    trackedPreservationSuppliedByIntertwinerFieldsIsFalse :
      trackedPreservationSuppliedByIntertwinerFields ≡ false

    foreignLaneInvisibilitySuppliedByIntertwinerFields :
      Bool

    foreignLaneInvisibilitySuppliedByIntertwinerFieldsIsFalse :
      foreignLaneInvisibilitySuppliedByIntertwinerFields ≡ false

    intertwinerCarrierSemanticsFirstMissingPiece :
      DHRIntertwinerCarrierSemanticsMissingPiece

    intertwinerCarrierSemanticsFirstMissingPieceIsAction :
      intertwinerCarrierSemanticsFirstMissingPiece
      ≡
      trackedCarrierActionMissing

    residualIntertwinerCarrierSemanticsMissingPieces :
      List DHRIntertwinerCarrierSemanticsMissingPiece

    absenceLedgerBoundary :
      List String

open DHRCarrierSemanticsAbsenceLedger public

dhrCarrierSemanticsAbsenceLedgerFromG6 :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRCarrierSemanticsAbsenceLedger operator
dhrCarrierSemanticsAbsenceLedgerFromG6 operator =
  record
    { localisedSectorFieldUsable =
        DHR.LocalisedEndomorphism.localisedSector
    ; localisedSectorFieldMatches =
        λ _ → refl
    ; endomorphismActionFieldUsable =
        false
    ; endomorphismActionFieldUsableIsFalse =
        refl
    ; g6TrackedCrossLaneCommutationAvailable =
        G6.trackedScalingCrossLaneCommutationFromNontrivialOperator
          operator
    ; g6AssignedLaneTrackedPrimeBumpAvailable =
        G6.NontrivialTrackedLaneOperator.laneActionBumpsTrackedPrime
          operator
    ; g6ForeignTrackedPrimeLocalityAvailable =
        G6.NontrivialTrackedLaneOperator.laneActionPreservesOtherTrackedPrime
          operator
    ; g6OutsideBasisCoordinateIdentityAvailable =
        G6.NontrivialTrackedLaneOperator.laneActionOutsideBasisIdentity
          operator
    ; carrierPredicateSuppliedByDHRFields =
        false
    ; carrierPredicateSuppliedByDHRFieldsIsFalse =
        refl
    ; assignedLanePredicatePreservationSupplied =
        false
    ; assignedLanePredicatePreservationSuppliedIsFalse =
        refl
    ; foreignLaneGlobalActionIdentitySupplied =
        false
    ; foreignLaneGlobalActionIdentitySuppliedIsFalse =
        refl
    ; localCarrierSemanticsFirstMissingPiece =
        carrierPredicateMissing
    ; localCarrierSemanticsFirstMissingPieceIsCarrierPredicate =
        refl
    ; residualLocalCarrierSemanticsMissingPieces =
        assignedLanePreservationBlockedByMissingPredicate
        ∷ crossLaneGlobalActionIdentityMissing
        ∷ []
    ; arrowCarrierFieldUsable =
        λ _ _ f → DHR.Intertwiner.arrowCarrier f
    ; unitaryTransportTargetFieldUsable =
        λ _ _ f → DHR.Intertwiner.unitaryTransportTarget f
    ; trackedCarrierActionSuppliedByIntertwinerFields =
        false
    ; trackedCarrierActionSuppliedByIntertwinerFieldsIsFalse =
        refl
    ; trackedPreservationSuppliedByIntertwinerFields =
        false
    ; trackedPreservationSuppliedByIntertwinerFieldsIsFalse =
        refl
    ; foreignLaneInvisibilitySuppliedByIntertwinerFields =
        false
    ; foreignLaneInvisibilitySuppliedByIntertwinerFieldsIsFalse =
        refl
    ; intertwinerCarrierSemanticsFirstMissingPiece =
        trackedCarrierActionMissing
    ; intertwinerCarrierSemanticsFirstMissingPieceIsAction =
        refl
    ; residualIntertwinerCarrierSemanticsMissingPieces =
        trackedPreservationBlockedByMissingAction
        ∷ foreignLaneInvisibilityWitnessMissing
        ∷ []
    ; absenceLedgerBoundary =
        "DHR.LocalisedEndomorphism supplies sector and endomorphismAction fields, but no predicate on the G6 tracked carrier"
        ∷ "G6 supplies tracked cross-lane commutation, assigned-prime bump, other-prime locality, and outside-basis coordinate identity"
        ∷ "Those G6 laws are coordinate laws; they do not supply the global foreign-lane action identity required by LocalisedEndomorphismCarrierSemantics"
        ∷ "DHR.Intertwiner supplies arrowCarrier and unitaryTransportTarget fields, but no tracked carrier action, tracked preservation proof, or foreign-lane invisibility witness"
        ∷ "No DHR carrier semantics, tracked intertwiner semantics, hexagon, DR classification, or gauge assignment is promoted by this ledger"
        ∷ []
    }

record LocalisedEndomorphismCarrierAdapterBoundary
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane)
  (semantics :
    LocalisedEndomorphismCarrierSemantics operator ρ lane) :
  Setω where
  field
    localisedSectorWitness :
      DHR.SuperselectionSector

    localisedSectorWitnessMatches :
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      localisedSectorWitness

    endomorphismActionWitness :
      Bool

    endomorphismActionWitnessMatches :
      endomorphismActionWitness ≡ false

    carriedCarrierSemantics :
      LocalisedEndomorphismCarrierSemantics operator ρ lane

    carriedCarrierSemanticsMatches :
      carriedCarrierSemantics
      ≡
      semantics

    localisedAdapterBoundary :
      List String

open LocalisedEndomorphismCarrierAdapterBoundary public

localisedEndomorphismCarrierAdapterBoundaryFromSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  (semantics :
    LocalisedEndomorphismCarrierSemantics operator ρ lane) →
  LocalisedEndomorphismCarrierAdapterBoundary operator ρ lane semantics
localisedEndomorphismCarrierAdapterBoundaryFromSemantics
  operator ρ lane semantics =
  record
    { localisedSectorWitness =
        DHR.LocalisedEndomorphism.localisedSector ρ
    ; localisedSectorWitnessMatches =
        refl
    ; endomorphismActionWitness =
        false
    ; endomorphismActionWitnessMatches =
        refl
    ; carriedCarrierSemantics =
        semantics
    ; carriedCarrierSemanticsMatches =
        refl
    ; localisedAdapterBoundary =
        "Adapter boundary is inhabited from the actual DHR.LocalisedEndomorphism sector and endomorphismAction fields"
        ∷ "It still requires an already supplied carrier semantics witness for the selected tracked lane"
        ∷ []
    }

record IntertwinerTrackedCarrierAdapterBoundary
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ σ : DHR.LocalisedEndomorphism)
  (f : DHR.Intertwiner ρ σ)
  (ρLane σLane : G6.Lane)
  (ρSemantics :
    LocalisedEndomorphismCarrierSemantics operator ρ ρLane)
  (σSemantics :
    LocalisedEndomorphismCarrierSemantics operator σ σLane)
  (trackedSemantics :
    IntertwinerTrackedCarrierSemantics
      operator
      ρ
      σ
      f
      ρLane
      σLane
      ρSemantics
      σSemantics) :
  Setω where
  field
    sourceLocalisedBoundary :
      LocalisedEndomorphismCarrierAdapterBoundary
        operator
        ρ
        ρLane
        ρSemantics

    targetLocalisedBoundary :
      LocalisedEndomorphismCarrierAdapterBoundary
        operator
        σ
        σLane
        σSemantics

    arrowCarrierWitness :
      DHR.LocalObservableAlgebra (DHR.Intertwiner.supportRegion f)

    arrowCarrierWitnessMatches :
      DHR.Intertwiner.arrowCarrier f
      ≡
      arrowCarrierWitness

    unitaryTransportSocketWitness :
      Set

    unitaryTransportSocketWitnessMatches :
      DHR.Intertwiner.unitaryTransportTarget f
      ≡
      unitaryTransportSocketWitness

    carriedTrackedCarrierSemantics :
      IntertwinerTrackedCarrierSemantics
        operator
        ρ
        σ
        f
        ρLane
        σLane
        ρSemantics
        σSemantics

    carriedTrackedCarrierSemanticsMatches :
      carriedTrackedCarrierSemantics
      ≡
      trackedSemantics

    intertwinerAdapterBoundary :
      List String

open IntertwinerTrackedCarrierAdapterBoundary public

intertwinerTrackedCarrierAdapterBoundaryFromSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  (f : DHR.Intertwiner ρ σ) →
  (ρLane σLane : G6.Lane) →
  (ρSemantics :
    LocalisedEndomorphismCarrierSemantics operator ρ ρLane) →
  (σSemantics :
    LocalisedEndomorphismCarrierSemantics operator σ σLane) →
  (trackedSemantics :
    IntertwinerTrackedCarrierSemantics
      operator
      ρ
      σ
      f
      ρLane
      σLane
      ρSemantics
      σSemantics) →
  IntertwinerTrackedCarrierAdapterBoundary
    operator
    ρ
    σ
    f
    ρLane
    σLane
    ρSemantics
    σSemantics
    trackedSemantics
intertwinerTrackedCarrierAdapterBoundaryFromSemantics
  operator ρ σ f ρLane σLane ρSemantics σSemantics trackedSemantics =
  record
    { sourceLocalisedBoundary =
        localisedEndomorphismCarrierAdapterBoundaryFromSemantics
          operator
          ρ
          ρLane
          ρSemantics
    ; targetLocalisedBoundary =
        localisedEndomorphismCarrierAdapterBoundaryFromSemantics
          operator
          σ
          σLane
          σSemantics
    ; arrowCarrierWitness =
        DHR.Intertwiner.arrowCarrier f
    ; arrowCarrierWitnessMatches =
        refl
    ; unitaryTransportSocketWitness =
        DHR.Intertwiner.unitaryTransportTarget f
    ; unitaryTransportSocketWitnessMatches =
        refl
    ; carriedTrackedCarrierSemantics =
        trackedSemantics
    ; carriedTrackedCarrierSemanticsMatches =
        refl
    ; intertwinerAdapterBoundary =
        "Adapter boundary is inhabited from the actual DHR.Intertwiner arrowCarrier and unitaryTransportTarget fields"
        ∷ "It still requires source and target carrier semantics plus a tracked carrier semantics witness"
        ∷ []
    }

record NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane) :
  Setω where
  field
    semanticSectorWitness :
      DHR.SuperselectionSector

    semanticSectorWitnessMatchesLocalisedSector :
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      semanticSectorWitness

    selectedCarrierPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    selectedCarrierWitness :
      G6.NontrivialTrackedLaneOperator.Carrier operator

    selectedCarrierWitnessSelected :
      selectedCarrierPredicate selectedCarrierWitness
      ≡
      true

    assignedLaneActionPreservesSelectedCarrier :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate x ≡ true →
      selectedCarrierPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      true

    globalForeignLaneActionIdentityOnSelectedCarrier :
      (otherLane : G6.Lane) →
      lane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    nondegenerateCarrierPredicateSupplied :
      Bool

    nondegenerateCarrierPredicateSuppliedIsTrue :
      nondegenerateCarrierPredicateSupplied ≡ true

    globalForeignLaneActionIdentitySupplied :
      Bool

    globalForeignLaneActionIdentitySuppliedIsTrue :
      globalForeignLaneActionIdentitySupplied ≡ true

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    nondegenerateLocalisedInterfaceBoundary :
      List String

open NondegenerateLocalisedEndomorphismCarrierSemanticsInterface public

nondegenerateLocalisedInterfaceToCarrierSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
    operator
    ρ
    lane →
  LocalisedEndomorphismCarrierSemantics operator ρ lane
nondegenerateLocalisedInterfaceToCarrierSemantics
  operator ρ lane external =
  record
    { semanticSector =
        semanticSectorWitness external
    ; semanticSectorMatchesLocalisedSector =
        semanticSectorWitnessMatchesLocalisedSector external
    ; carrierPredicate =
        selectedCarrierPredicate external
    ; assignedLaneActionPreservesCarrier =
        assignedLaneActionPreservesSelectedCarrier external
    ; crossLaneActionInvisibleOnCarrier =
        globalForeignLaneActionIdentityOnSelectedCarrier external
    ; carrierSemanticsBoundary =
        "Derived from a supplied nondegenerate external interface with an explicitly selected carrier witness"
        ∷ "The interface must supply global foreign-lane action identity on the selected carrier; G6 coordinate locality alone is not used as that proof"
        ∷ "This adapter consumption does not promote DR classification, gauge reconstruction, or symmetric hexagon closure"
        ∷ nondegenerateLocalisedInterfaceBoundary external
    }

nondegenerateLocalisedInterfaceToAdapterBoundary :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  (external :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      lane) →
  LocalisedEndomorphismCarrierAdapterBoundary
    operator
    ρ
    lane
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      ρ
      lane
      external)
nondegenerateLocalisedInterfaceToAdapterBoundary
  operator ρ lane external =
  localisedEndomorphismCarrierAdapterBoundaryFromSemantics
    operator
    ρ
    lane
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      ρ
      lane
      external)

record LocalisedEndomorphismNonemptyCarrierWitness
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane)
  (semantics :
    LocalisedEndomorphismCarrierSemantics operator ρ lane) :
  Set where
  field
    nonemptyCarrierWitness :
      G6.NontrivialTrackedLaneOperator.Carrier operator

    nonemptyCarrierWitnessSelected :
      LocalisedEndomorphismCarrierSemantics.carrierPredicate
        semantics
        nonemptyCarrierWitness
      ≡
      true

    nonemptyWitnessBoundary :
      List String

open LocalisedEndomorphismNonemptyCarrierWitness public

nondegenerateLocalisedInterfaceToNonemptyCarrierWitness :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  (external :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      lane) →
  LocalisedEndomorphismNonemptyCarrierWitness
    operator
    ρ
    lane
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      ρ
      lane
      external)
nondegenerateLocalisedInterfaceToNonemptyCarrierWitness
  operator ρ lane external =
  record
    { nonemptyCarrierWitness =
        selectedCarrierWitness external
    ; nonemptyCarrierWitnessSelected =
        selectedCarrierWitnessSelected external
    ; nonemptyWitnessBoundary =
        "Nonempty witness extracted from the supplied nondegenerate localised-endomorphism interface"
        ∷ "This proves only that the selected carrier predicate is inhabited"
        ∷ []
    }

record LocalisedEndomorphismWithForeignLaneIdEvidence
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane)
  (foreignLaneId : G6.Lane) :
  Setω where
  field
    localisedForeignLaneInterface :
      NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
        operator
        ρ
        lane

    foreignLaneIdDistinctFromAssignedLane :
      lane ≢ foreignLaneId

    localisedForeignLaneCarrierSemantics :
      LocalisedEndomorphismCarrierSemantics operator ρ lane

    localisedForeignLaneCarrierSemanticsMatchesInterface :
      localisedForeignLaneCarrierSemantics
      ≡
      nondegenerateLocalisedInterfaceToCarrierSemantics
        operator
        ρ
        lane
        localisedForeignLaneInterface

    localisedForeignLaneNonemptyWitness :
      LocalisedEndomorphismNonemptyCarrierWitness
        operator
        ρ
        lane
        localisedForeignLaneCarrierSemantics

    foreignLaneIdActionFixesNonemptyWitness :
      G6.NontrivialTrackedLaneOperator.laneAction
        operator
        foreignLaneId
        (LocalisedEndomorphismNonemptyCarrierWitness.nonemptyCarrierWitness
          localisedForeignLaneNonemptyWitness)
      ≡
      LocalisedEndomorphismNonemptyCarrierWitness.nonemptyCarrierWitness
        localisedForeignLaneNonemptyWitness

    foreignLaneIdEvidenceBoundary :
      List String

open LocalisedEndomorphismWithForeignLaneIdEvidence public

localisedEndomorphismWithForeignLaneIdEvidenceFromInterface :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane foreignLaneId : G6.Lane) →
  (external :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      lane) →
  lane ≢ foreignLaneId →
  LocalisedEndomorphismWithForeignLaneIdEvidence
    operator
    ρ
    lane
    foreignLaneId
localisedEndomorphismWithForeignLaneIdEvidenceFromInterface
  operator ρ lane foreignLaneId external lane≢foreign =
  record
    { localisedForeignLaneInterface =
        external
    ; foreignLaneIdDistinctFromAssignedLane =
        lane≢foreign
    ; localisedForeignLaneCarrierSemantics =
        nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          ρ
          lane
          external
    ; localisedForeignLaneCarrierSemanticsMatchesInterface =
        refl
    ; localisedForeignLaneNonemptyWitness =
        nondegenerateLocalisedInterfaceToNonemptyCarrierWitness
          operator
          ρ
          lane
          external
    ; foreignLaneIdActionFixesNonemptyWitness =
        globalForeignLaneActionIdentityOnSelectedCarrier
          external
          foreignLaneId
          lane≢foreign
          (selectedCarrierWitness external)
          (selectedCarrierWitnessSelected external)
    ; foreignLaneIdEvidenceBoundary =
        "Structural foreignLaneId evidence extracted from a nondegenerate localised-endomorphism interface"
        ∷ "The selected nonempty carrier is fixed by the named foreign lane using the interface's global foreign-lane identity field"
        ∷ "No object-to-lane classifier, DR classification, gauge reconstruction, or symmetric hexagon is promoted by this evidence"
        ∷ []
    }

localisedEndomorphismWithForeignLaneIdToAdapterBoundary :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane foreignLaneId : G6.Lane) →
  (evidence :
    LocalisedEndomorphismWithForeignLaneIdEvidence
    operator
    ρ
    lane
    foreignLaneId) →
  LocalisedEndomorphismCarrierAdapterBoundary
    operator
    ρ
    lane
    (localisedForeignLaneCarrierSemantics evidence)
localisedEndomorphismWithForeignLaneIdToAdapterBoundary
  operator ρ lane foreignLaneId evidence =
  localisedEndomorphismCarrierAdapterBoundaryFromSemantics
    operator
    ρ
    lane
    (localisedForeignLaneCarrierSemantics evidence)

record NondegenerateIntertwinerTrackedCarrierSemanticsInterface
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ σ : DHR.LocalisedEndomorphism)
  (f : DHR.Intertwiner ρ σ)
  (ρLane σLane : G6.Lane)
  (ρExternal :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      ρLane)
  (σExternal :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      σ
      σLane) :
  Setω where
  field
    trackedCarrierAction :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    trackedCarrierActionPreservesSelectedCarrier :
      (x y : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate ρExternal x
      ≡
      true →
      trackedCarrierAction x y ≡ true →
      selectedCarrierPredicate σExternal y
      ≡
      true

    trackedCarrierActionSeesNoForeignLane :
      (otherLane : G6.Lane) →
      ρLane ≢ otherLane →
      σLane ≢ otherLane →
      Bool

    trackedCarrierActionSupplied :
      Bool

    trackedCarrierActionSuppliedIsTrue :
      trackedCarrierActionSupplied ≡ true

    trackedCarrierActionPreservationSupplied :
      Bool

    trackedCarrierActionPreservationSuppliedIsTrue :
      trackedCarrierActionPreservationSupplied ≡ true

    trackedCarrierActionForeignLaneInvisibilitySupplied :
      Bool

    trackedCarrierActionForeignLaneInvisibilitySuppliedIsTrue :
      trackedCarrierActionForeignLaneInvisibilitySupplied ≡ true

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    nondegenerateIntertwinerInterfaceBoundary :
      List String

open NondegenerateIntertwinerTrackedCarrierSemanticsInterface public

targetSelectedNondegenerateIntertwinerTrackedCarrierSemanticsInterface :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  (f : DHR.Intertwiner ρ σ) →
  (ρLane σLane : G6.Lane) →
  (ρExternal :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      ρLane) →
  (σExternal :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      σ
      σLane) →
  NondegenerateIntertwinerTrackedCarrierSemanticsInterface
    operator
    ρ
    σ
    f
    ρLane
    σLane
    ρExternal
    σExternal
targetSelectedNondegenerateIntertwinerTrackedCarrierSemanticsInterface
  operator ρ σ f ρLane σLane ρExternal σExternal =
  record
    { trackedCarrierAction =
        λ _ y →
          selectedCarrierPredicate σExternal y
    ; trackedCarrierActionPreservesSelectedCarrier =
        λ _ _ _ actionSelected →
          actionSelected
    ; trackedCarrierActionSeesNoForeignLane =
        λ _ _ _ →
          true
    ; trackedCarrierActionSupplied =
        true
    ; trackedCarrierActionSuppliedIsTrue =
        refl
    ; trackedCarrierActionPreservationSupplied =
        true
    ; trackedCarrierActionPreservationSuppliedIsTrue =
        refl
    ; trackedCarrierActionForeignLaneInvisibilitySupplied =
        true
    ; trackedCarrierActionForeignLaneInvisibilitySuppliedIsTrue =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; nondegenerateIntertwinerInterfaceBoundary =
        "Conditional target-selected tracked carrier action: an arrow relates x to exactly the selected target carriers"
        ∷ "Preservation is definitional because trackedCarrierAction x y is the target selected-carrier predicate"
        ∷ "This supplies only the primitive IntertwinerTrackedCarrierSemanticsInterface after source and target nondegenerate local interfaces are already supplied"
        ∷ "It does not construct the missing localised carrier interface, DHR naturality square, DR classification, gauge reconstruction, or symmetric hexagon"
        ∷ []
    }

nondegenerateIntertwinerInterfaceToCarrierSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  (f : DHR.Intertwiner ρ σ) →
  (ρLane σLane : G6.Lane) →
  (ρExternal :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      ρLane) →
  (σExternal :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      σ
      σLane) →
  NondegenerateIntertwinerTrackedCarrierSemanticsInterface
    operator
    ρ
    σ
    f
    ρLane
    σLane
    ρExternal
    σExternal →
  IntertwinerTrackedCarrierSemantics
    operator
    ρ
    σ
    f
    ρLane
    σLane
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      ρ
      ρLane
      ρExternal)
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      σ
      σLane
      σExternal)
nondegenerateIntertwinerInterfaceToCarrierSemantics
  operator ρ σ f ρLane σLane ρExternal σExternal external =
  record
    { trackedCarrierAction =
        trackedCarrierAction external
    ; trackedCarrierActionPreservesSemantics =
        trackedCarrierActionPreservesSelectedCarrier external
    ; trackedCarrierActionSeesNoForeignLane =
        trackedCarrierActionSeesNoForeignLane external
    ; trackedCarrierSemanticsBoundary =
        "Derived from a supplied nondegenerate external interface with a tracked carrier action"
        ∷ "The interface must supply preservation of selected source and target carrier predicates"
        ∷ "This adapter consumption does not promote DHR naturality, DR classification, gauge reconstruction, or symmetric hexagon closure"
        ∷ nondegenerateIntertwinerInterfaceBoundary external
    }

nondegenerateIntertwinerInterfaceToAdapterBoundary :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  (f : DHR.Intertwiner ρ σ) →
  (ρLane σLane : G6.Lane) →
  (ρExternal :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      ρLane) →
  (σExternal :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      σ
      σLane) →
  (external :
    NondegenerateIntertwinerTrackedCarrierSemanticsInterface
      operator
      ρ
      σ
      f
      ρLane
      σLane
      ρExternal
      σExternal) →
  IntertwinerTrackedCarrierAdapterBoundary
    operator
    ρ
    σ
    f
    ρLane
    σLane
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      ρ
      ρLane
      ρExternal)
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      σ
      σLane
      σExternal)
    (nondegenerateIntertwinerInterfaceToCarrierSemantics
      operator
      ρ
      σ
      f
      ρLane
      σLane
      ρExternal
      σExternal
      external)
nondegenerateIntertwinerInterfaceToAdapterBoundary
  operator ρ σ f ρLane σLane ρExternal σExternal external =
  intertwinerTrackedCarrierAdapterBoundaryFromSemantics
    operator
    ρ
    σ
    f
    ρLane
    σLane
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      ρ
      ρLane
      ρExternal)
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      σ
      σLane
      σExternal)
    (nondegenerateIntertwinerInterfaceToCarrierSemantics
      operator
      ρ
      σ
      f
      ρLane
      σLane
      ρExternal
      σExternal
      external)

record TrackedIntertwinerForeignLaneIdAdapter
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ σ : DHR.LocalisedEndomorphism)
  (f : DHR.Intertwiner ρ σ)
  (ρLane σLane foreignLaneId : G6.Lane)
  (ρEvidence :
    LocalisedEndomorphismWithForeignLaneIdEvidence
      operator
      ρ
      ρLane
      foreignLaneId)
  (σEvidence :
    LocalisedEndomorphismWithForeignLaneIdEvidence
      operator
      σ
      σLane
      foreignLaneId) :
  Setω where
  field
    trackedForeignLaneIntertwinerInterface :
      NondegenerateIntertwinerTrackedCarrierSemanticsInterface
        operator
        ρ
        σ
        f
        ρLane
        σLane
        (localisedForeignLaneInterface ρEvidence)
        (localisedForeignLaneInterface σEvidence)

    trackedForeignLaneCarrierSemantics :
      IntertwinerTrackedCarrierSemantics
        operator
        ρ
        σ
        f
        ρLane
        σLane
        (nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          ρ
          ρLane
          (localisedForeignLaneInterface ρEvidence))
        (nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          σ
          σLane
          (localisedForeignLaneInterface σEvidence))

    trackedForeignLaneCarrierSemanticsMatchesInterface :
      trackedForeignLaneCarrierSemantics
      ≡
      nondegenerateIntertwinerInterfaceToCarrierSemantics
        operator
        ρ
        σ
        f
        ρLane
        σLane
        (localisedForeignLaneInterface ρEvidence)
        (localisedForeignLaneInterface σEvidence)
        trackedForeignLaneIntertwinerInterface

    trackedForeignLaneAdapterBoundary :
      IntertwinerTrackedCarrierAdapterBoundary
        operator
        ρ
        σ
        f
        ρLane
        σLane
        (nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          ρ
          ρLane
          (localisedForeignLaneInterface ρEvidence))
        (nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          σ
          σLane
          (localisedForeignLaneInterface σEvidence))
        trackedForeignLaneCarrierSemantics

    trackedActionSeesForeignLaneId :
      NondegenerateIntertwinerTrackedCarrierSemanticsInterface.trackedCarrierActionSeesNoForeignLane
        trackedForeignLaneIntertwinerInterface
        foreignLaneId
        (foreignLaneIdDistinctFromAssignedLane ρEvidence)
        (foreignLaneIdDistinctFromAssignedLane σEvidence)
      ≡
      true

    trackedForeignLaneAdapterBoundaryNotes :
      List String

open TrackedIntertwinerForeignLaneIdAdapter public

targetSelectedTrackedIntertwinerForeignLaneIdAdapter :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  (f : DHR.Intertwiner ρ σ) →
  (ρLane σLane foreignLaneId : G6.Lane) →
  (ρEvidence :
    LocalisedEndomorphismWithForeignLaneIdEvidence
      operator
      ρ
      ρLane
      foreignLaneId) →
  (σEvidence :
    LocalisedEndomorphismWithForeignLaneIdEvidence
      operator
      σ
      σLane
      foreignLaneId) →
  TrackedIntertwinerForeignLaneIdAdapter
    operator
    ρ
    σ
    f
    ρLane
    σLane
    foreignLaneId
    ρEvidence
    σEvidence
targetSelectedTrackedIntertwinerForeignLaneIdAdapter
  operator ρ σ f ρLane σLane foreignLaneId ρEvidence σEvidence =
  record
    { trackedForeignLaneIntertwinerInterface =
        targetSelectedNondegenerateIntertwinerTrackedCarrierSemanticsInterface
          operator
          ρ
          σ
          f
          ρLane
          σLane
          (localisedForeignLaneInterface ρEvidence)
          (localisedForeignLaneInterface σEvidence)
    ; trackedForeignLaneCarrierSemantics =
        nondegenerateIntertwinerInterfaceToCarrierSemantics
          operator
          ρ
          σ
          f
          ρLane
          σLane
          (localisedForeignLaneInterface ρEvidence)
          (localisedForeignLaneInterface σEvidence)
          (targetSelectedNondegenerateIntertwinerTrackedCarrierSemanticsInterface
            operator
            ρ
            σ
            f
            ρLane
            σLane
            (localisedForeignLaneInterface ρEvidence)
            (localisedForeignLaneInterface σEvidence))
    ; trackedForeignLaneCarrierSemanticsMatchesInterface =
        refl
    ; trackedForeignLaneAdapterBoundary =
        nondegenerateIntertwinerInterfaceToAdapterBoundary
          operator
          ρ
          σ
          f
          ρLane
          σLane
          (localisedForeignLaneInterface ρEvidence)
          (localisedForeignLaneInterface σEvidence)
          (targetSelectedNondegenerateIntertwinerTrackedCarrierSemanticsInterface
            operator
            ρ
            σ
            f
            ρLane
            σLane
            (localisedForeignLaneInterface ρEvidence)
            (localisedForeignLaneInterface σEvidence))
    ; trackedActionSeesForeignLaneId =
        refl
    ; trackedForeignLaneAdapterBoundaryNotes =
        "Target-selected tracked intertwiner adapter over source and target localised foreignLaneId evidence"
        ∷ "The adapter supplies the primitive carrier action by selecting the target carrier predicate; it is not a DHR naturality square"
        ∷ "The named foreignLaneId is recorded as invisible to this target-selected action, while local nonempty witnesses are fixed by the local foreign-lane identity evidence"
        ∷ "No fusion product, braiding naturality, DR classification, gauge reconstruction, or symmetric hexagon is closed here"
        ∷ []
    }

data DHRPrimitiveSectorClass : Set where
  primitiveMaxwellSectorClass :
    DHRPrimitiveSectorClass

  primitiveSchrodingerSectorClass :
    DHRPrimitiveSectorClass

  primitiveGRSectorClass :
    DHRPrimitiveSectorClass

  primitiveEmpiricalSectorClass :
    DHRPrimitiveSectorClass

primitiveSectorClassAssignedLane :
  DHRPrimitiveSectorClass →
  G6.Lane
primitiveSectorClassAssignedLane primitiveMaxwellSectorClass =
  G6.maxwellLane
primitiveSectorClassAssignedLane primitiveSchrodingerSectorClass =
  G6.schrodingerLane
primitiveSectorClassAssignedLane primitiveGRSectorClass =
  G6.grLane
primitiveSectorClassAssignedLane primitiveEmpiricalSectorClass =
  G6.empiricalLane

record DHRPrimitiveSuperselectionSectorConstructorSurface : Set₁ where
  field
    sectorForPrimitiveClass :
      DHRPrimitiveSectorClass →
      DHR.SuperselectionSector

    primitiveClassForSectorPredicate :
      DHR.SuperselectionSector →
      DHRPrimitiveSectorClass →
      Set

    primitiveClassPredicateSelectsConstructor :
      (sectorClass : DHRPrimitiveSectorClass) →
      primitiveClassForSectorPredicate
        (sectorForPrimitiveClass sectorClass)
        sectorClass

    constructorSurfaceBoundary :
      List String

open DHRPrimitiveSuperselectionSectorConstructorSurface public

postulate
  primitiveMaxwellSuperselectionSector :
    DHR.SuperselectionSector

  primitiveSchrodingerSuperselectionSector :
    DHR.SuperselectionSector

  primitiveGRSuperselectionSector :
    DHR.SuperselectionSector

  primitiveEmpiricalSuperselectionSector :
    DHR.SuperselectionSector

primitiveSuperselectionSectorForClass :
  DHRPrimitiveSectorClass →
  DHR.SuperselectionSector
primitiveSuperselectionSectorForClass primitiveMaxwellSectorClass =
  primitiveMaxwellSuperselectionSector
primitiveSuperselectionSectorForClass primitiveSchrodingerSectorClass =
  primitiveSchrodingerSuperselectionSector
primitiveSuperselectionSectorForClass primitiveGRSectorClass =
  primitiveGRSuperselectionSector
primitiveSuperselectionSectorForClass primitiveEmpiricalSectorClass =
  primitiveEmpiricalSuperselectionSector

primitiveSuperselectionSectorClassPredicate :
  DHR.SuperselectionSector →
  DHRPrimitiveSectorClass →
  Set
primitiveSuperselectionSectorClassPredicate sector sectorClass =
  sector
  ≡
  primitiveSuperselectionSectorForClass sectorClass

canonicalDHRPrimitiveSuperselectionSectorConstructorSurface :
  DHRPrimitiveSuperselectionSectorConstructorSurface
canonicalDHRPrimitiveSuperselectionSectorConstructorSurface =
  record
    { sectorForPrimitiveClass =
        primitiveSuperselectionSectorForClass
    ; primitiveClassForSectorPredicate =
        primitiveSuperselectionSectorClassPredicate
    ; primitiveClassPredicateSelectsConstructor =
        λ _ → refl
    ; constructorSurfaceBoundary =
        "Primitive DHR superselection-sector constants are named for the four tracked lane classes"
        ∷ "The class predicate is equality to the selected primitive sector constructor"
        ∷ "This inhabits only DHRPrimitiveSuperselectionSectorConstructorSurface; arbitrary sector-to-lane predicates are not constructed"
        ∷ "No sector-specific carrier predicate, foreign-lane identity, irreducibility predicate, DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

canonicalPrimitiveSectorClassPredicateSelectsConstructor :
  (sectorClass : DHRPrimitiveSectorClass) →
  primitiveClassForSectorPredicate
    canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
    (sectorForPrimitiveClass
      canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
      sectorClass)
    sectorClass
canonicalPrimitiveSectorClassPredicateSelectsConstructor =
  primitiveClassPredicateSelectsConstructor
    canonicalDHRPrimitiveSuperselectionSectorConstructorSurface

record DHRPrimitiveSectorAssignedLaneEvidence
  (sector : DHR.SuperselectionSector)
  (lane : G6.Lane) :
  Set where
  field
    primitiveSectorClass :
      DHRPrimitiveSectorClass

    sectorMatchesPrimitiveConstructor :
      sector
      ≡
      primitiveSuperselectionSectorForClass primitiveSectorClass

    laneMatchesPrimitiveAssignedLane :
      lane
      ≡
      primitiveSectorClassAssignedLane primitiveSectorClass

    primitiveAssignedLaneEvidenceBoundary :
      List String

open DHRPrimitiveSectorAssignedLaneEvidence public

primitiveSectorAssignedLaneEvidenceForClass :
  (sectorClass : DHRPrimitiveSectorClass) →
  DHRPrimitiveSectorAssignedLaneEvidence
    (primitiveSuperselectionSectorForClass sectorClass)
    (primitiveSectorClassAssignedLane sectorClass)
primitiveSectorAssignedLaneEvidenceForClass sectorClass =
  record
    { primitiveSectorClass =
        sectorClass
    ; sectorMatchesPrimitiveConstructor =
        refl
    ; laneMatchesPrimitiveAssignedLane =
        refl
    ; primitiveAssignedLaneEvidenceBoundary =
        "Primitive sector-to-lane evidence is available only for the four named primitive sector constructors"
        ∷ "The lane is the canonical primitiveSectorClassAssignedLane for the selected class"
        ∷ "This is not an arbitrary SuperselectionSector classifier and does not supply carrier predicates or irreducibility"
        ∷ []
    }

primitiveLocalisedEndomorphismAssignedLaneEvidence :
  (ρ : DHR.LocalisedEndomorphism) →
  (sectorClass : DHRPrimitiveSectorClass) →
  DHR.LocalisedEndomorphism.localisedSector ρ
  ≡
  primitiveSuperselectionSectorForClass sectorClass →
  DHRPrimitiveSectorAssignedLaneEvidence
    (DHR.LocalisedEndomorphism.localisedSector ρ)
    (primitiveSectorClassAssignedLane sectorClass)
primitiveLocalisedEndomorphismAssignedLaneEvidence
  ρ sectorClass localisedSectorMatchesPrimitive =
  record
    { primitiveSectorClass =
        sectorClass
    ; sectorMatchesPrimitiveConstructor =
        localisedSectorMatchesPrimitive
    ; laneMatchesPrimitiveAssignedLane =
        refl
    ; primitiveAssignedLaneEvidenceBoundary =
        "A localised endomorphism can be assigned a primitive lane when its localisedSector is proved equal to a named primitive sector constructor"
        ∷ "The equality proof is explicit input; no arbitrary sector-to-lane classifier is inferred"
        ∷ "This evidence can feed the primitive sector-lane supply bridge once carrier predicate and foreign-lane identity witnesses are also supplied"
        ∷ []
    }

record DHRPrimitiveSectorToLaneClassifierProgress : Setω where
  field
    primitiveConstructorSurface :
      DHRPrimitiveSuperselectionSectorConstructorSurface

    primitiveSectorAssignedLanePredicate :
      DHR.SuperselectionSector →
      G6.Lane →
      Set

    primitiveSectorAssignedLanePredicateIsEvidence :
      primitiveSectorAssignedLanePredicate
      ≡
      DHRPrimitiveSectorAssignedLaneEvidence

    primitiveAssignedLaneEvidenceForClass :
      (sectorClass : DHRPrimitiveSectorClass) →
      primitiveSectorAssignedLanePredicate
        (DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
          primitiveConstructorSurface
          sectorClass)
        (primitiveSectorClassAssignedLane sectorClass)

    primitiveLocalisedAssignedLaneEvidence :
      (ρ : DHR.LocalisedEndomorphism) →
      (sectorClass : DHRPrimitiveSectorClass) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
        primitiveConstructorSurface
        sectorClass →
      primitiveSectorAssignedLanePredicate
        (DHR.LocalisedEndomorphism.localisedSector ρ)
        (primitiveSectorClassAssignedLane sectorClass)

    primitiveAssignedLaneClassifierConstructed :
      Bool

    primitiveAssignedLaneClassifierConstructedIsTrue :
      primitiveAssignedLaneClassifierConstructed ≡ true

    arbitrarySectorToLanePredicateSupplied :
      Bool

    arbitrarySectorToLanePredicateSuppliedIsFalse :
      arbitrarySectorToLanePredicateSupplied ≡ false

    sectorSpecificCarrierPredicateSupplied :
      Bool

    sectorSpecificCarrierPredicateSuppliedIsFalse :
      sectorSpecificCarrierPredicateSupplied ≡ false

    foreignLaneIdentitySupplied :
      Bool

    foreignLaneIdentitySuppliedIsFalse :
      foreignLaneIdentitySupplied ≡ false

    irreducibleClassifierSupplied :
      Bool

    irreducibleClassifierSuppliedIsFalse :
      irreducibleClassifierSupplied ≡ false

    primitiveClassifierProgressBoundary :
      List String

open DHRPrimitiveSectorToLaneClassifierProgress public

canonicalDHRPrimitiveSectorToLaneClassifierProgress :
  DHRPrimitiveSectorToLaneClassifierProgress
canonicalDHRPrimitiveSectorToLaneClassifierProgress =
  record
    { primitiveConstructorSurface =
        canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
    ; primitiveSectorAssignedLanePredicate =
        DHRPrimitiveSectorAssignedLaneEvidence
    ; primitiveSectorAssignedLanePredicateIsEvidence =
        refl
    ; primitiveAssignedLaneEvidenceForClass =
        primitiveSectorAssignedLaneEvidenceForClass
    ; primitiveLocalisedAssignedLaneEvidence =
        primitiveLocalisedEndomorphismAssignedLaneEvidence
    ; primitiveAssignedLaneClassifierConstructed =
        true
    ; primitiveAssignedLaneClassifierConstructedIsTrue =
        refl
    ; arbitrarySectorToLanePredicateSupplied =
        false
    ; arbitrarySectorToLanePredicateSuppliedIsFalse =
        refl
    ; sectorSpecificCarrierPredicateSupplied =
        false
    ; sectorSpecificCarrierPredicateSuppliedIsFalse =
        refl
    ; foreignLaneIdentitySupplied =
        false
    ; foreignLaneIdentitySuppliedIsFalse =
        refl
    ; irreducibleClassifierSupplied =
        false
    ; irreducibleClassifierSuppliedIsFalse =
        refl
    ; primitiveClassifierProgressBoundary =
        "Primitive sector-to-lane evidence is now packaged for the four constructed primitive sector classes"
        ∷ "A localised endomorphism can use that evidence only after an explicit equality to one primitive sector constructor is supplied"
        ∷ "The surface narrows the Gate 6 blocker but keeps arbitrary sector classification, sector-specific carrier predicates, foreign-lane identity, irreducibility, DR classification, gauge reconstruction, and hexagon closure unpromoted"
        ∷ []
    }

data DHRPrimitiveConstructorResidualMissingPiece : Set where
  missingArbitrarySectorToLanePredicateAfterPrimitiveConstructors :
    DHRPrimitiveConstructorResidualMissingPiece

  missingSectorSpecificCarrierPredicateAfterPrimitiveConstructors :
    DHRPrimitiveConstructorResidualMissingPiece

  missingForeignLaneIdentityAfterPrimitiveConstructors :
    DHRPrimitiveConstructorResidualMissingPiece

  missingIrreducibleClassifierAfterPrimitiveConstructors :
    DHRPrimitiveConstructorResidualMissingPiece

record DHRPrimitiveConstructorSurfaceProgress : Setω where
  field
    primitiveConstructorSurface :
      DHRPrimitiveSuperselectionSectorConstructorSurface

    primitiveConstructorsSupplied :
      Bool

    primitiveConstructorsSuppliedIsTrue :
      primitiveConstructorsSupplied ≡ true

    arbitrarySectorToLanePredicateSupplied :
      Bool

    arbitrarySectorToLanePredicateSuppliedIsFalse :
      arbitrarySectorToLanePredicateSupplied ≡ false

    sectorSpecificCarrierPredicateSupplied :
      Bool

    sectorSpecificCarrierPredicateSuppliedIsFalse :
      sectorSpecificCarrierPredicateSupplied ≡ false

    foreignLaneIdentitySupplied :
      Bool

    foreignLaneIdentitySuppliedIsFalse :
      foreignLaneIdentitySupplied ≡ false

    irreducibleClassifierSupplied :
      Bool

    irreducibleClassifierSuppliedIsFalse :
      irreducibleClassifierSupplied ≡ false

    residualMissingPieces :
      List DHRPrimitiveConstructorResidualMissingPiece

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    primitiveConstructorProgressBoundary :
      List String

open DHRPrimitiveConstructorSurfaceProgress public

canonicalDHRPrimitiveConstructorSurfaceProgress :
  DHRPrimitiveConstructorSurfaceProgress
canonicalDHRPrimitiveConstructorSurfaceProgress =
  record
    { primitiveConstructorSurface =
        canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
    ; primitiveConstructorsSupplied =
        true
    ; primitiveConstructorsSuppliedIsTrue =
        refl
    ; arbitrarySectorToLanePredicateSupplied =
        false
    ; arbitrarySectorToLanePredicateSuppliedIsFalse =
        refl
    ; sectorSpecificCarrierPredicateSupplied =
        false
    ; sectorSpecificCarrierPredicateSuppliedIsFalse =
        refl
    ; foreignLaneIdentitySupplied =
        false
    ; foreignLaneIdentitySuppliedIsFalse =
        refl
    ; irreducibleClassifierSupplied =
        false
    ; irreducibleClassifierSuppliedIsFalse =
        refl
    ; residualMissingPieces =
        missingArbitrarySectorToLanePredicateAfterPrimitiveConstructors
        ∷ missingSectorSpecificCarrierPredicateAfterPrimitiveConstructors
        ∷ missingForeignLaneIdentityAfterPrimitiveConstructors
        ∷ missingIrreducibleClassifierAfterPrimitiveConstructors
        ∷ []
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; primitiveConstructorProgressBoundary =
        "The four primitive DHR sector-class constructors are now an explicit consumed surface"
        ∷ "This removes only the primitive-constructor absence from the supplied-sector bridge path"
        ∷ "Arbitrary sector-to-lane classification, sector-specific carrier predicates, global foreign-lane identity, and irreducibility remain open"
        ∷ "No DR classification, gauge reconstruction, fusion law, braiding naturality, or symmetric hexagon closure is promoted"
        ∷ []
    }

record DHRAssignedLaneClassifierPrimitiveSurface
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    sectorConstructorSurfaceTarget :
      Set₁

    sectorAssignedLanePredicate :
      DHR.SuperselectionSector →
      G6.Lane →
      Set

    sectorSpecificCarrierPredicate :
      DHR.SuperselectionSector →
      G6.Lane →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    sectorSpecificCarrierNonemptyWitness :
      (sector : DHR.SuperselectionSector) →
      (lane : G6.Lane) →
      G6.NontrivialTrackedLaneOperator.Carrier operator

    sectorSpecificCarrierWitnessSelected :
      (sector : DHR.SuperselectionSector) →
      (lane : G6.Lane) →
      sectorSpecificCarrierPredicate
        sector
        lane
        (sectorSpecificCarrierNonemptyWitness sector lane)
      ≡
      true

    localisedObjectAssignedLane :
      DHR.LocalisedEndomorphism →
      G6.Lane

    localisedObjectAssignedLaneClassifiesSector :
      (ρ : DHR.LocalisedEndomorphism) →
      sectorAssignedLanePredicate
        (DHR.LocalisedEndomorphism.localisedSector ρ)
        (localisedObjectAssignedLane ρ)

    assignedClassifierEvidenceConstructed :
      Bool

    assignedClassifierEvidenceConstructedIsFalse :
      assignedClassifierEvidenceConstructed ≡ false

    classifierPrimitiveSurfaceBoundary :
      List String

open DHRAssignedLaneClassifierPrimitiveSurface public

record DHRForeignLaneIdentityStructuralField
  (operator : G6.NontrivialTrackedLaneOperator)
  (lane : G6.Lane)
  (selectedCarrierPredicate :
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Bool) :
  Set where
  field
    foreignLaneIdentityOnSelectedCarrier :
      (otherLane : G6.Lane) →
      lane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    foreignLaneIdentityBoundary :
      List String

open DHRForeignLaneIdentityStructuralField public

record DHRConcreteNonemptySectorWitness
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane) :
  Setω where
  field
    concreteSectorWitness :
      DHR.SuperselectionSector

    concreteSectorWitnessMatchesLocalisedSector :
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      concreteSectorWitness

    concreteAssignedLane :
      G6.Lane

    concreteAssignedLaneMatchesInput :
      lane
      ≡
      concreteAssignedLane

    concreteSelectedCarrierPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    concreteSelectedCarrierWitness :
      G6.NontrivialTrackedLaneOperator.Carrier operator

    concreteSelectedCarrierWitnessSelected :
      concreteSelectedCarrierPredicate concreteSelectedCarrierWitness
      ≡
      true

    concreteAssignedLaneActionPreservesSelectedCarrier :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      concreteSelectedCarrierPredicate x ≡ true →
      concreteSelectedCarrierPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      true

    foreignLaneIdentityStructuralFieldTarget :
      DHRForeignLaneIdentityStructuralField
        operator
        lane
        concreteSelectedCarrierPredicate →
      Set

    g6ConcreteNonemptyCarrierWitnessConstructed :
      Bool

    g6ConcreteNonemptyCarrierWitnessConstructedIsTrue :
      g6ConcreteNonemptyCarrierWitnessConstructed ≡ true

    dhrSectorSpecificPredicateConstructed :
      Bool

    dhrSectorSpecificPredicateConstructedIsFalse :
      dhrSectorSpecificPredicateConstructed ≡ false

    foreignLaneIdentityConstructed :
      Bool

    foreignLaneIdentityConstructedIsFalse :
      foreignLaneIdentityConstructed ≡ false

    concreteWitnessBoundary :
      List String

open DHRConcreteNonemptySectorWitness public

dhrConcreteNonemptySectorWitness :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  DHRConcreteNonemptySectorWitness operator ρ lane
dhrConcreteNonemptySectorWitness operator ρ lane =
  record
    { concreteSectorWitness =
        DHR.LocalisedEndomorphism.localisedSector ρ
    ; concreteSectorWitnessMatchesLocalisedSector =
        refl
    ; concreteAssignedLane =
        lane
    ; concreteAssignedLaneMatchesInput =
        refl
    ; concreteSelectedCarrierPredicate =
        λ _ →
          true
    ; concreteSelectedCarrierWitness =
        G6.NontrivialTrackedLaneOperator.nontrivialWitness operator
    ; concreteSelectedCarrierWitnessSelected =
        refl
    ; concreteAssignedLaneActionPreservesSelectedCarrier =
        λ _ _ →
          refl
    ; foreignLaneIdentityStructuralFieldTarget =
        λ _ →
          ⊥
    ; g6ConcreteNonemptyCarrierWitnessConstructed =
        true
    ; g6ConcreteNonemptyCarrierWitnessConstructedIsTrue =
        refl
    ; dhrSectorSpecificPredicateConstructed =
        false
    ; dhrSectorSpecificPredicateConstructedIsFalse =
        refl
    ; foreignLaneIdentityConstructed =
        false
    ; foreignLaneIdentityConstructedIsFalse =
        refl
    ; concreteWitnessBoundary =
        "Concrete witness: the G6 nontrivial carrier witness inhabits the all-carrier predicate for the localised sector field"
        ∷ "The all-carrier predicate is assigned-lane stable by definitional equality"
        ∷ "This is not a DHR sector-specific predicate and does not provide global foreign-lane identity"
        ∷ "No classifier evidence, DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

record DHRConcreteTrackedIntertwinerActionPrimitive
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ σ : DHR.LocalisedEndomorphism)
  (f : DHR.Intertwiner ρ σ)
  (ρLane σLane : G6.Lane)
  (ρWitness : DHRConcreteNonemptySectorWitness operator ρ ρLane)
  (σWitness : DHRConcreteNonemptySectorWitness operator σ σLane) :
  Setω where
  field
    concreteTrackedIntertwinerAction :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    concreteTrackedIntertwinerActionPreservesTargetSelection :
      (x y : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      DHRConcreteNonemptySectorWitness.concreteSelectedCarrierPredicate
        ρWitness
        x
      ≡
      true →
      concreteTrackedIntertwinerAction x y ≡ true →
      DHRConcreteNonemptySectorWitness.concreteSelectedCarrierPredicate
        σWitness
        y
      ≡
      true

    concreteTrackedIntertwinerActionForeignLaneInvisibleFlag :
      (otherLane : G6.Lane) →
      ρLane ≢ otherLane →
      σLane ≢ otherLane →
      Bool

    concreteTrackedIntertwinerActionConstructed :
      Bool

    concreteTrackedIntertwinerActionConstructedIsTrue :
      concreteTrackedIntertwinerActionConstructed ≡ true

    dhrIntertwinerNaturalityConstructed :
      Bool

    dhrIntertwinerNaturalityConstructedIsFalse :
      dhrIntertwinerNaturalityConstructed ≡ false

    trackedActionBoundary :
      List String

open DHRConcreteTrackedIntertwinerActionPrimitive public

targetSelectedDHRConcreteTrackedIntertwinerActionPrimitive :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  (f : DHR.Intertwiner ρ σ) →
  (ρLane σLane : G6.Lane) →
  (ρWitness : DHRConcreteNonemptySectorWitness operator ρ ρLane) →
  (σWitness : DHRConcreteNonemptySectorWitness operator σ σLane) →
  DHRConcreteTrackedIntertwinerActionPrimitive
    operator
    ρ
    σ
    f
    ρLane
    σLane
    ρWitness
    σWitness
targetSelectedDHRConcreteTrackedIntertwinerActionPrimitive
  operator ρ σ f ρLane σLane ρWitness σWitness =
  record
    { concreteTrackedIntertwinerAction =
        λ _ y →
          DHRConcreteNonemptySectorWitness.concreteSelectedCarrierPredicate
            σWitness
            y
    ; concreteTrackedIntertwinerActionPreservesTargetSelection =
        λ _ _ _ targetSelected →
          targetSelected
    ; concreteTrackedIntertwinerActionForeignLaneInvisibleFlag =
        λ _ _ _ →
          true
    ; concreteTrackedIntertwinerActionConstructed =
        true
    ; concreteTrackedIntertwinerActionConstructedIsTrue =
        refl
    ; dhrIntertwinerNaturalityConstructed =
        false
    ; dhrIntertwinerNaturalityConstructedIsFalse =
        refl
    ; trackedActionBoundary =
        "Concrete target-selected tracked action: an intertwiner relates any source carrier to selected target carriers"
        ∷ "Preservation is definitional for the target-selected action"
        ∷ "The action is a carrier-level primitive only; it is not a DHR naturality square"
        ∷ "No tensor compatibility, braiding, DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

data DHRExactClassifierIrreducibilityAbsentPrimitive : Set where
  absentDHRSuperselectionSectorConstructors :
    DHRExactClassifierIrreducibilityAbsentPrimitive

  absentSectorAssignedLanePredicate :
    DHRExactClassifierIrreducibilityAbsentPrimitive

  absentSectorSpecificCarrierPredicate :
    DHRExactClassifierIrreducibilityAbsentPrimitive

  absentForeignLaneIdentityStructuralField :
    DHRExactClassifierIrreducibilityAbsentPrimitive

  absentIrreducibleSectorPredicate :
    DHRExactClassifierIrreducibilityAbsentPrimitive

record DHRExactClassifierIrreducibilityRecord
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    superselectionSectorConstructorSurfaceTarget :
      Set₁

    sectorAssignedLanePredicateTarget :
      DHR.SuperselectionSector →
      G6.Lane →
      Set

    sectorSpecificCarrierPredicateTarget :
      DHR.SuperselectionSector →
      G6.Lane →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    foreignLaneIdentityStructuralFieldTarget :
      (lane : G6.Lane) →
      (selectedCarrierPredicate :
        G6.NontrivialTrackedLaneOperator.Carrier operator →
        Bool) →
      Set

    irreducibleSectorPredicateTarget :
      DHR.SuperselectionSector →
      Set

    superselectionSectorConstructorsSupplied :
      Bool

    superselectionSectorConstructorsSuppliedIsTrue :
      superselectionSectorConstructorsSupplied ≡ true

    sectorAssignedLanePredicateSupplied :
      Bool

    sectorAssignedLanePredicateSuppliedIsFalse :
      sectorAssignedLanePredicateSupplied ≡ false

    sectorSpecificCarrierPredicateSupplied :
      Bool

    sectorSpecificCarrierPredicateSuppliedIsFalse :
      sectorSpecificCarrierPredicateSupplied ≡ false

    foreignLaneIdentityStructuralFieldSupplied :
      Bool

    foreignLaneIdentityStructuralFieldSuppliedIsFalse :
      foreignLaneIdentityStructuralFieldSupplied ≡ false

    irreducibleSectorPredicateSupplied :
      Bool

    irreducibleSectorPredicateSuppliedIsTrueForPrimitiveConstructors :
      irreducibleSectorPredicateSupplied ≡ true

    exactAbsentPrimitives :
      List DHRExactClassifierIrreducibilityAbsentPrimitive

    exactClassifierEvidenceConstructed :
      Bool

    exactClassifierEvidenceConstructedIsFalse :
      exactClassifierEvidenceConstructed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    exactIrreducibilityBoundary :
      List String

open DHRExactClassifierIrreducibilityRecord public

dhrExactClassifierIrreducibilityRecord :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRExactClassifierIrreducibilityRecord operator
dhrExactClassifierIrreducibilityRecord operator =
  record
    { superselectionSectorConstructorSurfaceTarget =
        DHRPrimitiveSuperselectionSectorConstructorSurface
    ; sectorAssignedLanePredicateTarget =
        λ _ _ →
          ⊥
    ; sectorSpecificCarrierPredicateTarget =
        λ _ _ _ →
          false
    ; foreignLaneIdentityStructuralFieldTarget =
        λ lane selectedCarrierPredicate →
          DHRForeignLaneIdentityStructuralField
            operator
            lane
            selectedCarrierPredicate
    ; irreducibleSectorPredicateTarget =
        λ sector →
          sector ≡ primitiveMaxwellSuperselectionSector
    ; superselectionSectorConstructorsSupplied =
        true
    ; superselectionSectorConstructorsSuppliedIsTrue =
        refl
    ; sectorAssignedLanePredicateSupplied =
        false
    ; sectorAssignedLanePredicateSuppliedIsFalse =
        refl
    ; sectorSpecificCarrierPredicateSupplied =
        false
    ; sectorSpecificCarrierPredicateSuppliedIsFalse =
        refl
    ; foreignLaneIdentityStructuralFieldSupplied =
        false
    ; foreignLaneIdentityStructuralFieldSuppliedIsFalse =
        refl
    ; irreducibleSectorPredicateSupplied =
        true
    ; irreducibleSectorPredicateSuppliedIsTrueForPrimitiveConstructors =
        refl
    ; exactAbsentPrimitives =
        absentSectorAssignedLanePredicate
        ∷ absentSectorSpecificCarrierPredicate
        ∷ absentForeignLaneIdentityStructuralField
        ∷ []
    ; exactClassifierEvidenceConstructed =
        false
    ; exactClassifierEvidenceConstructedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; exactIrreducibilityBoundary =
        "Primitive DHR superselection-sector constructors and primitive irreducibility predicates are now supplied for the four named primitive classes"
        ∷ "Exact classifier blocker: no arbitrary sectorAssignedLanePredicate : SuperselectionSector -> G6.Lane -> Set is supplied"
        ∷ "Exact classifier blocker: no DHR sector-specific nonempty carrier predicate on the G6 tracked carrier is supplied"
        ∷ "Exact classifier blocker: foreign-lane identity is only a structural field target, not a theorem derivable from tracked-prime coordinate locality"
        ∷ "Exact classifier blocker: primitive irreducibility does not classify arbitrary sectors or supply DR fibre-functor reconstruction"
        ∷ "The record is deliberately fail-closed and does not promote DR classification or symmetric hexagon closure"
        ∷ []
    }

record DHRNonemptySectorCarrierPredicateRequest
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane) :
  Set₁ where
  field
    requestedSelectedCarrierPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    requestedSelectedCarrierWitness :
      G6.NontrivialTrackedLaneOperator.Carrier operator

    requestedSelectedCarrierWitnessSelected :
      requestedSelectedCarrierPredicate requestedSelectedCarrierWitness
      ≡
      true

    requestedAssignedLaneActionPreservesSelectedCarrier :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      requestedSelectedCarrierPredicate x ≡ true →
      requestedSelectedCarrierPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      true

    predicateRequestBoundary :
      List String

open DHRNonemptySectorCarrierPredicateRequest public

record DHRGlobalForeignLaneIdentityForPredicateRequest
  (operator : G6.NontrivialTrackedLaneOperator)
  (lane : G6.Lane)
  (selectedCarrierPredicate :
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Bool) :
  Set where
  field
    requestedGlobalForeignLaneActionIdentity :
      (otherLane : G6.Lane) →
      lane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    identityRequestBoundary :
      List String

open DHRGlobalForeignLaneIdentityForPredicateRequest public

dhrArbitrarySectorGlobalForeignLaneIdentityEliminator :
  {operator : G6.NontrivialTrackedLaneOperator} →
  {lane : G6.Lane} →
  {selectedCarrierPredicate :
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Bool} →
  (identityRequest :
    DHRGlobalForeignLaneIdentityForPredicateRequest
      operator
      lane
      selectedCarrierPredicate) →
  (otherLane : G6.Lane) →
  lane ≢ otherLane →
  (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
  selectedCarrierPredicate x ≡ true →
  G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
  ≡
  x
dhrArbitrarySectorGlobalForeignLaneIdentityEliminator
  identityRequest
  otherLane
  laneDistinctFromOther
  x
  xSelected =
  requestedGlobalForeignLaneActionIdentity
    identityRequest
    otherLane
    laneDistinctFromOther
    x
    xSelected

record DHRSelectedCarrierLaneActionPreservationRequest
  (operator : G6.NontrivialTrackedLaneOperator)
  (lane : G6.Lane)
  (selectedCarrierPredicate :
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Bool) :
  Set where
  field
    requestedAssignedLaneActionPreservesSelectedCarrier :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate x ≡ true →
      selectedCarrierPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      true

    preservationRequestBoundary :
      List String

open DHRSelectedCarrierLaneActionPreservationRequest public

record DHRPrimitiveSectorNonemptyCarrierPredicateEvidence
  (operator : G6.NontrivialTrackedLaneOperator)
  (sectorClass : DHRPrimitiveSectorClass) :
  Setω where
  field
    primitiveCarrierSector :
      DHR.SuperselectionSector

    primitiveCarrierSectorMatchesConstructor :
      primitiveCarrierSector
      ≡
      primitiveSuperselectionSectorForClass sectorClass

    primitiveCarrierLane :
      G6.Lane

    primitiveCarrierLaneMatchesAssignedLane :
      primitiveCarrierLane
      ≡
      primitiveSectorClassAssignedLane sectorClass

    primitiveAssignedLaneEvidence :
      DHRPrimitiveSectorAssignedLaneEvidence
        primitiveCarrierSector
        primitiveCarrierLane

    primitiveSelectedCarrierPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    primitiveSelectedCarrierWitness :
      G6.NontrivialTrackedLaneOperator.Carrier operator

    primitiveSelectedCarrierWitnessSelected :
      primitiveSelectedCarrierPredicate primitiveSelectedCarrierWitness
      ≡
      true

    primitiveAssignedLaneActionPreservesSelectedCarrier :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      primitiveSelectedCarrierPredicate x ≡ true →
      primitiveSelectedCarrierPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction
          operator
          primitiveCarrierLane
          x)
      ≡
      true

    primitiveCarrierPredicateConstructed :
      Bool

    primitiveCarrierPredicateConstructedIsTrue :
      primitiveCarrierPredicateConstructed ≡ true

    arbitrarySectorClassifierSupplied :
      Bool

    arbitrarySectorClassifierSuppliedIsFalse :
      arbitrarySectorClassifierSupplied ≡ false

    foreignLaneIdentitySupplied :
      Bool

    foreignLaneIdentitySuppliedIsFalse :
      foreignLaneIdentitySupplied ≡ false

    irreduciblePredicateSupplied :
      Bool

    irreduciblePredicateSuppliedIsFalse :
      irreduciblePredicateSupplied ≡ false

    primitiveCarrierPredicateBoundary :
      List String

open DHRPrimitiveSectorNonemptyCarrierPredicateEvidence public

primitiveSectorNonemptyCarrierPredicateEvidenceForClass :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (sectorClass : DHRPrimitiveSectorClass) →
  DHRPrimitiveSectorNonemptyCarrierPredicateEvidence
    operator
    sectorClass
primitiveSectorNonemptyCarrierPredicateEvidenceForClass
  operator sectorClass =
  record
    { primitiveCarrierSector =
        primitiveSuperselectionSectorForClass sectorClass
    ; primitiveCarrierSectorMatchesConstructor =
        refl
    ; primitiveCarrierLane =
        primitiveSectorClassAssignedLane sectorClass
    ; primitiveCarrierLaneMatchesAssignedLane =
        refl
    ; primitiveAssignedLaneEvidence =
        primitiveSectorAssignedLaneEvidenceForClass sectorClass
    ; primitiveSelectedCarrierPredicate =
        λ _ →
          true
    ; primitiveSelectedCarrierWitness =
        G6.NontrivialTrackedLaneOperator.nontrivialWitness operator
    ; primitiveSelectedCarrierWitnessSelected =
        refl
    ; primitiveAssignedLaneActionPreservesSelectedCarrier =
        λ _ _ →
          refl
    ; primitiveCarrierPredicateConstructed =
        true
    ; primitiveCarrierPredicateConstructedIsTrue =
        refl
    ; arbitrarySectorClassifierSupplied =
        false
    ; arbitrarySectorClassifierSuppliedIsFalse =
        refl
    ; foreignLaneIdentitySupplied =
        false
    ; foreignLaneIdentitySuppliedIsFalse =
        refl
    ; irreduciblePredicateSupplied =
        false
    ; irreduciblePredicateSuppliedIsFalse =
        refl
    ; primitiveCarrierPredicateBoundary =
        "Primitive constructor carrier predicate: the G6 nontrivial carrier witness inhabits the selected all-carrier predicate for the named primitive sector class"
        ∷ "The selected predicate is indexed by the primitive sector constructor and its assigned lane, but it is not an arbitrary SuperselectionSector classifier"
        ∷ "Assigned-lane preservation is definitional for this all-carrier predicate"
        ∷ "Foreign-lane identity, irreducibility, DR classification, gauge reconstruction, and symmetric hexagon closure remain unpromoted"
        ∷ []
    }

primitiveSectorNonemptyCarrierPredicateRequest :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (sectorClass : DHRPrimitiveSectorClass) →
  DHR.LocalisedEndomorphism.localisedSector ρ
  ≡
  primitiveSuperselectionSectorForClass sectorClass →
  DHRNonemptySectorCarrierPredicateRequest
    operator
    ρ
    (primitiveSectorClassAssignedLane sectorClass)
primitiveSectorNonemptyCarrierPredicateRequest
  operator ρ sectorClass localisedSectorMatchesPrimitive =
  record
    { requestedSelectedCarrierPredicate =
        primitiveSelectedCarrierPredicate evidence
    ; requestedSelectedCarrierWitness =
        primitiveSelectedCarrierWitness evidence
    ; requestedSelectedCarrierWitnessSelected =
        primitiveSelectedCarrierWitnessSelected evidence
    ; requestedAssignedLaneActionPreservesSelectedCarrier =
        primitiveAssignedLaneActionPreservesSelectedCarrier evidence
    ; predicateRequestBoundary =
        "Primitive localised-endomorphism carrier predicate request is supplied after rho.localisedSector is explicitly matched to the named primitive constructor"
        ∷ "The equality input is a guardrail: this request is not an arbitrary sector classifier"
        ∷ "The request still needs a separate global foreign-lane identity witness before it can build a DHRSuperselectionSectorLaneSupply"
        ∷ primitiveCarrierPredicateBoundary evidence
    }
  where
    evidence :
      DHRPrimitiveSectorNonemptyCarrierPredicateEvidence
        operator
        sectorClass
    evidence =
      primitiveSectorNonemptyCarrierPredicateEvidenceForClass
        operator
        sectorClass

record DHRPrimitiveSectorCarrierPredicateProgress
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    primitiveConstructorSurface :
      DHRPrimitiveSuperselectionSectorConstructorSurface

    primitiveAssignedLaneProgress :
      DHRPrimitiveSectorToLaneClassifierProgress

    primitiveCarrierPredicateEvidenceForClass :
      (sectorClass : DHRPrimitiveSectorClass) →
      DHRPrimitiveSectorNonemptyCarrierPredicateEvidence
        operator
        sectorClass

    primitiveCarrierPredicateRequestForLocalisedEndomorphism :
      (ρ : DHR.LocalisedEndomorphism) →
      (sectorClass : DHRPrimitiveSectorClass) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      primitiveSuperselectionSectorForClass sectorClass →
      DHRNonemptySectorCarrierPredicateRequest
        operator
        ρ
        (primitiveSectorClassAssignedLane sectorClass)

    primitiveSectorCarrierPredicateSupplied :
      Bool

    primitiveSectorCarrierPredicateSuppliedIsTrue :
      primitiveSectorCarrierPredicateSupplied ≡ true

    arbitrarySectorClassifierSupplied :
      Bool

    arbitrarySectorClassifierSuppliedIsFalse :
      arbitrarySectorClassifierSupplied ≡ false

    foreignLaneIdentitySupplied :
      Bool

    foreignLaneIdentitySuppliedIsFalse :
      foreignLaneIdentitySupplied ≡ false

    irreduciblePredicateSupplied :
      Bool

    irreduciblePredicateSuppliedIsFalse :
      irreduciblePredicateSupplied ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    primitiveCarrierPredicateProgressBoundary :
      List String

open DHRPrimitiveSectorCarrierPredicateProgress public

canonicalDHRPrimitiveSectorCarrierPredicateProgress :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRPrimitiveSectorCarrierPredicateProgress operator
canonicalDHRPrimitiveSectorCarrierPredicateProgress operator =
  record
    { primitiveConstructorSurface =
        canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
    ; primitiveAssignedLaneProgress =
        canonicalDHRPrimitiveSectorToLaneClassifierProgress
    ; primitiveCarrierPredicateEvidenceForClass =
        primitiveSectorNonemptyCarrierPredicateEvidenceForClass
          operator
    ; primitiveCarrierPredicateRequestForLocalisedEndomorphism =
        primitiveSectorNonemptyCarrierPredicateRequest
          operator
    ; primitiveSectorCarrierPredicateSupplied =
        true
    ; primitiveSectorCarrierPredicateSuppliedIsTrue =
        refl
    ; arbitrarySectorClassifierSupplied =
        false
    ; arbitrarySectorClassifierSuppliedIsFalse =
        refl
    ; foreignLaneIdentitySupplied =
        false
    ; foreignLaneIdentitySuppliedIsFalse =
        refl
    ; irreduciblePredicateSupplied =
        false
    ; irreduciblePredicateSuppliedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; primitiveCarrierPredicateProgressBoundary =
        "Primitive sector-specific nonempty carrier predicates are now packaged for the four named primitive sector constructors"
        ∷ "Each predicate is conditional on an explicit localisedSector equality to one primitive constructor and uses the existing G6 nontrivial carrier witness"
        ∷ "This narrows the supplied-sector bridge blocker but leaves arbitrary sector classification, global foreign-lane identity, and irreducibility evidence open"
        ∷ "No DR classification, gauge reconstruction, fusion law, braiding naturality, or symmetric hexagon closure is promoted"
        ∷ []
    }

data DHRConcreteSectorConstructorsResidualBlocker : Set where
  blockedByNoPrimitiveGlobalForeignLaneIdentity :
    DHRConcreteSectorConstructorsResidualBlocker

  blockedByNoArbitrarySectorClassifier :
    DHRConcreteSectorConstructorsResidualBlocker

  blockedByNoDRFibreFunctorClassifier :
    DHRConcreteSectorConstructorsResidualBlocker

record DHRConcreteSectorConstructorsProgress
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    primitiveConstructorProgress :
      DHRPrimitiveConstructorSurfaceProgress

    primitiveLaneClassifierProgress :
      DHRPrimitiveSectorToLaneClassifierProgress

    primitiveCarrierPredicateProgress :
      DHRPrimitiveSectorCarrierPredicateProgress operator

    primitiveAssignedLaneEvidenceForLocalisedEndomorphism :
      (ρ : DHR.LocalisedEndomorphism) →
      (sectorClass : DHRPrimitiveSectorClass) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      primitiveSuperselectionSectorForClass sectorClass →
      DHRPrimitiveSectorAssignedLaneEvidence
        (DHR.LocalisedEndomorphism.localisedSector ρ)
        (primitiveSectorClassAssignedLane sectorClass)

    primitiveCarrierPredicateRequestForLocalisedEndomorphism :
      (ρ : DHR.LocalisedEndomorphism) →
      (sectorClass : DHRPrimitiveSectorClass) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      primitiveSuperselectionSectorForClass sectorClass →
      DHRNonemptySectorCarrierPredicateRequest
        operator
        ρ
        (primitiveSectorClassAssignedLane sectorClass)

    concreteNonemptyWitnessForLocalisedEndomorphism :
      (ρ : DHR.LocalisedEndomorphism) →
      (sectorClass : DHRPrimitiveSectorClass) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      primitiveSuperselectionSectorForClass sectorClass →
      DHRConcreteNonemptySectorWitness
        operator
        ρ
        (primitiveSectorClassAssignedLane sectorClass)

    primitiveConstructorsSupplied :
      Bool

    primitiveConstructorsSuppliedIsTrue :
      primitiveConstructorsSupplied ≡ true

    primitiveLaneSemanticsSupplied :
      Bool

    primitiveLaneSemanticsSuppliedIsTrue :
      primitiveLaneSemanticsSupplied ≡ true

    primitiveNonemptyWitnessSurfaceSupplied :
      Bool

    primitiveNonemptyWitnessSurfaceSuppliedIsTrue :
      primitiveNonemptyWitnessSurfaceSupplied ≡ true

    primitiveGlobalForeignLaneIdentitySupplied :
      Bool

    primitiveGlobalForeignLaneIdentitySuppliedIsFalse :
      primitiveGlobalForeignLaneIdentitySupplied ≡ false

    arbitrarySectorClassifierSupplied :
      Bool

    arbitrarySectorClassifierSuppliedIsFalse :
      arbitrarySectorClassifierSupplied ≡ false

    dhrSuperselectionSectorLaneSupplyConstructed :
      Bool

    dhrSuperselectionSectorLaneSupplyConstructedIsFalse :
      dhrSuperselectionSectorLaneSupplyConstructed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    firstResidualBlocker :
      DHRConcreteSectorConstructorsResidualBlocker

    firstResidualBlockerIsPrimitiveGlobalForeignLaneIdentity :
      firstResidualBlocker
      ≡
      blockedByNoPrimitiveGlobalForeignLaneIdentity

    residualBlockers :
      List DHRConcreteSectorConstructorsResidualBlocker

    concreteSectorConstructorsProgressBoundary :
      List String

open DHRConcreteSectorConstructorsProgress public

canonicalDHRConcreteSectorConstructorsProgress :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRConcreteSectorConstructorsProgress operator
canonicalDHRConcreteSectorConstructorsProgress operator =
  record
    { primitiveConstructorProgress =
        canonicalDHRPrimitiveConstructorSurfaceProgress
    ; primitiveLaneClassifierProgress =
        canonicalDHRPrimitiveSectorToLaneClassifierProgress
    ; primitiveCarrierPredicateProgress =
        canonicalDHRPrimitiveSectorCarrierPredicateProgress operator
    ; primitiveAssignedLaneEvidenceForLocalisedEndomorphism =
        primitiveLocalisedEndomorphismAssignedLaneEvidence
    ; primitiveCarrierPredicateRequestForLocalisedEndomorphism =
        primitiveSectorNonemptyCarrierPredicateRequest operator
    ; concreteNonemptyWitnessForLocalisedEndomorphism =
        λ ρ sectorClass _ →
          dhrConcreteNonemptySectorWitness
            operator
            ρ
            (primitiveSectorClassAssignedLane sectorClass)
    ; primitiveConstructorsSupplied =
        true
    ; primitiveConstructorsSuppliedIsTrue =
        refl
    ; primitiveLaneSemanticsSupplied =
        true
    ; primitiveLaneSemanticsSuppliedIsTrue =
        refl
    ; primitiveNonemptyWitnessSurfaceSupplied =
        true
    ; primitiveNonemptyWitnessSurfaceSuppliedIsTrue =
        refl
    ; primitiveGlobalForeignLaneIdentitySupplied =
        false
    ; primitiveGlobalForeignLaneIdentitySuppliedIsFalse =
        refl
    ; arbitrarySectorClassifierSupplied =
        false
    ; arbitrarySectorClassifierSuppliedIsFalse =
        refl
    ; dhrSuperselectionSectorLaneSupplyConstructed =
        false
    ; dhrSuperselectionSectorLaneSupplyConstructedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; firstResidualBlocker =
        blockedByNoPrimitiveGlobalForeignLaneIdentity
    ; firstResidualBlockerIsPrimitiveGlobalForeignLaneIdentity =
        refl
    ; residualBlockers =
        blockedByNoArbitrarySectorClassifier
        ∷ blockedByNoDRFibreFunctorClassifier
        ∷ []
    ; concreteSectorConstructorsProgressBoundary =
        "Concrete sector constructor progress now packages primitive constructor data, primitive lane semantics, and primitive nonempty carrier request/witness surfaces"
        ∷ "The nonempty witness surface remains local and conditional on explicit localisedSector equality to a named primitive constructor class"
        ∷ "The first unresolved blocker remains global foreign-lane identity for the primitive selected predicate, with arbitrary-sector classification and DR classifier work still open"
        ∷ "No DR classification, gauge reconstruction, braiding naturality, or symmetric hexagon closure is promoted"
        ∷ []
    }

record DHRPrimitiveIrreducibleSectorEvidence
  (sectorClass : DHRPrimitiveSectorClass) :
  Setω where
  field
    irreduciblePrimitiveSector :
      DHR.SuperselectionSector

    irreduciblePrimitiveSectorMatchesConstructor :
      irreduciblePrimitiveSector
      ≡
      primitiveSuperselectionSectorForClass sectorClass

    primitiveIrreduciblePredicate :
      DHR.SuperselectionSector →
      Set

    primitiveIrreduciblePredicateSelectsConstructor :
      primitiveIrreduciblePredicate irreduciblePrimitiveSector

    primitiveIrreducibilityConstructed :
      Bool

    primitiveIrreducibilityConstructedIsTrue :
      primitiveIrreducibilityConstructed ≡ true

    arbitraryIrreducibilityClassifierSupplied :
      Bool

    arbitraryIrreducibilityClassifierSuppliedIsFalse :
      arbitraryIrreducibilityClassifierSupplied ≡ false

    primitiveIrreducibilityBoundary :
      List String

open DHRPrimitiveIrreducibleSectorEvidence public

primitiveIrreducibleSectorEvidenceForClass :
  (sectorClass : DHRPrimitiveSectorClass) →
  DHRPrimitiveIrreducibleSectorEvidence sectorClass
primitiveIrreducibleSectorEvidenceForClass sectorClass =
  record
    { irreduciblePrimitiveSector =
        primitiveSuperselectionSectorForClass sectorClass
    ; irreduciblePrimitiveSectorMatchesConstructor =
        refl
    ; primitiveIrreduciblePredicate =
        λ sector →
          sector ≡ primitiveSuperselectionSectorForClass sectorClass
    ; primitiveIrreduciblePredicateSelectsConstructor =
        refl
    ; primitiveIrreducibilityConstructed =
        true
    ; primitiveIrreducibilityConstructedIsTrue =
        refl
    ; arbitraryIrreducibilityClassifierSupplied =
        false
    ; arbitraryIrreducibilityClassifierSuppliedIsFalse =
        refl
    ; primitiveIrreducibilityBoundary =
        "Primitive irreducibility evidence is equality to the selected primitive sector constructor"
        ∷ "This inhabits irreducibility only for the four primitive constructor classes"
        ∷ "It is not an arbitrary irreducible-sector classifier over all DHR.SuperselectionSector values"
        ∷ []
    }

data DHRPrimitiveSectorClosureResidualBlocker : Set where
  primitiveClosureBlockedByGlobalForeignLaneIdentity :
    DHRPrimitiveSectorClosureResidualBlocker

  primitiveClosureBlockedByArbitrarySuperselectionSectorClassifier :
    DHRPrimitiveSectorClosureResidualBlocker

  primitiveClosureBlockedByDRFibreFunctorClassification :
    DHRPrimitiveSectorClosureResidualBlocker

record DHRPrimitiveSectorClassificationNonemptyIrreducibilityProgress
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    primitiveConstructorSurface :
      DHRPrimitiveSuperselectionSectorConstructorSurface

    primitiveLaneClassifierProgress :
      DHRPrimitiveSectorToLaneClassifierProgress

    primitiveCarrierPredicateProgress :
      DHRPrimitiveSectorCarrierPredicateProgress operator

    primitiveAssignedLaneEvidenceForClass :
      (sectorClass : DHRPrimitiveSectorClass) →
      DHRPrimitiveSectorAssignedLaneEvidence
        (primitiveSuperselectionSectorForClass sectorClass)
        (primitiveSectorClassAssignedLane sectorClass)

    primitiveCarrierPredicateEvidenceForClass :
      (sectorClass : DHRPrimitiveSectorClass) →
      DHRPrimitiveSectorNonemptyCarrierPredicateEvidence
        operator
        sectorClass

    primitiveIrreducibleEvidenceForClass :
      (sectorClass : DHRPrimitiveSectorClass) →
      DHRPrimitiveIrreducibleSectorEvidence sectorClass

    primitiveClassificationConstructed :
      Bool

    primitiveClassificationConstructedIsTrue :
      primitiveClassificationConstructed ≡ true

    primitiveNonemptyCarrierPredicateConstructed :
      Bool

    primitiveNonemptyCarrierPredicateConstructedIsTrue :
      primitiveNonemptyCarrierPredicateConstructed ≡ true

    primitiveIrreducibilityConstructed :
      Bool

    primitiveIrreducibilityConstructedIsTrue :
      primitiveIrreducibilityConstructed ≡ true

    globalForeignLaneIdentityForPrimitivePredicateSupplied :
      Bool

    globalForeignLaneIdentityForPrimitivePredicateSuppliedIsFalse :
      globalForeignLaneIdentityForPrimitivePredicateSupplied ≡ false

    arbitrarySectorClassifierSupplied :
      Bool

    arbitrarySectorClassifierSuppliedIsFalse :
      arbitrarySectorClassifierSupplied ≡ false

    dhrSuperselectionSectorLaneSupplyConstructed :
      Bool

    dhrSuperselectionSectorLaneSupplyConstructedIsFalse :
      dhrSuperselectionSectorLaneSupplyConstructed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    firstResidualBlocker :
      DHRPrimitiveSectorClosureResidualBlocker

    firstResidualBlockerIsGlobalForeignLaneIdentity :
      firstResidualBlocker
      ≡
      primitiveClosureBlockedByGlobalForeignLaneIdentity

    residualBlockers :
      List DHRPrimitiveSectorClosureResidualBlocker

    primitiveClosureProgressBoundary :
      List String

open DHRPrimitiveSectorClassificationNonemptyIrreducibilityProgress public

canonicalDHRPrimitiveSectorClassificationNonemptyIrreducibilityProgress :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRPrimitiveSectorClassificationNonemptyIrreducibilityProgress operator
canonicalDHRPrimitiveSectorClassificationNonemptyIrreducibilityProgress
  operator =
  record
    { primitiveConstructorSurface =
        canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
    ; primitiveLaneClassifierProgress =
        canonicalDHRPrimitiveSectorToLaneClassifierProgress
    ; primitiveCarrierPredicateProgress =
        canonicalDHRPrimitiveSectorCarrierPredicateProgress operator
    ; primitiveAssignedLaneEvidenceForClass =
        primitiveSectorAssignedLaneEvidenceForClass
    ; primitiveCarrierPredicateEvidenceForClass =
        primitiveSectorNonemptyCarrierPredicateEvidenceForClass operator
    ; primitiveIrreducibleEvidenceForClass =
        primitiveIrreducibleSectorEvidenceForClass
    ; primitiveClassificationConstructed =
        true
    ; primitiveClassificationConstructedIsTrue =
        refl
    ; primitiveNonemptyCarrierPredicateConstructed =
        true
    ; primitiveNonemptyCarrierPredicateConstructedIsTrue =
        refl
    ; primitiveIrreducibilityConstructed =
        true
    ; primitiveIrreducibilityConstructedIsTrue =
        refl
    ; globalForeignLaneIdentityForPrimitivePredicateSupplied =
        false
    ; globalForeignLaneIdentityForPrimitivePredicateSuppliedIsFalse =
        refl
    ; arbitrarySectorClassifierSupplied =
        false
    ; arbitrarySectorClassifierSuppliedIsFalse =
        refl
    ; dhrSuperselectionSectorLaneSupplyConstructed =
        false
    ; dhrSuperselectionSectorLaneSupplyConstructedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; firstResidualBlocker =
        primitiveClosureBlockedByGlobalForeignLaneIdentity
    ; firstResidualBlockerIsGlobalForeignLaneIdentity =
        refl
    ; residualBlockers =
        primitiveClosureBlockedByArbitrarySuperselectionSectorClassifier
        ∷ primitiveClosureBlockedByDRFibreFunctorClassification
        ∷ []
    ; primitiveClosureProgressBoundary =
        "Primitive Gate 6 closure progress now packages lane classification, sector-indexed nonempty carrier predicates, and primitive irreducibility evidence for the four named primitive sector classes"
        ∷ "The package deliberately stops before DHRSuperselectionSectorLaneSupply because that record requires global foreign-lane action identity on the selected carrier predicate"
        ∷ "For the current nontrivial G6 scaling operator, foreign-lane actions are live prime bumps, so global foreign-lane identity is not supplied by the tracked-prime locality laws"
        ∷ "No arbitrary SuperselectionSector classifier, DR fibre functor classifier, DR classification, gauge reconstruction, fusion law, braiding naturality, or symmetric hexagon closure is promoted"
        ∷ []
    }

data DHRG6TrackedLocalisedInterfaceAttemptBlocker : Set where
  blockedByNoDHRSectorSpecificNonemptyPredicate :
    DHRG6TrackedLocalisedInterfaceAttemptBlocker

  blockedByNoGlobalForeignLaneActionIdentity :
    DHRG6TrackedLocalisedInterfaceAttemptBlocker

record G6TrackedLocalisedCarrierSemanticsAttempt
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane) :
  Setω where
  field
    semanticSectorWitness :
      DHR.SuperselectionSector

    semanticSectorWitnessMatchesLocalisedSector :
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      semanticSectorWitness

    g6NonemptyCarrierPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    g6NonemptyCarrierWitness :
      G6.NontrivialTrackedLaneOperator.Carrier operator

    g6NonemptyCarrierWitnessSelected :
      g6NonemptyCarrierPredicate g6NonemptyCarrierWitness
      ≡
      true

    g6AssignedLaneActionPreservesNonemptyCarrier :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      g6NonemptyCarrierPredicate x ≡ true →
      g6NonemptyCarrierPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      true

    g6TrackedCrossLaneCommutationAvailable :
      G6.G6TrackedCrossLaneCommutationTheorem operator

    g6AssignedLaneTrackedPrimeBumpAvailable :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      G6.NontrivialTrackedLaneOperator.trackedValuationAt operator
        (G6.NontrivialTrackedLaneOperator.laneActionPrime operator lane)
        (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
      ≡
      suc
        (G6.NontrivialTrackedLaneOperator.trackedValuationAt operator
          (G6.NontrivialTrackedLaneOperator.laneActionPrime operator lane)
          x)

    g6ForeignTrackedPrimeLocalityAvailable :
      (otherLane : G6.Lane) →
      (q : TP.SSP) →
      G6.NontrivialTrackedLaneOperator.laneActionPrime operator otherLane
      ≢
      q →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      G6.NontrivialTrackedLaneOperator.trackedValuationAt operator q
        (G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x)
      ≡
      G6.NontrivialTrackedLaneOperator.trackedValuationAt operator q x

    g6OutsideBasisCoordinateIdentityAvailable :
      (p : Nat) →
      (otherLane : G6.Lane) →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      71 < p →
      G6.NontrivialTrackedLaneOperator.outsideBasisValuationAt operator p
        (G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x)
      ≡
      G6.NontrivialTrackedLaneOperator.outsideBasisValuationAt operator p x

    dhrSectorSpecificNonemptyPredicateRequest :
      Set₁

    globalForeignLaneIdentityForSelectedPredicateRequest :
      (selectedCarrierPredicate :
        G6.NontrivialTrackedLaneOperator.Carrier operator →
        Bool) →
      Set

    g6NonemptyCarrierPredicateConstructed :
      Bool

    g6NonemptyCarrierPredicateConstructedIsTrue :
      g6NonemptyCarrierPredicateConstructed ≡ true

    dhrSectorSpecificNonemptyPredicateConstructed :
      Bool

    dhrSectorSpecificNonemptyPredicateConstructedIsFalse :
      dhrSectorSpecificNonemptyPredicateConstructed ≡ false

    globalForeignLaneActionIdentityConstructed :
      Bool

    globalForeignLaneActionIdentityConstructedIsFalse :
      globalForeignLaneActionIdentityConstructed ≡ false

    nondegenerateLocalisedInterfaceConstructed :
      Bool

    nondegenerateLocalisedInterfaceConstructedIsFalse :
      nondegenerateLocalisedInterfaceConstructed ≡ false

    firstBlocker :
      DHRG6TrackedLocalisedInterfaceAttemptBlocker

    firstBlockerIsNoSectorSpecificPredicate :
      firstBlocker
      ≡
      blockedByNoDHRSectorSpecificNonemptyPredicate

    attemptBoundary :
      List String

open G6TrackedLocalisedCarrierSemanticsAttempt public

g6TrackedLocalisedCarrierSemanticsAttempt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  G6TrackedLocalisedCarrierSemanticsAttempt operator ρ lane
g6TrackedLocalisedCarrierSemanticsAttempt operator ρ lane =
  record
    { semanticSectorWitness =
        DHR.LocalisedEndomorphism.localisedSector ρ
    ; semanticSectorWitnessMatchesLocalisedSector =
        refl
    ; g6NonemptyCarrierPredicate =
        λ _ →
          true
    ; g6NonemptyCarrierWitness =
        G6.NontrivialTrackedLaneOperator.nontrivialWitness operator
    ; g6NonemptyCarrierWitnessSelected =
        refl
    ; g6AssignedLaneActionPreservesNonemptyCarrier =
        λ _ _ →
          refl
    ; g6TrackedCrossLaneCommutationAvailable =
        G6.trackedScalingCrossLaneCommutationFromNontrivialOperator
          operator
    ; g6AssignedLaneTrackedPrimeBumpAvailable =
        G6.NontrivialTrackedLaneOperator.laneActionBumpsTrackedPrime
          operator
          lane
    ; g6ForeignTrackedPrimeLocalityAvailable =
        G6.NontrivialTrackedLaneOperator.laneActionPreservesOtherTrackedPrime
          operator
    ; g6OutsideBasisCoordinateIdentityAvailable =
        G6.NontrivialTrackedLaneOperator.laneActionOutsideBasisIdentity
          operator
    ; dhrSectorSpecificNonemptyPredicateRequest =
        DHRNonemptySectorCarrierPredicateRequest operator ρ lane
    ; globalForeignLaneIdentityForSelectedPredicateRequest =
        DHRGlobalForeignLaneIdentityForPredicateRequest operator lane
    ; g6NonemptyCarrierPredicateConstructed =
        true
    ; g6NonemptyCarrierPredicateConstructedIsTrue =
        refl
    ; dhrSectorSpecificNonemptyPredicateConstructed =
        false
    ; dhrSectorSpecificNonemptyPredicateConstructedIsFalse =
        refl
    ; globalForeignLaneActionIdentityConstructed =
        false
    ; globalForeignLaneActionIdentityConstructedIsFalse =
        refl
    ; nondegenerateLocalisedInterfaceConstructed =
        false
    ; nondegenerateLocalisedInterfaceConstructedIsFalse =
        refl
    ; firstBlocker =
        blockedByNoDHRSectorSpecificNonemptyPredicate
    ; firstBlockerIsNoSectorSpecificPredicate =
        refl
    ; attemptBoundary =
        "G6.NontrivialTrackedLaneOperator supplies a concrete nontrivial carrier witness, so the all-carrier Bool predicate is nonempty and assigned-lane stable"
        ∷ "That all-carrier predicate is not a DHR sector-specific selected carrier predicate for rho and lane"
        ∷ "G6 tracked laws supply cross-lane commutation, tracked-prime bump/locality, and outside-basis coordinate identity"
        ∷ "They do not supply the global foreign-lane action identity required by NondegenerateLocalisedEndomorphismCarrierSemanticsInterface"
        ∷ "The attempt therefore records typed requests for a DHR nonempty sector predicate and global foreign-lane identity, while keeping the localised interface unconstructed"
        ∷ []
    }

data DHRFinalNondegenerateLocalisedCarrierMissingPiece : Set where
  missingFinalSectorSpecificNonemptyCarrierPredicate :
    DHRFinalNondegenerateLocalisedCarrierMissingPiece

  missingFinalGlobalForeignLaneActionIdentity :
    DHRFinalNondegenerateLocalisedCarrierMissingPiece

  missingFinalAssignedLaneActionPreservation :
    DHRFinalNondegenerateLocalisedCarrierMissingPiece

record FinalNondegenerateLocalisedCarrierSuppliedInterfaceAbsenceLedger
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane) :
  Setω where
  field
    g6TrackedAttempt :
      G6TrackedLocalisedCarrierSemanticsAttempt operator ρ lane

    suppliedInterfaceConsumerAvailable :
      NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
        operator
        ρ
        lane →
      LocalisedEndomorphismCarrierSemantics operator ρ lane

    suppliedInterfaceAdapterBoundaryAvailable :
      (external :
        NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
          operator
          ρ
          lane) →
      LocalisedEndomorphismCarrierAdapterBoundary
        operator
        ρ
        lane
        (nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          ρ
          lane
          external)

    sectorSpecificNonemptyCarrierPredicateRequest :
      Set₁

    globalForeignLaneIdentityForSelectedPredicateRequest :
      (selectedCarrierPredicate :
        G6.NontrivialTrackedLaneOperator.Carrier operator →
        Bool) →
      Set

    assignedLaneActionPreservationForSelectedPredicateRequest :
      (selectedCarrierPredicate :
        G6.NontrivialTrackedLaneOperator.Carrier operator →
        Bool) →
      Set

    g6AllCarrierPredicateNonemptyAvailable :
      Bool

    g6AllCarrierPredicateNonemptyAvailableIsTrue :
      g6AllCarrierPredicateNonemptyAvailable ≡ true

    g6AllCarrierAssignedLanePreservationAvailable :
      Bool

    g6AllCarrierAssignedLanePreservationAvailableIsTrue :
      g6AllCarrierAssignedLanePreservationAvailable ≡ true

    sectorSpecificNonemptyCarrierPredicateConstructed :
      Bool

    sectorSpecificNonemptyCarrierPredicateConstructedIsFalse :
      sectorSpecificNonemptyCarrierPredicateConstructed ≡ false

    globalForeignLaneActionIdentityConstructed :
      Bool

    globalForeignLaneActionIdentityConstructedIsFalse :
      globalForeignLaneActionIdentityConstructed ≡ false

    sectorSpecificAssignedLaneActionPreservationConstructed :
      Bool

    sectorSpecificAssignedLaneActionPreservationConstructedIsFalse :
      sectorSpecificAssignedLaneActionPreservationConstructed ≡ false

    nondegenerateLocalisedInterfaceConstructedFromG6 :
      Bool

    nondegenerateLocalisedInterfaceConstructedFromG6IsFalse :
      nondegenerateLocalisedInterfaceConstructedFromG6 ≡ false

    firstMissingPiece :
      DHRFinalNondegenerateLocalisedCarrierMissingPiece

    firstMissingPieceIsSectorSpecificPredicate :
      firstMissingPiece
      ≡
      missingFinalSectorSpecificNonemptyCarrierPredicate

    residualMissingPieces :
      List DHRFinalNondegenerateLocalisedCarrierMissingPiece

    finalLedgerBoundary :
      List String

open FinalNondegenerateLocalisedCarrierSuppliedInterfaceAbsenceLedger public

finalNondegenerateLocalisedCarrierSuppliedInterfaceAbsenceLedger :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  FinalNondegenerateLocalisedCarrierSuppliedInterfaceAbsenceLedger
    operator
    ρ
    lane
finalNondegenerateLocalisedCarrierSuppliedInterfaceAbsenceLedger
  operator ρ lane =
  record
    { g6TrackedAttempt =
        g6TrackedLocalisedCarrierSemanticsAttempt operator ρ lane
    ; suppliedInterfaceConsumerAvailable =
        nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          ρ
          lane
    ; suppliedInterfaceAdapterBoundaryAvailable =
        nondegenerateLocalisedInterfaceToAdapterBoundary
          operator
          ρ
          lane
    ; sectorSpecificNonemptyCarrierPredicateRequest =
        DHRNonemptySectorCarrierPredicateRequest operator ρ lane
    ; globalForeignLaneIdentityForSelectedPredicateRequest =
        DHRGlobalForeignLaneIdentityForPredicateRequest operator lane
    ; assignedLaneActionPreservationForSelectedPredicateRequest =
        DHRSelectedCarrierLaneActionPreservationRequest operator lane
    ; g6AllCarrierPredicateNonemptyAvailable =
        true
    ; g6AllCarrierPredicateNonemptyAvailableIsTrue =
        refl
    ; g6AllCarrierAssignedLanePreservationAvailable =
        true
    ; g6AllCarrierAssignedLanePreservationAvailableIsTrue =
        refl
    ; sectorSpecificNonemptyCarrierPredicateConstructed =
        false
    ; sectorSpecificNonemptyCarrierPredicateConstructedIsFalse =
        refl
    ; globalForeignLaneActionIdentityConstructed =
        false
    ; globalForeignLaneActionIdentityConstructedIsFalse =
        refl
    ; sectorSpecificAssignedLaneActionPreservationConstructed =
        false
    ; sectorSpecificAssignedLaneActionPreservationConstructedIsFalse =
        refl
    ; nondegenerateLocalisedInterfaceConstructedFromG6 =
        false
    ; nondegenerateLocalisedInterfaceConstructedFromG6IsFalse =
        refl
    ; firstMissingPiece =
        missingFinalSectorSpecificNonemptyCarrierPredicate
    ; firstMissingPieceIsSectorSpecificPredicate =
        refl
    ; residualMissingPieces =
        missingFinalGlobalForeignLaneActionIdentity
        ∷ missingFinalAssignedLaneActionPreservation
        ∷ []
    ; finalLedgerBoundary =
        "Final localised-interface ledger: G6 gives a nonempty all-carrier predicate and assigned-lane preservation for that all-carrier predicate"
        ∷ "The all-carrier predicate is not a DHR sector-specific selected nonempty carrier predicate for rho and lane"
        ∷ "G6 tracked-prime and outside-basis laws do not derive the required global foreign-lane identity on the selected carrier"
        ∷ "Assigned-lane preservation for the final selected predicate remains a supplied-interface field because the final selected predicate is absent"
        ∷ "A supplied NondegenerateLocalisedEndomorphismCarrierSemanticsInterface can be consumed by the existing carrier-semantics and adapter-boundary constructors"
        ∷ "No DHR bridge closure, DR classification, gauge reconstruction, or symmetric hexagon closure is promoted by this final ledger"
        ∷ []
    }

data DHRObjectClassifierIrreducibilityMissingPiece : Set where
  missingSuperselectionSectorConstructors :
    DHRObjectClassifierIrreducibilityMissingPiece

  missingSectorToCanonicalLanePredicate :
    DHRObjectClassifierIrreducibilityMissingPiece

  missingSectorSpecificNonemptyCarrierPredicate :
    DHRObjectClassifierIrreducibilityMissingPiece

  missingGlobalForeignLaneIdentityForSectorPredicate :
    DHRObjectClassifierIrreducibilityMissingPiece

  missingIrreducibleSectorPredicate :
    DHRObjectClassifierIrreducibilityMissingPiece

  missingDRFibreFunctorLaneRepClassifier :
    DHRObjectClassifierIrreducibilityMissingPiece

  missingPrimeLaneClassificationProof :
    DHRObjectClassifierIrreducibilityMissingPiece

record DHRObjectToLaneClassifierIrreducibilityLedger
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    candidateCanonicalLaneClassifier :
      DHR.LocalisedEndomorphism →
      G6.Lane

    candidateClassifierTargetsMaxwellLane :
      (ρ : DHR.LocalisedEndomorphism) →
      candidateCanonicalLaneClassifier ρ
      ≡
      G6.maxwellLane

    candidateCanonicalLaneClassifierConstructed :
      Bool

    candidateCanonicalLaneClassifierConstructedIsTrue :
      candidateCanonicalLaneClassifierConstructed ≡ true

    candidateClassifierCarriesSectorInvariantEvidence :
      Bool

    candidateClassifierCarriesSectorInvariantEvidenceIsFalse :
      candidateClassifierCarriesSectorInvariantEvidence ≡ false

    localisedEndomorphismPrimitiveAvailable :
      DHR.SuperselectionSector →
      DHR.LocalisedEndomorphism

    localisedEndomorphismHasSectorField :
      Bool

    localisedEndomorphismHasSectorFieldIsTrue :
      localisedEndomorphismHasSectorField ≡ true

    superselectionSectorConstructorsSupplied :
      Bool

    superselectionSectorConstructorsSuppliedIsFalse :
      superselectionSectorConstructorsSupplied ≡ false

    sectorToCanonicalLanePredicateSupplied :
      Bool

    sectorToCanonicalLanePredicateSuppliedIsFalse :
      sectorToCanonicalLanePredicateSupplied ≡ false

    sectorSpecificNonemptyCarrierPredicateSupplied :
      Bool

    sectorSpecificNonemptyCarrierPredicateSuppliedIsFalse :
      sectorSpecificNonemptyCarrierPredicateSupplied ≡ false

    globalForeignLaneIdentityForSectorPredicateSupplied :
      Bool

    globalForeignLaneIdentityForSectorPredicateSuppliedIsFalse :
      globalForeignLaneIdentityForSectorPredicateSupplied ≡ false

    categoryObjectTargetSocket :
      DHR.LocalisedEndomorphism →
      Set

    categoryObjectConstructorFromCanonicalLaneSupplied :
      Bool

    categoryObjectConstructorFromCanonicalLaneSuppliedIsFalse :
      categoryObjectConstructorFromCanonicalLaneSupplied ≡ false

    drH5EndUnitScalars :
      DHR.DRH5EndUnitScalars

    irreducibilityInputTarget :
      Set

    irreducibleSectorPredicateConstructed :
      Bool

    irreducibleSectorPredicateConstructedIsFalse :
      irreducibleSectorPredicateConstructed ≡ false

    primeLaneDHRClassification :
      DHR.PrimeLaneDHREndomorphismClassificationReceipt

    primeLaneClassificationProvesSerreTateHere :
      Bool

    primeLaneClassificationProvesSerreTateHereIsFalse :
      primeLaneClassificationProvesSerreTateHere ≡ false

    primeLaneClassificationProvesLaneDimensionHere :
      Bool

    primeLaneClassificationProvesLaneDimensionHereIsFalse :
      primeLaneClassificationProvesLaneDimensionHere ≡ false

    finalLocalisedInterfaceLedger :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane : G6.Lane) →
      FinalNondegenerateLocalisedCarrierSuppliedInterfaceAbsenceLedger
        operator
        ρ
        lane

    nondegenerateLocalisedInterfaceConstructedFromDHRFields :
      Bool

    nondegenerateLocalisedInterfaceConstructedFromDHRFieldsIsFalse :
      nondegenerateLocalisedInterfaceConstructedFromDHRFields ≡ false

    evidencedObjectToLaneClassifierConstructed :
      Bool

    evidencedObjectToLaneClassifierConstructedIsFalse :
      evidencedObjectToLaneClassifierConstructed ≡ false

    firstMissingPiece :
      DHRObjectClassifierIrreducibilityMissingPiece

    firstMissingPieceIsSectorToCanonicalLanePredicate :
      firstMissingPiece
      ≡
      missingSectorToCanonicalLanePredicate

    residualMissingPieces :
      List DHRObjectClassifierIrreducibilityMissingPiece

    finalIrreducibilityLedgerBoundary :
      List String

open DHRObjectToLaneClassifierIrreducibilityLedger public

dhrObjectToLaneClassifierIrreducibilityLedger :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRObjectToLaneClassifierIrreducibilityLedger operator
dhrObjectToLaneClassifierIrreducibilityLedger operator =
  record
    { candidateCanonicalLaneClassifier =
        λ _ →
          G6.maxwellLane
    ; candidateClassifierTargetsMaxwellLane =
        λ _ →
          refl
    ; candidateCanonicalLaneClassifierConstructed =
        true
    ; candidateCanonicalLaneClassifierConstructedIsTrue =
        refl
    ; candidateClassifierCarriesSectorInvariantEvidence =
        false
    ; candidateClassifierCarriesSectorInvariantEvidenceIsFalse =
        refl
    ; localisedEndomorphismPrimitiveAvailable =
        DHR.DHRFormalismPrimitiveReceipt.formalismLocalisedEndomorphismPrimitive
          DHR.canonicalDHRFormalismPrimitiveReceipt
    ; localisedEndomorphismHasSectorField =
        true
    ; localisedEndomorphismHasSectorFieldIsTrue =
        refl
    ; superselectionSectorConstructorsSupplied =
        false
    ; superselectionSectorConstructorsSuppliedIsFalse =
        refl
    ; sectorToCanonicalLanePredicateSupplied =
        false
    ; sectorToCanonicalLanePredicateSuppliedIsFalse =
        refl
    ; sectorSpecificNonemptyCarrierPredicateSupplied =
        false
    ; sectorSpecificNonemptyCarrierPredicateSuppliedIsFalse =
        refl
    ; globalForeignLaneIdentityForSectorPredicateSupplied =
        false
    ; globalForeignLaneIdentityForSectorPredicateSuppliedIsFalse =
        refl
    ; categoryObjectTargetSocket =
        DHR.DHRCategoryPrimitiveSurface.objectTarget
          DHR.canonicalDHRCategoryPrimitiveSurface
    ; categoryObjectConstructorFromCanonicalLaneSupplied =
        false
    ; categoryObjectConstructorFromCanonicalLaneSuppliedIsFalse =
        refl
    ; drH5EndUnitScalars =
        DHR.canonicalDRH5EndUnitScalars
    ; irreducibilityInputTarget =
        DHR.DRH5EndUnitScalars.irreducibilityInputTarget
          DHR.canonicalDRH5EndUnitScalars
    ; irreducibleSectorPredicateConstructed =
        false
    ; irreducibleSectorPredicateConstructedIsFalse =
        refl
    ; primeLaneDHRClassification =
        DHR.canonicalPrimeLaneDHREndomorphismClassificationReceipt
    ; primeLaneClassificationProvesSerreTateHere =
        DHR.PrimeLaneDHREndomorphismClassificationReceipt.provesSerreTateLaneGroupTheoremHere
          DHR.canonicalPrimeLaneDHREndomorphismClassificationReceipt
    ; primeLaneClassificationProvesSerreTateHereIsFalse =
        DHR.PrimeLaneDHREndomorphismClassificationReceipt.provesSerreTateLaneGroupTheoremHereIsFalse
          DHR.canonicalPrimeLaneDHREndomorphismClassificationReceipt
    ; primeLaneClassificationProvesLaneDimensionHere =
        DHR.PrimeLaneDHREndomorphismClassificationReceipt.provesLaneDimensionHere
          DHR.canonicalPrimeLaneDHREndomorphismClassificationReceipt
    ; primeLaneClassificationProvesLaneDimensionHereIsFalse =
        DHR.PrimeLaneDHREndomorphismClassificationReceipt.provesLaneDimensionHereIsFalse
          DHR.canonicalPrimeLaneDHREndomorphismClassificationReceipt
    ; finalLocalisedInterfaceLedger =
        finalNondegenerateLocalisedCarrierSuppliedInterfaceAbsenceLedger
          operator
    ; nondegenerateLocalisedInterfaceConstructedFromDHRFields =
        false
    ; nondegenerateLocalisedInterfaceConstructedFromDHRFieldsIsFalse =
        refl
    ; evidencedObjectToLaneClassifierConstructed =
        false
    ; evidencedObjectToLaneClassifierConstructedIsFalse =
        refl
    ; firstMissingPiece =
        missingSectorToCanonicalLanePredicate
    ; firstMissingPieceIsSectorToCanonicalLanePredicate =
        refl
    ; residualMissingPieces =
        missingSuperselectionSectorConstructors
        ∷ missingSectorSpecificNonemptyCarrierPredicate
        ∷ missingGlobalForeignLaneIdentityForSectorPredicate
        ∷ missingIrreducibleSectorPredicate
        ∷ missingDRFibreFunctorLaneRepClassifier
        ∷ missingPrimeLaneClassificationProof
        ∷ []
    ; finalIrreducibilityLedgerBoundary =
        "A total candidate LocalisedEndomorphism -> G6.Lane map is inhabited as the constant maxwellLane classifier"
        ∷ "That candidate is not classifier evidence: it carries no sector-lane invariant, no representation predicate on the tracked carrier, and no cross-lane invisibility proof"
        ∷ "DHR.LocalisedEndomorphism exposes localisedSector and DHRFormalismPrimitiveReceipt can make an abstract endomorphism from an abstract SuperselectionSector"
        ∷ "SuperselectionSector itself has no constructors here, and no predicate classifies a sector as maxwell, schrodinger, gr, or empirical"
        ∷ "DHRCategoryPrimitiveSurface.objectTarget is a socket, not a constructor for canonical-lane objects"
        ∷ "DR H5 records irreducibility as an input target only; no irreducible-sector predicate is supplied for object classification"
        ∷ "Prime-lane DHR classification remains conditional on SerreTate/lane-group input and does not prove laneDimension here"
        ∷ "The final nondegenerate localised interface is therefore irreducibly blocked by missing sector-to-lane and sector-specific carrier predicates"
        ∷ []
    }

record DHRTrackedLaneBridgeObligation
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    objectLaneClassifierTarget :
      DHR.LocalisedEndomorphism →
      G6.Lane

    sectorRepresentationTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    assignedLaneRepresentationPreservedTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      sectorRepresentationTarget ρ x ≡ true →
      sectorRepresentationTarget ρ
        (G6.NontrivialTrackedLaneOperator.laneAction
          operator
          (objectLaneClassifierTarget ρ)
          x)
      ≡
      true

    crossLaneInvisibilityTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (otherLane : G6.Lane) →
      objectLaneClassifierTarget ρ ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      sectorRepresentationTarget ρ x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction
        operator
        otherLane
        x
      ≡
      x

    localisedEndomorphismCarrierSemanticsTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      LocalisedEndomorphismCarrierSemantics
        operator
        ρ
        (objectLaneClassifierTarget ρ)

    localisedEndomorphismCarrierSemanticsConstructed :
      Bool

    localisedEndomorphismCarrierSemanticsConstructedIsFalse :
      localisedEndomorphismCarrierSemanticsConstructed ≡ false

    classifierEvidenceConstructed :
      Bool

    classifierEvidenceConstructedIsFalse :
      classifierEvidenceConstructed ≡ false

    trackedIntertwinerCarrierActionTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    intertwinerTrackedCarrierSemanticsTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      IntertwinerTrackedCarrierSemantics
        operator
        ρ
        σ
        f
        (objectLaneClassifierTarget ρ)
        (objectLaneClassifierTarget σ)
        (localisedEndomorphismCarrierSemanticsTarget ρ)
        (localisedEndomorphismCarrierSemanticsTarget σ)

    intertwinerTrackedCarrierSemanticsConstructed :
      Bool

    intertwinerTrackedCarrierSemanticsConstructedIsFalse :
      intertwinerTrackedCarrierSemanticsConstructed ≡ false

    trackedIntertwinerCarrierActionConstructed :
      Bool

    trackedIntertwinerCarrierActionConstructedIsFalse :
      trackedIntertwinerCarrierActionConstructed ≡ false

    bridgeObligationBoundary :
      List String

open DHRTrackedLaneBridgeObligation public

record DHRFusionRulesFromLaneAlgebra : Setω where
  field
    dhrCategoryTarget :
      DHR.SymmetricTensorCStarCategoryTarget

    drHypotheses :
      DHR.DRHypothesesForDASHI

    laneDimensionStatus :
      LaneDimension.LaneDimensionTheoremSurfaceStatus

    laneDimensionTable :
      PrimeLane.MonsterPrimeLane →
      Nat

    fusionProductTarget :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    fusionMultiplicityTarget :
      PrimeLane.MonsterPrimeLane →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Nat →
      Set

    fusionRulesComputed :
      Bool

    fusionRulesComputedIsFalse :
      fusionRulesComputed ≡ false

    laneDimensionOnlyNotFusionRules :
      Bool

    laneDimensionOnlyNotFusionRulesIsTrue :
      laneDimensionOnlyNotFusionRules ≡ true

    fusionBoundary :
      List String

open DHRFusionRulesFromLaneAlgebra public

record DHRBraidingNaturalitySquareDecomposition : Setω where
  field
    sourceLeft :
      DHR.LocalisedEndomorphism

    sourceRight :
      DHR.LocalisedEndomorphism

    targetLeft :
      DHR.LocalisedEndomorphism

    targetRight :
      DHR.LocalisedEndomorphism

    leftIntertwiner :
      DHR.Intertwiner sourceLeft targetLeft

    rightIntertwiner :
      DHR.Intertwiner sourceRight targetRight

    sourceBraidingTarget :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    targetBraidingTarget :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    tensorMorphismTopTarget :
      Set

    tensorMorphismBottomTarget :
      Set

    naturalitySquareCommutesTarget :
      Set

    naturalitySquareInhabited :
      Bool

    naturalitySquareInhabitedIsFalse :
      naturalitySquareInhabited ≡ false

    squareBoundary :
      List String

open DHRBraidingNaturalitySquareDecomposition public

record DHRHexagonObligation : Setω where
  field
    fusionSurface :
      DHRFusionRulesFromLaneAlgebra

    associatorTarget :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    unitCoherenceTarget :
      DHR.LocalisedEndomorphism →
      Set

    braidingTarget :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    leftHexagonTarget :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    rightHexagonTarget :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    symmetryInvolutiveTarget :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    symmetricMonoidalCoherenceProved :
      Bool

    symmetricMonoidalCoherenceProvedIsFalse :
      symmetricMonoidalCoherenceProved ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    hexagonBoundary :
      List String

open DHRHexagonObligation public

postulate
  abstractDHRFusionProductTarget :
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    Set

  abstractDHRFusionMultiplicityTarget :
    PrimeLane.MonsterPrimeLane →
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    Nat →
    Set

  abstractDHRAssociatorTarget :
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    Set

  abstractDHRUnitCoherenceTarget :
    DHR.LocalisedEndomorphism →
    Set

  abstractDHRBraidingTarget :
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    Set

  abstractDHRLeftHexagonTarget :
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    Set

  abstractDHRRightHexagonTarget :
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    Set

  abstractDHRSymmetryInvolutiveTarget :
    DHR.LocalisedEndomorphism →
    DHR.LocalisedEndomorphism →
    Set

  abstractDHRBraidingNaturalitySourceLeft :
    DHR.LocalisedEndomorphism

  abstractDHRBraidingNaturalitySourceRight :
    DHR.LocalisedEndomorphism

  abstractDHRBraidingNaturalityTargetLeft :
    DHR.LocalisedEndomorphism

  abstractDHRBraidingNaturalityTargetRight :
    DHR.LocalisedEndomorphism

  abstractDHRBraidingNaturalityLeftIntertwiner :
    DHR.Intertwiner
      abstractDHRBraidingNaturalitySourceLeft
      abstractDHRBraidingNaturalityTargetLeft

  abstractDHRBraidingNaturalityRightIntertwiner :
    DHR.Intertwiner
      abstractDHRBraidingNaturalitySourceRight
      abstractDHRBraidingNaturalityTargetRight

  abstractDHRBraidingNaturalitySquareCommutesTarget :
    Set

canonicalDHRBraidingNaturalitySquareDecomposition :
  DHRBraidingNaturalitySquareDecomposition
canonicalDHRBraidingNaturalitySquareDecomposition =
  record
    { sourceLeft =
        abstractDHRBraidingNaturalitySourceLeft
    ; sourceRight =
        abstractDHRBraidingNaturalitySourceRight
    ; targetLeft =
        abstractDHRBraidingNaturalityTargetLeft
    ; targetRight =
        abstractDHRBraidingNaturalityTargetRight
    ; leftIntertwiner =
        abstractDHRBraidingNaturalityLeftIntertwiner
    ; rightIntertwiner =
        abstractDHRBraidingNaturalityRightIntertwiner
    ; sourceBraidingTarget =
        abstractDHRBraidingTarget
    ; targetBraidingTarget =
        abstractDHRBraidingTarget
    ; tensorMorphismTopTarget =
        DHR.abstractDHRCategoryTensorMorphismTarget
          abstractDHRBraidingNaturalitySourceLeft
          abstractDHRBraidingNaturalityTargetLeft
          abstractDHRBraidingNaturalitySourceRight
          abstractDHRBraidingNaturalityTargetRight
          abstractDHRBraidingNaturalityLeftIntertwiner
          abstractDHRBraidingNaturalityRightIntertwiner
    ; tensorMorphismBottomTarget =
        DHR.abstractDHRCategoryTensorMorphismTarget
          abstractDHRBraidingNaturalitySourceRight
          abstractDHRBraidingNaturalityTargetRight
          abstractDHRBraidingNaturalitySourceLeft
          abstractDHRBraidingNaturalityTargetLeft
          abstractDHRBraidingNaturalityRightIntertwiner
          abstractDHRBraidingNaturalityLeftIntertwiner
    ; naturalitySquareCommutesTarget =
        abstractDHRBraidingNaturalitySquareCommutesTarget
    ; naturalitySquareInhabited =
        false
    ; naturalitySquareInhabitedIsFalse =
        refl
    ; squareBoundary =
        "Naturality requires a square for intertwiners f : rho -> rho' and g : sigma -> sigma'"
        ∷ "The top and bottom legs are tensor-morphism targets because DHR tensor morphisms are still sockets"
        ∷ "The side legs are braiding targets because the statistics operator has not been computed as a braiding morphism"
        ∷ "No commutative-square inhabitant is supplied here"
        ∷ []
    }

canonicalDHRFusionRulesFromLaneAlgebra :
  DHRFusionRulesFromLaneAlgebra
canonicalDHRFusionRulesFromLaneAlgebra =
  record
    { dhrCategoryTarget =
        DHR.canonicalSymmetricTensorCStarCategoryTarget
    ; drHypotheses =
        DHR.canonicalDRHypothesesForDASHI
    ; laneDimensionStatus =
        LaneDimension.authorityBackedNoLocalLaneDimensionPromotion
    ; laneDimensionTable =
        LaneDimension.laneDimensionTable
    ; fusionProductTarget =
        abstractDHRFusionProductTarget
    ; fusionMultiplicityTarget =
        abstractDHRFusionMultiplicityTarget
    ; fusionRulesComputed =
        false
    ; fusionRulesComputedIsFalse =
        refl
    ; laneDimensionOnlyNotFusionRules =
        true
    ; laneDimensionOnlyNotFusionRulesIsTrue =
        refl
    ; fusionBoundary =
        "laneDimension is consumed as an authority-backed conditional table, not a local theorem promotion"
        ∷ "DHR fusion still requires tensor-product and multiplicity laws on localised endomorphisms"
        ∷ "The DR hypothesis package is an authority input, not a computed fusion-rule proof"
        ∷ []
    }

canonicalDHRHexagonObligation :
  DHRHexagonObligation
canonicalDHRHexagonObligation =
  record
    { fusionSurface =
        canonicalDHRFusionRulesFromLaneAlgebra
    ; associatorTarget =
        abstractDHRAssociatorTarget
    ; unitCoherenceTarget =
        abstractDHRUnitCoherenceTarget
    ; braidingTarget =
        abstractDHRBraidingTarget
    ; leftHexagonTarget =
        abstractDHRLeftHexagonTarget
    ; rightHexagonTarget =
        abstractDHRRightHexagonTarget
    ; symmetryInvolutiveTarget =
        abstractDHRSymmetryInvolutiveTarget
    ; symmetricMonoidalCoherenceProved =
        false
    ; symmetricMonoidalCoherenceProvedIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; hexagonBoundary =
        "The symmetric monoidal hexagon is an explicit target over DHR localised endomorphisms"
        ∷ "Neither gauge assignment nor DR classification is promoted by this surface"
        ∷ "A future promotion must inhabit associator, unit, braiding, left-hexagon, right-hexagon, and symmetry-involutive targets"
        ∷ []
    }

record DHRHexagonFailClosedCoherenceReceipt : Setω where
  field
    status :
      DHRHexagonClosureStatus

    obligation :
      DHRHexagonObligation

    categoryPrimitives :
      DHR.DHRCategoryPrimitiveSurface

    drHypotheses :
      DHR.DRHypothesesForDASHI

    dependencyReceipts :
      List DHRHexagonDependency

    openObligations :
      List DHRHexagonOpenObligation

    closureBlockers :
      List DHRHexagonClosureBlocker

    unitObjectTargetReceipt :
      DHR.LocalisedEndomorphism →
      Set

    tensorObjectTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    unitCoherenceTargetReceipt :
      DHR.LocalisedEndomorphism →
      Set

    braidingTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    statisticsSymmetryTargetReceipt :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.DHRStatisticsFormulaSocket ρ σ →
      Set

    associatorTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    leftHexagonTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    rightHexagonTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    symmetryInvolutiveTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    primitiveCategoryLawsProved :
      Bool

    primitiveCategoryLawsProvedIsFalse :
      primitiveCategoryLawsProved ≡ false

    unitCoherenceClosed :
      Bool

    unitCoherenceClosedIsFalse :
      unitCoherenceClosed ≡ false

    braidingNaturalityClosed :
      Bool

    braidingNaturalityClosedIsFalse :
      braidingNaturalityClosed ≡ false

    symmetricHexagonClosed :
      Bool

    symmetricHexagonClosedIsFalse :
      symmetricHexagonClosed ≡ false

    fullTransportDRHexagonClosed :
      Bool

    fullTransportDRHexagonClosedIsFalse :
      fullTransportDRHexagonClosed ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    clayClaimPromoted :
      Bool

    clayClaimPromotedIsFalse :
      clayClaimPromoted ≡ false

    w3GatePromoted :
      Bool

    w3GatePromotedIsFalse :
      w3GatePromoted ≡ false

    w4GatePromoted :
      Bool

    w4GatePromotedIsFalse :
      w4GatePromoted ≡ false

    w5GatePromoted :
      Bool

    w5GatePromotedIsFalse :
      w5GatePromoted ≡ false

    failClosedBoundary :
      List String

open DHRHexagonFailClosedCoherenceReceipt public

canonicalDHRHexagonFailClosedCoherenceReceipt :
  DHRHexagonFailClosedCoherenceReceipt
canonicalDHRHexagonFailClosedCoherenceReceipt =
  record
    { status =
        dhrHexagonFailClosedReceiptOnly
    ; obligation =
        canonicalDHRHexagonObligation
    ; categoryPrimitives =
        DHR.canonicalDHRCategoryPrimitiveSurface
    ; drHypotheses =
        DHRFusionRulesFromLaneAlgebra.drHypotheses
          canonicalDHRFusionRulesFromLaneAlgebra
    ; dependencyReceipts =
        canonicalDHRHexagonDependencies
    ; openObligations =
        canonicalDHRHexagonOpenObligations
    ; closureBlockers =
        canonicalDHRHexagonClosureBlockers
    ; unitObjectTargetReceipt =
        DHR.DHRCategoryPrimitiveSurface.unitObjectTarget
          DHR.canonicalDHRCategoryPrimitiveSurface
    ; tensorObjectTargetReceipt =
        DHR.DHRCategoryPrimitiveSurface.tensorObjectTarget
          DHR.canonicalDHRCategoryPrimitiveSurface
    ; unitCoherenceTargetReceipt =
        DHRHexagonObligation.unitCoherenceTarget
          canonicalDHRHexagonObligation
    ; braidingTargetReceipt =
        DHRHexagonObligation.braidingTarget
          canonicalDHRHexagonObligation
    ; statisticsSymmetryTargetReceipt =
        DHR.DHRCategoryPrimitiveSurface.symmetryFromStatisticsTarget
          DHR.canonicalDHRCategoryPrimitiveSurface
    ; associatorTargetReceipt =
        DHRHexagonObligation.associatorTarget
          canonicalDHRHexagonObligation
    ; leftHexagonTargetReceipt =
        DHRHexagonObligation.leftHexagonTarget
          canonicalDHRHexagonObligation
    ; rightHexagonTargetReceipt =
        DHRHexagonObligation.rightHexagonTarget
          canonicalDHRHexagonObligation
    ; symmetryInvolutiveTargetReceipt =
        DHRHexagonObligation.symmetryInvolutiveTarget
          canonicalDHRHexagonObligation
    ; primitiveCategoryLawsProved =
        DHR.DHRCategoryPrimitiveSurface.primitiveCategoryLawsProved
          DHR.canonicalDHRCategoryPrimitiveSurface
    ; primitiveCategoryLawsProvedIsFalse =
        DHR.DHRCategoryPrimitiveSurface.primitiveCategoryLawsProvedIsFalse
          DHR.canonicalDHRCategoryPrimitiveSurface
    ; unitCoherenceClosed =
        false
    ; unitCoherenceClosedIsFalse =
        refl
    ; braidingNaturalityClosed =
        false
    ; braidingNaturalityClosedIsFalse =
        refl
    ; symmetricHexagonClosed =
        false
    ; symmetricHexagonClosedIsFalse =
        refl
    ; fullTransportDRHexagonClosed =
        false
    ; fullTransportDRHexagonClosedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; clayClaimPromoted =
        false
    ; clayClaimPromotedIsFalse =
        refl
    ; w3GatePromoted =
        false
    ; w3GatePromotedIsFalse =
        refl
    ; w4GatePromoted =
        false
    ; w4GatePromotedIsFalse =
        refl
    ; w5GatePromoted =
        false
    ; w5GatePromotedIsFalse =
        refl
    ; failClosedBoundary =
        "Unit coherence is only a target receipt: the DHR tensor unit and tensor product remain abstract category sockets"
        ∷ "Braiding is only a target receipt from statistics symmetry; no intertwiner naturality square is inhabited"
        ∷ "The left and right hexagon targets are recorded, but neither hexagon proof is supplied"
        ∷ "fullTransportDRHexagonClosed remains false until unit, braiding naturality, and both hexagon fields are inhabited"
        ∷ "No terminal, Clay, W3, W4, W5, gauge assignment, or DR classification promotion is constructed"
        ∷ []
    }

canonicalDHRHexagonUnitCoherenceStillOpen :
  DHRHexagonFailClosedCoherenceReceipt.unitCoherenceClosed
    canonicalDHRHexagonFailClosedCoherenceReceipt
  ≡
  false
canonicalDHRHexagonUnitCoherenceStillOpen =
  refl

canonicalDHRHexagonBraidingNaturalityStillOpen :
  DHRHexagonFailClosedCoherenceReceipt.braidingNaturalityClosed
    canonicalDHRHexagonFailClosedCoherenceReceipt
  ≡
  false
canonicalDHRHexagonBraidingNaturalityStillOpen =
  refl

canonicalDHRHexagonSymmetricHexagonStillOpen :
  DHRHexagonFailClosedCoherenceReceipt.symmetricHexagonClosed
    canonicalDHRHexagonFailClosedCoherenceReceipt
  ≡
  false
canonicalDHRHexagonSymmetricHexagonStillOpen =
  refl

canonicalDHRHexagonFullTransportStillOpen :
  DHRHexagonFailClosedCoherenceReceipt.fullTransportDRHexagonClosed
    canonicalDHRHexagonFailClosedCoherenceReceipt
  ≡
  false
canonicalDHRHexagonFullTransportStillOpen =
  refl

------------------------------------------------------------------------
-- User-supplied DHR sector/lane primitive interface.
--
-- This is the narrow non-promoting surface requested for a supplied
-- DHRSuperselectionSector/sectorLane package.  It consumes an explicitly
-- selected nonempty carrier predicate plus foreign-lane identity evidence and
-- produces only the existing nondegenerate localised carrier interface.

DHRSuperselectionSector :
  Set
DHRSuperselectionSector =
  DHR.SuperselectionSector

record DHRSuperselectionSectorLaneSupply
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism) :
  Set₁ where
  field
    dhrSuperselectionSector :
      DHRSuperselectionSector

    dhrSuperselectionSectorMatchesLocalisedSector :
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      dhrSuperselectionSector

    sectorLane :
      G6.Lane

    selectedSectorCarrierPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    selectedSectorCarrierNonemptyWitness :
      G6.NontrivialTrackedLaneOperator.Carrier operator

    selectedSectorCarrierNonemptyWitnessSelected :
      selectedSectorCarrierPredicate
        selectedSectorCarrierNonemptyWitness
      ≡
      true

    sectorLaneActionPreservesSelectedCarrier :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedSectorCarrierPredicate x ≡ true →
      selectedSectorCarrierPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction operator sectorLane x)
      ≡
      true

    foreignLaneActionIdentityOnSelectedCarrier :
      (otherLane : G6.Lane) →
      sectorLane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedSectorCarrierPredicate x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    sectorLaneSupplyConstructed :
      Bool

    sectorLaneSupplyConstructedIsTrue :
      sectorLaneSupplyConstructed ≡ true

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    dhrSuperselectionSectorLaneSupplyBoundary :
      List String

open DHRSuperselectionSectorLaneSupply public

sectorPrimaryLane :
  {operator : G6.NontrivialTrackedLaneOperator} →
  {ρ : DHR.LocalisedEndomorphism} →
  DHRSuperselectionSectorLaneSupply operator ρ →
  G6.Lane
sectorPrimaryLane supply =
  sectorLane supply

sectorPrimaryLaneMatchesSectorLane :
  {operator : G6.NontrivialTrackedLaneOperator} →
  {ρ : DHR.LocalisedEndomorphism} →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  sectorPrimaryLane supply
  ≡
  sectorLane supply
sectorPrimaryLaneMatchesSectorLane _ =
  refl

dhrSectorLaneSupplyForeignLaneIdentityEliminator :
  {operator : G6.NontrivialTrackedLaneOperator} →
  {ρ : DHR.LocalisedEndomorphism} →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  (otherLane : G6.Lane) →
  sectorPrimaryLane supply ≢ otherLane →
  (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
  selectedSectorCarrierPredicate supply x ≡ true →
  G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
  ≡
  x
dhrSectorLaneSupplyForeignLaneIdentityEliminator
  supply
  otherLane
  sectorPrimaryLaneDistinctFromOther
  x
  xSelected =
  foreignLaneActionIdentityOnSelectedCarrier
    supply
    otherLane
    sectorPrimaryLaneDistinctFromOther
    x
    xSelected

dhrSectorLaneSupplyFromExplicitData :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (sector : DHR.SuperselectionSector) →
  (lane : G6.Lane) →
  DHR.LocalisedEndomorphism.localisedSector ρ
  ≡
  sector →
  (selectedCarrierPredicate :
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Bool) →
  (selectedCarrierWitness :
    G6.NontrivialTrackedLaneOperator.Carrier operator) →
  selectedCarrierPredicate selectedCarrierWitness
  ≡
  true →
  ((x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    selectedCarrierPredicate x ≡ true →
    selectedCarrierPredicate
      (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
    ≡
    true) →
  ((otherLane : G6.Lane) →
    lane ≢ otherLane →
    (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    selectedCarrierPredicate x ≡ true →
    G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
    ≡
    x) →
  DHRSuperselectionSectorLaneSupply operator ρ
dhrSectorLaneSupplyFromExplicitData
  operator
  ρ
  sector
  lane
  sectorMatchesLocalised
  selectedCarrierPredicate
  selectedCarrierWitness
  selectedCarrierWitnessSelected
  assignedLanePreservesSelectedCarrier
  foreignLaneIdentityOnSelectedCarrier =
  record
    { dhrSuperselectionSector =
        sector
    ; dhrSuperselectionSectorMatchesLocalisedSector =
        sectorMatchesLocalised
    ; sectorLane =
        lane
    ; selectedSectorCarrierPredicate =
        selectedCarrierPredicate
    ; selectedSectorCarrierNonemptyWitness =
        selectedCarrierWitness
    ; selectedSectorCarrierNonemptyWitnessSelected =
        selectedCarrierWitnessSelected
    ; sectorLaneActionPreservesSelectedCarrier =
        assignedLanePreservesSelectedCarrier
    ; foreignLaneActionIdentityOnSelectedCarrier =
        foreignLaneIdentityOnSelectedCarrier
    ; sectorLaneSupplyConstructed =
        true
    ; sectorLaneSupplyConstructedIsTrue =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; dhrSuperselectionSectorLaneSupplyBoundary =
        "Explicit DHR sector/lane bridge: localisedSector, selected carrier predicate, assigned-lane preservation, and foreign-lane identity are consumed as inputs"
        ∷ "The constructor is generic in sector and lane; it does not infer arbitrary sector classification or foreign-lane identity from tracked-prime coordinate locality"
        ∷ "This constructs only DHRSuperselectionSectorLaneSupply and does not promote DR classification, gauge reconstruction, or symmetric hexagon closure"
        ∷ []
    }

primitiveDHRClassSectorLaneSupply :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (constructorSurface :
    DHRPrimitiveSuperselectionSectorConstructorSurface) →
  (sectorClass : DHRPrimitiveSectorClass) →
  DHR.LocalisedEndomorphism.localisedSector ρ
  ≡
  DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
    constructorSurface
    sectorClass →
  (selectedCarrierPredicate :
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Bool) →
  (selectedCarrierWitness :
    G6.NontrivialTrackedLaneOperator.Carrier operator) →
  selectedCarrierPredicate selectedCarrierWitness
  ≡
  true →
  ((x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    selectedCarrierPredicate x ≡ true →
    selectedCarrierPredicate
      (G6.NontrivialTrackedLaneOperator.laneAction
        operator
        (primitiveSectorClassAssignedLane sectorClass)
        x)
    ≡
    true) →
  ((otherLane : G6.Lane) →
    primitiveSectorClassAssignedLane sectorClass ≢ otherLane →
    (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    selectedCarrierPredicate x ≡ true →
    G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
    ≡
    x) →
  DHRSuperselectionSectorLaneSupply operator ρ
primitiveDHRClassSectorLaneSupply
  operator
  ρ
  constructorSurface
  sectorClass
  sectorMatchesPrimitiveConstructor
  selectedCarrierPredicate
  selectedCarrierWitness
  selectedCarrierWitnessSelected
  assignedLanePreservesSelectedCarrier
  foreignLaneIdentityOnSelectedCarrier =
  dhrSectorLaneSupplyFromExplicitData
    operator
    ρ
    (DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
      constructorSurface
      sectorClass)
    (primitiveSectorClassAssignedLane sectorClass)
    sectorMatchesPrimitiveConstructor
    selectedCarrierPredicate
    selectedCarrierWitness
    selectedCarrierWitnessSelected
    assignedLanePreservesSelectedCarrier
    foreignLaneIdentityOnSelectedCarrier

primitiveDHRClassSectorLaneSupplyPrimaryLaneMatchesClass :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (constructorSurface :
    DHRPrimitiveSuperselectionSectorConstructorSurface) →
  (sectorClass : DHRPrimitiveSectorClass) →
  (sectorMatchesPrimitiveConstructor :
    DHR.LocalisedEndomorphism.localisedSector ρ
    ≡
    DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
      constructorSurface
      sectorClass) →
  (selectedCarrierPredicate :
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Bool) →
  (selectedCarrierWitness :
    G6.NontrivialTrackedLaneOperator.Carrier operator) →
  (selectedCarrierWitnessSelected :
    selectedCarrierPredicate selectedCarrierWitness
    ≡
    true) →
  (assignedLanePreservesSelectedCarrier :
    (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    selectedCarrierPredicate x ≡ true →
    selectedCarrierPredicate
      (G6.NontrivialTrackedLaneOperator.laneAction
        operator
        (primitiveSectorClassAssignedLane sectorClass)
        x)
    ≡
    true) →
  (foreignLaneIdentityOnSelectedCarrier :
    (otherLane : G6.Lane) →
    primitiveSectorClassAssignedLane sectorClass ≢ otherLane →
    (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    selectedCarrierPredicate x ≡ true →
    G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
    ≡
    x) →
  sectorPrimaryLane
    (primitiveDHRClassSectorLaneSupply
      operator
      ρ
      constructorSurface
      sectorClass
      sectorMatchesPrimitiveConstructor
      selectedCarrierPredicate
      selectedCarrierWitness
      selectedCarrierWitnessSelected
      assignedLanePreservesSelectedCarrier
      foreignLaneIdentityOnSelectedCarrier)
  ≡
  primitiveSectorClassAssignedLane sectorClass
primitiveDHRClassSectorLaneSupplyPrimaryLaneMatchesClass
  operator
  ρ
  constructorSurface
  sectorClass
  sectorMatchesPrimitiveConstructor
  selectedCarrierPredicate
  selectedCarrierWitness
  selectedCarrierWitnessSelected
  assignedLanePreservesSelectedCarrier
  foreignLaneIdentityOnSelectedCarrier =
  refl

primitiveSectorCarrierPredicateAndForeignIdentityToLaneSupply :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (constructorSurface :
    DHRPrimitiveSuperselectionSectorConstructorSurface) →
  (sectorClass : DHRPrimitiveSectorClass) →
  (sectorMatchesPrimitiveConstructor :
    DHR.LocalisedEndomorphism.localisedSector ρ
    ≡
    DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
      constructorSurface
      sectorClass) →
  (carrierPredicateRequest :
    DHRNonemptySectorCarrierPredicateRequest
      operator
      ρ
      (primitiveSectorClassAssignedLane sectorClass)) →
  (globalForeignIdentityRequest :
    DHRGlobalForeignLaneIdentityForPredicateRequest
      operator
      (primitiveSectorClassAssignedLane sectorClass)
      (DHRNonemptySectorCarrierPredicateRequest.requestedSelectedCarrierPredicate
        carrierPredicateRequest)) →
  DHRSuperselectionSectorLaneSupply operator ρ
primitiveSectorCarrierPredicateAndForeignIdentityToLaneSupply
  operator
  ρ
  constructorSurface
  sectorClass
  sectorMatchesPrimitiveConstructor
  carrierPredicateRequest
  globalForeignIdentityRequest =
  primitiveDHRClassSectorLaneSupply
    operator
    ρ
    constructorSurface
    sectorClass
    sectorMatchesPrimitiveConstructor
    (DHRNonemptySectorCarrierPredicateRequest.requestedSelectedCarrierPredicate
      carrierPredicateRequest)
    (DHRNonemptySectorCarrierPredicateRequest.requestedSelectedCarrierWitness
      carrierPredicateRequest)
    (DHRNonemptySectorCarrierPredicateRequest.requestedSelectedCarrierWitnessSelected
      carrierPredicateRequest)
    (DHRNonemptySectorCarrierPredicateRequest.requestedAssignedLaneActionPreservesSelectedCarrier
      carrierPredicateRequest)
    (DHRGlobalForeignLaneIdentityForPredicateRequest.requestedGlobalForeignLaneActionIdentity
      globalForeignIdentityRequest)

primitiveSectorCarrierPredicateAndForeignIdentityToLaneSupplyBoundary :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (constructorSurface :
    DHRPrimitiveSuperselectionSectorConstructorSurface) →
  (sectorClass : DHRPrimitiveSectorClass) →
  (sectorMatchesPrimitiveConstructor :
    DHR.LocalisedEndomorphism.localisedSector ρ
    ≡
    DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
      constructorSurface
      sectorClass) →
  (carrierPredicateRequest :
    DHRNonemptySectorCarrierPredicateRequest
      operator
      ρ
      (primitiveSectorClassAssignedLane sectorClass)) →
  (globalForeignIdentityRequest :
    DHRGlobalForeignLaneIdentityForPredicateRequest
      operator
      (primitiveSectorClassAssignedLane sectorClass)
      (DHRNonemptySectorCarrierPredicateRequest.requestedSelectedCarrierPredicate
        carrierPredicateRequest)) →
  List String
primitiveSectorCarrierPredicateAndForeignIdentityToLaneSupplyBoundary
  operator
  ρ
  constructorSurface
  sectorClass
  sectorMatchesPrimitiveConstructor
  carrierPredicateRequest
  globalForeignIdentityRequest =
  ("Primitive supplied-sector bridge: sector-specific nonempty predicate request and global foreign-lane identity request are jointly consumed into DHRSuperselectionSectorLaneSupply"
  ∷ "This narrows the next local blocker to supplying global foreign-lane identity for the selected predicate when only the primitive constructor path is available"
  ∷ "Arbitrary SuperselectionSector classification and irreducibility evidence remain open"
  ∷ [])
  ++ DHRNonemptySectorCarrierPredicateRequest.predicateRequestBoundary
      carrierPredicateRequest
  ++ DHRGlobalForeignLaneIdentityForPredicateRequest.identityRequestBoundary
      globalForeignIdentityRequest

nondegenerateInterfaceToCarrierPredicateRequest :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  (external :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      lane) →
  DHRNonemptySectorCarrierPredicateRequest operator ρ lane
nondegenerateInterfaceToCarrierPredicateRequest
  operator ρ lane external =
  record
    { requestedSelectedCarrierPredicate =
        selectedCarrierPredicate external
    ; requestedSelectedCarrierWitness =
        selectedCarrierWitness external
    ; requestedSelectedCarrierWitnessSelected =
        selectedCarrierWitnessSelected external
    ; requestedAssignedLaneActionPreservesSelectedCarrier =
        assignedLaneActionPreservesSelectedCarrier external
    ; predicateRequestBoundary =
        "Request packaged from a supplied nondegenerate localised-endomorphism interface"
        ∷ "Selected carrier predicate, nonempty witness, and assigned-lane preservation are copied exactly from the supplied interface"
        ∷ "No DR classification, gauge reconstruction, or symmetric hexagon closure is promoted by this packaging step"
        ∷ nondegenerateLocalisedInterfaceBoundary external
    }

nondegenerateInterfaceToGlobalForeignIdentityRequest :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  (external :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      lane) →
  DHRGlobalForeignLaneIdentityForPredicateRequest
    operator
    lane
    (selectedCarrierPredicate external)
nondegenerateInterfaceToGlobalForeignIdentityRequest
  operator ρ lane external =
  record
    { requestedGlobalForeignLaneActionIdentity =
        globalForeignLaneActionIdentityOnSelectedCarrier external
    ; identityRequestBoundary =
        "Global foreign-lane identity request packaged from a supplied nondegenerate localised-endomorphism interface"
        ∷ "Foreign-lane action identity remains explicit supplied evidence; it is not inferred from tracked-prime coordinate locality"
        ∷ "No DR classification, gauge reconstruction, or symmetric hexagon closure is promoted by this packaging step"
        ∷ nondegenerateLocalisedInterfaceBoundary external
    }

primitiveSectorInterfaceToLaneSupply :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (constructorSurface :
    DHRPrimitiveSuperselectionSectorConstructorSurface) →
  (sectorClass : DHRPrimitiveSectorClass) →
  (sectorMatchesPrimitiveConstructor :
    DHR.LocalisedEndomorphism.localisedSector ρ
    ≡
    DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
      constructorSurface
      sectorClass) →
  (external :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      (primitiveSectorClassAssignedLane sectorClass)) →
  DHRSuperselectionSectorLaneSupply operator ρ
primitiveSectorInterfaceToLaneSupply
  operator
  ρ
  constructorSurface
  sectorClass
  sectorMatchesPrimitiveConstructor
  external =
  primitiveSectorCarrierPredicateAndForeignIdentityToLaneSupply
    operator
    ρ
    constructorSurface
    sectorClass
    sectorMatchesPrimitiveConstructor
    (nondegenerateInterfaceToCarrierPredicateRequest
      operator
      ρ
      (primitiveSectorClassAssignedLane sectorClass)
      external)
    (nondegenerateInterfaceToGlobalForeignIdentityRequest
      operator
      ρ
      (primitiveSectorClassAssignedLane sectorClass)
      external)

primitiveSectorInterfaceToLaneSupplyBoundary :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (constructorSurface :
    DHRPrimitiveSuperselectionSectorConstructorSurface) →
  (sectorClass : DHRPrimitiveSectorClass) →
  (sectorMatchesPrimitiveConstructor :
    DHR.LocalisedEndomorphism.localisedSector ρ
    ≡
    DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
      constructorSurface
      sectorClass) →
  (external :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      (primitiveSectorClassAssignedLane sectorClass)) →
  List String
primitiveSectorInterfaceToLaneSupplyBoundary
  operator
  ρ
  constructorSurface
  sectorClass
  sectorMatchesPrimitiveConstructor
  external =
  ("Primitive supplied-interface bridge: a supplied nondegenerate localised interface is converted into predicate and global foreign-identity requests before constructing DHRSuperselectionSectorLaneSupply"
  ∷ "This narrows repeated wiring at the exact foreign-lane-identity boundary without claiming repo-supplied identity evidence"
  ∷ "Arbitrary SuperselectionSector classification and DR/Tannaka authority boundaries remain open"
  ∷ [])
  ++ primitiveSectorCarrierPredicateAndForeignIdentityToLaneSupplyBoundary
      operator
      ρ
      constructorSurface
      sectorClass
      sectorMatchesPrimitiveConstructor
      (nondegenerateInterfaceToCarrierPredicateRequest
        operator
        ρ
        (primitiveSectorClassAssignedLane sectorClass)
        external)
      (nondegenerateInterfaceToGlobalForeignIdentityRequest
        operator
        ρ
        (primitiveSectorClassAssignedLane sectorClass)
        external)

record DHRPrimitiveSelectedPredicateForeignIdentitySupplyProgress
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    primitiveConstructorSurface :
      DHRPrimitiveSuperselectionSectorConstructorSurface

    primitiveCarrierPredicateProgress :
      DHRPrimitiveSectorCarrierPredicateProgress operator

    globalForeignIdentityRequestFromSelectedPredicate :
      (ρ : DHR.LocalisedEndomorphism) →
      (sectorClass : DHRPrimitiveSectorClass) →
      (sectorMatchesPrimitiveConstructor :
        DHR.LocalisedEndomorphism.localisedSector ρ
        ≡
        DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
          primitiveConstructorSurface
          sectorClass) →
      (external :
        NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
          operator
          ρ
          (primitiveSectorClassAssignedLane sectorClass)) →
      DHRGlobalForeignLaneIdentityForPredicateRequest
        operator
        (primitiveSectorClassAssignedLane sectorClass)
        (selectedCarrierPredicate external)

    dhrSuperselectionSectorLaneSupplyFromSelectedPredicate :
      (ρ : DHR.LocalisedEndomorphism) →
      (sectorClass : DHRPrimitiveSectorClass) →
      (sectorMatchesPrimitiveConstructor :
        DHR.LocalisedEndomorphism.localisedSector ρ
        ≡
        DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
          primitiveConstructorSurface
          sectorClass) →
      (external :
        NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
          operator
          ρ
          (primitiveSectorClassAssignedLane sectorClass)) →
      DHRSuperselectionSectorLaneSupply operator ρ

    globalForeignIdentityRequestConstructed :
      Bool

    globalForeignIdentityRequestConstructedIsTrue :
      globalForeignIdentityRequestConstructed ≡ true

    primitiveLaneSupplyConstructed :
      Bool

    primitiveLaneSupplyConstructedIsTrue :
      primitiveLaneSupplyConstructed ≡ true

    arbitrarySectorClassifierSupplied :
      Bool

    arbitrarySectorClassifierSuppliedIsFalse :
      arbitrarySectorClassifierSupplied ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    primitiveSelectedPredicateForeignIdentityBoundary :
      List String

open DHRPrimitiveSelectedPredicateForeignIdentitySupplyProgress public

canonicalDHRPrimitiveSelectedPredicateForeignIdentitySupplyProgress :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRPrimitiveSelectedPredicateForeignIdentitySupplyProgress operator
canonicalDHRPrimitiveSelectedPredicateForeignIdentitySupplyProgress
  operator =
  record
    { primitiveConstructorSurface =
        canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
    ; primitiveCarrierPredicateProgress =
        canonicalDHRPrimitiveSectorCarrierPredicateProgress operator
    ; globalForeignIdentityRequestFromSelectedPredicate =
        λ ρ sectorClass _ external →
          nondegenerateInterfaceToGlobalForeignIdentityRequest
            operator
            ρ
            (primitiveSectorClassAssignedLane sectorClass)
            external
    ; dhrSuperselectionSectorLaneSupplyFromSelectedPredicate =
        λ ρ sectorClass sectorMatchesPrimitiveConstructor external →
          primitiveSectorInterfaceToLaneSupply
            operator
            ρ
            canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
            sectorClass
            sectorMatchesPrimitiveConstructor
            external
    ; globalForeignIdentityRequestConstructed =
        true
    ; globalForeignIdentityRequestConstructedIsTrue =
        refl
    ; primitiveLaneSupplyConstructed =
        true
    ; primitiveLaneSupplyConstructedIsTrue =
        refl
    ; arbitrarySectorClassifierSupplied =
        false
    ; arbitrarySectorClassifierSuppliedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; primitiveSelectedPredicateForeignIdentityBoundary =
        "Primitive selected-predicate bridge now includes a repo-native constructor for global foreign-lane identity requests when nondegenerate localised interfaces are supplied"
        ∷ "The same selected-predicate identity witness is consumed to build DHRSuperselectionSectorLaneSupply on the primitive constructor path"
        ∷ "This advances the selected-predicate foreign-identity lane-supply move without claiming arbitrary sector classification, DR classification, gauge reconstruction, or symmetric hexagon closure"
        ∷ []
    }

data DHRArbitrarySectorForeignIdentityResidualBlocker : Set where
  blockedByNoArbitrarySectorLaneClassifier :
    DHRArbitrarySectorForeignIdentityResidualBlocker

  blockedByNoArbitrarySectorCarrierPredicate :
    DHRArbitrarySectorForeignIdentityResidualBlocker

  blockedByNoArbitrarySectorGlobalForeignLaneIdentity :
    DHRArbitrarySectorForeignIdentityResidualBlocker

dhrArbitrarySectorCandidateLaneClassifier :
  DHR.SuperselectionSector →
  G6.Lane
dhrArbitrarySectorCandidateLaneClassifier _ =
  G6.maxwellLane

dhrArbitrarySectorCandidateLaneClassifierTargetsMaxwellLane :
  (sector : DHR.SuperselectionSector) →
  dhrArbitrarySectorCandidateLaneClassifier sector
  ≡
  G6.maxwellLane
dhrArbitrarySectorCandidateLaneClassifierTargetsMaxwellLane _ =
  refl

dhrArbitrarySectorNonemptyCarrierPredicateRequest :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (sector : DHR.SuperselectionSector) →
  (lane : G6.Lane) →
  DHR.LocalisedEndomorphism.localisedSector ρ
  ≡
  sector →
  DHRNonemptySectorCarrierPredicateRequest
    operator
    ρ
    lane
dhrArbitrarySectorNonemptyCarrierPredicateRequest
  operator
  ρ
  sector
  lane
  localisedSectorMatchesArbitrarySector =
  record
    { requestedSelectedCarrierPredicate =
        λ _ →
          true
    ; requestedSelectedCarrierWitness =
        G6.NontrivialTrackedLaneOperator.nontrivialWitness operator
    ; requestedSelectedCarrierWitnessSelected =
        refl
    ; requestedAssignedLaneActionPreservesSelectedCarrier =
        λ _ _ →
          refl
    ; predicateRequestBoundary =
        "Arbitrary-sector nonempty carrier predicate request: localisedSector equality is supplied explicitly, and the selected predicate is the nonempty all-carrier Bool predicate over the G6 tracked carrier"
        ∷ "Assigned-lane preservation is definitional for this request; no sector-sensitive invariant is claimed"
        ∷ "This request does not construct global foreign-lane identity, DR classification, gauge reconstruction, or symmetric hexagon closure"
        ∷ []
    }

dhrArbitrarySectorGlobalForeignIdentityRequestFromSuppliedInterface :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (sector : DHR.SuperselectionSector) →
  (lane : G6.Lane) →
  DHR.LocalisedEndomorphism.localisedSector ρ
  ≡
  sector →
  (external :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      lane) →
  DHRGlobalForeignLaneIdentityForPredicateRequest
    operator
    lane
    (selectedCarrierPredicate external)
dhrArbitrarySectorGlobalForeignIdentityRequestFromSuppliedInterface
  operator
  ρ
  sector
  lane
  localisedSectorMatchesArbitrarySector
  external =
  nondegenerateInterfaceToGlobalForeignIdentityRequest
    operator
    ρ
    lane
    external

dhrArbitrarySectorLaneSupplyFromSuppliedInterface :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (sector : DHR.SuperselectionSector) →
  (lane : G6.Lane) →
  DHR.LocalisedEndomorphism.localisedSector ρ
  ≡
  sector →
  (external :
    NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      lane) →
  DHRSuperselectionSectorLaneSupply operator ρ
dhrArbitrarySectorLaneSupplyFromSuppliedInterface
  operator
  ρ
  sector
  lane
  localisedSectorMatchesArbitrarySector
  external =
  dhrSectorLaneSupplyFromExplicitData
    operator
    ρ
    sector
    lane
    localisedSectorMatchesArbitrarySector
    (selectedCarrierPredicate external)
    (selectedCarrierWitness external)
    (selectedCarrierWitnessSelected external)
    (assignedLaneActionPreservesSelectedCarrier external)
    (DHRGlobalForeignLaneIdentityForPredicateRequest.requestedGlobalForeignLaneActionIdentity
      (dhrArbitrarySectorGlobalForeignIdentityRequestFromSuppliedInterface
        operator
        ρ
        sector
        lane
        localisedSectorMatchesArbitrarySector
        external))

dhrArbitrarySectorGlobalForeignIdentityRequestFromSuppliedLaneSupply :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  DHRGlobalForeignLaneIdentityForPredicateRequest
    operator
    (sectorPrimaryLane supply)
    (selectedSectorCarrierPredicate supply)
dhrArbitrarySectorGlobalForeignIdentityRequestFromSuppliedLaneSupply
  operator
  ρ
  supply =
  record
    { requestedGlobalForeignLaneActionIdentity =
        foreignLaneActionIdentityOnSelectedCarrier supply
    ; identityRequestBoundary =
        "Arbitrary-sector supplied-lane identity request: copies the global foreign-lane action identity field from an explicit DHRSuperselectionSectorLaneSupply"
        ∷ "This is conditional consumption of supplied evidence and does not derive foreign-lane identity from tracked-prime locality laws"
        ∷ "No DR classification, gauge reconstruction, or symmetric hexagon closure is promoted by this extraction step"
        ∷ dhrSuperselectionSectorLaneSupplyBoundary supply
    }

dhrArbitrarySectorGlobalForeignLaneIdentityEliminatorFromSuppliedLaneSupply :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  (otherLane : G6.Lane) →
  sectorPrimaryLane supply ≢ otherLane →
  (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
  selectedSectorCarrierPredicate supply x ≡ true →
  G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
  ≡
  x
dhrArbitrarySectorGlobalForeignLaneIdentityEliminatorFromSuppliedLaneSupply
  operator
  ρ
  supply
  otherLane
    sectorPrimaryLaneDistinctFromOther
    x
    xSelected =
  dhrSectorLaneSupplyForeignLaneIdentityEliminator
    supply
    otherLane
    sectorPrimaryLaneDistinctFromOther
    x
    xSelected

record DHRArbitrarySectorForeignIdentityProgress
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    primitiveSelectedPredicateProgress :
      DHRPrimitiveSelectedPredicateForeignIdentitySupplyProgress operator

    arbitrarySectorLaneSupplyConstructor :
      (ρ : DHR.LocalisedEndomorphism) →
      (sector : DHR.SuperselectionSector) →
      (lane : G6.Lane) →
      DHR.LocalisedEndomorphism.localisedSector ρ ≡ sector →
      (selectedCarrierPredicate :
        G6.NontrivialTrackedLaneOperator.Carrier operator →
        Bool) →
      (selectedCarrierWitness :
        G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate selectedCarrierWitness ≡ true →
      ((x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
        selectedCarrierPredicate x ≡ true →
        selectedCarrierPredicate
          (G6.NontrivialTrackedLaneOperator.laneAction operator lane x)
        ≡
        true) →
      ((otherLane : G6.Lane) →
        lane ≢ otherLane →
        (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
        selectedCarrierPredicate x ≡ true →
        G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
        ≡
        x) →
      DHRSuperselectionSectorLaneSupply operator ρ

    arbitrarySectorLaneSupplyConstructorAvailable :
      Bool

    arbitrarySectorLaneSupplyConstructorAvailableIsTrue :
      arbitrarySectorLaneSupplyConstructorAvailable ≡ true

    arbitrarySectorLaneClassifier :
      DHR.SuperselectionSector →
      G6.Lane

    arbitrarySectorLaneClassifierTargetsMaxwellLane :
      (sector : DHR.SuperselectionSector) →
      arbitrarySectorLaneClassifier sector
      ≡
      G6.maxwellLane

    arbitrarySectorCarrierPredicateRequestForLocalisedEndomorphism :
      (ρ : DHR.LocalisedEndomorphism) →
      (sector : DHR.SuperselectionSector) →
      (lane : G6.Lane) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      sector →
      DHRNonemptySectorCarrierPredicateRequest
        operator
        ρ
        lane

    arbitrarySectorGlobalForeignIdentityRequestFromSelectedPredicate :
      (ρ : DHR.LocalisedEndomorphism) →
      (sector : DHR.SuperselectionSector) →
      (lane : G6.Lane) →
      (localisedSectorMatchesArbitrarySector :
        DHR.LocalisedEndomorphism.localisedSector ρ
        ≡
        sector) →
      (external :
        NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
          operator
          ρ
          lane) →
      DHRGlobalForeignLaneIdentityForPredicateRequest
        operator
        lane
        (selectedCarrierPredicate external)

    arbitrarySectorGlobalForeignIdentityRequestFromSuppliedLaneSupply :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      DHRGlobalForeignLaneIdentityForPredicateRequest
        operator
        (sectorPrimaryLane supply)
        (selectedSectorCarrierPredicate supply)

    arbitrarySectorGlobalForeignLaneIdentityEliminatorFromSuppliedLaneSupply :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      (otherLane : G6.Lane) →
      sectorPrimaryLane supply ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedSectorCarrierPredicate supply x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    arbitrarySectorGlobalForeignLaneIdentityEliminator :
      (lane : G6.Lane) →
      (selectedCarrierPredicate :
        G6.NontrivialTrackedLaneOperator.Carrier operator →
        Bool) →
      (identityRequest :
        DHRGlobalForeignLaneIdentityForPredicateRequest
          operator
          lane
          selectedCarrierPredicate) →
      (otherLane : G6.Lane) →
      lane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    arbitrarySectorGlobalForeignLaneIdentityEliminatorAvailable :
      Bool

    arbitrarySectorGlobalForeignLaneIdentityEliminatorAvailableIsTrue :
      arbitrarySectorGlobalForeignLaneIdentityEliminatorAvailable ≡ true

    arbitrarySectorLaneSupplyFromSelectedPredicate :
      (ρ : DHR.LocalisedEndomorphism) →
      (sector : DHR.SuperselectionSector) →
      (lane : G6.Lane) →
      (localisedSectorMatchesArbitrarySector :
        DHR.LocalisedEndomorphism.localisedSector ρ
        ≡
        sector) →
      (external :
        NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
          operator
          ρ
          lane) →
      DHRSuperselectionSectorLaneSupply operator ρ

    arbitrarySectorClassifierSupplied :
      Bool

    arbitrarySectorClassifierSuppliedIsTrue :
      arbitrarySectorClassifierSupplied ≡ true

    arbitrarySectorCarrierPredicateSupplied :
      Bool

    arbitrarySectorCarrierPredicateSuppliedIsTrue :
      arbitrarySectorCarrierPredicateSupplied ≡ true

    arbitrarySectorGlobalForeignIdentityRequestConstructed :
      Bool

    arbitrarySectorGlobalForeignIdentityRequestConstructedIsTrue :
      arbitrarySectorGlobalForeignIdentityRequestConstructed ≡ true

    arbitrarySectorSelectedPredicateLaneSupplyConstructed :
      Bool

    arbitrarySectorSelectedPredicateLaneSupplyConstructedIsTrue :
      arbitrarySectorSelectedPredicateLaneSupplyConstructed ≡ true

    arbitrarySectorGlobalForeignLaneIdentitySupplied :
      Bool

    arbitrarySectorGlobalForeignLaneIdentitySuppliedIsFalse :
      arbitrarySectorGlobalForeignLaneIdentitySupplied ≡ false

    firstResidualBlocker :
      DHRArbitrarySectorForeignIdentityResidualBlocker

    firstResidualBlockerIsArbitrarySectorGlobalForeignLaneIdentity :
      firstResidualBlocker
      ≡
      blockedByNoArbitrarySectorGlobalForeignLaneIdentity

    residualBlockers :
      List DHRArbitrarySectorForeignIdentityResidualBlocker

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    arbitrarySectorForeignIdentityBoundary :
      List String

open DHRArbitrarySectorForeignIdentityProgress public

canonicalDHRArbitrarySectorForeignIdentityProgress :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRArbitrarySectorForeignIdentityProgress operator
canonicalDHRArbitrarySectorForeignIdentityProgress operator =
  record
    { primitiveSelectedPredicateProgress =
        canonicalDHRPrimitiveSelectedPredicateForeignIdentitySupplyProgress
          operator
    ; arbitrarySectorLaneSupplyConstructor =
        dhrSectorLaneSupplyFromExplicitData operator
    ; arbitrarySectorLaneSupplyConstructorAvailable =
        true
    ; arbitrarySectorLaneSupplyConstructorAvailableIsTrue =
        refl
    ; arbitrarySectorLaneClassifier =
        dhrArbitrarySectorCandidateLaneClassifier
    ; arbitrarySectorLaneClassifierTargetsMaxwellLane =
        dhrArbitrarySectorCandidateLaneClassifierTargetsMaxwellLane
    ; arbitrarySectorCarrierPredicateRequestForLocalisedEndomorphism =
        dhrArbitrarySectorNonemptyCarrierPredicateRequest operator
    ; arbitrarySectorGlobalForeignIdentityRequestFromSelectedPredicate =
        dhrArbitrarySectorGlobalForeignIdentityRequestFromSuppliedInterface
          operator
    ; arbitrarySectorGlobalForeignIdentityRequestFromSuppliedLaneSupply =
        dhrArbitrarySectorGlobalForeignIdentityRequestFromSuppliedLaneSupply
          operator
    ; arbitrarySectorGlobalForeignLaneIdentityEliminatorFromSuppliedLaneSupply =
        dhrArbitrarySectorGlobalForeignLaneIdentityEliminatorFromSuppliedLaneSupply
          operator
    ; arbitrarySectorGlobalForeignLaneIdentityEliminator =
        λ _ _ identityRequest →
          dhrArbitrarySectorGlobalForeignLaneIdentityEliminator
            identityRequest
    ; arbitrarySectorGlobalForeignLaneIdentityEliminatorAvailable =
        true
    ; arbitrarySectorGlobalForeignLaneIdentityEliminatorAvailableIsTrue =
        refl
    ; arbitrarySectorLaneSupplyFromSelectedPredicate =
        dhrArbitrarySectorLaneSupplyFromSuppliedInterface
          operator
    ; arbitrarySectorClassifierSupplied =
        true
    ; arbitrarySectorClassifierSuppliedIsTrue =
        refl
    ; arbitrarySectorCarrierPredicateSupplied =
        true
    ; arbitrarySectorCarrierPredicateSuppliedIsTrue =
        refl
    ; arbitrarySectorGlobalForeignIdentityRequestConstructed =
        true
    ; arbitrarySectorGlobalForeignIdentityRequestConstructedIsTrue =
        refl
    ; arbitrarySectorSelectedPredicateLaneSupplyConstructed =
        true
    ; arbitrarySectorSelectedPredicateLaneSupplyConstructedIsTrue =
        refl
    ; arbitrarySectorGlobalForeignLaneIdentitySupplied =
        false
    ; arbitrarySectorGlobalForeignLaneIdentitySuppliedIsFalse =
        refl
    ; firstResidualBlocker =
        blockedByNoArbitrarySectorGlobalForeignLaneIdentity
    ; firstResidualBlockerIsArbitrarySectorGlobalForeignLaneIdentity =
        refl
    ; residualBlockers =
        []
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; arbitrarySectorForeignIdentityBoundary =
        "Arbitrary-sector lane-supply constructor is now explicit and generic over sector/lane once sector match, selected carrier predicate data, and global foreign-lane identity are provided"
        ∷ "Primitive selected-predicate progress is preserved and reused as the currently available non-arbitrary evidence path"
        ∷ "A total arbitrary SuperselectionSector -> lane classifier is now explicitly inhabited as a constant maxwellLane candidate"
        ∷ "That classifier candidate is structural only; no sector-sensitive invariant or representation evidence is yet supplied"
        ∷ "Arbitrary-sector nonempty carrier predicate requests are now explicitly constructible from localised-sector equality plus the nonempty all-carrier predicate"
        ∷ "Arbitrary-sector foreign-lane identity requests are now explicitly packageable from supplied nondegenerate localised-endomorphism interfaces"
        ∷ "Arbitrary-sector foreign-lane identity requests are also extractable directly from explicit DHRSuperselectionSectorLaneSupply inputs"
        ∷ "A constructor-specific eliminator is now explicit: dhrArbitrarySectorGlobalForeignLaneIdentityEliminatorFromSuppliedLaneSupply"
        ∷ "A general arbitrary-sector foreign-lane identity eliminator is now explicit: dhrArbitrarySectorGlobalForeignLaneIdentityEliminator"
        ∷ "Those supplied identity requests can now be consumed to build arbitrary-sector DHRSuperselectionSectorLaneSupply conditionally from explicit data"
        ∷ "First exact blocker is now arbitrary-sector global foreign-lane identity"
        ∷ "No DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

data DHRArbitrarySectorForeignIdentityFieldLatticeResidual : Set where
  residualCandidateClassifierHasNoInvariantEvidence :
    DHRArbitrarySectorForeignIdentityFieldLatticeResidual

  residualAllCarrierPredicateIsNotSectorInvariant :
    DHRArbitrarySectorForeignIdentityFieldLatticeResidual

  residualGlobalForeignLaneIdentityRequiresExplicitWitness :
    DHRArbitrarySectorForeignIdentityFieldLatticeResidual

  residualNoDRFibreFunctorClassification :
    DHRArbitrarySectorForeignIdentityFieldLatticeResidual

record DHRArbitrarySectorForeignIdentityFieldLattice
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    arbitrarySectorForeignIdentityProgress :
      DHRArbitrarySectorForeignIdentityProgress operator

    laneClassifierCandidate :
      DHR.SuperselectionSector →
      G6.Lane

    laneClassifierCandidateTargetsMaxwellLane :
      (sector : DHR.SuperselectionSector) →
      laneClassifierCandidate sector
      ≡
      G6.maxwellLane

    candidateCarrierPredicateRequest :
      (ρ : DHR.LocalisedEndomorphism) →
      (sector : DHR.SuperselectionSector) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      sector →
      DHRNonemptySectorCarrierPredicateRequest
        operator
        ρ
        (laneClassifierCandidate sector)

    explicitForeignIdentityRequestTarget :
      (lane : G6.Lane) →
      (selectedCarrierPredicate :
        G6.NontrivialTrackedLaneOperator.Carrier operator →
        Bool) →
      Set

    explicitForeignIdentityRequestTargetIsCanonical :
      (lane : G6.Lane) →
      (selectedCarrierPredicate :
        G6.NontrivialTrackedLaneOperator.Carrier operator →
        Bool) →
      explicitForeignIdentityRequestTarget
        lane
        selectedCarrierPredicate
      ≡
      DHRGlobalForeignLaneIdentityForPredicateRequest
        operator
        lane
        selectedCarrierPredicate

    explicitForeignIdentityEliminator :
      (lane : G6.Lane) →
      (selectedCarrierPredicate :
        G6.NontrivialTrackedLaneOperator.Carrier operator →
        Bool) →
      DHRGlobalForeignLaneIdentityForPredicateRequest
        operator
        lane
        selectedCarrierPredicate →
      (otherLane : G6.Lane) →
      lane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    suppliedLaneSupplyIdentityEliminator :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      (otherLane : G6.Lane) →
      sectorPrimaryLane supply ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedSectorCarrierPredicate supply x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    candidateClassifierEvidenceSupplied :
      Bool

    candidateClassifierEvidenceSuppliedIsFalse :
      candidateClassifierEvidenceSupplied ≡ false

    sectorInvariantCarrierPredicateSupplied :
      Bool

    sectorInvariantCarrierPredicateSuppliedIsFalse :
      sectorInvariantCarrierPredicateSupplied ≡ false

    repoGlobalForeignLaneIdentityTheoremSupplied :
      Bool

    repoGlobalForeignLaneIdentityTheoremSuppliedIsFalse :
      repoGlobalForeignLaneIdentityTheoremSupplied ≡ false

    firstFieldLatticeResidual :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    firstFieldLatticeResidualIsExplicitIdentityWitness :
      firstFieldLatticeResidual
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    residualFieldLattice :
      List DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    arbitrarySectorForeignIdentityFieldLatticeBoundary :
      List String

open DHRArbitrarySectorForeignIdentityFieldLattice public

canonicalDHRArbitrarySectorForeignIdentityFieldLattice :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRArbitrarySectorForeignIdentityFieldLattice operator
canonicalDHRArbitrarySectorForeignIdentityFieldLattice operator =
  record
    { arbitrarySectorForeignIdentityProgress =
        canonicalDHRArbitrarySectorForeignIdentityProgress operator
    ; laneClassifierCandidate =
        dhrArbitrarySectorCandidateLaneClassifier
    ; laneClassifierCandidateTargetsMaxwellLane =
        dhrArbitrarySectorCandidateLaneClassifierTargetsMaxwellLane
    ; candidateCarrierPredicateRequest =
        λ ρ sector localisedSectorMatchesArbitrarySector →
          dhrArbitrarySectorNonemptyCarrierPredicateRequest
            operator
            ρ
            sector
            (dhrArbitrarySectorCandidateLaneClassifier sector)
            localisedSectorMatchesArbitrarySector
    ; explicitForeignIdentityRequestTarget =
        λ lane selectedCarrierPredicate →
          DHRGlobalForeignLaneIdentityForPredicateRequest
            operator
            lane
            selectedCarrierPredicate
    ; explicitForeignIdentityRequestTargetIsCanonical =
        λ _ _ →
          refl
    ; explicitForeignIdentityEliminator =
        λ _ _ identityRequest →
          dhrArbitrarySectorGlobalForeignLaneIdentityEliminator
            identityRequest
    ; suppliedLaneSupplyIdentityEliminator =
        dhrArbitrarySectorGlobalForeignLaneIdentityEliminatorFromSuppliedLaneSupply
          operator
    ; candidateClassifierEvidenceSupplied =
        false
    ; candidateClassifierEvidenceSuppliedIsFalse =
        refl
    ; sectorInvariantCarrierPredicateSupplied =
        false
    ; sectorInvariantCarrierPredicateSuppliedIsFalse =
        refl
    ; repoGlobalForeignLaneIdentityTheoremSupplied =
        false
    ; repoGlobalForeignLaneIdentityTheoremSuppliedIsFalse =
        refl
    ; firstFieldLatticeResidual =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; firstFieldLatticeResidualIsExplicitIdentityWitness =
        refl
    ; residualFieldLattice =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
        ∷ residualCandidateClassifierHasNoInvariantEvidence
        ∷ residualAllCarrierPredicateIsNotSectorInvariant
        ∷ residualNoDRFibreFunctorClassification
        ∷ []
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; arbitrarySectorForeignIdentityFieldLatticeBoundary =
        "Field lattice refinement: candidate lane classification, all-carrier predicate requests, explicit identity requests, and supplied-supply identity eliminators are separated"
        ∷ "The constant maxwellLane classifier remains a candidate without invariant evidence and is not a DR fibre-functor classifier"
        ∷ "The all-carrier predicate gives a nonempty request surface but not a sector-sensitive invariant carrier predicate"
        ∷ "The exact remaining blocker is a repo-supplied global foreign-lane identity theorem or explicit witness for the selected predicate"
        ∷ "No DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

data DHRArbitrarySectorClassificationDownstreamBlocker : Set where
  missingDASHILocalAlgebra :
    DHRArbitrarySectorClassificationDownstreamBlocker

  blockedByMissingGate1GaugeRepresentationSemantics :
    DHRArbitrarySectorClassificationDownstreamBlocker

record DHRArbitrarySectorSelectedForeignIdentityPackagingReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    arbitrarySectorForeignIdentityFieldLattice :
      DHRArbitrarySectorForeignIdentityFieldLattice operator

    selectedInterfaceToForeignIdentityRequest :
      (ρ : DHR.LocalisedEndomorphism) →
      (sector : DHR.SuperselectionSector) →
      (lane : G6.Lane) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      sector →
      (external :
        NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
          operator
          ρ
          lane) →
      DHRGlobalForeignLaneIdentityForPredicateRequest
        operator
        lane
        (selectedCarrierPredicate external)

    selectedInterfaceToArbitrarySectorLaneSupply :
      (ρ : DHR.LocalisedEndomorphism) →
      (sector : DHR.SuperselectionSector) →
      (lane : G6.Lane) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      sector →
      (external :
        NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
          operator
          ρ
          lane) →
      DHRSuperselectionSectorLaneSupply operator ρ

    selectedPredicateIdentityPackagedFromSuppliedInterface :
      Bool

    selectedPredicateIdentityPackagedFromSuppliedInterfaceIsTrue :
      selectedPredicateIdentityPackagedFromSuppliedInterface ≡ true

    arbitrarySectorLaneSupplyRoutedFromSuppliedInterface :
      Bool

    arbitrarySectorLaneSupplyRoutedFromSuppliedInterfaceIsTrue :
      arbitrarySectorLaneSupplyRoutedFromSuppliedInterface ≡ true

    internalRepoGlobalForeignLaneIdentityTheoremSupplied :
      Bool

    internalRepoGlobalForeignLaneIdentityTheoremSuppliedIsFalse :
      internalRepoGlobalForeignLaneIdentityTheoremSupplied ≡ false

    arbitrarySectorClassificationPromoted :
      Bool

    arbitrarySectorClassificationPromotedIsFalse :
      arbitrarySectorClassificationPromoted ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    firstResidualBlocker :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    firstResidualBlockerIsExplicitIdentityWitness :
      firstResidualBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    downstreamAQFTDRBlockers :
      List DHRArbitrarySectorClassificationDownstreamBlocker

    packagingReceiptBoundary :
      List String

open DHRArbitrarySectorSelectedForeignIdentityPackagingReceipt public

canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRArbitrarySectorSelectedForeignIdentityPackagingReceipt operator
canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingReceipt operator =
  record
    { arbitrarySectorForeignIdentityFieldLattice =
        canonicalDHRArbitrarySectorForeignIdentityFieldLattice operator
    ; selectedInterfaceToForeignIdentityRequest =
        dhrArbitrarySectorGlobalForeignIdentityRequestFromSuppliedInterface
          operator
    ; selectedInterfaceToArbitrarySectorLaneSupply =
        dhrArbitrarySectorLaneSupplyFromSuppliedInterface
          operator
    ; selectedPredicateIdentityPackagedFromSuppliedInterface =
        true
    ; selectedPredicateIdentityPackagedFromSuppliedInterfaceIsTrue =
        refl
    ; arbitrarySectorLaneSupplyRoutedFromSuppliedInterface =
        true
    ; arbitrarySectorLaneSupplyRoutedFromSuppliedInterfaceIsTrue =
        refl
    ; internalRepoGlobalForeignLaneIdentityTheoremSupplied =
        false
    ; internalRepoGlobalForeignLaneIdentityTheoremSuppliedIsFalse =
        refl
    ; arbitrarySectorClassificationPromoted =
        false
    ; arbitrarySectorClassificationPromotedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; firstResidualBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; firstResidualBlockerIsExplicitIdentityWitness =
        refl
    ; downstreamAQFTDRBlockers =
        missingDASHILocalAlgebra
        ∷ blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; packagingReceiptBoundary =
        "u6 selected-predicate packaging receipt: a supplied NondegenerateLocalisedEndomorphismCarrierSemanticsInterface yields the canonical foreign-lane identity request"
        ∷ "The same supplied interface routes to DHRSuperselectionSectorLaneSupply for arbitrary-sector staging"
        ∷ "The repo still does not supply an internal global foreign-lane identity theorem for the selected predicate"
        ∷ "Downstream DR/AQFT blockers are named only after this packaging boundary: missingDASHILocalAlgebra and blockedByMissingGate1GaugeRepresentationSemantics"
        ∷ "No arbitrary-sector classification, DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

record DHRSelectedForeignIdentityEliminatorPackage
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    selectedForeignIdentityPackagingReceipt :
      DHRArbitrarySectorSelectedForeignIdentityPackagingReceipt operator

    selectedInterfaceForeignIdentityEliminator :
      (ρ : DHR.LocalisedEndomorphism) →
      (sector : DHR.SuperselectionSector) →
      (lane : G6.Lane) →
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      sector →
      (external :
        NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
          operator
          ρ
          lane) →
      (otherLane : G6.Lane) →
      lane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicate external x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    suppliedLaneSupplyForeignIdentityEliminator :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      (otherLane : G6.Lane) →
      sectorPrimaryLane supply ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedSectorCarrierPredicate supply x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    selectedInterfaceIdentityEliminatorPackaged :
      Bool

    selectedInterfaceIdentityEliminatorPackagedIsTrue :
      selectedInterfaceIdentityEliminatorPackaged ≡ true

    suppliedLaneSupplyIdentityEliminatorPackaged :
      Bool

    suppliedLaneSupplyIdentityEliminatorPackagedIsTrue :
      suppliedLaneSupplyIdentityEliminatorPackaged ≡ true

    repoDerivesForeignIdentityFromG6CoordinateLocality :
      Bool

    repoDerivesForeignIdentityFromG6CoordinateLocalityIsFalse :
      repoDerivesForeignIdentityFromG6CoordinateLocality ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    eliminatorPackageBoundary :
      List String

open DHRSelectedForeignIdentityEliminatorPackage public

canonicalDHRSelectedForeignIdentityEliminatorPackage :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRSelectedForeignIdentityEliminatorPackage operator
canonicalDHRSelectedForeignIdentityEliminatorPackage operator =
  record
    { selectedForeignIdentityPackagingReceipt =
        canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingReceipt
          operator
    ; selectedInterfaceForeignIdentityEliminator =
        λ ρ sector lane sectorMatch external otherLane lane≢other x xSelected →
          dhrArbitrarySectorGlobalForeignLaneIdentityEliminator
            (selectedInterfaceToForeignIdentityRequest
              (canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingReceipt
                operator)
              ρ
              sector
              lane
              sectorMatch
              external)
            otherLane
            lane≢other
            x
            xSelected
    ; suppliedLaneSupplyForeignIdentityEliminator =
        dhrArbitrarySectorGlobalForeignLaneIdentityEliminatorFromSuppliedLaneSupply
          operator
    ; selectedInterfaceIdentityEliminatorPackaged =
        true
    ; selectedInterfaceIdentityEliminatorPackagedIsTrue =
        refl
    ; suppliedLaneSupplyIdentityEliminatorPackaged =
        true
    ; suppliedLaneSupplyIdentityEliminatorPackagedIsTrue =
        refl
    ; repoDerivesForeignIdentityFromG6CoordinateLocality =
        false
    ; repoDerivesForeignIdentityFromG6CoordinateLocalityIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; eliminatorPackageBoundary =
        "u6 eliminator package: selected-interface foreign-lane identity requests are exposed as direct action-identity eliminators"
        ∷ "Explicit DHRSuperselectionSectorLaneSupply inputs expose the same eliminator through their supplied global foreign-lane identity field"
        ∷ "The package consumes explicit identity evidence only; it does not derive global action identity from G6 tracked-prime coordinate locality"
        ∷ "No arbitrary-sector classifier, DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

record AQFTGNSDHRStoneCarrierFunctorBlockerChain
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    aqftFirstBlocker :
      AQFTColim.AQFTCarrierAlgebraQuotientOpenObligation

    aqftFirstBlockerIsMissingQuotientConstruction :
      aqftFirstBlocker
      ≡
      AQFTColim.missingQuotientConstruction

    dhrForeignLanePackagingReceipt :
      DHRArbitrarySectorSelectedForeignIdentityPackagingReceipt operator

    dhrFirstResidualBlocker :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    dhrFirstResidualBlockerIsExplicitWitness :
      dhrFirstResidualBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    dhrDownstreamBlockers :
      List DHRArbitrarySectorClassificationDownstreamBlocker

    dhrDownstreamBlockersAreGateChain :
      dhrDownstreamBlockers
      ≡
      (missingDASHILocalAlgebra
       ∷ blockedByMissingGate1GaugeRepresentationSemantics
       ∷ [])

    gnsFirstBlocker :
      Modular.ModularTheoryOpenObligation

    gnsFirstBlockerIsMissingStateFunctional :
      gnsFirstBlocker
      ≡
      Modular.missingGNSStateFunctional

    stoneFirstRemainingTarget :
      Stone.StoneGeneratorSpectralGapRemainingTarget

    stoneFirstRemainingTargetIsGlobalNoncollapsedPhaseSpace :
      stoneFirstRemainingTarget
      ≡
      Stone.targetGlobalNoncollapsedPhysicalPhaseSpace

    carrierFunctorFirstRemainingPrimitive :
      CarrierFunctor.CarrierToPhysicsRemainingPrimitive

    carrierFunctorFirstRemainingPrimitiveIsFilteredColimitPreservation :
      carrierFunctorFirstRemainingPrimitive
      ≡
      CarrierFunctor.missingFilteredColimitPreservation

    promotesBW :
      Bool

    promotesBWIsFalse :
      promotesBW ≡ false

    promotesDR :
      Bool

    promotesDRIsFalse :
      promotesDR ≡ false

    promotesStone :
      Bool

    promotesStoneIsFalse :
      promotesStone ≡ false

    promotesStandardModel :
      Bool

    promotesStandardModelIsFalse :
      promotesStandardModel ≡ false

    blockerChainBoundary :
      List String

open AQFTGNSDHRStoneCarrierFunctorBlockerChain public

canonicalAQFTGNSDHRStoneCarrierFunctorBlockerChain :
  (operator : G6.NontrivialTrackedLaneOperator) →
  AQFTGNSDHRStoneCarrierFunctorBlockerChain operator
canonicalAQFTGNSDHRStoneCarrierFunctorBlockerChain operator =
  record
    { aqftFirstBlocker =
        AQFTColim.missingQuotientConstruction
    ; aqftFirstBlockerIsMissingQuotientConstruction =
        refl
    ; dhrForeignLanePackagingReceipt =
        canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingReceipt
          operator
    ; dhrFirstResidualBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; dhrFirstResidualBlockerIsExplicitWitness =
        refl
    ; dhrDownstreamBlockers =
        missingDASHILocalAlgebra
        ∷ blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; dhrDownstreamBlockersAreGateChain =
        refl
    ; gnsFirstBlocker =
        Modular.missingGNSStateFunctional
    ; gnsFirstBlockerIsMissingStateFunctional =
        refl
    ; stoneFirstRemainingTarget =
        Stone.targetGlobalNoncollapsedPhysicalPhaseSpace
    ; stoneFirstRemainingTargetIsGlobalNoncollapsedPhaseSpace =
        refl
    ; carrierFunctorFirstRemainingPrimitive =
        CarrierFunctor.missingFilteredColimitPreservation
    ; carrierFunctorFirstRemainingPrimitiveIsFilteredColimitPreservation =
        refl
    ; promotesBW =
        false
    ; promotesBWIsFalse =
        refl
    ; promotesDR =
        false
    ; promotesDRIsFalse =
        refl
    ; promotesStone =
        false
    ; promotesStoneIsFalse =
        refl
    ; promotesStandardModel =
        false
    ; promotesStandardModelIsFalse =
        refl
    ; blockerChainBoundary =
        "Exact non-promoting blocker chain: missingQuotientConstruction -> missingDASHILocalAlgebra -> blockedByMissingGate1GaugeRepresentationSemantics"
        ∷ "The DHR u6 residual remains residualGlobalForeignLaneIdentityRequiresExplicitWitness"
        ∷ "The GNS/modular first blocker remains missingGNSStateFunctional"
        ∷ "The bounded Stone/spectral-gap lane remains blocked at targetGlobalNoncollapsedPhysicalPhaseSpace"
        ∷ "The carrier-functor first remaining primitive remains missingFilteredColimitPreservation"
        ∷ "This receipt is only a blocker-chain ledger and does not promote BW, DR, Stone, Standard Model, DHR hexagon, or AQFT completion"
        ∷ []
    }

dhrSuperselectionSectorLaneSupplyToNondegenerateInterface :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
    operator
    ρ
    (sectorPrimaryLane supply)
dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
  operator ρ supply =
  record
    { semanticSectorWitness =
        dhrSuperselectionSector supply
    ; semanticSectorWitnessMatchesLocalisedSector =
        dhrSuperselectionSectorMatchesLocalisedSector supply
    ; selectedCarrierPredicate =
        selectedSectorCarrierPredicate supply
    ; selectedCarrierWitness =
        selectedSectorCarrierNonemptyWitness supply
    ; selectedCarrierWitnessSelected =
        selectedSectorCarrierNonemptyWitnessSelected supply
    ; assignedLaneActionPreservesSelectedCarrier =
        sectorLaneActionPreservesSelectedCarrier supply
    ; globalForeignLaneActionIdentityOnSelectedCarrier =
        foreignLaneActionIdentityOnSelectedCarrier supply
    ; nondegenerateCarrierPredicateSupplied =
        true
    ; nondegenerateCarrierPredicateSuppliedIsTrue =
        refl
    ; globalForeignLaneActionIdentitySupplied =
        true
    ; globalForeignLaneActionIdentitySuppliedIsTrue =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; nondegenerateLocalisedInterfaceBoundary =
        "Consumed DHRSuperselectionSector/sectorLane supply with an explicit nonempty selected carrier witness"
        ∷ "Foreign-lane identity is supplied as a global action identity field, not inferred from tracked-prime coordinate locality"
        ∷ "This constructs only the nondegenerate localised carrier interface; it does not promote DR classification, gauge assignment, or symmetric hexagon closure"
        ∷ dhrSuperselectionSectorLaneSupplyBoundary supply
    }

dhrSuperselectionSectorLaneSupplyNonemptyWitness :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  LocalisedEndomorphismNonemptyCarrierWitness
    operator
    ρ
    (sectorPrimaryLane supply)
    (nondegenerateLocalisedInterfaceToCarrierSemantics
      operator
      ρ
      (sectorPrimaryLane supply)
      (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
        operator
        ρ
        supply))
dhrSuperselectionSectorLaneSupplyNonemptyWitness
  operator ρ supply =
  nondegenerateLocalisedInterfaceToNonemptyCarrierWitness
    operator
    ρ
    (sectorPrimaryLane supply)
    (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
      operator
      ρ
      supply)

dhrSuperselectionSectorLaneSupplyToCarrierSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  LocalisedEndomorphismCarrierSemantics
    operator
    ρ
    (sectorPrimaryLane supply)
dhrSuperselectionSectorLaneSupplyToCarrierSemantics
  operator ρ supply =
  nondegenerateLocalisedInterfaceToCarrierSemantics
    operator
    ρ
    (sectorPrimaryLane supply)
    (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
      operator
      ρ
      supply)

dhrSuperselectionSectorLaneSuppliesToTrackedIntertwiner :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  (f : DHR.Intertwiner ρ σ) →
  (ρSupply : DHRSuperselectionSectorLaneSupply operator ρ) →
  (σSupply : DHRSuperselectionSectorLaneSupply operator σ) →
  IntertwinerTrackedCarrierSemantics
    operator
    ρ
    σ
    f
    (sectorPrimaryLane ρSupply)
    (sectorPrimaryLane σSupply)
    (dhrSuperselectionSectorLaneSupplyToCarrierSemantics
      operator
      ρ
      ρSupply)
    (dhrSuperselectionSectorLaneSupplyToCarrierSemantics
      operator
      σ
      σSupply)
dhrSuperselectionSectorLaneSuppliesToTrackedIntertwiner
  operator ρ σ f ρSupply σSupply =
  nondegenerateIntertwinerInterfaceToCarrierSemantics
    operator
    ρ
    σ
    f
    (sectorPrimaryLane ρSupply)
    (sectorPrimaryLane σSupply)
    (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
      operator
      ρ
      ρSupply)
    (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
      operator
      σ
      σSupply)
    (targetSelectedNondegenerateIntertwinerTrackedCarrierSemanticsInterface
      operator
      ρ
      σ
      f
      (sectorPrimaryLane ρSupply)
      (sectorPrimaryLane σSupply)
      (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
        operator
        ρ
        ρSupply)
      (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
        operator
        σ
        σSupply))

dhrSuperselectionSectorLaneSuppliesToTrackedIntertwinerAdapter :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  (f : DHR.Intertwiner ρ σ) →
  (ρSupply : DHRSuperselectionSectorLaneSupply operator ρ) →
  (σSupply : DHRSuperselectionSectorLaneSupply operator σ) →
  IntertwinerTrackedCarrierAdapterBoundary
    operator
    ρ
    σ
    f
    (sectorPrimaryLane ρSupply)
    (sectorPrimaryLane σSupply)
    (dhrSuperselectionSectorLaneSupplyToCarrierSemantics
      operator
      ρ
      ρSupply)
    (dhrSuperselectionSectorLaneSupplyToCarrierSemantics
      operator
      σ
      σSupply)
    (dhrSuperselectionSectorLaneSuppliesToTrackedIntertwiner
      operator
      ρ
      σ
      f
      ρSupply
      σSupply)
dhrSuperselectionSectorLaneSuppliesToTrackedIntertwinerAdapter
  operator ρ σ f ρSupply σSupply =
  nondegenerateIntertwinerInterfaceToAdapterBoundary
    operator
    ρ
    σ
    f
    (sectorPrimaryLane ρSupply)
    (sectorPrimaryLane σSupply)
    (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
      operator
      ρ
      ρSupply)
    (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
      operator
      σ
      σSupply)
    (targetSelectedNondegenerateIntertwinerTrackedCarrierSemanticsInterface
      operator
      ρ
      σ
      f
      (sectorPrimaryLane ρSupply)
      (sectorPrimaryLane σSupply)
      (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
        operator
        ρ
        ρSupply)
      (dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
        operator
        σ
        σSupply))

record DHRSuppliedSectorLaneNaturalityHexagonWiring
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    sectorPrimaryLaneFromSupply :
      (ρ : DHR.LocalisedEndomorphism) →
      DHRSuperselectionSectorLaneSupply operator ρ →
      G6.Lane

    sectorPrimaryLaneAgreesWithSuppliedLane :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      sectorPrimaryLaneFromSupply ρ supply
      ≡
      sectorLane supply

    localisedCarrierSemanticsFromSupply :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      LocalisedEndomorphismCarrierSemantics
        operator
        ρ
        (sectorPrimaryLaneFromSupply ρ supply)

    nonemptyCarrierWitnessFromSupply :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      LocalisedEndomorphismNonemptyCarrierWitness
        operator
        ρ
        (sectorPrimaryLaneFromSupply ρ supply)
        (localisedCarrierSemanticsFromSupply ρ supply)

    trackedIntertwinerActionFromSupplies :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (ρSupply : DHRSuperselectionSectorLaneSupply operator ρ) →
      (σSupply : DHRSuperselectionSectorLaneSupply operator σ) →
      IntertwinerTrackedCarrierSemantics
        operator
        ρ
        σ
        f
        (sectorPrimaryLaneFromSupply ρ ρSupply)
        (sectorPrimaryLaneFromSupply σ σSupply)
        (localisedCarrierSemanticsFromSupply ρ ρSupply)
        (localisedCarrierSemanticsFromSupply σ σSupply)

    trackedIntertwinerAdapterFromSupplies :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (ρSupply : DHRSuperselectionSectorLaneSupply operator ρ) →
      (σSupply : DHRSuperselectionSectorLaneSupply operator σ) →
      IntertwinerTrackedCarrierAdapterBoundary
        operator
        ρ
        σ
        f
        (sectorPrimaryLaneFromSupply ρ ρSupply)
        (sectorPrimaryLaneFromSupply σ σSupply)
        (localisedCarrierSemanticsFromSupply ρ ρSupply)
        (localisedCarrierSemanticsFromSupply σ σSupply)
        (trackedIntertwinerActionFromSupplies ρ σ f ρSupply σSupply)

    statisticsOperatorFromSuppliedSectors :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.DHRStatisticsOperator

    statisticsFormulaSocketFromSuppliedSectors :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.DHRStatisticsFormulaSocket ρ σ

    statisticsOperatorTargetReceipt :
      DHR.DHRStatisticsOperator →
      Set

    statisticsSymmetryTargetReceipt :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.DHRStatisticsFormulaSocket ρ σ →
      Set

    braidingNaturalitySquareTargetReceipt :
      DHRBraidingNaturalitySquareDecomposition

    coherenceReceipt :
      DHRHexagonFailClosedCoherenceReceipt

    unitCoherenceTargetReceipt :
      DHR.LocalisedEndomorphism →
      Set

    leftHexagonTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    rightHexagonTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    trackedIntertwinerActionWiredFromSupplies :
      Bool

    trackedIntertwinerActionWiredFromSuppliesIsTrue :
      trackedIntertwinerActionWiredFromSupplies ≡ true

    nonemptyCarrierWitnessWiredFromSupplies :
      Bool

    nonemptyCarrierWitnessWiredFromSuppliesIsTrue :
      nonemptyCarrierWitnessWiredFromSupplies ≡ true

    statisticsOperatorTargetWiredFromSupplies :
      Bool

    statisticsOperatorTargetWiredFromSuppliesIsTrue :
      statisticsOperatorTargetWiredFromSupplies ≡ true

    statisticsOperatorComputed :
      Bool

    statisticsOperatorComputedIsFalse :
      statisticsOperatorComputed ≡ false

    naturalitySquareInhabited :
      Bool

    naturalitySquareInhabitedIsFalse :
      naturalitySquareInhabited ≡ false

    braidingNaturalityClosed :
      Bool

    braidingNaturalityClosedIsFalse :
      braidingNaturalityClosed ≡ false

    leftHexagonClosed :
      Bool

    leftHexagonClosedIsFalse :
      leftHexagonClosed ≡ false

    rightHexagonClosed :
      Bool

    rightHexagonClosedIsFalse :
      rightHexagonClosed ≡ false

    symmetricHexagonClosed :
      Bool

    symmetricHexagonClosedIsFalse :
      symmetricHexagonClosed ≡ false

    fullTransportDRHexagonClosed :
      Bool

    fullTransportDRHexagonClosedIsFalse :
      fullTransportDRHexagonClosed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    suppliedSectorLaneWiringBoundary :
      List String

open DHRSuppliedSectorLaneNaturalityHexagonWiring public

dhrSuppliedSectorLaneNaturalityHexagonWiring :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRSuppliedSectorLaneNaturalityHexagonWiring operator
dhrSuppliedSectorLaneNaturalityHexagonWiring operator =
  record
    { sectorPrimaryLaneFromSupply =
        λ _ supply →
          sectorPrimaryLane supply
    ; sectorPrimaryLaneAgreesWithSuppliedLane =
        λ _ supply →
          sectorPrimaryLaneMatchesSectorLane supply
    ; localisedCarrierSemanticsFromSupply =
        dhrSuperselectionSectorLaneSupplyToCarrierSemantics
          operator
    ; nonemptyCarrierWitnessFromSupply =
        dhrSuperselectionSectorLaneSupplyNonemptyWitness
          operator
    ; trackedIntertwinerActionFromSupplies =
        dhrSuperselectionSectorLaneSuppliesToTrackedIntertwiner
          operator
    ; trackedIntertwinerAdapterFromSupplies =
        dhrSuperselectionSectorLaneSuppliesToTrackedIntertwinerAdapter
          operator
    ; statisticsOperatorFromSuppliedSectors =
        λ ρ σ →
          DHR.DHRSelectionCriterionTarget.statisticsOperator
            DHR.canonicalDHRSelectionCriterionTarget
            (DHR.LocalisedEndomorphism.localisedSector ρ)
            (DHR.LocalisedEndomorphism.localisedSector σ)
    ; statisticsFormulaSocketFromSuppliedSectors =
        DHR.DHRSelectionCriterionTarget.statisticsFormulaSocket
          DHR.canonicalDHRSelectionCriterionTarget
    ; statisticsOperatorTargetReceipt =
        DHR.DHRSelectionCriterionTarget.statisticsOperatorTarget
          DHR.canonicalDHRSelectionCriterionTarget
    ; statisticsSymmetryTargetReceipt =
        DHR.DHRCategoryPrimitiveSurface.symmetryFromStatisticsTarget
          DHR.canonicalDHRCategoryPrimitiveSurface
    ; braidingNaturalitySquareTargetReceipt =
        canonicalDHRBraidingNaturalitySquareDecomposition
    ; coherenceReceipt =
        canonicalDHRHexagonFailClosedCoherenceReceipt
    ; unitCoherenceTargetReceipt =
        DHRHexagonFailClosedCoherenceReceipt.unitCoherenceTargetReceipt
          canonicalDHRHexagonFailClosedCoherenceReceipt
    ; leftHexagonTargetReceipt =
        DHRHexagonFailClosedCoherenceReceipt.leftHexagonTargetReceipt
          canonicalDHRHexagonFailClosedCoherenceReceipt
    ; rightHexagonTargetReceipt =
        DHRHexagonFailClosedCoherenceReceipt.rightHexagonTargetReceipt
          canonicalDHRHexagonFailClosedCoherenceReceipt
    ; trackedIntertwinerActionWiredFromSupplies =
        true
    ; trackedIntertwinerActionWiredFromSuppliesIsTrue =
        refl
    ; nonemptyCarrierWitnessWiredFromSupplies =
        true
    ; nonemptyCarrierWitnessWiredFromSuppliesIsTrue =
        refl
    ; statisticsOperatorTargetWiredFromSupplies =
        true
    ; statisticsOperatorTargetWiredFromSuppliesIsTrue =
        refl
    ; statisticsOperatorComputed =
        false
    ; statisticsOperatorComputedIsFalse =
        refl
    ; naturalitySquareInhabited =
        DHRBraidingNaturalitySquareDecomposition.naturalitySquareInhabited
          canonicalDHRBraidingNaturalitySquareDecomposition
    ; naturalitySquareInhabitedIsFalse =
        DHRBraidingNaturalitySquareDecomposition.naturalitySquareInhabitedIsFalse
          canonicalDHRBraidingNaturalitySquareDecomposition
    ; braidingNaturalityClosed =
        false
    ; braidingNaturalityClosedIsFalse =
        refl
    ; leftHexagonClosed =
        false
    ; leftHexagonClosedIsFalse =
        refl
    ; rightHexagonClosed =
        false
    ; rightHexagonClosedIsFalse =
        refl
    ; symmetricHexagonClosed =
        false
    ; symmetricHexagonClosedIsFalse =
        refl
    ; fullTransportDRHexagonClosed =
        false
    ; fullTransportDRHexagonClosedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; suppliedSectorLaneWiringBoundary =
        "sectorPrimaryLane is the supplied sectorLane, named explicitly for downstream DHR bridge consumers"
        ∷ "Supplied sector-lane interfaces are consumed into local carrier semantics with nonempty witnesses and global foreign-lane identity"
        ∷ "Source and target supplies produce a target-selected tracked Intertwiner carrier action and adapter boundary"
        ∷ "The statistics operator is wired from canonical DHR selection sockets to category symmetry targets, while remaining uncomputed"
        ∷ "Braiding naturality and left/right hexagon remain fail-closed: targets are wired, but no naturality square or hexagon inhabitant is supplied"
        ∷ "No naturality square, symmetric hexagon, DR classification, gauge reconstruction, terminal, Clay, W3, W4, or W5 promotion is constructed"
        ∷ []
    }

record DHRSuperselectionSectorLaneSupplyAbsenceLedger
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    dhrSuperselectionSectorTarget :
      Set

    dhrSuperselectionSectorTargetIsPrimitive :
      dhrSuperselectionSectorTarget
      ≡
      DHRSuperselectionSector

    sectorLaneSupplyTarget :
      DHR.LocalisedEndomorphism →
      Set₁

    sectorLaneSupplyTargetIsCanonical :
      (ρ : DHR.LocalisedEndomorphism) →
      sectorLaneSupplyTarget ρ
      ≡
      DHRSuperselectionSectorLaneSupply operator ρ

    suppliedInterfaceConsumerAvailable :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
        operator
        ρ
        (sectorPrimaryLane supply)

    suppliedSectorLaneWiringAvailable :
      DHRSuppliedSectorLaneNaturalityHexagonWiring operator

    superselectionSectorConstructorsSupplied :
      Bool

    superselectionSectorConstructorsSuppliedIsFalse :
      superselectionSectorConstructorsSupplied ≡ false

    sectorLanePredicateSupplied :
      Bool

    sectorLanePredicateSuppliedIsFalse :
      sectorLanePredicateSupplied ≡ false

    nonemptyCarrierWitnessSuppliedByRepo :
      Bool

    nonemptyCarrierWitnessSuppliedByRepoIsFalse :
      nonemptyCarrierWitnessSuppliedByRepo ≡ false

    foreignLaneIdentitySuppliedByRepo :
      Bool

    foreignLaneIdentitySuppliedByRepoIsFalse :
      foreignLaneIdentitySuppliedByRepo ≡ false

    dhrSectorLaneSupplyPromoted :
      Bool

    dhrSectorLaneSupplyPromotedIsFalse :
      dhrSectorLaneSupplyPromoted ≡ false

    dhrSectorLaneSupplyLedgerBoundary :
      List String

open DHRSuperselectionSectorLaneSupplyAbsenceLedger public

dhrSuperselectionSectorLaneSupplyAbsenceLedger :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRSuperselectionSectorLaneSupplyAbsenceLedger operator
dhrSuperselectionSectorLaneSupplyAbsenceLedger operator =
  record
    { dhrSuperselectionSectorTarget =
        DHRSuperselectionSector
    ; dhrSuperselectionSectorTargetIsPrimitive =
        refl
    ; sectorLaneSupplyTarget =
        DHRSuperselectionSectorLaneSupply operator
    ; sectorLaneSupplyTargetIsCanonical =
        λ _ → refl
    ; suppliedInterfaceConsumerAvailable =
        dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
          operator
    ; suppliedSectorLaneWiringAvailable =
        dhrSuppliedSectorLaneNaturalityHexagonWiring
          operator
    ; superselectionSectorConstructorsSupplied =
        false
    ; superselectionSectorConstructorsSuppliedIsFalse =
        refl
    ; sectorLanePredicateSupplied =
        false
    ; sectorLanePredicateSuppliedIsFalse =
        refl
    ; nonemptyCarrierWitnessSuppliedByRepo =
        false
    ; nonemptyCarrierWitnessSuppliedByRepoIsFalse =
        refl
    ; foreignLaneIdentitySuppliedByRepo =
        false
    ; foreignLaneIdentitySuppliedByRepoIsFalse =
        refl
    ; dhrSectorLaneSupplyPromoted =
        false
    ; dhrSectorLaneSupplyPromotedIsFalse =
        refl
    ; dhrSectorLaneSupplyLedgerBoundary =
        "Exact supply interface recorded: DHRSuperselectionSector, sectorPrimaryLane, selected nonempty carrier predicate, assigned-lane preservation, and foreign-lane identity"
        ∷ "The repository can consume such a supply into the nondegenerate localised carrier interface, but it does not supply the sector constructors or lane predicate itself"
        ∷ "The repository can wire supplied local interfaces through target-selected tracked Intertwiner carrier semantics, but not through DHR naturality or hexagon proofs"
        ∷ "No DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

record DHRExplicitSuppliedGlobalForeignLaneIdentityWitness
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) :
  Setω where
  field
    suppliedSector :
      DHR.SuperselectionSector

    suppliedSectorMatchesLocalisedSector :
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      suppliedSector

    suppliedLane :
      G6.Lane

    suppliedLaneMatchesSectorLane :
      suppliedLane
      ≡
      sectorLane supply

    selectedPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    selectedPredicateMatchesSupply :
      selectedPredicate
      ≡
      selectedSectorCarrierPredicate supply

    selectedWitness :
      G6.NontrivialTrackedLaneOperator.Carrier operator

    selectedWitnessMatchesSupply :
      selectedWitness
      ≡
      selectedSectorCarrierNonemptyWitness supply

    selectedWitnessSelected :
      selectedPredicate selectedWitness ≡ true

    assignedLanePreservesSelectedPredicate :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedPredicate x ≡ true →
      selectedPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction
          operator
          suppliedLane
          x)
      ≡
      true

    explicitGlobalForeignLaneActionIdentity :
      (otherLane : G6.Lane) →
      suppliedLane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedPredicate x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    suppliedIdentityWitnessAvailable :
      Bool

    suppliedIdentityWitnessAvailableIsTrue :
      suppliedIdentityWitnessAvailable ≡ true

    repoDerivedArbitraryIdentityWitness :
      Bool

    repoDerivedArbitraryIdentityWitnessIsFalse :
      repoDerivedArbitraryIdentityWitness ≡ false

    firstResidualBlockerWithoutSupply :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    firstResidualBlockerWithoutSupplyIsExplicitIdentityWitness :
      firstResidualBlockerWithoutSupply
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    witnessBoundary :
      List String

open DHRExplicitSuppliedGlobalForeignLaneIdentityWitness public

dhrExplicitSuppliedGlobalForeignLaneIdentityWitness :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  DHRExplicitSuppliedGlobalForeignLaneIdentityWitness
    operator
    ρ
    supply
dhrExplicitSuppliedGlobalForeignLaneIdentityWitness operator ρ supply =
  record
    { suppliedSector =
        dhrSuperselectionSector supply
    ; suppliedSectorMatchesLocalisedSector =
        dhrSuperselectionSectorMatchesLocalisedSector supply
    ; suppliedLane =
        sectorLane supply
    ; suppliedLaneMatchesSectorLane =
        refl
    ; selectedPredicate =
        selectedSectorCarrierPredicate supply
    ; selectedPredicateMatchesSupply =
        refl
    ; selectedWitness =
        selectedSectorCarrierNonemptyWitness supply
    ; selectedWitnessMatchesSupply =
        refl
    ; selectedWitnessSelected =
        selectedSectorCarrierNonemptyWitnessSelected supply
    ; assignedLanePreservesSelectedPredicate =
        sectorLaneActionPreservesSelectedCarrier supply
    ; explicitGlobalForeignLaneActionIdentity =
        foreignLaneActionIdentityOnSelectedCarrier supply
    ; suppliedIdentityWitnessAvailable =
        true
    ; suppliedIdentityWitnessAvailableIsTrue =
        refl
    ; repoDerivedArbitraryIdentityWitness =
        false
    ; repoDerivedArbitraryIdentityWitnessIsFalse =
        refl
    ; firstResidualBlockerWithoutSupply =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; firstResidualBlockerWithoutSupplyIsExplicitIdentityWitness =
        refl
    ; witnessBoundary =
        "Concrete global foreign-lane identity is now exposed when a DHRSuperselectionSectorLaneSupply is supplied"
        ∷ "The witness includes the selected nonempty carrier, assigned-lane preservation, and the foreign-lane action identity eliminator"
        ∷ "This discharges only the supplied-witness consumption path; the repository still has no arbitrary unsupplied global foreign-lane identity theorem"
        ∷ "Without an explicit supply, the first residual blocker remains residualGlobalForeignLaneIdentityRequiresExplicitWitness"
        ∷ "No DHR classification, DR reconstruction, gauge assignment, or symmetric hexagon proof is promoted"
        ∷ []
    }

record DHRGate6Wave2ForeignIdentityHandoff
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    suppliedIdentityWitnessConsumer :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      DHRExplicitSuppliedGlobalForeignLaneIdentityWitness
        operator
        ρ
        supply

    suppliedLaneInterfaceConsumer :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
        operator
        ρ
        (sectorPrimaryLane supply)

    suppliedLaneHexagonWiringConsumer :
      DHRSuppliedSectorLaneNaturalityHexagonWiring operator

    aqftLocalAlgebraFirstResidual :
      AQFTColim.AQFTCarrierAlgebraQuotientOpenObligation

    aqftLocalAlgebraFirstResidualIsMissingQuotientConstruction :
      aqftLocalAlgebraFirstResidual
      ≡
      AQFTColim.missingQuotientConstruction

    dhrUnsuppliedForeignIdentityResidual :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    dhrUnsuppliedForeignIdentityResidualIsExplicitWitness :
      dhrUnsuppliedForeignIdentityResidual
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    downstreamBlockers :
      List DHRArbitrarySectorClassificationDownstreamBlocker

    downstreamBlockersAreExact :
      downstreamBlockers
      ≡
      (missingDASHILocalAlgebra
       ∷ blockedByMissingGate1GaugeRepresentationSemantics
       ∷ [])

    suppliedWitnessPathPromoted :
      Bool

    suppliedWitnessPathPromotedIsTrue :
      suppliedWitnessPathPromoted ≡ true

    repoNativeUnconditionalForeignIdentityPromoted :
      Bool

    repoNativeUnconditionalForeignIdentityPromotedIsFalse :
      repoNativeUnconditionalForeignIdentityPromoted ≡ false

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    gate1GaugeRepresentationSemanticsPromoted :
      Bool

    gate1GaugeRepresentationSemanticsPromotedIsFalse :
      gate1GaugeRepresentationSemanticsPromoted ≡ false

    handoffBoundary :
      List String

open DHRGate6Wave2ForeignIdentityHandoff public

canonicalDHRGate6Wave2ForeignIdentityHandoff :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRGate6Wave2ForeignIdentityHandoff operator
canonicalDHRGate6Wave2ForeignIdentityHandoff operator =
  record
    { suppliedIdentityWitnessConsumer =
        dhrExplicitSuppliedGlobalForeignLaneIdentityWitness
          operator
    ; suppliedLaneInterfaceConsumer =
        dhrSuperselectionSectorLaneSupplyToNondegenerateInterface
          operator
    ; suppliedLaneHexagonWiringConsumer =
        dhrSuppliedSectorLaneNaturalityHexagonWiring operator
    ; aqftLocalAlgebraFirstResidual =
        AQFTColim.missingQuotientConstruction
    ; aqftLocalAlgebraFirstResidualIsMissingQuotientConstruction =
        refl
    ; dhrUnsuppliedForeignIdentityResidual =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; dhrUnsuppliedForeignIdentityResidualIsExplicitWitness =
        refl
    ; downstreamBlockers =
        missingDASHILocalAlgebra
        ∷ blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; downstreamBlockersAreExact =
        refl
    ; suppliedWitnessPathPromoted =
        true
    ; suppliedWitnessPathPromotedIsTrue =
        refl
    ; repoNativeUnconditionalForeignIdentityPromoted =
        false
    ; repoNativeUnconditionalForeignIdentityPromotedIsFalse =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; gate1GaugeRepresentationSemanticsPromoted =
        false
    ; gate1GaugeRepresentationSemanticsPromotedIsFalse =
        refl
    ; handoffBoundary =
        "Wave 2 Gate6 handoff: explicit DHRSuperselectionSectorLaneSupply inputs now produce a concrete global foreign-lane identity witness"
        ∷ "The same supplied evidence feeds the nondegenerate localised carrier interface and supplied-sector hexagon wiring consumers"
        ∷ "No repo-native unconditional global foreign-lane identity theorem is derived for arbitrary unsupplied sectors"
        ∷ "l5 is currently halted at missingQuotientConstruction before missingDASHILocalAlgebra can be supplied"
        ∷ "Gate1 remains halted at blockedByMissingGate1GaugeRepresentationSemantics for exact reconstruction matching"
        ∷ []
    }

record DHRGate6Wave3FinalLocalForeignIdentityHandoff
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    wave2SuppliedForeignIdentityHandoff :
      DHRGate6Wave2ForeignIdentityHandoff operator

    suppliedIdentityWitnessConsumerFinal :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      DHRExplicitSuppliedGlobalForeignLaneIdentityWitness
        operator
        ρ
        supply

    quotientConstructionProgress :
      AQFTColim.TransportSetoidQuotientConstructionProgress

    aqftCurrentFirstResidual :
      AQFTColim.AQFTCarrierAlgebraQuotientOpenObligation

    aqftCurrentFirstResidualIsMissingPreciseQuotientRelation :
      aqftCurrentFirstResidual
      ≡
      AQFTColim.missingPreciseQuotientRelation

    unsuppliedForeignIdentityResidual :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    unsuppliedForeignIdentityResidualIsExplicitWitness :
      unsuppliedForeignIdentityResidual
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    downstreamBlockers :
      List DHRArbitrarySectorClassificationDownstreamBlocker

    downstreamBlockersAreExact :
      downstreamBlockers
      ≡
      (missingDASHILocalAlgebra
       ∷ blockedByMissingGate1GaugeRepresentationSemantics
       ∷ [])

    suppliedWitnessPathDischarged :
      Bool

    suppliedWitnessPathDischargedIsTrue :
      suppliedWitnessPathDischarged ≡ true

    repoNativeUnconditionalForeignIdentityPromoted :
      Bool

    repoNativeUnconditionalForeignIdentityPromotedIsFalse :
      repoNativeUnconditionalForeignIdentityPromoted ≡ false

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    gate1ExactMatchPromoted :
      Bool

    gate1ExactMatchPromotedIsFalse :
      gate1ExactMatchPromoted ≡ false

    finalLocalBoundary :
      List String

open DHRGate6Wave3FinalLocalForeignIdentityHandoff public

canonicalDHRGate6Wave3FinalLocalForeignIdentityHandoff :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRGate6Wave3FinalLocalForeignIdentityHandoff operator
canonicalDHRGate6Wave3FinalLocalForeignIdentityHandoff operator =
  record
    { wave2SuppliedForeignIdentityHandoff =
        canonicalDHRGate6Wave2ForeignIdentityHandoff operator
    ; suppliedIdentityWitnessConsumerFinal =
        dhrExplicitSuppliedGlobalForeignLaneIdentityWitness
          operator
    ; quotientConstructionProgress =
        AQFTColim.canonicalTransportSetoidQuotientConstructionProgress
    ; aqftCurrentFirstResidual =
        AQFTColim.missingPreciseQuotientRelation
    ; aqftCurrentFirstResidualIsMissingPreciseQuotientRelation =
        refl
    ; unsuppliedForeignIdentityResidual =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; unsuppliedForeignIdentityResidualIsExplicitWitness =
        refl
    ; downstreamBlockers =
        missingDASHILocalAlgebra
        ∷ blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; downstreamBlockersAreExact =
        refl
    ; suppliedWitnessPathDischarged =
        true
    ; suppliedWitnessPathDischargedIsTrue =
        refl
    ; repoNativeUnconditionalForeignIdentityPromoted =
        false
    ; repoNativeUnconditionalForeignIdentityPromotedIsFalse =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; gate1ExactMatchPromoted =
        false
    ; gate1ExactMatchPromotedIsFalse =
        refl
    ; finalLocalBoundary =
        "Wave 3 final-local handoff: supplied DHRSuperselectionSectorLaneSupply still gives the concrete global foreign-lane identity witness"
        ∷ "No unconditional repo-native foreign-lane identity theorem exists for arbitrary unsupplied sectors"
        ∷ "AQFT l5 has advanced past missingQuotientConstruction; the current upstream residual is missingPreciseQuotientRelation"
        ∷ "DHR classification waits behind missingDASHILocalAlgebra after the AQFT quotient relation/algebra/norm laws"
        ∷ "Gate1/Gate6 exact reconstruction remains blocked by blockedByMissingGate1GaugeRepresentationSemantics and missingExactStandardModelCarrierFunctorMatch"
        ∷ []
    }

record DHRGate6ArbitrarySectorConstructionBlockedReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    finalLocalForeignIdentityHandoff :
      DHRGate6Wave3FinalLocalForeignIdentityHandoff operator

    localAlgebraPreconditionAudit :
      DHR.DHRGate6LocalAlgebraPreconditionAuditReceipt

    suppliedIdentityWitnessConsumer :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      DHRExplicitSuppliedGlobalForeignLaneIdentityWitness
        operator
        ρ
        supply

    aqftCurrentFirstResidual :
      AQFTColim.AQFTCarrierAlgebraQuotientOpenObligation

    aqftCurrentFirstResidualIsMissingPreciseQuotientRelation :
      aqftCurrentFirstResidual
      ≡
      AQFTColim.missingPreciseQuotientRelation

    unsuppliedForeignIdentityResidual :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    unsuppliedForeignIdentityResidualIsExplicitWitness :
      unsuppliedForeignIdentityResidual
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    downstreamBlockers :
      List DHRArbitrarySectorClassificationDownstreamBlocker

    downstreamBlockersAreExact :
      downstreamBlockers
      ≡
      (missingDASHILocalAlgebra
       ∷ blockedByMissingGate1GaugeRepresentationSemantics
       ∷ [])

    suppliedWitnessPathStillAvailable :
      Bool

    suppliedWitnessPathStillAvailableIsTrue :
      suppliedWitnessPathStillAvailable ≡ true

    arbitraryPrimeLaneIdentityWitnessesConstructed :
      Bool

    arbitraryPrimeLaneIdentityWitnessesConstructedIsFalse :
      arbitraryPrimeLaneIdentityWitnessesConstructed ≡ false

    localisedTransportableEndomorphismsConstructed :
      Bool

    localisedTransportableEndomorphismsConstructedIsFalse :
      localisedTransportableEndomorphismsConstructed ≡ false

    statisticsAndHexagonCoherenceClosed :
      Bool

    statisticsAndHexagonCoherenceClosedIsFalse :
      statisticsAndHexagonCoherenceClosed ≡ false

    drReceiptConsumed :
      Bool

    drReceiptConsumedIsFalse :
      drReceiptConsumed ≡ false

    blockedBoundary :
      List String

open DHRGate6ArbitrarySectorConstructionBlockedReceipt public

canonicalDHRGate6ArbitrarySectorConstructionBlockedReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRGate6ArbitrarySectorConstructionBlockedReceipt operator
canonicalDHRGate6ArbitrarySectorConstructionBlockedReceipt operator =
  record
    { finalLocalForeignIdentityHandoff =
        canonicalDHRGate6Wave3FinalLocalForeignIdentityHandoff operator
    ; localAlgebraPreconditionAudit =
        DHR.canonicalDHRGate6LocalAlgebraPreconditionAuditReceipt
    ; suppliedIdentityWitnessConsumer =
        dhrExplicitSuppliedGlobalForeignLaneIdentityWitness operator
    ; aqftCurrentFirstResidual =
        AQFTColim.missingPreciseQuotientRelation
    ; aqftCurrentFirstResidualIsMissingPreciseQuotientRelation =
        refl
    ; unsuppliedForeignIdentityResidual =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; unsuppliedForeignIdentityResidualIsExplicitWitness =
        refl
    ; downstreamBlockers =
        missingDASHILocalAlgebra
        ∷ blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; downstreamBlockersAreExact =
        refl
    ; suppliedWitnessPathStillAvailable =
        true
    ; suppliedWitnessPathStillAvailableIsTrue =
        refl
    ; arbitraryPrimeLaneIdentityWitnessesConstructed =
        false
    ; arbitraryPrimeLaneIdentityWitnessesConstructedIsFalse =
        refl
    ; localisedTransportableEndomorphismsConstructed =
        false
    ; localisedTransportableEndomorphismsConstructedIsFalse =
        refl
    ; statisticsAndHexagonCoherenceClosed =
        false
    ; statisticsAndHexagonCoherenceClosedIsFalse =
        refl
    ; drReceiptConsumed =
        false
    ; drReceiptConsumedIsFalse =
        refl
    ; blockedBoundary =
        "u6 blocked receipt: supplied DHRSuperselectionSectorLaneSupply still gives a concrete identity-witness consumer"
        ∷ "Arbitrary prime-lane identity witnesses are not constructed without a repo-native unconditional foreign-lane identity theorem"
        ∷ "missingDASHILocalAlgebra is not consumed; AQFT currently first-misses at missingPreciseQuotientRelation"
        ∷ "Localized transportable endomorphisms, statistics operators, duals/Frobenius, hexagon coherence, and DR receipt stay fail-closed"
        ∷ "No DR, Standard Model, Gate1, Clay, W3, W4, or W5 semantics are fabricated"
        ∷ []
    }

record DHRU6SuppliedIdentityWitnessSurface
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) :
  Setω where
  field
    explicitSuppliedWitness :
      DHRExplicitSuppliedGlobalForeignLaneIdentityWitness
        operator
        ρ
        supply

    selectedWitness :
      G6.NontrivialTrackedLaneOperator.Carrier operator

    selectedWitnessMatchesExplicitWitness :
      selectedWitness
      ≡
      DHRExplicitSuppliedGlobalForeignLaneIdentityWitness.selectedWitness
        explicitSuppliedWitness

    suppliedIdentityWitnessShapeAvailable :
      Bool

    suppliedIdentityWitnessShapeAvailableIsTrue :
      suppliedIdentityWitnessShapeAvailable ≡ true

    unsuppliedResidualBlocker :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    unsuppliedResidualBlockerIsExplicitIdentityWitness :
      unsuppliedResidualBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    arbitraryIdentityWitnessPromoted :
      Bool

    arbitraryIdentityWitnessPromotedIsFalse :
      arbitraryIdentityWitnessPromoted ≡ false

    hexagonCoherencePromoted :
      Bool

    hexagonCoherencePromotedIsFalse :
      hexagonCoherencePromoted ≡ false

    u6SuppliedIdentityBoundary :
      List String

open DHRU6SuppliedIdentityWitnessSurface public

dhrU6SuppliedIdentityWitnessSurface :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  DHRU6SuppliedIdentityWitnessSurface operator ρ supply
dhrU6SuppliedIdentityWitnessSurface operator ρ supply =
  record
    { explicitSuppliedWitness =
        dhrExplicitSuppliedGlobalForeignLaneIdentityWitness
          operator
          ρ
          supply
    ; selectedWitness =
        selectedSectorCarrierNonemptyWitness supply
    ; selectedWitnessMatchesExplicitWitness =
        refl
    ; suppliedIdentityWitnessShapeAvailable =
        true
    ; suppliedIdentityWitnessShapeAvailableIsTrue =
        refl
    ; unsuppliedResidualBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; unsuppliedResidualBlockerIsExplicitIdentityWitness =
        refl
    ; arbitraryIdentityWitnessPromoted =
        false
    ; arbitraryIdentityWitnessPromotedIsFalse =
        refl
    ; hexagonCoherencePromoted =
        false
    ; hexagonCoherencePromotedIsFalse =
        refl
    ; u6SuppliedIdentityBoundary =
        "u6 explicit supplied identity-witness surface packages the existing DHRSuperselectionSectorLaneSupply consumer"
        ∷ "the selected nonempty witness is exposed directly from the supplied package"
        ∷ "the unsupplied arbitrary-sector residual remains residualGlobalForeignLaneIdentityRequiresExplicitWitness"
        ∷ "no arbitrary identity theorem, DHR hexagon coherence, DR reconstruction, or gauge assignment is promoted"
        ∷ []
    }

canonicalDHRPrimitiveSectorClasses :
  List DHRPrimitiveSectorClass
canonicalDHRPrimitiveSectorClasses =
  primitiveMaxwellSectorClass
  ∷ primitiveSchrodingerSectorClass
  ∷ primitiveGRSectorClass
  ∷ primitiveEmpiricalSectorClass
  ∷ []

data DHRSelectedPrimeLaneIdentityWitnessResidual : Set where
  selectedWitnessesRequireSuppliedNondegenerateInterface :
    DHRSelectedPrimeLaneIdentityWitnessResidual

  arbitraryWitnessBlockedByMissingDASHILocalAlgebra :
    DHRSelectedPrimeLaneIdentityWitnessResidual

  arbitraryWitnessBlockedByMissingSectorSemantics :
    DHRSelectedPrimeLaneIdentityWitnessResidual

record DHRSelectedPrimeLaneIdentityWitnessFailClosedReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    gaugeIdentityEndomorphismAudit :
      Bool

    selectedPrimitiveSectorClasses :
      List DHRPrimitiveSectorClass

    selectedPrimitiveSectorClassesAreCanonical :
      selectedPrimitiveSectorClasses
      ≡
      canonicalDHRPrimitiveSectorClasses

    primitiveSelectedPredicateProgress :
      DHRPrimitiveSelectedPredicateForeignIdentitySupplyProgress operator

    selectedPrimitiveIdentityWitnessFromSuppliedInterface :
      (ρ : DHR.LocalisedEndomorphism) →
      (sectorClass : DHRPrimitiveSectorClass) →
      (sectorMatchesPrimitiveConstructor :
        DHR.LocalisedEndomorphism.localisedSector ρ
        ≡
        DHRPrimitiveSuperselectionSectorConstructorSurface.sectorForPrimitiveClass
          canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
          sectorClass) →
      (external :
        NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
          operator
          ρ
          (primitiveSectorClassAssignedLane sectorClass)) →
      DHRExplicitSuppliedGlobalForeignLaneIdentityWitness
        operator
        ρ
        (primitiveSectorInterfaceToLaneSupply
          operator
          ρ
          canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
          sectorClass
          sectorMatchesPrimitiveConstructor
          external)

    selectedSuppliedLaneIdentityWitness :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      DHRExplicitSuppliedGlobalForeignLaneIdentityWitness
        operator
        ρ
        supply

    selectedPrimitiveSuppliedInterfaceWitnessesPackaged :
      Bool

    selectedPrimitiveSuppliedInterfaceWitnessesPackagedIsTrue :
      selectedPrimitiveSuppliedInterfaceWitnessesPackaged ≡ true

    selectedIdentityEndomorphismActionWitnessConstructed :
      Bool

    selectedIdentityEndomorphismActionWitnessConstructedIsFalse :
      selectedIdentityEndomorphismActionWitnessConstructed ≡ false

    arbitraryDhrSectorIdentityWitnessConstructed :
      Bool

    arbitraryDhrSectorIdentityWitnessConstructedIsFalse :
      arbitraryDhrSectorIdentityWitnessConstructed ≡ false

    repoNativeGlobalForeignLaneIdentityTheoremSupplied :
      Bool

    repoNativeGlobalForeignLaneIdentityTheoremSuppliedIsFalse :
      repoNativeGlobalForeignLaneIdentityTheoremSupplied ≡ false

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsFalse :
      missingDASHILocalAlgebraConsumed ≡ false

    drReceiptConsumed :
      Bool

    drReceiptConsumedIsFalse :
      drReceiptConsumed ≡ false

    firstResidualBlocker :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    firstResidualBlockerIsExplicitWitness :
      firstResidualBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    selectedPrimeLaneIdentityResiduals :
      List DHRSelectedPrimeLaneIdentityWitnessResidual

    downstreamBlockers :
      List DHRArbitrarySectorClassificationDownstreamBlocker

    downstreamBlockersAreExact :
      downstreamBlockers
      ≡
      (missingDASHILocalAlgebra
       ∷ blockedByMissingGate1GaugeRepresentationSemantics
       ∷ [])

    failClosedBoundary :
      List String

open DHRSelectedPrimeLaneIdentityWitnessFailClosedReceipt public

canonicalDHRSelectedPrimeLaneIdentityWitnessFailClosedReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRSelectedPrimeLaneIdentityWitnessFailClosedReceipt operator
canonicalDHRSelectedPrimeLaneIdentityWitnessFailClosedReceipt operator =
  record
    { gaugeIdentityEndomorphismAudit =
        true
    ; selectedPrimitiveSectorClasses =
        canonicalDHRPrimitiveSectorClasses
    ; selectedPrimitiveSectorClassesAreCanonical =
        refl
    ; primitiveSelectedPredicateProgress =
        canonicalDHRPrimitiveSelectedPredicateForeignIdentitySupplyProgress
          operator
    ; selectedPrimitiveIdentityWitnessFromSuppliedInterface =
        λ ρ sectorClass sectorMatchesPrimitiveConstructor external →
          dhrExplicitSuppliedGlobalForeignLaneIdentityWitness
            operator
            ρ
            (primitiveSectorInterfaceToLaneSupply
              operator
              ρ
              canonicalDHRPrimitiveSuperselectionSectorConstructorSurface
              sectorClass
              sectorMatchesPrimitiveConstructor
              external)
    ; selectedSuppliedLaneIdentityWitness =
        dhrExplicitSuppliedGlobalForeignLaneIdentityWitness
          operator
    ; selectedPrimitiveSuppliedInterfaceWitnessesPackaged =
        true
    ; selectedPrimitiveSuppliedInterfaceWitnessesPackagedIsTrue =
        refl
    ; selectedIdentityEndomorphismActionWitnessConstructed =
        false
    ; selectedIdentityEndomorphismActionWitnessConstructedIsFalse =
        refl
    ; arbitraryDhrSectorIdentityWitnessConstructed =
        false
    ; arbitraryDhrSectorIdentityWitnessConstructedIsFalse =
        refl
    ; repoNativeGlobalForeignLaneIdentityTheoremSupplied =
        false
    ; repoNativeGlobalForeignLaneIdentityTheoremSuppliedIsFalse =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; missingDASHILocalAlgebraConsumedIsFalse =
        refl
    ; drReceiptConsumed =
        false
    ; drReceiptConsumedIsFalse =
        refl
    ; firstResidualBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; firstResidualBlockerIsExplicitWitness =
        refl
    ; selectedPrimeLaneIdentityResiduals =
        selectedWitnessesRequireSuppliedNondegenerateInterface
        ∷ arbitraryWitnessBlockedByMissingDASHILocalAlgebra
        ∷ arbitraryWitnessBlockedByMissingSectorSemantics
        ∷ []
    ; downstreamBlockers =
        missingDASHILocalAlgebra
        ∷ blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; downstreamBlockersAreExact =
        refl
    ; failClosedBoundary =
        "u6 fail-closed receipt: selected primitive lane classes are enumerated and can consume explicit supplied nondegenerate-interface foreign-lane identity evidence"
        ∷ "For each selected primitive class, primitiveSectorInterfaceToLaneSupply followed by dhrExplicitSuppliedGlobalForeignLaneIdentityWitness records the concrete supplied identity witness"
        ∷ "The gauge-side audit records that no identity EndomorphismAction constructor is available locally; only the LocalisedEndomorphism.endomorphismAction field is exposed"
        ∷ "Arbitrary DHR-sector identity witnesses remain blocked by missingDASHILocalAlgebra, missing sector semantics, and the residual global foreign-lane identity witness requirement"
        ∷ "No repo-native global foreign-lane identity theorem, Doplicher-Roberts receipt consumption, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

record DHRHexagonNextWaveArbitrarySectorIdentitySurface
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    selectedPrimeLaneIdentityReceipt :
      Bool

    suppliedIdentityWitnessConsumer :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      DHRU6SuppliedIdentityWitnessSurface operator ρ supply

    arbitrarySectorIdentityShapeAttempted :
      Bool

    arbitrarySectorIdentityShapeAttemptedIsTrue :
      arbitrarySectorIdentityShapeAttempted ≡ true

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    globalForeignLaneIdentityTheoremSupplied :
      Bool

    globalForeignLaneIdentityTheoremSuppliedIsFalse :
      globalForeignLaneIdentityTheoremSupplied ≡ false

    hexagonCoherencePromoted :
      Bool

    hexagonCoherencePromotedIsFalse :
      hexagonCoherencePromoted ≡ false

    firstResidualBlocker :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    firstResidualBlocker-v :
      firstResidualBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    downstreamBlockers :
      List DHRArbitrarySectorClassificationDownstreamBlocker

    downstreamBlockersAreCanonical :
      downstreamBlockers
      ≡
      (missingDASHILocalAlgebra
       ∷ blockedByMissingGate1GaugeRepresentationSemantics
       ∷ [])

    nextWaveIdentityBoundary :
      List String

open DHRHexagonNextWaveArbitrarySectorIdentitySurface public

canonicalDHRHexagonNextWaveArbitrarySectorIdentitySurface :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRHexagonNextWaveArbitrarySectorIdentitySurface operator
canonicalDHRHexagonNextWaveArbitrarySectorIdentitySurface operator =
  record
    { selectedPrimeLaneIdentityReceipt =
        true
    ; suppliedIdentityWitnessConsumer =
        dhrU6SuppliedIdentityWitnessSurface operator
    ; arbitrarySectorIdentityShapeAttempted =
        true
    ; arbitrarySectorIdentityShapeAttemptedIsTrue =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; globalForeignLaneIdentityTheoremSupplied =
        false
    ; globalForeignLaneIdentityTheoremSuppliedIsFalse =
        refl
    ; hexagonCoherencePromoted =
        false
    ; hexagonCoherencePromotedIsFalse =
        refl
    ; firstResidualBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; firstResidualBlocker-v =
        refl
    ; downstreamBlockers =
        missingDASHILocalAlgebra
        ∷ blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; downstreamBlockersAreCanonical =
        refl
    ; nextWaveIdentityBoundary =
        "u6 next-wave surface keeps the supplied-sector identity witness consumer available"
        ∷ "the arbitrary-sector identity endomorphism shape is attempted, but no repo-native arbitrary-sector identity theorem is constructed"
        ∷ "residualGlobalForeignLaneIdentityRequiresExplicitWitness remains the first unsupplied DHR identity blocker"
        ∷ "hexagon coherence, DR reconstruction, gauge assignment, and Standard Model matching remain unpromoted"
        ∷ []
    }

record DHRGlobalForeignLaneIdentityBundle
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) :
  Setω where
  field
    explicitSuppliedGlobalForeignLaneIdentityWitness :
      DHRExplicitSuppliedGlobalForeignLaneIdentityWitness
        operator
        ρ
        supply

    bundledLane :
      G6.Lane

    bundledLaneMatchesSupply :
      bundledLane
      ≡
      sectorPrimaryLane supply

    bundledSelectedCarrierPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    bundledSelectedCarrierPredicateMatchesSupply :
      bundledSelectedCarrierPredicate
      ≡
      selectedSectorCarrierPredicate supply

    bundledForeignLaneIdentity :
      (otherLane : G6.Lane) →
      sectorPrimaryLane supply ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedSectorCarrierPredicate supply x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction operator otherLane x
      ≡
      x

    bundleRequiresExplicitSupply :
      Bool

    bundleRequiresExplicitSupplyIsTrue :
      bundleRequiresExplicitSupply ≡ true

    repoDerivedForUnsuppliedArbitrarySector :
      Bool

    repoDerivedForUnsuppliedArbitrarySectorIsFalse :
      repoDerivedForUnsuppliedArbitrarySector ≡ false

    bundleBoundary :
      List String

open DHRGlobalForeignLaneIdentityBundle public

globalForeignLaneIdentityBundle :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
  DHRGlobalForeignLaneIdentityBundle operator ρ supply
globalForeignLaneIdentityBundle operator ρ supply =
  record
    { explicitSuppliedGlobalForeignLaneIdentityWitness =
        dhrExplicitSuppliedGlobalForeignLaneIdentityWitness
          operator
          ρ
          supply
    ; bundledLane =
        sectorPrimaryLane supply
    ; bundledLaneMatchesSupply =
        refl
    ; bundledSelectedCarrierPredicate =
        selectedSectorCarrierPredicate supply
    ; bundledSelectedCarrierPredicateMatchesSupply =
        refl
    ; bundledForeignLaneIdentity =
        foreignLaneActionIdentityOnSelectedCarrier supply
    ; bundleRequiresExplicitSupply =
        true
    ; bundleRequiresExplicitSupplyIsTrue =
        refl
    ; repoDerivedForUnsuppliedArbitrarySector =
        false
    ; repoDerivedForUnsuppliedArbitrarySectorIsFalse =
        refl
    ; bundleBoundary =
        "globalForeignLaneIdentityBundle packages the existing explicit DHRSuperselectionSectorLaneSupply identity field"
        ∷ "The bundle is conditional on supplied sector/lane/predicate evidence"
        ∷ "It is not a repo-derived theorem for arbitrary unsupplied DHR sectors"
        ∷ []
    }

data DHRUpper6IdentityEndomorphismResidual : Set where
  upper6BlockedByMissingIdentityEndomorphismActionConstructor :
    DHRUpper6IdentityEndomorphismResidual

  upper6BlockedByMissingDASHILocalAlgebraSemantics :
    DHRUpper6IdentityEndomorphismResidual

  upper6BlockedByResidualGlobalForeignLaneIdentityRequiresExplicitWitness :
    DHRUpper6IdentityEndomorphismResidual

record DHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    gaugeUpper6IdentityEndomorphismReceipt :
      Bool

    gaugeIdentityActionConstructorShapeReceipt :
      Bool

    selectedPrimeLaneIdentityWitnessReceipt :
      Bool

    globalForeignLaneIdentityBundleFromExplicitSupply :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      DHRGlobalForeignLaneIdentityBundle operator ρ supply

    arbitrarySectorIdentityEndomorphismTarget :
      DHR.SuperselectionSector →
      Set

    missingIdentityActionConstructor :
      DHR.DHRIdentityEndomorphismWitnessBlocker

    missingIdentityActionConstructorIsExact :
      missingIdentityActionConstructor
      ≡
      DHR.missingIdentityEndomorphismActionConstructor

    missingDASHILocalAlgebraSemantics :
      DHR.DHRIdentityEndomorphismWitnessBlocker

    missingDASHILocalAlgebraSemanticsIsExact :
      missingDASHILocalAlgebraSemantics
      ≡
      DHR.missingDASHILocalAlgebraForIdentityActionSemantics

    unsuppliedForeignIdentityResidual :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    unsuppliedForeignIdentityResidualIsExplicitWitness :
      unsuppliedForeignIdentityResidual
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    explicitSupplyBundleConstructed :
      Bool

    explicitSupplyBundleConstructedIsTrue :
      explicitSupplyBundleConstructed ≡ true

    repoNativeGlobalForeignLaneIdentityBundleConstructed :
      Bool

    repoNativeGlobalForeignLaneIdentityBundleConstructedIsFalse :
      repoNativeGlobalForeignLaneIdentityBundleConstructed ≡ false

    residualGlobalForeignLaneIdentityClosed :
      Bool

    residualGlobalForeignLaneIdentityClosedIsFalse :
      residualGlobalForeignLaneIdentityClosed ≡ false

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsFalse :
      missingDASHILocalAlgebraConsumed ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    upper6Residuals :
      List DHRUpper6IdentityEndomorphismResidual

    downstreamBlockers :
      List DHRArbitrarySectorClassificationDownstreamBlocker

    downstreamBlockersAreExact :
      downstreamBlockers
      ≡
      (missingDASHILocalAlgebra
       ∷ blockedByMissingGate1GaugeRepresentationSemantics
       ∷ [])

    upper6Boundary :
      List String

open DHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt public

canonicalDHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt operator
canonicalDHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt operator =
  record
    { gaugeUpper6IdentityEndomorphismReceipt =
        true
    ; gaugeIdentityActionConstructorShapeReceipt =
        false
    ; selectedPrimeLaneIdentityWitnessReceipt =
        true
    ; globalForeignLaneIdentityBundleFromExplicitSupply =
        globalForeignLaneIdentityBundle operator
    ; arbitrarySectorIdentityEndomorphismTarget =
        DHR.DHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt.arbitrarySectorIdentityEndomorphismTarget
          DHR.canonicalDHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt
    ; missingIdentityActionConstructor =
        DHR.missingIdentityEndomorphismActionConstructor
    ; missingIdentityActionConstructorIsExact =
        refl
    ; missingDASHILocalAlgebraSemantics =
        DHR.missingDASHILocalAlgebraForIdentityActionSemantics
    ; missingDASHILocalAlgebraSemanticsIsExact =
        refl
    ; unsuppliedForeignIdentityResidual =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; unsuppliedForeignIdentityResidualIsExplicitWitness =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; explicitSupplyBundleConstructed =
        true
    ; explicitSupplyBundleConstructedIsTrue =
        refl
    ; repoNativeGlobalForeignLaneIdentityBundleConstructed =
        false
    ; repoNativeGlobalForeignLaneIdentityBundleConstructedIsFalse =
        refl
    ; residualGlobalForeignLaneIdentityClosed =
        false
    ; residualGlobalForeignLaneIdentityClosedIsFalse =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; missingDASHILocalAlgebraConsumedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; upper6Residuals =
        upper6BlockedByMissingIdentityEndomorphismActionConstructor
        ∷ upper6BlockedByMissingDASHILocalAlgebraSemantics
        ∷ upper6BlockedByResidualGlobalForeignLaneIdentityRequiresExplicitWitness
        ∷ []
    ; downstreamBlockers =
        missingDASHILocalAlgebra
        ∷ blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; downstreamBlockersAreExact =
        refl
    ; upper6Boundary =
        "upper6 u6 receipt: globalForeignLaneIdentityBundle is constructed only from explicit DHRSuperselectionSectorLaneSupply"
        ∷ "arbitrarySectorIdentityEndomorphism remains fail-closed because EndomorphismAction is a postulated bare Set, not a datatype or record identity-field surface"
        ∷ "no local identity EndomorphismAction constructor is fabricated from the LocalisedEndomorphism.endomorphismAction projection"
        ∷ "missingDASHILocalAlgebra semantics are recorded and not consumed"
        ∷ "residualGlobalForeignLaneIdentityRequiresExplicitWitness is preserved as an open unsupplied residual, not closed"
        ∷ "No arbitrary DHR sectors, DR reconstruction, Standard Model match, or symmetric hexagon closure are fabricated"
        ∷ []
    }

record DHRSelectedPrimeLaneDoesNotCloseArbitrarySectorIdentityReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    selectedPrimeLaneReceipt :
      Bool

    upper6ArbitraryIdentityReceipt :
      Bool

    gaugeLocalAlgebraDependencyReceipt :
      Bool

    suppliedIdentityBundleConsumer :
      (ρ : DHR.LocalisedEndomorphism) →
      (supply : DHRSuperselectionSectorLaneSupply operator ρ) →
      DHRGlobalForeignLaneIdentityBundle operator ρ supply

    firstUnclosedResidual :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    firstUnclosedResidualIsExplicitWitness :
      firstUnclosedResidual
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    selectedWitnessPathAvailable :
      Bool

    selectedWitnessPathAvailableIsTrue :
      selectedWitnessPathAvailable ≡ true

    selectedWitnessPathGeneralisesToArbitrarySector :
      Bool

    selectedWitnessPathGeneralisesToArbitrarySectorIsFalse :
      selectedWitnessPathGeneralisesToArbitrarySector ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsFalse :
      missingDASHILocalAlgebraConsumed ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    downstreamBlockers :
      List DHRArbitrarySectorClassificationDownstreamBlocker

    downstreamBlockersAreExact :
      downstreamBlockers
      ≡
      (missingDASHILocalAlgebra
       ∷ blockedByMissingGate1GaugeRepresentationSemantics
       ∷ [])

    failClosedBoundary :
      List String

open DHRSelectedPrimeLaneDoesNotCloseArbitrarySectorIdentityReceipt public

canonicalDHRSelectedPrimeLaneDoesNotCloseArbitrarySectorIdentityReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRSelectedPrimeLaneDoesNotCloseArbitrarySectorIdentityReceipt operator
canonicalDHRSelectedPrimeLaneDoesNotCloseArbitrarySectorIdentityReceipt operator =
  record
    { selectedPrimeLaneReceipt =
        true
    ; upper6ArbitraryIdentityReceipt =
        true
    ; gaugeLocalAlgebraDependencyReceipt =
        false
    ; suppliedIdentityBundleConsumer =
        globalForeignLaneIdentityBundle operator
    ; firstUnclosedResidual =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; firstUnclosedResidualIsExplicitWitness =
        refl
    ; selectedWitnessPathAvailable =
        true
    ; selectedWitnessPathAvailableIsTrue =
        refl
    ; selectedWitnessPathGeneralisesToArbitrarySector =
        false
    ; selectedWitnessPathGeneralisesToArbitrarySectorIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; missingDASHILocalAlgebraConsumedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; downstreamBlockers =
        missingDASHILocalAlgebra
        ∷ blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; downstreamBlockersAreExact =
        refl
    ; failClosedBoundary =
        "Selected primitive lane identity witnesses close only the supplied DHRSuperselectionSectorLaneSupply path"
        ∷ "They do not close residualGlobalForeignLaneIdentityRequiresExplicitWitness for arbitrary unsupplied sectors"
        ∷ "The missing semantics are an arbitrary-sector DASHI local algebra, an identity EndomorphismAction constructor/law on that algebra, and sector-to-lane classification evidence"
        ∷ "DR reconstruction and G_DHR ~= G_SM remain blocked until tensor/dual/category laws and Gate1 exact representation semantics are supplied"
        ∷ []
    }

record DHRHexagonIdentityActionConstructorCurrentWaveReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    gaugeConstructorAudit :
      Bool

    upper6IdentityReceipt :
      Bool

    selectedPrimeLaneDoesNotGeneralise :
      Bool

    identityActionConstructorAttempted :
      Bool

    identityActionConstructorProvided :
      Bool

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    residualGlobalForeignLaneIdentityStillOpen :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    residualGlobalForeignLaneIdentityStillOpen-v :
      residualGlobalForeignLaneIdentityStillOpen
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    hexagonCoherencePromoted :
      Bool

    hexagonCoherencePromotedIsFalse :
      hexagonCoherencePromoted ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    currentWaveBoundary :
      List String

open DHRHexagonIdentityActionConstructorCurrentWaveReceipt public

canonicalDHRHexagonIdentityActionConstructorCurrentWaveReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRHexagonIdentityActionConstructorCurrentWaveReceipt operator
canonicalDHRHexagonIdentityActionConstructorCurrentWaveReceipt operator =
  record
    { gaugeConstructorAudit =
        false
    ; upper6IdentityReceipt =
        true
    ; selectedPrimeLaneDoesNotGeneralise =
        true
    ; identityActionConstructorAttempted =
        false
    ; identityActionConstructorProvided =
        false
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; residualGlobalForeignLaneIdentityStillOpen =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualGlobalForeignLaneIdentityStillOpen-v =
        refl
    ; hexagonCoherencePromoted =
        false
    ; hexagonCoherencePromotedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; currentWaveBoundary =
        "hexagon current-wave receipt consumes the gauge-side identity EndomorphismAction constructor audit"
        ∷ "the constructor was attempted but not provided because EndomorphismAction remains abstract"
        ∷ "selected supplied-lane identity bundles remain available but do not generalise to arbitrary unsupplied sectors"
        ∷ "residualGlobalForeignLaneIdentityRequiresExplicitWitness, hexagon coherence, DR reconstruction, and SM matching remain fail-closed"
        ∷ []
    }

record DHRHexagonEndomorphismActionReplacementInspectionReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    gaugeReplacementInspection :
      DHR.DHRUpper6EndomorphismActionReplacementInspectionReceipt

    currentWaveReceipt :
      DHRHexagonIdentityActionConstructorCurrentWaveReceipt operator

    replacementDecision :
      DHR.EndomorphismActionReplacementInspectionDecision

    replacementDecisionIsSemanticBreaking :
      replacementDecision
      ≡
      DHR.rejectDatatypeReplacementAsSemanticBreaking

    identityActionConstructorProvided :
      Bool

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    residualGlobalForeignLaneIdentityStillOpen :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    residualGlobalForeignLaneIdentityStillOpen-v :
      residualGlobalForeignLaneIdentityStillOpen
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    missingDASHILocalAlgebraConsumed :
      Bool

    hexagonCoherencePromoted :
      Bool

    hexagonCoherencePromotedIsFalse :
      hexagonCoherencePromoted ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    replacementInspectionBoundary :
      List String

open DHRHexagonEndomorphismActionReplacementInspectionReceipt public

canonicalDHRHexagonEndomorphismActionReplacementInspectionReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRHexagonEndomorphismActionReplacementInspectionReceipt operator
canonicalDHRHexagonEndomorphismActionReplacementInspectionReceipt operator =
  record
    { gaugeReplacementInspection =
        DHR.canonicalDHRUpper6EndomorphismActionReplacementInspectionReceipt
    ; currentWaveReceipt =
        canonicalDHRHexagonIdentityActionConstructorCurrentWaveReceipt operator
    ; replacementDecision =
        DHR.rejectDatatypeReplacementAsSemanticBreaking
    ; replacementDecisionIsSemanticBreaking =
        refl
    ; identityActionConstructorProvided =
        false
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; residualGlobalForeignLaneIdentityStillOpen =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualGlobalForeignLaneIdentityStillOpen-v =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; hexagonCoherencePromoted =
        false
    ; hexagonCoherencePromotedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; replacementInspectionBoundary =
        "hexagon replacement inspection consumes the gauge-side u6 decision that EndomorphismAction cannot be safely replaced by an identity-only datatype"
        ∷ "the required refactor is a semantic EndomorphismAction surface indexed by DASHI local-algebra actions with identity and composition laws"
        ∷ "residualGlobalForeignLaneIdentityRequiresExplicitWitness remains open; no arbitrary-sector identity endomorphism is constructed"
        ∷ "hexagon coherence, DR reconstruction, and Standard Model matching remain fail-closed"
        ∷ []
    }

record DHRHexagonDoplicherRobertsScopingCorrectionReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    gaugeDRScopingCorrection :
      DHR.DHRDoplicherRobertsScopingCorrectionReceipt

    replacementInspection :
      DHRHexagonEndomorphismActionReplacementInspectionReceipt operator

    literatureTheoremRecorded :
      DHR.DHRDoplicherRobertsScopingCorrectionReceipt.literatureTheoremRecorded
        gaugeDRScopingCorrection
      ≡
      true

    h1h5LocalEvidenceTermsSupplied :
      DHR.DHRDoplicherRobertsScopingCorrectionReceipt.h1h5LocalEvidenceTermsSupplied
        gaugeDRScopingCorrection
      ≡
      true

    missingLocalCategoricalEvidence :
      List DHR.DRLocalCategoricalEvidenceBlocker

    missingLocalCategoricalEvidenceIsCanonical :
      missingLocalCategoricalEvidence
      ≡
      DHR.canonicalDRLocalCategoricalEvidenceBlockers

    firstEvidenceBlocker :
      DHR.DHRIdentityEndomorphismWitnessBlocker

    firstEvidenceBlockerIsMissingDASHILocalAlgebraSemantics :
      firstEvidenceBlocker
      ≡
      DHR.missingDASHILocalAlgebraForIdentityActionSemantics

    residualGlobalForeignLaneIdentityStillOpen :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    residualGlobalForeignLaneIdentityStillOpen-v :
      residualGlobalForeignLaneIdentityStillOpen
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    hexagonCoherencePromoted :
      Bool

    hexagonCoherencePromotedIsFalse :
      hexagonCoherencePromoted ≡ false

    drReconstructionPromoted :
      Bool

    drReconstructionPromotedIsFalse :
      drReconstructionPromoted ≡ false

    standardModelMatchingPromoted :
      Bool

    standardModelMatchingPromotedIsFalse :
      standardModelMatchingPromoted ≡ false

    scopingCorrectionBoundary :
      List String

open DHRHexagonDoplicherRobertsScopingCorrectionReceipt public

canonicalDHRHexagonDoplicherRobertsScopingCorrectionReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRHexagonDoplicherRobertsScopingCorrectionReceipt operator
canonicalDHRHexagonDoplicherRobertsScopingCorrectionReceipt operator =
  record
    { gaugeDRScopingCorrection =
        DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; replacementInspection =
        canonicalDHRHexagonEndomorphismActionReplacementInspectionReceipt operator
    ; literatureTheoremRecorded =
        DHR.DHRDoplicherRobertsScopingCorrectionReceipt.literatureTheoremRecordedIsTrue
          DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; h1h5LocalEvidenceTermsSupplied =
        DHR.DHRDoplicherRobertsScopingCorrectionReceipt.h1h5LocalEvidenceTermsSuppliedIsFalse
          DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; missingLocalCategoricalEvidence =
        DHR.canonicalDRLocalCategoricalEvidenceBlockers
    ; missingLocalCategoricalEvidenceIsCanonical =
        refl
    ; firstEvidenceBlocker =
        DHR.missingDASHILocalAlgebraForIdentityActionSemantics
    ; firstEvidenceBlockerIsMissingDASHILocalAlgebraSemantics =
        refl
    ; residualGlobalForeignLaneIdentityStillOpen =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualGlobalForeignLaneIdentityStillOpen-v =
        refl
    ; hexagonCoherencePromoted =
        false
    ; hexagonCoherencePromotedIsFalse =
        refl
    ; drReconstructionPromoted =
        false
    ; drReconstructionPromotedIsFalse =
        refl
    ; standardModelMatchingPromoted =
        false
    ; standardModelMatchingPromotedIsFalse =
        refl
    ; scopingCorrectionBoundary =
        "hexagon DR scoping correction consumes the gauge-side receipt that separates Doplicher-Roberts literature authority from missing local H1-H5 categorical evidence"
        ∷ "the current H1-H5 package is not enough to run DR: localized transportable endomorphisms, tensor laws, conjugates/Frobenius, direct sums/subobjects, and braiding/hexagon evidence remain open"
        ∷ "residualGlobalForeignLaneIdentityRequiresExplicitWitness remains open because DASHI local-algebra identity-action semantics are not supplied"
        ∷ "No hexagon coherence, DR reconstruction, compact group, Standard Model matching, or arbitrary identity action is promoted"
        ∷ []
    }

record DHRHexagonIdentityActionSemanticAdapterHandoff
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    gaugeSemanticAdapterRequest :
      Bool

    gaugeSemanticAdapterAuditLedger :
      Bool

    replacementInspection :
      DHRHexagonEndomorphismActionReplacementInspectionReceipt operator

    residualGlobalForeignLaneIdentityStillOpen :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    residualGlobalForeignLaneIdentityStillOpen-v :
      residualGlobalForeignLaneIdentityStillOpen
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    localAlgebraResidual :
      AQFTColim.AQFTM4U6ResidualBlocker

    localAlgebraResidualIsMissingDASHILocalAlgebra :
      localAlgebraResidual
      ≡
      AQFTColim.missingDASHILocalAlgebra

    semanticDependencies :
      List DHR.DHRIdentityActionSemanticDependency

    semanticDependenciesAreCanonical :
      semanticDependencies
      ≡
      DHR.canonicalDHRIdentityActionSemanticDependencies

    missingEndomorphismActionDataFields :
      List DHR.EndomorphismActionDataMissingField

    missingEndomorphismActionDataFieldsAreCanonical :
      missingEndomorphismActionDataFields
      ≡
      DHR.canonicalEndomorphismActionDataMissingFields

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    hexagonCoherencePromoted :
      Bool

    hexagonCoherencePromotedIsFalse :
      hexagonCoherencePromoted ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    semanticAdapterHandoffBoundary :
      List String

open DHRHexagonIdentityActionSemanticAdapterHandoff public

canonicalDHRHexagonIdentityActionSemanticAdapterHandoff :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRHexagonIdentityActionSemanticAdapterHandoff operator
canonicalDHRHexagonIdentityActionSemanticAdapterHandoff operator =
  record
    { gaugeSemanticAdapterRequest =
        false
    ; gaugeSemanticAdapterAuditLedger =
        true
    ; replacementInspection =
        canonicalDHRHexagonEndomorphismActionReplacementInspectionReceipt operator
    ; residualGlobalForeignLaneIdentityStillOpen =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualGlobalForeignLaneIdentityStillOpen-v =
        refl
    ; localAlgebraResidual =
        AQFTColim.missingDASHILocalAlgebra
    ; localAlgebraResidualIsMissingDASHILocalAlgebra =
        refl
    ; semanticDependencies =
        DHR.canonicalDHRIdentityActionSemanticDependencies
    ; semanticDependenciesAreCanonical =
        refl
    ; missingEndomorphismActionDataFields =
        DHR.canonicalEndomorphismActionDataMissingFields
    ; missingEndomorphismActionDataFieldsAreCanonical =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; hexagonCoherencePromoted =
        false
    ; hexagonCoherencePromotedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; semanticAdapterHandoffBoundary =
        "hexagon handoff consumes the gauge-side identity-action semantic adapter request"
        ∷ "the EndomorphismActionData missing-field audit is carried with the handoff before unit/hexagon target sockets are used"
        ∷ "the exact constructor target is now visible downstream, but identity EndomorphismAction is still not constructed"
        ∷ "missingDASHILocalAlgebra and residualGlobalForeignLaneIdentityRequiresExplicitWitness remain the arbitrary-sector blockers"
        ∷ "No hexagon coherence, DR reconstruction, Standard Model matching, or arbitrary-sector identity promotion is produced"
        ∷ []
    }

record DHRHexagonAlgebraIndexedIdentityActionAdapterReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    gaugeAlgebraIndexedAdapterTarget :
      Bool

    semanticAdapterHandoff :
      Bool

    gaugeSemanticAdapterAuditLedger :
      Bool

    coherenceReceipt :
      DHRHexagonFailClosedCoherenceReceipt

    localAlgebraResidual :
      AQFTColim.AQFTM4U6ResidualBlocker

    localAlgebraResidualIsMissingDASHILocalAlgebra :
      localAlgebraResidual
      ≡
      AQFTColim.missingDASHILocalAlgebra

    semanticDependencies :
      List DHR.DHRIdentityActionSemanticDependency

    semanticDependenciesAreCanonical :
      semanticDependencies
      ≡
      DHR.canonicalDHRIdentityActionSemanticDependencies

    missingEndomorphismActionDataFields :
      List DHR.EndomorphismActionDataMissingField

    missingEndomorphismActionDataFieldsAreCanonical :
      missingEndomorphismActionDataFields
      ≡
      DHR.canonicalEndomorphismActionDataMissingFields

    unitCoherenceTargetReceipt :
      DHR.LocalisedEndomorphism →
      Set

    unitCoherenceTargetReceiptMatchesCoherenceSocket :
      Bool

    unitCoherenceTargetReceiptMatchesCoherenceSocket-v :
      unitCoherenceTargetReceiptMatchesCoherenceSocket ≡ true

    leftHexagonTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    leftHexagonTargetReceiptMatchesCoherenceSocket :
      Bool

    leftHexagonTargetReceiptMatchesCoherenceSocket-v :
      leftHexagonTargetReceiptMatchesCoherenceSocket ≡ true

    rightHexagonTargetReceipt :
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      DHR.LocalisedEndomorphism →
      Set

    rightHexagonTargetReceiptMatchesCoherenceSocket :
      Bool

    rightHexagonTargetReceiptMatchesCoherenceSocket-v :
      rightHexagonTargetReceiptMatchesCoherenceSocket ≡ true

    identityActionAdapterTargetThreaded :
      Bool

    identityActionAdapterTargetThreadedIsTrue :
      identityActionAdapterTargetThreaded ≡ true

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    unitCoherenceClosed :
      Bool

    unitCoherenceClosedIsFalse :
      unitCoherenceClosed ≡ false

    symmetricHexagonClosed :
      Bool

    symmetricHexagonClosedIsFalse :
      symmetricHexagonClosed ≡ false

    doplicherRobertsConsumed :
      Bool

    doplicherRobertsConsumedIsFalse :
      doplicherRobertsConsumed ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    algebraIndexedHexagonBoundary :
      List String

open DHRHexagonAlgebraIndexedIdentityActionAdapterReceipt public

canonicalDHRHexagonAlgebraIndexedIdentityActionAdapterReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRHexagonAlgebraIndexedIdentityActionAdapterReceipt operator
canonicalDHRHexagonAlgebraIndexedIdentityActionAdapterReceipt operator =
  record
    { gaugeAlgebraIndexedAdapterTarget =
        true
    ; semanticAdapterHandoff =
        true
    ; gaugeSemanticAdapterAuditLedger =
        true
    ; coherenceReceipt =
        canonicalDHRHexagonFailClosedCoherenceReceipt
    ; localAlgebraResidual =
        AQFTColim.missingDASHILocalAlgebra
    ; localAlgebraResidualIsMissingDASHILocalAlgebra =
        refl
    ; semanticDependencies =
        DHR.canonicalDHRIdentityActionSemanticDependencies
    ; semanticDependenciesAreCanonical =
        refl
    ; missingEndomorphismActionDataFields =
        DHR.canonicalEndomorphismActionDataMissingFields
    ; missingEndomorphismActionDataFieldsAreCanonical =
        refl
    ; unitCoherenceTargetReceipt =
        DHRHexagonFailClosedCoherenceReceipt.unitCoherenceTargetReceipt
          canonicalDHRHexagonFailClosedCoherenceReceipt
    ; unitCoherenceTargetReceiptMatchesCoherenceSocket =
        true
    ; unitCoherenceTargetReceiptMatchesCoherenceSocket-v =
        refl
    ; leftHexagonTargetReceipt =
        DHRHexagonFailClosedCoherenceReceipt.leftHexagonTargetReceipt
          canonicalDHRHexagonFailClosedCoherenceReceipt
    ; leftHexagonTargetReceiptMatchesCoherenceSocket =
        true
    ; leftHexagonTargetReceiptMatchesCoherenceSocket-v =
        refl
    ; rightHexagonTargetReceipt =
        DHRHexagonFailClosedCoherenceReceipt.rightHexagonTargetReceipt
          canonicalDHRHexagonFailClosedCoherenceReceipt
    ; rightHexagonTargetReceiptMatchesCoherenceSocket =
        true
    ; rightHexagonTargetReceiptMatchesCoherenceSocket-v =
        refl
    ; identityActionAdapterTargetThreaded =
        true
    ; identityActionAdapterTargetThreadedIsTrue =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; unitCoherenceClosed =
        false
    ; unitCoherenceClosedIsFalse =
        refl
    ; symmetricHexagonClosed =
        false
    ; symmetricHexagonClosedIsFalse =
        refl
    ; doplicherRobertsConsumed =
        false
    ; doplicherRobertsConsumedIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; algebraIndexedHexagonBoundary =
        "hexagon receipt threads the gauge algebra-indexed identity-action adapter target into unit and left/right hexagon target sockets"
        ∷ "the u6 EndomorphismActionData missing-field audit is preserved as a precondition for any future coherence closure"
        ∷ "AQFTColim.missingDASHILocalAlgebra is preserved as the exact local-algebra residual"
        ∷ "identity-action constructor and arbitrary-sector identity endomorphism remain unconstructed"
        ∷ "unit coherence and symmetric hexagon are target receipts only, not closed laws"
        ∷ "No Doplicher-Roberts consumption, gauge reconstruction, or Standard Model matching is asserted"
        ∷ []
    }

record DHRHexagonConcreteLocalAlgebraIdentityActionAdapterReceipt
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω₁ where
  field
    algebraIndexedHexagonReceipt :
      DHRHexagonAlgebraIndexedIdentityActionAdapterReceipt operator

    gaugeConcreteLocalAlgebraIdentityAdapter :
      Bool

    concreteLocalCarrier :
      AQFT.Region →
      Set

    concreteLocalCarrierMatchesGaugeAdapter :
      concreteLocalCarrier
      ≡
      AQFTColim.DASHILocalAlgebraNet.net
        AQFTColim.dASHILocalAlgebraNet

    concreteLocalCarrierMatchesDASHILocalNet :
      (region : AQFT.Region) →
      concreteLocalCarrier region
      ≡
      AQFTColim.DASHILocalAlgebraNet.net
        AQFTColim.dASHILocalAlgebraNet
        region

    concreteLocalCarrierMatchesAbstractCompletion :
      (region : AQFT.Region) →
      concreteLocalCarrier region
      ≡
      AQFTColim.abstractQuotientCStarCompletion
        region

    completionEmbedThreaded :
      {region : AQFT.Region} →
      AQFTColim.abstractPromotedReceiptQuotient region →
      concreteLocalCarrier region

    identityActionLawTargetForConcreteElement :
      (sector : DHR.SuperselectionSector) →
      (region : AQFT.Region) →
      AQFTColim.DASHILocalAlgebraNet.net
        AQFTColim.dASHILocalAlgebraNet
        region →
      DHR.EndomorphismAction →
      Set

    identityActionLawTargetForConcreteElementThreaded :
      Bool

    preparedArbitrarySectorIdActionTarget :
      DHR.SuperselectionSector →
      Setω

    preparedArbitrarySectorIdActionTargetThreaded :
      Bool

    concreteLocalAlgebraElementIndexingPrepared :
      Bool

    concreteLocalAlgebraElementIndexingPreparedIsTrue :
      concreteLocalAlgebraElementIndexingPrepared ≡ true

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    arbitrarySectorIdConstructed :
      Bool

    arbitrarySectorIdConstructedIsFalse :
      arbitrarySectorIdConstructed ≡ false

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsTrue :
      missingDASHILocalAlgebraConsumed ≡ true

    residualGlobalForeignLaneIdentityStillOpen :
      DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    residualGlobalForeignLaneIdentityStillOpen-v :
      residualGlobalForeignLaneIdentityStillOpen
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    hexagonCoherencePromoted :
      Bool

    hexagonCoherencePromotedIsFalse :
      hexagonCoherencePromoted ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    concreteLocalAlgebraHexagonBoundary :
      List String

open DHRHexagonConcreteLocalAlgebraIdentityActionAdapterReceipt public

canonicalDHRHexagonConcreteLocalAlgebraIdentityActionAdapterReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  DHRHexagonConcreteLocalAlgebraIdentityActionAdapterReceipt operator
canonicalDHRHexagonConcreteLocalAlgebraIdentityActionAdapterReceipt operator =
  record
    { algebraIndexedHexagonReceipt =
        canonicalDHRHexagonAlgebraIndexedIdentityActionAdapterReceipt operator
    ; gaugeConcreteLocalAlgebraIdentityAdapter =
        true
    ; concreteLocalCarrier =
        DHR.DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.dashiLocalQuotientCarrier
          DHR.canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; concreteLocalCarrierMatchesGaugeAdapter =
        refl
    ; concreteLocalCarrierMatchesDASHILocalNet =
        DHR.DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.dashiLocalQuotientCarrierMatchesDASHILocalNet
          DHR.canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; concreteLocalCarrierMatchesAbstractCompletion =
        DHR.DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.dashiLocalQuotientCarrierMatchesAbstractCompletion
          DHR.canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; completionEmbedThreaded =
        DHR.DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.dashiLocalCompletionEmbed
          DHR.canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; identityActionLawTargetForConcreteElement =
        λ _ _ _ _ → Bool
    ; identityActionLawTargetForConcreteElementThreaded =
        true
    ; preparedArbitrarySectorIdActionTarget =
        DHR.DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.preparedArbitrarySectorIdActionTarget
          DHR.canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; preparedArbitrarySectorIdActionTargetThreaded =
        true
    ; concreteLocalAlgebraElementIndexingPrepared =
        true
    ; concreteLocalAlgebraElementIndexingPreparedIsTrue =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdConstructed =
        false
    ; arbitrarySectorIdConstructedIsFalse =
        refl
    ; missingDASHILocalAlgebraConsumed =
        DHR.DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.missingDASHILocalAlgebraConsumed
          DHR.canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; missingDASHILocalAlgebraConsumedIsTrue =
        DHR.DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.missingDASHILocalAlgebraConsumedIsTrue
          DHR.canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; residualGlobalForeignLaneIdentityStillOpen =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualGlobalForeignLaneIdentityStillOpen-v =
        refl
    ; hexagonCoherencePromoted =
        false
    ; hexagonCoherencePromotedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; concreteLocalAlgebraHexagonBoundary =
        "hexagon receipt threads the u6 identity-action adapter over AQFTColim.dASHILocalAlgebraNet into the coherence surface"
        ∷ "the identity law target is indexed by completed local algebra elements, with pre-completion quotient elements entering by completionEmbed"
        ∷ "the local algebra dependency is consumed here; residualGlobalForeignLaneIdentityRequiresExplicitWitness remains the unclosed arbitrary-sector identity witness"
        ∷ "no EndomorphismAction constructor, arbitrarySectorId, hexagon coherence, DR reconstruction, or Standard Model match is promoted"
        ∷ []
    }

record DHRHexagonExistingEndomorphismActionAdapterConsumptionReceipt
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism) :
  Setω₁ where
  field
    concreteLocalAlgebraHexagonAdapter :
      DHRHexagonConcreteLocalAlgebraIdentityActionAdapterReceipt operator

    gaugeExistingActionAdapter :
      DHR.DHRExistingEndomorphismActionDASHILocalNetAdapterReceipt ρ

    projectedEndomorphismAction :
      Bool

    projectedEndomorphismActionMatchesGaugeAdapter :
      Bool

    projectedEndomorphismActionMatchesLocalisedField :
      Bool

    dashiLocalNet :
      AQFT.Region →
      Set

    dashiLocalNetMatchesGaugeAdapter :
      dashiLocalNet
      ≡
      DHR.DHRExistingEndomorphismActionDASHILocalNetAdapterReceipt.dashiLocalNet
        gaugeExistingActionAdapter

    dashiLocalNetMatchesCanonicalNet :
      Bool

    completedElementIdentityReceipt :
      (region : AQFT.Region) →
      dashiLocalNet region →
      Set

    completedElementIdentityReceiptInhabited :
      (region : AQFT.Region) →
      (element : dashiLocalNet region) →
      completedElementIdentityReceipt region element

    existingActionAdapterConsumed :
      Bool

    existingActionAdapterConsumedIsTrue :
      existingActionAdapterConsumed ≡ true

    identityEndomorphismActionConstructorProvided :
      Bool

    identityEndomorphismActionConstructorProvidedIsFalse :
      identityEndomorphismActionConstructorProvided ≡ false

    hexagonCoherencePromoted :
      Bool

    hexagonCoherencePromotedIsFalse :
      hexagonCoherencePromoted ≡ false

    doplicherRobertsConsumed :
      Bool

    doplicherRobertsConsumedIsFalse :
      doplicherRobertsConsumed ≡ false

    existingActionHexagonBoundary :
      List String

open DHRHexagonExistingEndomorphismActionAdapterConsumptionReceipt public

canonicalDHRHexagonExistingEndomorphismActionAdapterConsumptionReceipt :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  DHRHexagonExistingEndomorphismActionAdapterConsumptionReceipt operator ρ
canonicalDHRHexagonExistingEndomorphismActionAdapterConsumptionReceipt operator ρ =
  record
    { concreteLocalAlgebraHexagonAdapter =
        canonicalDHRHexagonConcreteLocalAlgebraIdentityActionAdapterReceipt operator
    ; gaugeExistingActionAdapter =
        DHR.canonicalDHRExistingEndomorphismActionDASHILocalNetAdapterReceipt ρ
    ; projectedEndomorphismAction =
        true
    ; projectedEndomorphismActionMatchesGaugeAdapter =
        true
    ; projectedEndomorphismActionMatchesLocalisedField =
        true
    ; dashiLocalNet =
        DHR.DHRExistingEndomorphismActionDASHILocalNetAdapterReceipt.dashiLocalNet
          (DHR.canonicalDHRExistingEndomorphismActionDASHILocalNetAdapterReceipt ρ)
    ; dashiLocalNetMatchesGaugeAdapter =
        refl
    ; dashiLocalNetMatchesCanonicalNet =
        DHR.DHRExistingEndomorphismActionDASHILocalNetAdapterReceipt.dashiLocalNetMatchesCanonicalNet
          (DHR.canonicalDHRExistingEndomorphismActionDASHILocalNetAdapterReceipt ρ)
    ; completedElementIdentityReceipt =
        DHR.DHRExistingEndomorphismActionDASHILocalNetAdapterReceipt.completedElementIdentityReceipt
          (DHR.canonicalDHRExistingEndomorphismActionDASHILocalNetAdapterReceipt ρ)
    ; completedElementIdentityReceiptInhabited =
        DHR.DHRExistingEndomorphismActionDASHILocalNetAdapterReceipt.completedElementIdentityReceiptInhabited
          (DHR.canonicalDHRExistingEndomorphismActionDASHILocalNetAdapterReceipt ρ)
    ; existingActionAdapterConsumed =
        true
    ; existingActionAdapterConsumedIsTrue =
        refl
    ; identityEndomorphismActionConstructorProvided =
        false
    ; identityEndomorphismActionConstructorProvidedIsFalse =
        refl
    ; hexagonCoherencePromoted =
        false
    ; hexagonCoherencePromotedIsFalse =
        refl
    ; doplicherRobertsConsumed =
        false
    ; doplicherRobertsConsumedIsFalse =
        refl
    ; existingActionHexagonBoundary =
        "hexagon consumes the gauge-side non-postulated adapter for an already supplied LocalisedEndomorphism"
        ∷ "the projected EndomorphismAction is exactly LocalisedEndomorphism.endomorphismAction, so existing action APIs can receive it"
        ∷ "the local carrier is AQFTColim.dASHILocalAlgebraNet and only reflexive completed-element receipts are threaded"
        ∷ "no identity EndomorphismAction constructor, hexagon law, DR reconstruction, or gauge assignment is promoted"
        ∷ []
    }
