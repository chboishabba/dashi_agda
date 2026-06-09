module DASHI.Biology.ProteinHormoneChemistryCellBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.CellDifferentiationCommunicationBridge as Cell
import DASHI.Interop.ObservationTransportSpine as Spine
import DASHI.Physics.Closure.ChemistryRightLimitsGateTheorem as Chem

------------------------------------------------------------------------
-- Protein / hormone / chemistry / cell bridge.
--
-- This is a theorem-thin observation bridge between the current
-- chemistry-right-limits gate and the bounded cell communication physiology
-- bridge.  It only records receipt-gated observation of protein/hormone
-- candidates at a cell-communication boundary.  It does not promote protein
-- folding, disease causation, cell-fate prediction, hormone-to-behaviour
-- closure, or completed chemistry-to-biology derivation.

data Never : Set where

data ProteinHormoneChemistryCellLane : Set where
  chemistryRightLimitReceiptLane :
    ProteinHormoneChemistryCellLane

  proteinCandidateObservationLane :
    ProteinHormoneChemistryCellLane

  hormoneCandidateObservationLane :
    ProteinHormoneChemistryCellLane

  receptorCellCommunicationLane :
    ProteinHormoneChemistryCellLane

  boundedCellPhysiologyReceiptLane :
    ProteinHormoneChemistryCellLane

data ProteinHormoneChemistryCellGuard : Set where
  NoDiseaseCausationClaim :
    ProteinHormoneChemistryCellGuard

  NoFullProteinFoldingClaim :
    ProteinHormoneChemistryCellGuard

  NoFullCellFatePredictionClaim :
    ProteinHormoneChemistryCellGuard

  NoHormoneToBehaviourClosureClaim :
    ProteinHormoneChemistryCellGuard

  NoChemistryToBiologyClosureClaim :
    ProteinHormoneChemistryCellGuard

  NoReceiptlessPromotionClaim :
    ProteinHormoneChemistryCellGuard

data ProteinHormoneChemistryCellRoute : Set where
  boundedProteinHormoneCellObservationRoute :
    ProteinHormoneChemistryCellRoute

  diseaseCausationRoute :
    ProteinHormoneChemistryCellRoute

  fullProteinFoldingRoute :
    ProteinHormoneChemistryCellRoute

  cellFatePredictionRoute :
    ProteinHormoneChemistryCellRoute

  hormoneToBehaviourClosureRoute :
    ProteinHormoneChemistryCellRoute

  chemistryToBiologyClosureRoute :
    ProteinHormoneChemistryCellRoute

AdmissibleProteinHormoneChemistryCellRoute :
  ProteinHormoneChemistryCellRoute -> Set
AdmissibleProteinHormoneChemistryCellRoute
  boundedProteinHormoneCellObservationRoute = ⊤
AdmissibleProteinHormoneChemistryCellRoute diseaseCausationRoute = Never
AdmissibleProteinHormoneChemistryCellRoute fullProteinFoldingRoute = Never
AdmissibleProteinHormoneChemistryCellRoute cellFatePredictionRoute = Never
AdmissibleProteinHormoneChemistryCellRoute hormoneToBehaviourClosureRoute =
  Never
AdmissibleProteinHormoneChemistryCellRoute chemistryToBiologyClosureRoute =
  Never

diseaseCausationRejected :
  AdmissibleProteinHormoneChemistryCellRoute diseaseCausationRoute -> Never
diseaseCausationRejected impossible = impossible

fullProteinFoldingRejected :
  AdmissibleProteinHormoneChemistryCellRoute fullProteinFoldingRoute -> Never
fullProteinFoldingRejected impossible = impossible

cellFatePredictionRejected :
  AdmissibleProteinHormoneChemistryCellRoute cellFatePredictionRoute -> Never
cellFatePredictionRejected impossible = impossible

hormoneToBehaviourClosureRejected :
  AdmissibleProteinHormoneChemistryCellRoute
    hormoneToBehaviourClosureRoute ->
  Never
hormoneToBehaviourClosureRejected impossible = impossible

chemistryToBiologyClosureRejected :
  AdmissibleProteinHormoneChemistryCellRoute
    chemistryToBiologyClosureRoute ->
  Never
chemistryToBiologyClosureRejected impossible = impossible

canonicalProteinHormoneChemistryCellLanes :
  List ProteinHormoneChemistryCellLane
canonicalProteinHormoneChemistryCellLanes =
  chemistryRightLimitReceiptLane
  ∷ proteinCandidateObservationLane
  ∷ hormoneCandidateObservationLane
  ∷ receptorCellCommunicationLane
  ∷ boundedCellPhysiologyReceiptLane
  ∷ []

canonicalProteinHormoneChemistryCellGuards :
  List ProteinHormoneChemistryCellGuard
canonicalProteinHormoneChemistryCellGuards =
  NoDiseaseCausationClaim
  ∷ NoFullProteinFoldingClaim
  ∷ NoFullCellFatePredictionClaim
  ∷ NoHormoneToBehaviourClosureClaim
  ∷ NoChemistryToBiologyClosureClaim
  ∷ NoReceiptlessPromotionClaim
  ∷ []

canonicalProteinHormoneSpineNonClaims :
  List Spine.NonClaimBoundary
canonicalProteinHormoneSpineNonClaims =
  Spine.quotientIsNotInjective
  ∷ Spine.correlationIsNotCausation
  ∷ Spine.localReceiptIsNotGlobalOntology
  ∷ []

record ProteinHormoneChemistryCellBridge : Setω where
  field
    chemistryGate :
      Chem.ChemistryRightLimitsGateTheorem

    cellBridge :
      Cell.CellDifferentiationCommunicationBridge

    cellObservation :
      Cell.PhysiologyObservation cellBridge

    cellCandidate :
      Cell.CandidateIntegratedPhysiologyState
        cellBridge
        cellObservation

    cellReceipt :
      Cell.PhysiologyPromotionReceipt
        cellBridge
        cellObservation
        cellCandidate

    ProteinCandidate :
      Set

    HormoneCandidate :
      Set

    ReceptorContext :
      Set

    ChemistryCellObservation :
      Set

    ProteinHormoneCandidate :
      Set

    BridgeReceipt :
      Set

    observeProteinHormoneCell :
      ProteinCandidate ->
      HormoneCandidate ->
      ReceptorContext ->
      ChemistryCellObservation

    candidateProteinHormoneCell :
      ChemistryCellObservation ->
      ProteinHormoneCandidate

    bridgeReceipt :
      ChemistryCellObservation ->
      ProteinHormoneCandidate ->
      BridgeReceipt

    receiptGate :
      ChemistryCellObservation ->
      ProteinHormoneCandidate ->
      BridgeReceipt ->
      Set

    lanes :
      List ProteinHormoneChemistryCellLane

    lanesAreCanonical :
      lanes ≡ canonicalProteinHormoneChemistryCellLanes

    guards :
      List ProteinHormoneChemistryCellGuard

    guardsAreCanonical :
      guards ≡ canonicalProteinHormoneChemistryCellGuards

    spineSurface :
      Spine.ObservationTransportSurface

    spineDomainIsProteinHormone :
      Spine.ObservationTransportSurface.domain spineSurface
      ≡
      Spine.proteinHormoneChemistryCellDomain

    route :
      ProteinHormoneChemistryCellRoute

    routeIsBoundedObservation :
      route ≡ boundedProteinHormoneCellObservationRoute

    routeAdmissible :
      AdmissibleProteinHormoneChemistryCellRoute route

    diseaseCausationPromoted :
      Bool

    diseaseCausationPromotedIsFalse :
      diseaseCausationPromoted ≡ false

    fullProteinFoldingPromoted :
      Bool

    fullProteinFoldingPromotedIsFalse :
      fullProteinFoldingPromoted ≡ false

    cellFatePredictionPromoted :
      Bool

    cellFatePredictionPromotedIsFalse :
      cellFatePredictionPromoted ≡ false

    hormoneBehaviourClosurePromoted :
      Bool

    hormoneBehaviourClosurePromotedIsFalse :
      hormoneBehaviourClosurePromoted ≡ false

    chemistryBiologyClosurePromoted :
      Bool

    chemistryBiologyClosurePromotedIsFalse :
      chemistryBiologyClosurePromoted ≡ false

    bridgeReading :
      String

open ProteinHormoneChemistryCellBridge public

record ProteinHormoneChemistryCellNonPromotionCertificate
    (bridge : ProteinHormoneChemistryCellBridge) : Set where
  field
    guards :
      List ProteinHormoneChemistryCellGuard

    guardsMatch :
      guards ≡ ProteinHormoneChemistryCellBridge.guards bridge

    boundedObservationOnly :
      Bool

    boundedObservationOnlyIsTrue :
      boundedObservationOnly ≡ true

    noDiseaseCausation :
      Bool

    noDiseaseCausationIsTrue :
      noDiseaseCausation ≡ true

    noFullProteinFolding :
      Bool

    noFullProteinFoldingIsTrue :
      noFullProteinFolding ≡ true

    noCellFatePrediction :
      Bool

    noCellFatePredictionIsTrue :
      noCellFatePrediction ≡ true

    noHormoneToBehaviourClosure :
      Bool

    noHormoneToBehaviourClosureIsTrue :
      noHormoneToBehaviourClosure ≡ true

    noChemistryToBiologyClosure :
      Bool

    noChemistryToBiologyClosureIsTrue :
      noChemistryToBiologyClosure ≡ true

    certificateReading :
      String

open ProteinHormoneChemistryCellNonPromotionCertificate public

canonicalProteinHormoneChemistryCellSpineSurface :
  Spine.ObservationTransportSurface
canonicalProteinHormoneChemistryCellSpineSurface =
  record
    { domain =
        Spine.proteinHormoneChemistryCellDomain
    ; LatentCarrier =
        ⊤
    ; ObservationQuotient =
        ⊤
    ; AdmissibilityGate =
        ⊤
    ; TransportOperator =
        ⊤
    ; Artifact =
        ⊤
    ; observe =
        λ _ -> tt
    ; gate =
        λ _ -> tt
    ; transport =
        λ _ _ _ -> tt
    ; promotionBoundary =
        Spine.nonPromotingObservation
    ; nonClaims =
        canonicalProteinHormoneSpineNonClaims
    ; plainReading =
        "Protein and hormone chemistry-cell observations are quotient, receipt-gated candidates only."
    }

canonicalProteinHormoneChemistryCellBridge :
  ProteinHormoneChemistryCellBridge
canonicalProteinHormoneChemistryCellBridge =
  record
    { chemistryGate =
        Chem.canonicalChemistryRightLimitsGateTheorem
    ; cellBridge =
        Cell.canonicalCellDifferentiationCommunicationBridge
    ; cellObservation =
        Cell.canonicalPhysiologyObservation
    ; cellCandidate =
        Cell.canonicalCandidateIntegratedPhysiologyState
    ; cellReceipt =
        Cell.canonicalPhysiologyPromotionReceipt
    ; ProteinCandidate =
        ⊤
    ; HormoneCandidate =
        ⊤
    ; ReceptorContext =
        ⊤
    ; ChemistryCellObservation =
        ⊤
    ; ProteinHormoneCandidate =
        ⊤
    ; BridgeReceipt =
        ⊤
    ; observeProteinHormoneCell =
        λ _ _ _ -> tt
    ; candidateProteinHormoneCell =
        λ _ -> tt
    ; bridgeReceipt =
        λ _ _ -> tt
    ; receiptGate =
        λ _ _ _ -> ⊤
    ; lanes =
        canonicalProteinHormoneChemistryCellLanes
    ; lanesAreCanonical =
        refl
    ; guards =
        canonicalProteinHormoneChemistryCellGuards
    ; guardsAreCanonical =
        refl
    ; spineSurface =
        canonicalProteinHormoneChemistryCellSpineSurface
    ; spineDomainIsProteinHormone =
        refl
    ; route =
        boundedProteinHormoneCellObservationRoute
    ; routeIsBoundedObservation =
        refl
    ; routeAdmissible =
        tt
    ; diseaseCausationPromoted =
        false
    ; diseaseCausationPromotedIsFalse =
        refl
    ; fullProteinFoldingPromoted =
        false
    ; fullProteinFoldingPromotedIsFalse =
        refl
    ; cellFatePredictionPromoted =
        false
    ; cellFatePredictionPromotedIsFalse =
        refl
    ; hormoneBehaviourClosurePromoted =
        false
    ; hormoneBehaviourClosurePromotedIsFalse =
        refl
    ; chemistryBiologyClosurePromoted =
        false
    ; chemistryBiologyClosurePromotedIsFalse =
        refl
    ; bridgeReading =
        "The protein/hormone chemistry-cell bridge links chemistry right-limits and cell communication as bounded observations with receipts only."
    }

canonicalProteinHormoneChemistryCellNonPromotionCertificate :
  ProteinHormoneChemistryCellNonPromotionCertificate
    canonicalProteinHormoneChemistryCellBridge
canonicalProteinHormoneChemistryCellNonPromotionCertificate =
  record
    { guards =
        canonicalProteinHormoneChemistryCellGuards
    ; guardsMatch =
        refl
    ; boundedObservationOnly =
        true
    ; boundedObservationOnlyIsTrue =
        refl
    ; noDiseaseCausation =
        true
    ; noDiseaseCausationIsTrue =
        refl
    ; noFullProteinFolding =
        true
    ; noFullProteinFoldingIsTrue =
        refl
    ; noCellFatePrediction =
        true
    ; noCellFatePredictionIsTrue =
        refl
    ; noHormoneToBehaviourClosure =
        true
    ; noHormoneToBehaviourClosureIsTrue =
        refl
    ; noChemistryToBiologyClosure =
        true
    ; noChemistryToBiologyClosureIsTrue =
        refl
    ; certificateReading =
        "The canonical protein/hormone bridge is non-promoting: no disease, folding, cell-fate, hormone-behaviour, or chemistry-biology closure claim is admitted."
    }
