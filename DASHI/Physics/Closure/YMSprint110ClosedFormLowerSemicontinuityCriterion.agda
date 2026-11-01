module DASHI.Physics.Closure.YMSprint110ClosedFormLowerSemicontinuityCriterion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSprint109MoscoLiminfLowerSemicontinuity
  as Liminf109
import DASHI.Physics.Closure.YMSprint109MoscoRecoverySequence
  as Recovery109
import DASHI.Physics.Closure.YMSprint109MoscoSpectralLiminfAssembly
  as Assembly109

------------------------------------------------------------------------
-- Sprint 110 closed-form lower-semicontinuity criterion.
--
-- Sprint109 isolated the Mosco liminf, recovery, and spectral-liminf lanes.
-- This module advances the closed semibounded quadratic-form lane by naming
-- the exact criterion that would close the lower-semicontinuity side:
--
--   * the continuum physical Hilbert carrier and form domain are identified,
--   * the finite transfer forms are compared with one renormalized domain
--     identification,
--   * the continuum form is closed and semibounded with a common lower bound,
--   * weak bounded-energy sequences preserve the physical gauge sector, and
--   * the liminf inequality is proved on that identified sector.
--
-- The receipt is concrete and fail-closed: it records the criterion and its
-- Sprint109 dependencies, but it does not assert that the analytic inputs are
-- already discharged and it does not promote Yang-Mills.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

criterionReceiptRecorded : Bool
criterionReceiptRecorded = true

closedFormCriterionClosedHere : Bool
closedFormCriterionClosedHere = false

domainIdentificationClosedHere : Bool
domainIdentificationClosedHere = false

closednessSemiboundednessClosedHere : Bool
closednessSemiboundednessClosedHere = false

liminfInequalityClosedHere : Bool
liminfInequalityClosedHere = false

gaugeSectorPreservationClosedHere : Bool
gaugeSectorPreservationClosedHere = false

sprint109LiminfImported : Bool
sprint109LiminfImported = true

sprint109RecoveryImported : Bool
sprint109RecoveryImported = true

sprint109AssemblyImported : Bool
sprint109AssemblyImported = true

sprint109ClosedFormLowerSemicontinuityClosed : Bool
sprint109ClosedFormLowerSemicontinuityClosed =
  Liminf109.moscoLowerSemicontinuityProvedHereFlag
    Liminf109.canonicalReceipt

sprint109TransferPathClosed : Bool
sprint109TransferPathClosed =
  Liminf109.transferLiminfLowerBoundPathClosedHereFlag
    Liminf109.canonicalReceipt

sprint109RecoverySideClosed : Bool
sprint109RecoverySideClosed =
  Recovery109.TheoremAndPromotionBoundary.moscoConvergenceProvedHereStatus
    (Recovery109.theoremAndPromotionBoundary Recovery109.canonicalReceipt)

sprint109AssemblyTheoremClosed : Bool
sprint109AssemblyTheoremClosed =
  Assembly109.moscoSpectralLiminfTheoremProvedHereFlag
    Assembly109.canonicalReceipt

targetFormulaText : String
targetFormulaText =
  "gap(T(a)) >= c_transfer * m_eff(a) * a"

criterionStatementText : String
criterionStatementText =
  "Closed semibounded quadratic-form lower semicontinuity closes exactly when every weakly convergent bounded-energy finite-transfer sequence in the identified physical gauge sector satisfies q(u) <= liminf_a q_a(u_a)."

domainIdentificationText : String
domainIdentificationText =
  "Identify the common continuum Hilbert carrier H, the physical gauge-sector subspace H_phys, the closed form domain D(q), and comparison maps from finite transfer domains into H_phys."

formDomainEqualityText : String
formDomainEqualityText =
  "The criterion requires D(q) to be exactly the closure of the gauge-compatible finite lattice core in the graph norm of q, not merely a named ambient target."

closednessSemiboundednessText : String
closednessSemiboundednessText =
  "The continuum form q must be closed and semibounded, and the renormalized finite transfer forms q_a must share a lower bound compatible with the Sprint109 transfer constants."

liminfInequalityText : String
liminfInequalityText =
  "For every admissible sequence u_a weakly converging to u with sup_a q_a(u_a) finite after renormalization, require u in D(q) and q(u) <= liminf_a q_a(u_a)."

gaugeSectorPreservationText : String
gaugeSectorPreservationText =
  "Gauge constraints, physical projection, quotient identification, and non-vacuum sector labels must survive weak limits and recovery/domain comparison maps."

analyticClosureConditionText : String
analyticClosureConditionText =
  "The criterion closes only after domain identification, common lower bound, closedness, weak compactness, gauge-sector preservation, and the liminf inequality are all proved in one carrier."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint110 records the closed-form lower-semicontinuity criterion only; Mosco convergence, spectral liminf, continuum gap transport, and Clay Yang-Mills promotion remain false."

sprint109LiminfPath : String
sprint109LiminfPath =
  "DASHI/Physics/Closure/YMSprint109MoscoLiminfLowerSemicontinuity.agda"

sprint109RecoveryPath : String
sprint109RecoveryPath =
  "DASHI/Physics/Closure/YMSprint109MoscoRecoverySequence.agda"

sprint109AssemblyPath : String
sprint109AssemblyPath =
  "DASHI/Physics/Closure/YMSprint109MoscoSpectralLiminfAssembly.agda"

data CriterionLane : Set where
  form-domain-identification-lane :
    CriterionLane
  closedness-semiboundedness-lane :
    CriterionLane
  weak-compactness-lane :
    CriterionLane
  liminf-inequality-lane :
    CriterionLane
  gauge-sector-preservation-lane :
    CriterionLane
  sprint109-consumption-lane :
    CriterionLane
  promotion-boundary-lane :
    CriterionLane

canonicalCriterionLanes : List CriterionLane
canonicalCriterionLanes =
  form-domain-identification-lane
  ∷ closedness-semiboundedness-lane
  ∷ weak-compactness-lane
  ∷ liminf-inequality-lane
  ∷ gauge-sector-preservation-lane
  ∷ sprint109-consumption-lane
  ∷ promotion-boundary-lane
  ∷ []

data CriterionStatus : Set where
  recorded-required :
    CriterionStatus
  imported-sprint109-support :
    CriterionStatus
  identified-not-proved :
    CriterionStatus
  closedness-required :
    CriterionStatus
  semiboundedness-required :
    CriterionStatus
  liminf-required :
    CriterionStatus
  gauge-preservation-required :
    CriterionStatus
  exact-closure-conditions-recorded :
    CriterionStatus
  theorem-open :
    CriterionStatus
  nonpromotion-boundary :
    CriterionStatus

record Sprint109CriterionSupply : Setω where
  constructor mkSprint109CriterionSupply
  field
    liminfReceipt :
      Liminf109.YMSprint109MoscoLiminfLowerSemicontinuityReceipt
    recoveryReceipt :
      Recovery109.YMSprint109MoscoRecoverySequenceReceipt
    assemblyReceipt :
      Assembly109.YMSprint109MoscoSpectralLiminfAssemblyReceipt
    liminfModulePath :
      String
    recoveryModulePath :
      String
    assemblyModulePath :
      String
    liminfImported :
      Bool
    recoveryImported :
      Bool
    assemblyImported :
      Bool
    sprint109LiminfInputClosed :
      Bool
    sprint109RecoveryInputClosed :
      Bool
    sprint109AssemblyInputClosed :
      Bool
    importedClayFlagsKeptFalse :
      Bool

record FormDomainIdentificationStatus : Set where
  constructor mkFormDomainIdentificationStatus
  field
    lane :
      CriterionLane
    identificationStatement :
      String
    graphNormDomainStatement :
      String
    continuumHilbertCarrierRequired :
      Bool
    physicalGaugeSectorRequired :
      Bool
    finiteDomainComparisonMapsRequired :
      Bool
    graphNormCoreEqualityRequired :
      Bool
    identifiedHere :
      Bool
    status :
      CriterionStatus

record ClosednessSemiboundednessLedger : Set where
  constructor mkClosednessSemiboundednessLedger
  field
    lane :
      CriterionLane
    ledgerStatement :
      String
    continuumFormClosedRequired :
      Bool
    continuumFormSemiboundedRequired :
      Bool
    finiteFormsCommonLowerBoundRequired :
      Bool
    renormalizedLowerBoundCompatibleWithTransferConstants :
      Bool
    closednessProvedHere :
      Bool
    semiboundednessProvedHere :
      Bool
    status :
      CriterionStatus

record WeakCompactnessLedger : Set where
  constructor mkWeakCompactnessLedger
  field
    lane :
      CriterionLane
    statement :
      String
    boundedEnergyHypothesisRequired :
      Bool
    weakLimitExtractionRequired :
      Bool
    identifiedCarrierRequired :
      Bool
    provedHere :
      Bool
    status :
      CriterionStatus

record LiminfInequalityCriterion : Set where
  constructor mkLiminfInequalityCriterion
  field
    lane :
      CriterionLane
    inequalityStatement :
      String
    finiteFormSymbol :
      String
    continuumFormSymbol :
      String
    weakConvergenceHypothesisRequired :
      Bool
    boundedEnergyHypothesisRequired :
      Bool
    limitInFormDomainConclusionRequired :
      Bool
    liminfInequalityConclusionRequired :
      Bool
    provedHere :
      Bool
    status :
      CriterionStatus

record GaugeSectorPreservationStatus : Set where
  constructor mkGaugeSectorPreservationStatus
  field
    lane :
      CriterionLane
    statement :
      String
    gaugeConstraintsPreservedByWeakLimits :
      Bool
    physicalProjectionStable :
      Bool
    quotientIdentificationStable :
      Bool
    nonVacuumSectorLabelStable :
      Bool
    provedHere :
      Bool
    status :
      CriterionStatus

record ExactAnalyticClosureConditions : Set where
  constructor mkExactAnalyticClosureConditions
  field
    conditionStatement :
      String
    requiredConditions :
      List String
    domainIdentificationRequired :
      Bool
    commonLowerBoundRequired :
      Bool
    closedContinuumFormRequired :
      Bool
    weakCompactnessRequired :
      Bool
    gaugeSectorPreservationRequired :
      Bool
    liminfInequalityRequired :
      Bool
    allConditionsProvedHere :
      Bool
    criterionWouldCloseIfAllConditionsProved :
      Bool
    status :
      CriterionStatus

record CriterionClosureLedger : Set where
  constructor mkCriterionClosureLedger
  field
    targetFormula :
      String
    criterionStatement :
      String
    sprint109ClosedFormInputClosed :
      Bool
    sprint109RecoveryInputClosed :
      Bool
    sprint109AssemblyInputClosed :
      Bool
    domainIdentificationClosed :
      Bool
    closednessSemiboundednessClosed :
      Bool
    liminfInequalityClosed :
      Bool
    gaugeSectorPreservationClosed :
      Bool
    criterionClosedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    criterionClosedHereIsFalse :
      criterionClosedHere ≡ false
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      CriterionStatus

record YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt : Setω where
  field
    sprint109Supply :
      Sprint109CriterionSupply
    lanes :
      List CriterionLane
    formDomainIdentification :
      FormDomainIdentificationStatus
    closednessSemiboundedness :
      ClosednessSemiboundednessLedger
    weakCompactness :
      WeakCompactnessLedger
    liminfInequality :
      LiminfInequalityCriterion
    gaugeSectorPreservation :
      GaugeSectorPreservationStatus
    exactAnalyticClosureConditions :
      ExactAnalyticClosureConditions
    closureLedger :
      CriterionClosureLedger
    receiptRecorded :
      Bool
    closedFormCriterionClosedHereFlag :
      Bool
    closedFormCriterionClosedHereFlagIsFalse :
      closedFormCriterionClosedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    evidenceLedger :
      List String

open YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt public

canonicalRequiredConditions : List String
canonicalRequiredConditions =
  domainIdentificationText
  ∷ formDomainEqualityText
  ∷ closednessSemiboundednessText
  ∷ Liminf109.weakCompactnessRequirementText
  ∷ gaugeSectorPreservationText
  ∷ liminfInequalityText
  ∷ []

canonicalSprint109CriterionSupply : Sprint109CriterionSupply
canonicalSprint109CriterionSupply =
  mkSprint109CriterionSupply
    Liminf109.canonicalReceipt
    Recovery109.canonicalReceipt
    Assembly109.canonicalReceipt
    sprint109LiminfPath
    sprint109RecoveryPath
    sprint109AssemblyPath
    sprint109LiminfImported
    sprint109RecoveryImported
    sprint109AssemblyImported
    sprint109ClosedFormLowerSemicontinuityClosed
    sprint109RecoverySideClosed
    sprint109AssemblyTheoremClosed
    true

canonicalFormDomainIdentificationStatus :
  FormDomainIdentificationStatus
canonicalFormDomainIdentificationStatus =
  mkFormDomainIdentificationStatus
    form-domain-identification-lane
    domainIdentificationText
    formDomainEqualityText
    true
    true
    true
    true
    domainIdentificationClosedHere
    identified-not-proved

canonicalClosednessSemiboundednessLedger :
  ClosednessSemiboundednessLedger
canonicalClosednessSemiboundednessLedger =
  mkClosednessSemiboundednessLedger
    closedness-semiboundedness-lane
    closednessSemiboundednessText
    true
    true
    true
    true
    closednessSemiboundednessClosedHere
    closednessSemiboundednessClosedHere
    closedness-required

canonicalWeakCompactnessLedger : WeakCompactnessLedger
canonicalWeakCompactnessLedger =
  mkWeakCompactnessLedger
    weak-compactness-lane
    Liminf109.weakCompactnessRequirementText
    true
    true
    true
    false
    theorem-open

canonicalLiminfInequalityCriterion : LiminfInequalityCriterion
canonicalLiminfInequalityCriterion =
  mkLiminfInequalityCriterion
    liminf-inequality-lane
    liminfInequalityText
    "q_a(u_a)"
    "q(u)"
    true
    true
    true
    true
    liminfInequalityClosedHere
    liminf-required

canonicalGaugeSectorPreservationStatus :
  GaugeSectorPreservationStatus
canonicalGaugeSectorPreservationStatus =
  mkGaugeSectorPreservationStatus
    gauge-sector-preservation-lane
    gaugeSectorPreservationText
    true
    true
    true
    true
    gaugeSectorPreservationClosedHere
    gauge-preservation-required

canonicalExactAnalyticClosureConditions :
  ExactAnalyticClosureConditions
canonicalExactAnalyticClosureConditions =
  mkExactAnalyticClosureConditions
    analyticClosureConditionText
    canonicalRequiredConditions
    true
    true
    true
    true
    true
    true
    false
    true
    exact-closure-conditions-recorded

canonicalCriterionClosureLedger : CriterionClosureLedger
canonicalCriterionClosureLedger =
  mkCriterionClosureLedger
    targetFormulaText
    criterionStatementText
    sprint109ClosedFormLowerSemicontinuityClosed
    sprint109RecoverySideClosed
    sprint109AssemblyTheoremClosed
    domainIdentificationClosedHere
    closednessSemiboundednessClosedHere
    liminfInequalityClosedHere
    gaugeSectorPreservationClosedHere
    closedFormCriterionClosedHere
    clayYangMillsPromoted
    refl
    refl
    theorem-open

canonicalYMSprint110ClosedFormLowerSemicontinuityCriterionReceipt :
  YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt
canonicalYMSprint110ClosedFormLowerSemicontinuityCriterionReceipt =
  record
    { sprint109Supply =
        canonicalSprint109CriterionSupply
    ; lanes =
        canonicalCriterionLanes
    ; formDomainIdentification =
        canonicalFormDomainIdentificationStatus
    ; closednessSemiboundedness =
        canonicalClosednessSemiboundednessLedger
    ; weakCompactness =
        canonicalWeakCompactnessLedger
    ; liminfInequality =
        canonicalLiminfInequalityCriterion
    ; gaugeSectorPreservation =
        canonicalGaugeSectorPreservationStatus
    ; exactAnalyticClosureConditions =
        canonicalExactAnalyticClosureConditions
    ; closureLedger =
        canonicalCriterionClosureLedger
    ; receiptRecorded =
        criterionReceiptRecorded
    ; closedFormCriterionClosedHereFlag =
        closedFormCriterionClosedHere
    ; closedFormCriterionClosedHereFlagIsFalse =
        refl
    ; clayYangMillsPromotedHere =
        clayYangMillsPromoted
    ; clayYangMillsPromotedHereIsFalse =
        refl
    ; evidenceLedger =
        criterionStatementText
        ∷ domainIdentificationText
        ∷ formDomainEqualityText
        ∷ closednessSemiboundednessText
        ∷ Liminf109.weakCompactnessRequirementText
        ∷ liminfInequalityText
        ∷ gaugeSectorPreservationText
        ∷ analyticClosureConditionText
        ∷ nonPromotionBoundaryText
        ∷ []
    }

canonicalReceipt :
  YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt
canonicalReceipt =
  canonicalYMSprint110ClosedFormLowerSemicontinuityCriterionReceipt

canonicalReceiptRecorded : Bool
canonicalReceiptRecorded =
  receiptRecorded canonicalReceipt

canonicalReceiptCriterionClosedIsFalse :
  closedFormCriterionClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptCriterionClosedIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl

canonicalReceiptCriterionWouldCloseUnderExactConditions :
  ExactAnalyticClosureConditions.criterionWouldCloseIfAllConditionsProved
    (exactAnalyticClosureConditions canonicalReceipt) ≡ true
canonicalReceiptCriterionWouldCloseUnderExactConditions =
  refl

canonicalReceiptAllConditionsNotProvedHere :
  ExactAnalyticClosureConditions.allConditionsProvedHere
    (exactAnalyticClosureConditions canonicalReceipt) ≡ false
canonicalReceiptAllConditionsNotProvedHere =
  refl
