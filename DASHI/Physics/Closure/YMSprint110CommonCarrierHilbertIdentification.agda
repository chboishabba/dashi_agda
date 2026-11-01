module DASHI.Physics.Closure.YMSprint110CommonCarrierHilbertIdentification where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSprint109MoscoLiminfLowerSemicontinuity
  as Liminf109
import DASHI.Physics.Closure.YMSprint109MoscoRecoverySequence
  as Recovery109

------------------------------------------------------------------------
-- Sprint 110 common physical Hilbert carrier identification.
--
-- Sprint109 split the Mosco package into liminf/compactness and recovery
-- sides.  Both sides need the same finite-to-continuum physical carrier
-- dictionary before weak compactness, recovery maps, and spectral passage can
-- be stated without ambiguity.  This module records that common layer as a
-- concrete inhabited receipt:
--
--   finite physical carriers,
--   continuum physical carrier,
--   embedding/projection map surfaces,
--   physical-sector and gauge-quotient compatibility,
--   a norm-comparison window, and
--   exact blockers for the still-open analytic identifications.
--
-- It is a non-promoting status module.  No Mosco theorem, compactness theorem,
-- recovery theorem, or Clay Yang-Mills statement is proved here.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

commonCarrierReceiptRecorded : Bool
commonCarrierReceiptRecorded = true

finiteCarrierRecorded : Bool
finiteCarrierRecorded = true

continuumCarrierRecorded : Bool
continuumCarrierRecorded = true

embeddingProjectionSurfacesRecorded : Bool
embeddingProjectionSurfacesRecorded = true

physicalSectorGaugeQuotientCompatibilityRecorded : Bool
physicalSectorGaugeQuotientCompatibilityRecorded = true

normComparisonWindowRecorded : Bool
normComparisonWindowRecorded = true

sharedByLiminfAndRecoveryRecorded : Bool
sharedByLiminfAndRecoveryRecorded = true

finiteCarrierHilbertCompletedHere : Bool
finiteCarrierHilbertCompletedHere = false

continuumCarrierHilbertConstructedHere : Bool
continuumCarrierHilbertConstructedHere = false

embeddingMapsConstructedHere : Bool
embeddingMapsConstructedHere = false

projectionMapsConstructedHere : Bool
projectionMapsConstructedHere = false

embeddingProjectionAdjointnessProvedHere : Bool
embeddingProjectionAdjointnessProvedHere = false

strongNormIdentificationProvedHere : Bool
strongNormIdentificationProvedHere = false

weakCompactnessProvedHere : Bool
weakCompactnessProvedHere = false

recoveryMapConvergenceProvedHere : Bool
recoveryMapConvergenceProvedHere = false

gaugeQuotientCompatibilityProvedHere : Bool
gaugeQuotientCompatibilityProvedHere = false

physicalProjectionStabilityProvedHere : Bool
physicalProjectionStabilityProvedHere = false

normEquivalenceUniformInAProvedHere : Bool
normEquivalenceUniformInAProvedHere = false

moscoCommonCarrierClosedHere : Bool
moscoCommonCarrierClosedHere = false

moscoConvergenceProvedHere : Bool
moscoConvergenceProvedHere = false

continuumSpectralPassageProvedHere : Bool
continuumSpectralPassageProvedHere = false

liminfReceiptImported : Bool
liminfReceiptImported =
  Liminf109.receiptRecorded

recoveryReceiptImported : Bool
recoveryReceiptImported =
  Recovery109.recoverySequenceReceiptRecorded

liminfWeakCompactnessStillOpen : Bool
liminfWeakCompactnessStillOpen =
  Liminf109.moscoLowerSemicontinuityProvedHere

recoveryNormConvergenceStillOpen : Bool
recoveryNormConvergenceStillOpen =
  Recovery109.normConvergenceProvedHere

targetFormulaText : String
targetFormulaText =
  "gap(T(a)) >= c_transfer * m_eff(a) * a"

finiteCarrierStatementText : String
finiteCarrierStatementText =
  "Finite physical carrier: for each lattice spacing a in the admissible window, use a finite-volume gauge-compatible transfer-form carrier, then pass to the physical sector and gauge quotient before comparison."

continuumCarrierStatementText : String
continuumCarrierStatementText =
  "Continuum physical carrier: use the closed semibounded physical Hilbert carrier of finite-energy continuum Yang-Mills states after gauge quotienting and vacuum/non-vacuum sector separation."

embeddingStatementText : String
embeddingStatementText =
  "Embedding surface E_a: finite physical vectors are inserted into the continuum carrier through a renormalized interpolation/field-normalization convention shared by liminf and recovery."

projectionStatementText : String
projectionStatementText =
  "Projection surface P_a: continuum finite-energy vectors are sampled or projected to finite physical carriers with the same gauge quotient and renormalization convention as E_a."

sectorCompatibilityStatementText : String
sectorCompatibilityStatementText =
  "Physical-sector compatibility: E_a and P_a must commute with finite and continuum physical projections, preserve the vacuum/non-vacuum split, and avoid gauge-sector leakage."

gaugeQuotientCompatibilityStatementText : String
gaugeQuotientCompatibilityStatementText =
  "Gauge-quotient compatibility: equivalent gauge representatives must have equivalent embedded/projection images, and the quotient norm must be compared after representative choices are removed."

normComparisonWindowStatementText : String
normComparisonWindowStatementText =
  "Norm comparison window: for 0 < a <= a0, finite physical norms, quotient norms, and continuum Hilbert norms must be compared by one renormalized convention with uniform constants."

sharedUseStatementText : String
sharedUseStatementText =
  "The liminf side uses this layer for weak compactness and lower semicontinuity; the recovery side uses it for finite approximants, norm convergence, and energy limsup control."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint110 records the common carrier identification requirements only; it does not prove Mosco convergence, compactness, recovery convergence, spectral passage, or Clay Yang-Mills."

exactEmbeddingBlockerText : String
exactEmbeddingBlockerText =
  "Exact blocker: no DASHI-native renormalized interpolation map E_a from gauge-quotiented finite physical carriers into the continuum physical Hilbert carrier is constructed."

exactProjectionBlockerText : String
exactProjectionBlockerText =
  "Exact blocker: no DASHI-native sampling/projection map P_a from the continuum finite-energy form domain to finite physical carriers is constructed."

exactAdjointnessBlockerText : String
exactAdjointnessBlockerText =
  "Exact blocker: E_a/P_a adjointness or approximate inverse laws in the physical quotient Hilbert norms are not proved."

exactGaugeQuotientBlockerText : String
exactGaugeQuotientBlockerText =
  "Exact blocker: compatibility of finite gauge quotient, continuum gauge quotient, and physical-sector projection is recorded but not proved."

exactNormWindowBlockerText : String
exactNormWindowBlockerText =
  "Exact blocker: uniform norm-equivalence constants over the admissible a-window are not proved."

exactWeakCompactnessBlockerText : String
exactWeakCompactnessBlockerText =
  "Exact blocker: weak compactness for bounded finite-energy finite-carrier sequences is still open."

exactRecoveryBlockerText : String
exactRecoveryBlockerText =
  "Exact blocker: recovery approximants with strong norm convergence and energy limsup control are still open."

liminf109Path : String
liminf109Path =
  "DASHI/Physics/Closure/YMSprint109MoscoLiminfLowerSemicontinuity.agda"

recovery109Path : String
recovery109Path =
  "DASHI/Physics/Closure/YMSprint109MoscoRecoverySequence.agda"

data CommonCarrierLane : Set where
  finite-physical-carrier :
    CommonCarrierLane
  continuum-physical-carrier :
    CommonCarrierLane
  embedding-map-surface :
    CommonCarrierLane
  projection-map-surface :
    CommonCarrierLane
  physical-sector-compatibility :
    CommonCarrierLane
  gauge-quotient-compatibility :
    CommonCarrierLane
  norm-comparison-window :
    CommonCarrierLane
  liminf-recovery-shared-use :
    CommonCarrierLane

data CommonCarrierStatus : Set where
  recorded-inhabited :
    CommonCarrierStatus
  evidence-surface-recorded :
    CommonCarrierStatus
  analytic-map-required :
    CommonCarrierStatus
  quotient-compatibility-required :
    CommonCarrierStatus
  norm-window-required :
    CommonCarrierStatus
  shared-requirement-recorded :
    CommonCarrierStatus
  exact-blocked-gap :
    CommonCarrierStatus
  theorem-open :
    CommonCarrierStatus
  nonpromotion :
    CommonCarrierStatus

data CarrierScaleKind : Set where
  finite-lattice-scale :
    CarrierScaleKind
  continuum-limit-scale :
    CarrierScaleKind

record Sprint109CommonInputs : Setω where
  constructor mkSprint109CommonInputs
  field
    liminfReceipt :
      Liminf109.YMSprint109MoscoLiminfLowerSemicontinuityReceipt
    recoveryReceipt :
      Recovery109.YMSprint109MoscoRecoverySequenceReceipt
    liminfModulePath :
      String
    recoveryModulePath :
      String
    liminfReceiptRecordedHere :
      Bool
    recoveryReceiptRecordedHere :
      Bool
    importedClayFlagsKeptFalse :
      Bool

record FinitePhysicalHilbertCarrier : Set where
  constructor mkFinitePhysicalHilbertCarrier
  field
    lane :
      CommonCarrierLane
    scaleKind :
      CarrierScaleKind
    statement :
      String
    latticeSpacingParameterName :
      String
    admissibleWindowName :
      String
    finiteVolumeCutoffName :
      String
    transferFormName :
      String
    physicalProjectionRecorded :
      Bool
    gaugeQuotientRecorded :
      Bool
    nonVacuumSectorRecorded :
      Bool
    hilbertCompletionConstructedHere :
      Bool
    status :
      CommonCarrierStatus

record ContinuumPhysicalHilbertCarrier : Set where
  constructor mkContinuumPhysicalHilbertCarrier
  field
    lane :
      CommonCarrierLane
    scaleKind :
      CarrierScaleKind
    statement :
      String
    continuumHilbertName :
      String
    closedFormDomainName :
      String
    continuumQuadraticFormName :
      String
    physicalProjectionRecorded :
      Bool
    gaugeQuotientRecorded :
      Bool
    vacuumNonVacuumSplitRecorded :
      Bool
    constructedHere :
      Bool
    status :
      CommonCarrierStatus

record MapEvidenceSurface : Set where
  constructor mkMapEvidenceSurface
  field
    lane :
      CommonCarrierLane
    statement :
      String
    mapSymbol :
      String
    sourceCarrier :
      String
    targetCarrier :
      String
    renormalizedConventionRequired :
      Bool
    physicalProjectionCompatibleRequired :
      Bool
    gaugeQuotientCompatibleRequired :
      Bool
    constructedHere :
      Bool
    status :
      CommonCarrierStatus

record EmbeddingProjectionPairStatus : Set where
  constructor mkEmbeddingProjectionPairStatus
  field
    embedding :
      MapEvidenceSurface
    projection :
      MapEvidenceSurface
    commonRenormalizationConventionRecorded :
      Bool
    approximateInverseLawProvedHere :
      Bool
    adjointnessProvedHere :
      Bool
    strongIdentificationProvedHere :
      Bool
    status :
      CommonCarrierStatus

record PhysicalSectorGaugeQuotientCompatibility : Set where
  constructor mkPhysicalSectorGaugeQuotientCompatibility
  field
    physicalSectorLane :
      CommonCarrierLane
    gaugeQuotientLane :
      CommonCarrierLane
    physicalSectorStatement :
      String
    gaugeQuotientStatement :
      String
    finitePhysicalProjectionRecorded :
      Bool
    continuumPhysicalProjectionRecorded :
      Bool
    vacuumNonVacuumSplitPreservedRequired :
      Bool
    gaugeRepresentativeIndependenceRequired :
      Bool
    physicalProjectionStabilityProvedHereStatus :
      Bool
    gaugeQuotientCompatibilityProvedHereStatus :
      Bool
    status :
      CommonCarrierStatus

record NormComparisonWindow : Set where
  constructor mkNormComparisonWindow
  field
    lane :
      CommonCarrierLane
    statement :
      String
    lowerEndpointText :
      String
    upperEndpointText :
      String
    finiteNormSymbol :
      String
    quotientNormSymbol :
      String
    continuumNormSymbol :
      String
    uniformConstantsRequired :
      Bool
    fieldStrengthNormalizationRequired :
      Bool
    volumeNormalizationRequired :
      Bool
    provedHere :
      Bool
    status :
      CommonCarrierStatus

record SharedLiminfRecoveryUse : Set where
  constructor mkSharedLiminfRecoveryUse
  field
    lane :
      CommonCarrierLane
    statement :
      String
    liminfWeakCompactnessUsesCarrier :
      Bool
    liminfLowerSemicontinuityUsesCarrier :
      Bool
    recoveryApproximantsUseCarrier :
      Bool
    recoveryNormConvergenceUsesCarrier :
      Bool
    recoveryEnergyLimsupUsesCarrier :
      Bool
    liminfSideClosedHere :
      Bool
    recoverySideClosedHere :
      Bool
    status :
      CommonCarrierStatus

record ExactCommonCarrierBlockers : Set where
  constructor mkExactCommonCarrierBlockers
  field
    embeddingBlocker :
      String
    projectionBlocker :
      String
    adjointnessBlocker :
      String
    gaugeQuotientBlocker :
      String
    normWindowBlocker :
      String
    weakCompactnessBlocker :
      String
    recoveryBlocker :
      String
    allBlockersExact :
      Bool
    theoremStillOpen :
      Bool
    blockerLedger :
      List String
    status :
      CommonCarrierStatus

record TheoremAndPromotionBoundary : Set where
  constructor mkTheoremAndPromotionBoundary
  field
    targetFormula :
      String
    boundaryStatement :
      String
    finiteCarrierHilbertCompletedHereFlag :
      Bool
    continuumCarrierHilbertConstructedHereFlag :
      Bool
    embeddingMapsConstructedHereFlag :
      Bool
    projectionMapsConstructedHereFlag :
      Bool
    embeddingProjectionAdjointnessProvedHereFlag :
      Bool
    strongNormIdentificationProvedHereFlag :
      Bool
    weakCompactnessProvedHereFlag :
      Bool
    recoveryMapConvergenceProvedHereFlag :
      Bool
    normEquivalenceUniformInAProvedHereFlag :
      Bool
    moscoCommonCarrierClosedHereFlag :
      Bool
    moscoConvergenceProvedHereFlag :
      Bool
    continuumSpectralPassageProvedHereFlag :
      Bool
    clayYangMillsPromotedHere :
      Bool
    moscoCommonCarrierClosedHereFlagIsFalse :
      moscoCommonCarrierClosedHereFlag ≡ false
    moscoConvergenceProvedHereFlagIsFalse :
      moscoConvergenceProvedHereFlag ≡ false
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      CommonCarrierStatus

record YMSprint110CommonCarrierHilbertIdentificationReceipt : Setω where
  field
    sprint109Inputs :
      Sprint109CommonInputs
    finiteCarrier :
      FinitePhysicalHilbertCarrier
    continuumCarrier :
      ContinuumPhysicalHilbertCarrier
    embeddingProjectionPair :
      EmbeddingProjectionPairStatus
    physicalSectorGaugeQuotientCompatibility :
      PhysicalSectorGaugeQuotientCompatibility
    normComparisonWindow :
      NormComparisonWindow
    sharedLiminfRecoveryUse :
      SharedLiminfRecoveryUse
    exactBlockers :
      ExactCommonCarrierBlockers
    theoremAndPromotionBoundary :
      TheoremAndPromotionBoundary
    receiptRecordedHere :
      Bool
    commonCarrierClosedHere :
      Bool
    commonCarrierClosedHereIsFalse :
      commonCarrierClosedHere ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    evidenceLedger :
      List String

open YMSprint110CommonCarrierHilbertIdentificationReceipt public

canonicalSprint109CommonInputs : Sprint109CommonInputs
canonicalSprint109CommonInputs =
  mkSprint109CommonInputs
    Liminf109.canonicalReceipt
    Recovery109.canonicalReceipt
    liminf109Path
    recovery109Path
    liminfReceiptImported
    recoveryReceiptImported
    true

canonicalFinitePhysicalHilbertCarrier :
  FinitePhysicalHilbertCarrier
canonicalFinitePhysicalHilbertCarrier =
  mkFinitePhysicalHilbertCarrier
    finite-physical-carrier
    finite-lattice-scale
    finiteCarrierStatementText
    "a"
    "0 < a <= a0"
    "finite volume Lambda(a)"
    "q_a"
    true
    true
    true
    finiteCarrierHilbertCompletedHere
    recorded-inhabited

canonicalContinuumPhysicalHilbertCarrier :
  ContinuumPhysicalHilbertCarrier
canonicalContinuumPhysicalHilbertCarrier =
  mkContinuumPhysicalHilbertCarrier
    continuum-physical-carrier
    continuum-limit-scale
    continuumCarrierStatementText
    "H_phys"
    "D(q)"
    "q"
    true
    true
    true
    continuumCarrierHilbertConstructedHere
    recorded-inhabited

canonicalEmbeddingMapSurface : MapEvidenceSurface
canonicalEmbeddingMapSurface =
  mkMapEvidenceSurface
    embedding-map-surface
    embeddingStatementText
    "E_a"
    "H_a,phys / gauge"
    "H_phys"
    true
    true
    true
    embeddingMapsConstructedHere
    analytic-map-required

canonicalProjectionMapSurface : MapEvidenceSurface
canonicalProjectionMapSurface =
  mkMapEvidenceSurface
    projection-map-surface
    projectionStatementText
    "P_a"
    "D(q) subset H_phys"
    "H_a,phys / gauge"
    true
    true
    true
    projectionMapsConstructedHere
    analytic-map-required

canonicalEmbeddingProjectionPairStatus :
  EmbeddingProjectionPairStatus
canonicalEmbeddingProjectionPairStatus =
  mkEmbeddingProjectionPairStatus
    canonicalEmbeddingMapSurface
    canonicalProjectionMapSurface
    true
    false
    embeddingProjectionAdjointnessProvedHere
    strongNormIdentificationProvedHere
    analytic-map-required

canonicalPhysicalSectorGaugeQuotientCompatibility :
  PhysicalSectorGaugeQuotientCompatibility
canonicalPhysicalSectorGaugeQuotientCompatibility =
  mkPhysicalSectorGaugeQuotientCompatibility
    physical-sector-compatibility
    gauge-quotient-compatibility
    sectorCompatibilityStatementText
    gaugeQuotientCompatibilityStatementText
    true
    true
    true
    true
    physicalProjectionStabilityProvedHere
    gaugeQuotientCompatibilityProvedHere
    quotient-compatibility-required

canonicalNormComparisonWindow : NormComparisonWindow
canonicalNormComparisonWindow =
  mkNormComparisonWindow
    norm-comparison-window
    normComparisonWindowStatementText
    "0 < a"
    "a <= a0"
    "||-||_a,phys"
    "||-||_a,quot"
    "||-||_H_phys"
    true
    true
    true
    normEquivalenceUniformInAProvedHere
    norm-window-required

canonicalSharedLiminfRecoveryUse : SharedLiminfRecoveryUse
canonicalSharedLiminfRecoveryUse =
  mkSharedLiminfRecoveryUse
    liminf-recovery-shared-use
    sharedUseStatementText
    true
    true
    true
    true
    true
    weakCompactnessProvedHere
    recoveryMapConvergenceProvedHere
    shared-requirement-recorded

canonicalExactCommonCarrierBlockers :
  ExactCommonCarrierBlockers
canonicalExactCommonCarrierBlockers =
  mkExactCommonCarrierBlockers
    exactEmbeddingBlockerText
    exactProjectionBlockerText
    exactAdjointnessBlockerText
    exactGaugeQuotientBlockerText
    exactNormWindowBlockerText
    exactWeakCompactnessBlockerText
    exactRecoveryBlockerText
    true
    true
    (exactEmbeddingBlockerText
     ∷ exactProjectionBlockerText
     ∷ exactAdjointnessBlockerText
     ∷ exactGaugeQuotientBlockerText
     ∷ exactNormWindowBlockerText
     ∷ exactWeakCompactnessBlockerText
     ∷ exactRecoveryBlockerText
     ∷ [])
    exact-blocked-gap

canonicalTheoremAndPromotionBoundary :
  TheoremAndPromotionBoundary
canonicalTheoremAndPromotionBoundary =
  mkTheoremAndPromotionBoundary
    targetFormulaText
    nonPromotionBoundaryText
    finiteCarrierHilbertCompletedHere
    continuumCarrierHilbertConstructedHere
    embeddingMapsConstructedHere
    projectionMapsConstructedHere
    embeddingProjectionAdjointnessProvedHere
    strongNormIdentificationProvedHere
    weakCompactnessProvedHere
    recoveryMapConvergenceProvedHere
    normEquivalenceUniformInAProvedHere
    moscoCommonCarrierClosedHere
    moscoConvergenceProvedHere
    continuumSpectralPassageProvedHere
    clayYangMillsPromoted
    refl
    refl
    refl
    nonpromotion

canonicalYMSprint110CommonCarrierHilbertIdentificationReceipt :
  YMSprint110CommonCarrierHilbertIdentificationReceipt
canonicalYMSprint110CommonCarrierHilbertIdentificationReceipt =
  record
    { sprint109Inputs =
        canonicalSprint109CommonInputs
    ; finiteCarrier =
        canonicalFinitePhysicalHilbertCarrier
    ; continuumCarrier =
        canonicalContinuumPhysicalHilbertCarrier
    ; embeddingProjectionPair =
        canonicalEmbeddingProjectionPairStatus
    ; physicalSectorGaugeQuotientCompatibility =
        canonicalPhysicalSectorGaugeQuotientCompatibility
    ; normComparisonWindow =
        canonicalNormComparisonWindow
    ; sharedLiminfRecoveryUse =
        canonicalSharedLiminfRecoveryUse
    ; exactBlockers =
        canonicalExactCommonCarrierBlockers
    ; theoremAndPromotionBoundary =
        canonicalTheoremAndPromotionBoundary
    ; receiptRecordedHere =
        commonCarrierReceiptRecorded
    ; commonCarrierClosedHere =
        moscoCommonCarrierClosedHere
    ; commonCarrierClosedHereIsFalse =
        refl
    ; clayYangMillsPromotedHere =
        clayYangMillsPromoted
    ; clayYangMillsPromotedHereIsFalse =
        refl
    ; evidenceLedger =
        finiteCarrierStatementText
        ∷ continuumCarrierStatementText
        ∷ embeddingStatementText
        ∷ projectionStatementText
        ∷ sectorCompatibilityStatementText
        ∷ gaugeQuotientCompatibilityStatementText
        ∷ normComparisonWindowStatementText
        ∷ sharedUseStatementText
        ∷ exactEmbeddingBlockerText
        ∷ exactProjectionBlockerText
        ∷ exactAdjointnessBlockerText
        ∷ exactGaugeQuotientBlockerText
        ∷ exactNormWindowBlockerText
        ∷ exactWeakCompactnessBlockerText
        ∷ exactRecoveryBlockerText
        ∷ nonPromotionBoundaryText
        ∷ []
    }

canonicalReceipt :
  YMSprint110CommonCarrierHilbertIdentificationReceipt
canonicalReceipt =
  canonicalYMSprint110CommonCarrierHilbertIdentificationReceipt

canonicalReceiptCommonCarrierClosedHereIsFalse :
  commonCarrierClosedHere canonicalReceipt ≡ false
canonicalReceiptCommonCarrierClosedHereIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl

canonicalReceiptEmbeddingMapsConstructedHereIsFalse :
  TheoremAndPromotionBoundary.embeddingMapsConstructedHereFlag
    (theoremAndPromotionBoundary canonicalReceipt) ≡ false
canonicalReceiptEmbeddingMapsConstructedHereIsFalse =
  refl

canonicalReceiptProjectionMapsConstructedHereIsFalse :
  TheoremAndPromotionBoundary.projectionMapsConstructedHereFlag
    (theoremAndPromotionBoundary canonicalReceipt) ≡ false
canonicalReceiptProjectionMapsConstructedHereIsFalse =
  refl

canonicalReceiptNormEquivalenceUniformInAProvedHereIsFalse :
  TheoremAndPromotionBoundary.normEquivalenceUniformInAProvedHereFlag
    (theoremAndPromotionBoundary canonicalReceipt) ≡ false
canonicalReceiptNormEquivalenceUniformInAProvedHereIsFalse =
  refl

canonicalReceiptExactBlockers :
  ExactCommonCarrierBlockers
canonicalReceiptExactBlockers =
  exactBlockers canonicalReceipt
