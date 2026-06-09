module DASHI.Physics.Closure.YMSprint109MoscoRecoverySequence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSprint107FiniteContinuumUniformityBoundary
  as Uniformity107
import DASHI.Physics.Closure.YMSprint108MoscoNoPollutionBridge
  as Mosco108
import DASHI.Physics.Closure.YMSprint108UniformFormLowerBound
  as UniformForm108

------------------------------------------------------------------------
-- Sprint 109 Mosco recovery-sequence side.
--
-- Sprint108 recorded the Mosco/no-bottom-pollution bridge and marked the
-- recovery-sequence side as required but not constructed.  This module
-- advances that package by isolating the exact recovery data needed for
-- continuum finite-energy vectors:
--
--   * finite lattice approximants for each continuum finite-energy vector,
--   * norm convergence back to the continuum vector,
--   * quadratic-form energy limsup control,
--   * a carrier-density and renormalization boundary identifying why the
--     finite carrier cannot be used raw, and
--   * the reason this side is indispensable for Mosco convergence.
--
-- It is a checked, non-promoting receipt.  The analytic theorems are recorded
-- as concrete blocked gaps rather than assumed.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

recoverySequenceReceiptRecorded : Bool
recoverySequenceReceiptRecorded = true

finiteLatticeApproximantsSpecified : Bool
finiteLatticeApproximantsSpecified = true

normConvergenceRequirementRecorded : Bool
normConvergenceRequirementRecorded = true

energyLimsupRequirementRecorded : Bool
energyLimsupRequirementRecorded = true

carrierDensityBoundaryRecorded : Bool
carrierDensityBoundaryRecorded = true

renormalizationBoundaryRecorded : Bool
renormalizationBoundaryRecorded = true

moscoNecessityRecorded : Bool
moscoNecessityRecorded = true

finiteLatticeApproximantsConstructedHere : Bool
finiteLatticeApproximantsConstructedHere = false

normConvergenceProvedHere : Bool
normConvergenceProvedHere = false

energyLimsupProvedHere : Bool
energyLimsupProvedHere = false

carrierDensityProvedHere : Bool
carrierDensityProvedHere = false

renormalizedCarrierIdentificationProvedHere : Bool
renormalizedCarrierIdentificationProvedHere = false

moscoRecoverySideClosedHere : Bool
moscoRecoverySideClosedHere = false

moscoConvergenceProvedHere : Bool
moscoConvergenceProvedHere = false

continuumSpectralPassageProvedHere : Bool
continuumSpectralPassageProvedHere = false

uniformTransferTargetProvedHere : Bool
uniformTransferTargetProvedHere = false

sprint108RecoveryConstructedInput : Bool
sprint108RecoveryConstructedInput =
  Mosco108.recoverySequenceConstructedHere

sprint108MoscoBridgeProvedInput : Bool
sprint108MoscoBridgeProvedInput =
  Mosco108.moscoBridgeProvedHere

sprint108NoBottomPollutionProvedInput : Bool
sprint108NoBottomPollutionProvedInput =
  Mosco108.noBottomSpectrumPollutionProvedHere

sprint107ContinuumPassageProvedInput : Bool
sprint107ContinuumPassageProvedInput =
  Uniformity107.continuumPassageProvedHere

targetFormulaText : String
targetFormulaText =
  "gap(T(a)) >= c * m_eff(a) * a"

continuumFiniteEnergyVectorText : String
continuumFiniteEnergyVectorText =
  "For every vector u in the continuum closed quadratic-form domain with finite energy q(u), choose lattice-scale vectors u_a in the finite carrier Hilbert spaces."

finiteApproximantText : String
finiteApproximantText =
  "The approximants must be built from gauge-compatible finite lattice carriers, projected to the physical sector, and compared through the renormalized embedding/projection maps."

normConvergenceText : String
normConvergenceText =
  "Norm recovery requirement: after the Sprint108 carrier identification, u_a must converge strongly to u in the continuum Hilbert norm."

energyLimsupText : String
energyLimsupText =
  "Energy limsup requirement: limsup_a q_a(u_a) <= q(u), with q_a the renormalized finite transfer quadratic form and q the continuum closed semibounded form."

carrierDensityText : String
carrierDensityText =
  "Carrier density boundary: finite lattice physical vectors must be dense in the continuum finite-energy form domain after gauge quotienting, ultraviolet cutoff removal, and finite-volume exhaustion."

renormalizationBoundaryText : String
renormalizationBoundaryText =
  "Renormalization boundary: the raw finite action/form is not the recovery form until coupling, field-strength normalization, volume, and carrier embedding conventions are fixed uniformly in the a-window."

moscoNecessityText : String
moscoNecessityText =
  "Mosco convergence needs both sides: Sprint108 liminf/no-pollution prevents energy loss below the limit, while this recovery limsup side prevents the limit form from being too large and identifies the continuum operator."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint109 records the recovery-sequence side and concrete analytic inputs only; it does not prove Mosco convergence, no-pollution, the transfer lower bound, or the Clay Yang-Mills claim."

nextAnalyticDensityInputText : String
nextAnalyticDensityInputText =
  "Input A: prove a gauge-compatible finite-lattice core dense in the continuum finite-energy form domain, including quotient/physical-sector projection stability."

nextAnalyticInterpolationInputText : String
nextAnalyticInterpolationInputText =
  "Input B: construct interpolation and sampling maps between finite carriers and continuum fields with strong norm convergence on the dense core."

nextAnalyticEnergyInputText : String
nextAnalyticEnergyInputText =
  "Input C: prove the renormalized Wilson/Balaban finite forms satisfy the limsup inequality on the recovery maps uniformly over the a-window."

nextAnalyticRenormalizationInputText : String
nextAnalyticRenormalizationInputText =
  "Input D: fix the coupling, field normalization, volume exhaustion, and embedding conventions so q_a and q are compared in one Hilbert-space identification."

sprint107UniformityPath : String
sprint107UniformityPath =
  "DASHI/Physics/Closure/YMSprint107FiniteContinuumUniformityBoundary.agda"

sprint108MoscoPath : String
sprint108MoscoPath =
  "DASHI/Physics/Closure/YMSprint108MoscoNoPollutionBridge.agda"

sprint108UniformFormPath : String
sprint108UniformFormPath =
  "DASHI/Physics/Closure/YMSprint108UniformFormLowerBound.agda"

data RecoverySequenceLane : Set where
  continuum-finite-energy-vector :
    RecoverySequenceLane
  finite-lattice-approximants :
    RecoverySequenceLane
  norm-convergence :
    RecoverySequenceLane
  energy-limsup :
    RecoverySequenceLane
  carrier-density :
    RecoverySequenceLane
  renormalization-boundary :
    RecoverySequenceLane
  mosco-necessity :
    RecoverySequenceLane

data RecoverySequenceStatus : Set where
  recorded-required :
    RecoverySequenceStatus
  specified-not-constructed :
    RecoverySequenceStatus
  analytic-input-required :
    RecoverySequenceStatus
  boundary-not-proved :
    RecoverySequenceStatus
  sprint108-gap-advanced :
    RecoverySequenceStatus
  theorem-open :
    RecoverySequenceStatus
  nonpromotion :
    RecoverySequenceStatus

record Sprint108RecoverySupply : Setω where
  constructor mkSprint108RecoverySupply
  field
    sprint107UniformityReceipt :
      Uniformity107.YMSprint107FiniteContinuumUniformityBoundaryReceipt
    sprint108MoscoReceipt :
      Mosco108.YMSprint108MoscoNoPollutionBridgeReceipt
    sprint108UniformFormReceipt :
      UniformForm108.YMSprint108UniformFormLowerBoundReceipt
    sprint107UniformityModulePath :
      String
    sprint108MoscoModulePath :
      String
    sprint108UniformFormModulePath :
      String
    sprint108RecoveryConstructed :
      Bool
    sprint108MoscoBridgeProved :
      Bool
    sprint108NoBottomPollutionProved :
      Bool
    sprint107ContinuumPassageProved :
      Bool
    importedClayFlagsKeptFalse :
      Bool

record ContinuumFiniteEnergyVectorStatus : Set where
  constructor mkContinuumFiniteEnergyVectorStatus
  field
    lane :
      RecoverySequenceLane
    statement :
      String
    formDomainRequired :
      Bool
    finiteEnergyRequired :
      Bool
    physicalSectorRequired :
      Bool
    status :
      RecoverySequenceStatus

record FiniteLatticeApproximantStatus : Set where
  constructor mkFiniteLatticeApproximantStatus
  field
    lane :
      RecoverySequenceLane
    statement :
      String
    gaugeCompatibleCarriersRequired :
      Bool
    finiteVolumeCutoffRequired :
      Bool
    ultravioletCutoffRequired :
      Bool
    physicalProjectionRequired :
      Bool
    constructedHere :
      Bool
    status :
      RecoverySequenceStatus

record NormConvergenceStatus : Set where
  constructor mkNormConvergenceStatus
  field
    lane :
      RecoverySequenceLane
    statement :
      String
    strongHilbertConvergenceRequired :
      Bool
    renormalizedIdentificationRequired :
      Bool
    provedHere :
      Bool
    status :
      RecoverySequenceStatus

record EnergyLimsupStatus : Set where
  constructor mkEnergyLimsupStatus
  field
    lane :
      RecoverySequenceLane
    statement :
      String
    finiteFormSymbol :
      String
    continuumFormSymbol :
      String
    limsupInequalityRequired :
      Bool
    uniformAWindowRequired :
      Bool
    provedHere :
      Bool
    status :
      RecoverySequenceStatus

record CarrierDensityRenormalizationBoundary : Set where
  constructor mkCarrierDensityRenormalizationBoundary
  field
    carrierDensityLane :
      RecoverySequenceLane
    renormalizationLane :
      RecoverySequenceLane
    carrierDensityStatement :
      String
    renormalizationStatement :
      String
    gaugeQuotientDensityRequired :
      Bool
    physicalSectorProjectionStabilityRequired :
      Bool
    couplingNormalizationRequired :
      Bool
    fieldStrengthNormalizationRequired :
      Bool
    volumeExhaustionRequired :
      Bool
    densityProvedHere :
      Bool
    renormalizedIdentificationProvedHere :
      Bool
    status :
      RecoverySequenceStatus

record MoscoRecoveryNecessityStatus : Set where
  constructor mkMoscoRecoveryNecessityStatus
  field
    lane :
      RecoverySequenceLane
    statement :
      String
    sprint108LiminfSideRecorded :
      Bool
    sprint108RecoverySideWasGap :
      Bool
    limsupSideRequiredForMosco :
      Bool
    preventsLimitFormTooLarge :
      Bool
    identifiesContinuumOperator :
      Bool
    moscoRecoveryClosedHere :
      Bool
    moscoConvergenceProvedHereStatus :
      Bool
    status :
      RecoverySequenceStatus

record NextAnalyticInputs : Set where
  constructor mkNextAnalyticInputs
  field
    densityInput :
      String
    interpolationSamplingInput :
      String
    energyLimsupInput :
      String
    renormalizationInput :
      String
    allInputsProvedHere :
      Bool
    status :
      RecoverySequenceStatus

record TheoremAndPromotionBoundary : Set where
  constructor mkTheoremAndPromotionBoundary
  field
    targetFormula :
      String
    boundaryStatement :
      String
    finiteApproximantsConstructedHere :
      Bool
    normConvergenceProvedHereStatus :
      Bool
    energyLimsupProvedHereStatus :
      Bool
    carrierDensityProvedHereStatus :
      Bool
    renormalizedCarrierIdentificationProvedHereStatus :
      Bool
    moscoConvergenceProvedHereStatus :
      Bool
    continuumSpectralPassageProvedHereStatus :
      Bool
    uniformTransferTargetProvedHereStatus :
      Bool
    clayYangMillsPromotedHere :
      Bool
    moscoConvergenceProvedHereIsFalse :
      moscoConvergenceProvedHereStatus ≡ false
    uniformTransferTargetProvedHereIsFalse :
      uniformTransferTargetProvedHereStatus ≡ false
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      RecoverySequenceStatus

record YMSprint109MoscoRecoverySequenceReceipt : Setω where
  field
    sprint108Supply :
      Sprint108RecoverySupply
    continuumFiniteEnergyVector :
      ContinuumFiniteEnergyVectorStatus
    finiteLatticeApproximants :
      FiniteLatticeApproximantStatus
    normConvergence :
      NormConvergenceStatus
    energyLimsup :
      EnergyLimsupStatus
    carrierDensityRenormalizationBoundary :
      CarrierDensityRenormalizationBoundary
    moscoRecoveryNecessity :
      MoscoRecoveryNecessityStatus
    nextAnalyticInputs :
      NextAnalyticInputs
    theoremAndPromotionBoundary :
      TheoremAndPromotionBoundary
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    receiptStatements :
      List String

open YMSprint109MoscoRecoverySequenceReceipt public

canonicalSprint108RecoverySupply : Sprint108RecoverySupply
canonicalSprint108RecoverySupply =
  mkSprint108RecoverySupply
    Uniformity107.canonicalYMSprint107FiniteContinuumUniformityBoundaryReceipt
    Mosco108.canonicalYMSprint108MoscoNoPollutionBridgeReceipt
    UniformForm108.canonicalYMSprint108UniformFormLowerBoundReceipt
    sprint107UniformityPath
    sprint108MoscoPath
    sprint108UniformFormPath
    sprint108RecoveryConstructedInput
    sprint108MoscoBridgeProvedInput
    sprint108NoBottomPollutionProvedInput
    sprint107ContinuumPassageProvedInput
    true

canonicalContinuumFiniteEnergyVectorStatus :
  ContinuumFiniteEnergyVectorStatus
canonicalContinuumFiniteEnergyVectorStatus =
  mkContinuumFiniteEnergyVectorStatus
    continuum-finite-energy-vector
    continuumFiniteEnergyVectorText
    true
    true
    true
    recorded-required

canonicalFiniteLatticeApproximantStatus :
  FiniteLatticeApproximantStatus
canonicalFiniteLatticeApproximantStatus =
  mkFiniteLatticeApproximantStatus
    finite-lattice-approximants
    finiteApproximantText
    true
    true
    true
    true
    finiteLatticeApproximantsConstructedHere
    specified-not-constructed

canonicalNormConvergenceStatus : NormConvergenceStatus
canonicalNormConvergenceStatus =
  mkNormConvergenceStatus
    norm-convergence
    normConvergenceText
    true
    true
    normConvergenceProvedHere
    analytic-input-required

canonicalEnergyLimsupStatus : EnergyLimsupStatus
canonicalEnergyLimsupStatus =
  mkEnergyLimsupStatus
    energy-limsup
    energyLimsupText
    "q_a(u_a)"
    "q(u)"
    true
    true
    energyLimsupProvedHere
    analytic-input-required

canonicalCarrierDensityRenormalizationBoundary :
  CarrierDensityRenormalizationBoundary
canonicalCarrierDensityRenormalizationBoundary =
  mkCarrierDensityRenormalizationBoundary
    carrier-density
    renormalization-boundary
    carrierDensityText
    renormalizationBoundaryText
    true
    true
    true
    true
    true
    carrierDensityProvedHere
    renormalizedCarrierIdentificationProvedHere
    boundary-not-proved

canonicalMoscoRecoveryNecessityStatus :
  MoscoRecoveryNecessityStatus
canonicalMoscoRecoveryNecessityStatus =
  mkMoscoRecoveryNecessityStatus
    mosco-necessity
    moscoNecessityText
    Mosco108.bridgeReceiptRecorded
    true
    true
    true
    true
    moscoRecoverySideClosedHere
    moscoConvergenceProvedHere
    sprint108-gap-advanced

canonicalNextAnalyticInputs : NextAnalyticInputs
canonicalNextAnalyticInputs =
  mkNextAnalyticInputs
    nextAnalyticDensityInputText
    nextAnalyticInterpolationInputText
    nextAnalyticEnergyInputText
    nextAnalyticRenormalizationInputText
    false
    analytic-input-required

canonicalTheoremAndPromotionBoundary :
  TheoremAndPromotionBoundary
canonicalTheoremAndPromotionBoundary =
  mkTheoremAndPromotionBoundary
    targetFormulaText
    nonPromotionBoundaryText
    finiteLatticeApproximantsConstructedHere
    normConvergenceProvedHere
    energyLimsupProvedHere
    carrierDensityProvedHere
    renormalizedCarrierIdentificationProvedHere
    moscoConvergenceProvedHere
    continuumSpectralPassageProvedHere
    uniformTransferTargetProvedHere
    clayYangMillsPromoted
    refl
    refl
    refl
    nonpromotion

canonicalYMSprint109MoscoRecoverySequenceReceipt :
  YMSprint109MoscoRecoverySequenceReceipt
canonicalYMSprint109MoscoRecoverySequenceReceipt =
  record
    { sprint108Supply =
        canonicalSprint108RecoverySupply
    ; continuumFiniteEnergyVector =
        canonicalContinuumFiniteEnergyVectorStatus
    ; finiteLatticeApproximants =
        canonicalFiniteLatticeApproximantStatus
    ; normConvergence =
        canonicalNormConvergenceStatus
    ; energyLimsup =
        canonicalEnergyLimsupStatus
    ; carrierDensityRenormalizationBoundary =
        canonicalCarrierDensityRenormalizationBoundary
    ; moscoRecoveryNecessity =
        canonicalMoscoRecoveryNecessityStatus
    ; nextAnalyticInputs =
        canonicalNextAnalyticInputs
    ; theoremAndPromotionBoundary =
        canonicalTheoremAndPromotionBoundary
    ; receiptRecorded =
        recoverySequenceReceiptRecorded
    ; clayYangMillsPromotedHere =
        clayYangMillsPromoted
    ; clayYangMillsPromotedHereIsFalse =
        refl
    ; receiptStatements =
        continuumFiniteEnergyVectorText
        ∷ finiteApproximantText
        ∷ normConvergenceText
        ∷ energyLimsupText
        ∷ carrierDensityText
        ∷ renormalizationBoundaryText
        ∷ moscoNecessityText
        ∷ nextAnalyticDensityInputText
        ∷ nextAnalyticInterpolationInputText
        ∷ nextAnalyticEnergyInputText
        ∷ nextAnalyticRenormalizationInputText
        ∷ nonPromotionBoundaryText
        ∷ []
    }

canonicalReceipt :
  YMSprint109MoscoRecoverySequenceReceipt
canonicalReceipt =
  canonicalYMSprint109MoscoRecoverySequenceReceipt

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl

canonicalReceiptMoscoConvergenceProvedHereIsFalse :
  TheoremAndPromotionBoundary.moscoConvergenceProvedHereStatus
    (theoremAndPromotionBoundary canonicalReceipt) ≡ false
canonicalReceiptMoscoConvergenceProvedHereIsFalse =
  refl

canonicalReceiptUniformTransferTargetProvedHereIsFalse :
  TheoremAndPromotionBoundary.uniformTransferTargetProvedHereStatus
    (theoremAndPromotionBoundary canonicalReceipt) ≡ false
canonicalReceiptUniformTransferTargetProvedHereIsFalse =
  refl

canonicalReceiptEnergyLimsupProvedHere : Bool
canonicalReceiptEnergyLimsupProvedHere =
  EnergyLimsupStatus.provedHere (energyLimsup canonicalReceipt)

canonicalReceiptNormConvergenceProvedHere : Bool
canonicalReceiptNormConvergenceProvedHere =
  NormConvergenceStatus.provedHere (normConvergence canonicalReceipt)

canonicalReceiptNextAnalyticInputsAllProvedHere : Bool
canonicalReceiptNextAnalyticInputsAllProvedHere =
  NextAnalyticInputs.allInputsProvedHere (nextAnalyticInputs canonicalReceipt)
