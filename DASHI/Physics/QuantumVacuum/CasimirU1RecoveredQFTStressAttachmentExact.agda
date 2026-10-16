module DASHI.Physics.QuantumVacuum.CasimirU1RecoveredQFTStressAttachmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Sym
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as U1YM
import DASHI.Physics.QuantumVacuum.CasimirGRQFTUnificationCrossPollinationExact as CasimirGRQFT
import DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact as SU2Host
import DASHI.Physics.QuantumVacuum.CasimirBrownMaclaySymmetricStressReductionExact as Reduction

record CasimirU1RecoveredQFTStressAttachment
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    candidate : Weld.Candidate U
    regime : Weld.Regime U
    qftAtRegime : Weld.qftRegime U regime
    qftRecovery : Weld.QFTRecoveryReceipt U

    selectedGroup : QFT.CompactSimpleGroup (Weld.qftCarriers U)
    selectedSU2Host : SU2Host.CasimirSelectedQFTSU2Host U selectedGroup

    stressEvaluator :
      Cut.CMP119RationalStressComponentEvaluator
        (QFT.StressTensor (Weld.qftCarriers U))

    selectedStressCoordinateSymmetry :
      Sym.PairingComponentSymmetry
        stressEvaluator
        (Weld.actualQFTStressTensor U
          (Weld.coarseGrain U candidate regime)
          selectedGroup)

    brownMaclayTenValues :
      Reduction.CasimirBrownMaclayTenIndependentValues
        stressEvaluator
        (Weld.actualQFTStressTensor U
          (Weld.coarseGrain U candidate regime)
          selectedGroup)

    sameElectromagneticBoundaryObject : Set
    sameRenormalizedStressConvention : Set
    reading : String

open CasimirU1RecoveredQFTStressAttachment public

recoveredQFTConstructionIsSelectedTarget :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Weld.recoverQFT U
    (Weld.microscopicState U
      (Weld.coarseGrain U
        (candidate attachment)
        (regime attachment)))
  ≡
  Weld.qftTarget U
    (Weld.coarseGrain U
      (candidate attachment)
      (regime attachment))
recoveredQFTConstructionIsSelectedTarget {U} attachment =
  Weld.qftRecoveryAfterCoarseGrainingCommutes
    (qftRecovery attachment)
    (candidate attachment)
    (regime attachment)
    (qftAtRegime attachment)

selectedGroupHostReceipt :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  SU2Host.CasimirSelectedQFTSU2Host U (selectedGroup attachment)
selectedGroupHostReceipt = selectedSU2Host

actualSelectedQFTStress :
  ∀ {U : Weld.UnifiedCandidate} →
  CasimirU1RecoveredQFTStressAttachment U →
  QFT.StressTensor (Weld.qftCarriers U)
actualSelectedQFTStress {U} attachment =
  Weld.actualQFTStressTensor U
    (Weld.coarseGrain U
      (candidate attachment)
      (regime attachment))
    (selectedGroup attachment)

selectedQFTStressSymmetryReceipt :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Sym.PairingComponentSymmetry
    (stressEvaluator attachment)
    (actualSelectedQFTStress attachment)
selectedQFTStressSymmetryReceipt = selectedStressCoordinateSymmetry

selectedQFTBrownMaclayTenValuesReceipt :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Reduction.CasimirBrownMaclayTenIndependentValues
    (stressEvaluator attachment)
    (actualSelectedQFTStress attachment)
selectedQFTBrownMaclayTenValuesReceipt = brownMaclayTenValues

compiledSymmetricBrownMaclayPayment :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Reduction.CasimirBrownMaclaySymmetricTenComponentPayment
    (stressEvaluator attachment)
    (actualSelectedQFTStress attachment)
compiledSymmetricBrownMaclayPayment attachment =
  Reduction.compileSymmetryAndTenValues
    (selectedStressCoordinateSymmetry attachment)
    (brownMaclayTenValues attachment)

actualSelectedQFTStressComponent :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Flat.Axis4 → Flat.Axis4 → ℚ
actualSelectedQFTStressComponent attachment a b =
  Cut.component (stressEvaluator attachment)
    (actualSelectedQFTStress attachment)
    a b

actualSelectedQFTStressComponentIsBrownMaclay :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  ∀ a b →
  actualSelectedQFTStressComponent attachment a b
  ≡ CasimirGRQFT.casimirNormalizedRationalTensor4 a b
actualSelectedQFTStressComponentIsBrownMaclay attachment =
  Reduction.casimirTenComponentsCompileToTensorEquality
    (compiledSymmetricBrownMaclayPayment attachment)

actualSelectedQFTSectorShared :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Weld.SharedStressEnergy U
actualSelectedQFTSectorShared {U} attachment =
  Weld.actualQFTSectorStressShared U
    (Weld.coarseGrain U
      (candidate attachment)
      (regime attachment))
    (selectedGroup attachment)

u1YangMillsArchitectureWitness : U1YM.U1SU2PromotionBoundary
u1YangMillsArchitectureWitness = U1YM.canonicalU1SU2PromotionBoundary

u1AbelianRestrictionAvailable :
  U1YM.abelianYangMillsRestrictionPaid u1YangMillsArchitectureWitness ≡ true
u1AbelianRestrictionAvailable = refl

u1StillNotWholeNonAbelianSU2 :
  U1YM.u1EqualsWholeSU2Theory u1YangMillsArchitectureWitness ≡ false
u1StillNotWholeNonAbelianSU2 = refl

data U1GaugeArchitectureAutomaticallyIdentifiesBrownMaclayWithSelectedQFTStress : Set where
data SelectedSectorStressEqualityAutomaticallyPaysAllSectorAggregation : Set where
data SelectedSectorStressEqualityAutomaticallyPaysCommonActionVariation : Set where
data SelectedSectorStressEqualityAutomaticallyPromotesUnifiedQuantumGravity : Set where

u1GaugeArchitectureDoesNotIdentifySelectedQFTStress :
  U1GaugeArchitectureAutomaticallyIdentifiesBrownMaclayWithSelectedQFTStress → ⊥
u1GaugeArchitectureDoesNotIdentifySelectedQFTStress ()

selectedSectorStressDoesNotPayAllSectorAggregation :
  SelectedSectorStressEqualityAutomaticallyPaysAllSectorAggregation → ⊥
selectedSectorStressDoesNotPayAllSectorAggregation ()

selectedSectorStressDoesNotPayCommonActionVariation :
  SelectedSectorStressEqualityAutomaticallyPaysCommonActionVariation → ⊥
selectedSectorStressDoesNotPayCommonActionVariation ()

selectedSectorStressDoesNotPromoteUnifiedQG :
  SelectedSectorStressEqualityAutomaticallyPromotesUnifiedQuantumGravity → ⊥
selectedSectorStressDoesNotPromoteUnifiedQG ()

record CasimirU1RecoveredQFTStressAttachmentBoundary : Set where
  constructor casimir-u1-recovered-qft-stress-attachment-boundary
  field
    u1YangMillsGaugeArchitectureAvailable : Bool
    selectedQFTSectorStressAttachmentInterfaceOwned : Bool
    recoveredQFTCommutationConsumed : Bool
    concreteSU2HostReceiptRequired : Bool
    symmetryAndTenValuesSeparatedInAttachment : Bool
    symmetricTenComponentBrownMaclayCompilerConsumed : Bool
    componentwiseBrownMaclayEqualityTargetOwned : Bool
    sixteenIndependentBrownMaclayComponentsRequired : Bool
    actualSelectedSectorSharedTransportAlreadyExists : Bool

    concreteSelectedGroupHostsCanonicalU1Paid : Bool
    selectedQFTStressCoordinateSymmetryPaid : Bool
    brownMaclayTenIndependentComponentValuesPaid : Bool
    actualSelectedQFTSectorEqualsBrownMaclayPaid : Bool
    allSectorStressAggregationPaid : Bool
    commonActionVariationPaid : Bool
    unifiedQuantumGravityPromoted : Bool

open CasimirU1RecoveredQFTStressAttachmentBoundary public

canonicalCasimirU1RecoveredQFTStressAttachmentBoundary :
  CasimirU1RecoveredQFTStressAttachmentBoundary
canonicalCasimirU1RecoveredQFTStressAttachmentBoundary =
  casimir-u1-recovered-qft-stress-attachment-boundary
    true true true true true true true false true
    false false false false false false false

casimirU1RecoveredQFTStressAttachmentReading : String
casimirU1RecoveredQFTStressAttachmentReading =
  "The selected-QFT Casimir attachment now exposes the terminal cut literally: selected SU(2) host, coordinate symmetry on the same actual recovered selected-QFT stress/evaluator, and ten independent Brown-Maclay values are separate fields. Symmetry plus ten values compile internally to all sixteen component equalities; no bundled receipt can hide either unpaid coordinate. Existing qftSectorStressToShared then handles selected-sector transport. None of these selected-sector payments imply all-sector aggregation, common-action variation, GR equality, backreaction, or unified-QG promotion."
