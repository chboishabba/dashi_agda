module DASHI.Physics.QuantumVacuum.CasimirU1RecoveredQFTStressAttachmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as U1YM
import DASHI.Physics.QuantumVacuum.CasimirGRQFTUnificationCrossPollinationExact as CasimirGRQFT
import DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact as SU2Host
import DASHI.Physics.QuantumVacuum.CasimirBrownMaclaySymmetricStressReductionExact as Reduction

------------------------------------------------------------------------
-- CASIMIR U(1) -> ACTUAL RECOVERED-QFT SELECTED-SECTOR STRESS ATTACHMENT
------------------------------------------------------------------------

record CasimirU1RecoveredQFTStressAttachment
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    candidate : Weld.Candidate U
    regime : Weld.Regime U
    qftAtRegime : Weld.qftRegime U regime
    qftRecovery : Weld.QFTRecoveryReceipt U

    selectedGroup : QFT.CompactSimpleGroup (Weld.qftCarriers U)

    selectedSU2Host :
      SU2Host.CasimirSelectedQFTSU2Host U selectedGroup

    stressEvaluator :
      Cut.CMP119RationalStressComponentEvaluator
        (QFT.StressTensor (Weld.qftCarriers U))

    symmetricBrownMaclayPayment :
      Reduction.CasimirBrownMaclaySymmetricTenComponentPayment
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

selectedQFTStressSymmetryReceipt :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  let stress =
        Weld.actualQFTStressTensor U
          (Weld.coarseGrain U
            (candidate attachment)
            (regime attachment))
          (selectedGroup attachment)
  in
  DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact.PairingComponentSymmetry
    (stressEvaluator attachment) stress
selectedQFTStressSymmetryReceipt attachment =
  Reduction.symmetry (symmetricBrownMaclayPayment attachment)

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
    (symmetricBrownMaclayPayment attachment)

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
    true true true true true true false true
    false false false false false false false

casimirU1RecoveredQFTStressAttachmentReading : String
casimirU1RecoveredQFTStressAttachmentReading =
  "The first Casimir GR/QFT unification stress attachment is explicit and minimized. QFT recovery commutes to the selected target. The group-host payment is a concrete CasimirSelectedQFTSU2Host receipt. The stress payment then separates into coordinate symmetry for the same actual selected QFT stress plus ten independent Brown-Maclay component values 00,01,02,03,11,12,13,22,23,33; six lower-triangular equations are compiler output. Existing qftSectorStressToShared handles selected-sector transport after full equality. None of these selected-sector payments imply all-sector aggregation, common-action variation, GR equality, backreaction, or unified-QG promotion."
