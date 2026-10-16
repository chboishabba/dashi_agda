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

    -- The group-host obligation is no longer an opaque Set.  It must identify
    -- the selected abstract QFT-group token with the repository's concrete
    -- unit-quaternion SU(2), while also classifying that token as Sprint105 SU2.
    selectedSU2Host :
      SU2Host.CasimirSelectedQFTSU2Host U selectedGroup

    stressEvaluator :
      Cut.CMP119RationalStressComponentEvaluator
        (QFT.StressTensor (Weld.qftCarriers U))

    actualSelectedStressMatchesBrownMaclay :
      ∀ a b →
      Cut.component stressEvaluator
        (Weld.actualQFTStressTensor U
          (Weld.coarseGrain U candidate regime)
          selectedGroup)
        a b
      ≡ CasimirGRQFT.casimirNormalizedRationalTensor4 a b

    sameElectromagneticBoundaryObject : Set
    sameRenormalizedStressConvention : Set

    reading : String

open CasimirU1RecoveredQFTStressAttachment public

------------------------------------------------------------------------
-- Recovered construction = selected QFT target on the declared overlap regime.
------------------------------------------------------------------------

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
  actualSelectedStressMatchesBrownMaclay attachment

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

------------------------------------------------------------------------
-- Existing U(1) architectural authority is consumed, not redefined.
------------------------------------------------------------------------

u1YangMillsArchitectureWitness : U1YM.U1SU2PromotionBoundary
u1YangMillsArchitectureWitness = U1YM.canonicalU1SU2PromotionBoundary

u1AbelianRestrictionAvailable :
  U1YM.abelianYangMillsRestrictionPaid u1YangMillsArchitectureWitness ≡ true
u1AbelianRestrictionAvailable = refl

u1StillNotWholeNonAbelianSU2 :
  U1YM.u1EqualsWholeSU2Theory u1YangMillsArchitectureWitness ≡ false
u1StillNotWholeNonAbelianSU2 = refl

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Machine-readable first-leaf boundary.
------------------------------------------------------------------------

record CasimirU1RecoveredQFTStressAttachmentBoundary : Set where
  constructor casimir-u1-recovered-qft-stress-attachment-boundary
  field
    u1YangMillsGaugeArchitectureAvailable : Bool
    selectedQFTSectorStressAttachmentInterfaceOwned : Bool
    recoveredQFTCommutationConsumed : Bool
    concreteSU2HostReceiptRequired : Bool
    componentwiseBrownMaclayEqualityTargetOwned : Bool
    actualSelectedSectorSharedTransportAlreadyExists : Bool

    concreteSelectedGroupHostsCanonicalU1Paid : Bool
    actualSelectedQFTSectorEqualsBrownMaclayPaid : Bool
    allSectorStressAggregationPaid : Bool
    commonActionVariationPaid : Bool
    unifiedQuantumGravityPromoted : Bool

open CasimirU1RecoveredQFTStressAttachmentBoundary public

canonicalCasimirU1RecoveredQFTStressAttachmentBoundary :
  CasimirU1RecoveredQFTStressAttachmentBoundary
canonicalCasimirU1RecoveredQFTStressAttachmentBoundary =
  casimir-u1-recovered-qft-stress-attachment-boundary
    true true true true true true
    false false false false false

casimirU1RecoveredQFTStressAttachmentReading : String
casimirU1RecoveredQFTStressAttachmentReading =
  "The first Casimir GR/QFT unification stress attachment is now explicit and non-opaque. On an already-declared QFT overlap regime, QFT recovery commutes to the selected target; the selected compact-simple group must carry a CasimirSelectedQFTSU2Host receipt identifying its group interpretation with the repository's concrete unit-quaternion SU(2) and classifying it as Sprint105 SU2. Then a rational evaluator for the actual selected QFT stress must prove every Axis4 component equals the normalized Brown-Maclay tensor on the same boundary/renormalization object. Existing qftSectorStressToShared handles selected-sector transport after that. The attachment does not pay all-sector aggregation, common-action variation, GR stress equality, backreaction, or unified-QG promotion."
