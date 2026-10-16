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
import DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact as U1Restriction
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

    canonicalU1StressRestriction :
      U1Restriction.CasimirCanonicalU1StressRestriction
        U candidate regime selectedGroup selectedSU2Host

    stressEvaluator :
      Cut.CMP119RationalStressComponentEvaluator
        (QFT.StressTensor (Weld.qftCarriers U))

    restrictedStressCoordinateSymmetry :
      Sym.PairingComponentSymmetry
        stressEvaluator
        (U1Restriction.u1RestrictedSelectedQFTStress canonicalU1StressRestriction)

    brownMaclayTenValues :
      Reduction.CasimirBrownMaclayTenIndependentValues
        stressEvaluator
        (U1Restriction.u1RestrictedSelectedQFTStress canonicalU1StressRestriction)

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
  ≡ Weld.qftTarget U
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

fullSelectedQFTStress :
  ∀ {U : Weld.UnifiedCandidate} →
  CasimirU1RecoveredQFTStressAttachment U →
  QFT.StressTensor (Weld.qftCarriers U)
fullSelectedQFTStress {U} attachment =
  Weld.actualQFTStressTensor U
    (Weld.coarseGrain U
      (candidate attachment)
      (regime attachment))
    (selectedGroup attachment)

u1RestrictedSelectedQFTStress :
  ∀ {U : Weld.UnifiedCandidate} →
  CasimirU1RecoveredQFTStressAttachment U →
  QFT.StressTensor (Weld.qftCarriers U)
u1RestrictedSelectedQFTStress attachment =
  U1Restriction.u1RestrictedSelectedQFTStress
    (canonicalU1StressRestriction attachment)

restrictedQFTStressSymmetryReceipt :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Sym.PairingComponentSymmetry
    (stressEvaluator attachment)
    (u1RestrictedSelectedQFTStress attachment)
restrictedQFTStressSymmetryReceipt = restrictedStressCoordinateSymmetry

restrictedQFTBrownMaclayTenValuesReceipt :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Reduction.CasimirBrownMaclayTenIndependentValues
    (stressEvaluator attachment)
    (u1RestrictedSelectedQFTStress attachment)
restrictedQFTBrownMaclayTenValuesReceipt = brownMaclayTenValues

compiledSymmetricBrownMaclayPayment :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Reduction.CasimirBrownMaclaySymmetricTenComponentPayment
    (stressEvaluator attachment)
    (u1RestrictedSelectedQFTStress attachment)
compiledSymmetricBrownMaclayPayment attachment =
  Reduction.compileSymmetryAndTenValues
    (restrictedStressCoordinateSymmetry attachment)
    (brownMaclayTenValues attachment)

u1RestrictedSelectedQFTStressComponent :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Flat.Axis4 → Flat.Axis4 → ℚ
u1RestrictedSelectedQFTStressComponent attachment a b =
  Cut.component (stressEvaluator attachment)
    (u1RestrictedSelectedQFTStress attachment)
    a b

u1RestrictedSelectedQFTStressComponentIsBrownMaclay :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  ∀ a b →
  u1RestrictedSelectedQFTStressComponent attachment a b
  ≡ CasimirGRQFT.casimirNormalizedRationalTensor4 a b
u1RestrictedSelectedQFTStressComponentIsBrownMaclay attachment =
  Reduction.casimirTenComponentsCompileToTensorEquality
    (compiledSymmetricBrownMaclayPayment attachment)

-- Shared-sector transport remains a property of the full selected QFT sector.
-- Restricting that shared stress consistently is a later all-sector/common-action
-- question; this module does not silently replace the declared total sector stress.
fullSelectedQFTSectorShared :
  ∀ {U : Weld.UnifiedCandidate} →
  (attachment : CasimirU1RecoveredQFTStressAttachment U) →
  Weld.SharedStressEnergy U
fullSelectedQFTSectorShared {U} attachment =
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
data FullSelectedSU2StressAutomaticallyBecomesBrownMaclayTarget : Set where
data SelectedSectorStressEqualityAutomaticallyPaysAllSectorAggregation : Set where

data SelectedSectorStressEqualityAutomaticallyPaysCommonActionVariation : Set where
data SelectedSectorStressEqualityAutomaticallyPromotesUnifiedQuantumGravity : Set where

u1GaugeArchitectureDoesNotIdentifySelectedQFTStress :
  U1GaugeArchitectureAutomaticallyIdentifiesBrownMaclayWithSelectedQFTStress → ⊥
u1GaugeArchitectureDoesNotIdentifySelectedQFTStress ()

fullSelectedSU2StressDoesNotBecomeBrownMaclayTarget :
  FullSelectedSU2StressAutomaticallyBecomesBrownMaclayTarget → ⊥
fullSelectedSU2StressDoesNotBecomeBrownMaclayTarget ()

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
    u1RestrictedSelectedQFTStressRequired : Bool
    fullSelectedSU2StressIsBrownMaclayTarget : Bool
    symmetryAndTenValuesSeparatedInAttachment : Bool
    symmetricTenComponentBrownMaclayCompilerConsumed : Bool
    componentwiseBrownMaclayEqualityTargetOwned : Bool
    sixteenIndependentBrownMaclayComponentsRequired : Bool

    concreteSelectedGroupHostsCanonicalU1Paid : Bool
    canonicalU1StressRestrictionPaid : Bool
    selectedQFTStressCoordinateSymmetryPaid : Bool
    brownMaclayTenIndependentComponentValuesPaid : Bool
    u1RestrictedSelectedQFTSectorEqualsBrownMaclayPaid : Bool
    allSectorStressAggregationPaid : Bool
    commonActionVariationPaid : Bool
    unifiedQuantumGravityPromoted : Bool

open CasimirU1RecoveredQFTStressAttachmentBoundary public

canonicalCasimirU1RecoveredQFTStressAttachmentBoundary :
  CasimirU1RecoveredQFTStressAttachmentBoundary
canonicalCasimirU1RecoveredQFTStressAttachmentBoundary =
  casimir-u1-recovered-qft-stress-attachment-boundary
    true true true true true false true true true false
    false false false false false false false false

casimirU1RecoveredQFTStressAttachmentReading : String
casimirU1RecoveredQFTStressAttachmentReading =
  "Brown-Maclay is now welded only to the canonical electromagnetic U(1)-restricted stress derived from the selected recovered SU(2) QFT sector, never to the full non-abelian sector stress. The attachment therefore requires: selected SU(2) host; an explicit canonical-U1 stress restriction carrying the field/action/metric-variation/boundary-renormalization semantics; coordinate symmetry of that restricted stress; and ten independent Brown-Maclay values. Those compile to all sixteen restricted-stress components. The full selected QFT sector retains its own shared-stress transport and is not silently replaced by the U(1) subsector."
