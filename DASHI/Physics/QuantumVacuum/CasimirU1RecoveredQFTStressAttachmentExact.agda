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

------------------------------------------------------------------------
-- CASIMIR U(1) -> ACTUAL RECOVERED-QFT SELECTED-SECTOR STRESS ATTACHMENT
--
-- The pinned-YM GR/QFT max-cut established the correct theorem shape:
-- first identify one literal/recovered QFT construction, then its stress is the
-- actual selected QFT stress; only after that does all-sector aggregation enter.
--
-- Casimir is an electromagnetic U(1) effect.  The live donor already pays the
-- group/Lie-algebra architectural statement that U(1) is an abelian restriction
-- inside the repository SU(2)/Yang-Mills architecture.  That does NOT identify
-- a particular compact-simple QFT sector in an arbitrary UnifiedCandidate and
-- does NOT identify its actual recovered stress with Brown-Maclay.
--
-- This owner therefore makes the first real same-object unification payment
-- literal and componentwise:
--
--   actual selected QFT sector stress
--      -- rational component evaluator --> T_ab
--      == normalized Brown-Maclay T_ab  for every Axis4 pair.
--
-- Once this attachment is inhabited, the existing qftSectorStressToShared map
-- can transport that already-selected actual QFT stress into the shared carrier.
-- It still does not pay total all-sector aggregation, common-action variation,
-- the GR stress equality, backreaction, or physical promotion.
------------------------------------------------------------------------

record CasimirU1RecoveredQFTStressAttachment
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    candidate : Weld.Candidate U
    regime : Weld.Regime U
    qftAtRegime : Weld.qftRegime U regime
    qftRecovery : Weld.QFTRecoveryReceipt U

    selectedGroup : QFT.CompactSimpleGroup (Weld.qftCarriers U)

    SelectedGroupHostsCanonicalU1Restriction : Set
    selectedGroupHostsCanonicalU1Restriction :
      SelectedGroupHostsCanonicalU1Restriction

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
    true true true true
    false false false false false

casimirU1RecoveredQFTStressAttachmentReading : String
casimirU1RecoveredQFTStressAttachmentReading =
  "The first Casimir GR/QFT unification stress leaf is now explicit: choose the actual recovered-QFT compact-simple sector that hosts the canonical electromagnetic U(1) restriction, provide a rational evaluator for its actual selected QFT stress, and prove every Axis4 component equals the normalized Brown-Maclay tensor on the same boundary/renormalization object. The existing qftSectorStressToShared map then transports that selected stress into the shared carrier. This attachment does not pay all-sector aggregation, common-action variation, GR stress equality, backreaction, or unified-QG promotion."
