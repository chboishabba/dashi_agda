module DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact as Host

record CasimirCanonicalU1StressRestriction
    (U : Weld.UnifiedCandidate)
    (candidate : Weld.Candidate U)
    (regime : Weld.Regime U)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    (host : Host.CasimirSelectedQFTSU2Host U group) : Set₁ where
  field
    restrictStressToCanonicalU1 :
      QFT.StressTensor (Weld.qftCarriers U) →
      QFT.StressTensor (Weld.qftCarriers U)

    CanonicalCartanU1FieldRestriction : Set
    canonicalCartanU1FieldRestriction : CanonicalCartanU1FieldRestriction

    NonAbelianCommutatorVanishesOnRestrictedField : Set
    nonAbelianCommutatorVanishesOnRestrictedField :
      NonAbelianCommutatorVanishesOnRestrictedField

    YangMillsActionRestrictsToMaxwellAction : Set
    yangMillsActionRestrictsToMaxwellAction : YangMillsActionRestrictsToMaxwellAction

    MetricVariationCommutesWithU1Restriction : Set
    metricVariationCommutesWithU1Restriction : MetricVariationCommutesWithU1Restriction

    RestrictedStressIsMaxwellStress : Set
    restrictedStressIsMaxwellStress : RestrictedStressIsMaxwellStress

    SameConductingPlateBoundaryObject : Set
    sameConductingPlateBoundaryObject : SameConductingPlateBoundaryObject

    SameRenormalizationPrescription : Set
    sameRenormalizationPrescription : SameRenormalizationPrescription

    reading : String

open CasimirCanonicalU1StressRestriction public

fullSelectedQFTStress :
  ∀ {U : Weld.UnifiedCandidate}
    {candidate : Weld.Candidate U}
    {regime : Weld.Regime U}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)}
    {host : Host.CasimirSelectedQFTSU2Host U group} →
  CasimirCanonicalU1StressRestriction U candidate regime group host →
  QFT.StressTensor (Weld.qftCarriers U)
fullSelectedQFTStress {U} {candidate} {regime} {group} restriction =
  Weld.actualQFTStressTensor U (Weld.coarseGrain U candidate regime) group

u1RestrictedSelectedQFTStress :
  ∀ {U : Weld.UnifiedCandidate}
    {candidate : Weld.Candidate U}
    {regime : Weld.Regime U}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)}
    {host : Host.CasimirSelectedQFTSU2Host U group} →
  (restriction : CasimirCanonicalU1StressRestriction U candidate regime group host) →
  QFT.StressTensor (Weld.qftCarriers U)
u1RestrictedSelectedQFTStress restriction =
  restrictStressToCanonicalU1 restriction (fullSelectedQFTStress restriction)

data FullSelectedSU2StressAutomaticallyEqualsBrownMaclay : Set where
data U1GaugeEmbeddingAutomaticallyClosesStressRestriction : Set where
data VanishingLieBracketAutomaticallyProvesActionRestriction : Set where

fullSelectedSU2StressDoesNotAutomaticallyEqualBrownMaclay : FullSelectedSU2StressAutomaticallyEqualsBrownMaclay → ⊥
fullSelectedSU2StressDoesNotAutomaticallyEqualBrownMaclay ()
u1GaugeEmbeddingDoesNotCloseStressRestriction : U1GaugeEmbeddingAutomaticallyClosesStressRestriction → ⊥
u1GaugeEmbeddingDoesNotCloseStressRestriction ()
vanishingLieBracketDoesNotProveActionRestriction : VanishingLieBracketAutomaticallyProvesActionRestriction → ⊥
vanishingLieBracketDoesNotProveActionRestriction ()

record CasimirU1RestrictedSelectedQFTStressBoundary : Set where
  constructor casimir-u1-restricted-selected-qft-stress-boundary
  field
    u1RestrictedSelectedQFTStressInterfaceOwned : Bool
    fullSelectedSU2StressIsBrownMaclayTarget : Bool
    u1GaugeEmbeddingAloneClosesStressRestriction : Bool

    cartanU1FieldRestrictionPaid : Bool
    nonAbelianCommutatorRestrictionPaid : Bool
    yangMillsActionToMaxwellRestrictionPaid : Bool
    metricVariationStressRestrictionPaid : Bool
    restrictedStressIsMaxwellStressPaid : Bool
    sameBoundaryRenormalizedU1StressPaid : Bool

open CasimirU1RestrictedSelectedQFTStressBoundary public

canonicalCasimirU1RestrictedSelectedQFTStressBoundary : CasimirU1RestrictedSelectedQFTStressBoundary
canonicalCasimirU1RestrictedSelectedQFTStressBoundary =
  casimir-u1-restricted-selected-qft-stress-boundary
    true false false
    false false false false false false

data RemainingCanonicalU1StressRestrictionBlocker : Set where
  missingCanonicalCartanU1FieldRestriction : RemainingCanonicalU1StressRestrictionBlocker
  missingRestrictedFieldNonAbelianCommutatorVanishing : RemainingCanonicalU1StressRestrictionBlocker
  missingYangMillsActionToMaxwellRestriction : RemainingCanonicalU1StressRestrictionBlocker
  missingMetricVariationStressRestriction : RemainingCanonicalU1StressRestrictionBlocker
  missingRestrictedQuantumStressMaxwellIdentification : RemainingCanonicalU1StressRestrictionBlocker
  missingSamePlateBoundaryRenormalization : RemainingCanonicalU1StressRestrictionBlocker

firstU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
firstU1RestrictionBlocker = missingCanonicalCartanU1FieldRestriction
secondU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
secondU1RestrictionBlocker = missingRestrictedFieldNonAbelianCommutatorVanishing
thirdU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
thirdU1RestrictionBlocker = missingYangMillsActionToMaxwellRestriction
fourthU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
fourthU1RestrictionBlocker = missingMetricVariationStressRestriction
fifthU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
fifthU1RestrictionBlocker = missingRestrictedQuantumStressMaxwellIdentification
sixthU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
sixthU1RestrictionBlocker = missingSamePlateBoundaryRenormalization

casimirU1RestrictedSelectedQFTStressReading : String
casimirU1RestrictedSelectedQFTStressReading =
  "Brown-Maclay targets the canonical electromagnetic U(1)-restricted stress, not the full selected SU(2) stress. The restriction max-cut is now explicit: first identify the selected continuum field/configuration as the canonical Cartan-U(1) field; then prove the non-abelian commutator contribution vanishes on that SAME restricted field; prove the selected YM action restricts to Maxwell; prove restriction commutes with metric variation/stress construction; identify the resulting restricted quantum stress as Maxwell stress; and finally weld the same conducting-plate boundary and renormalization prescription. Only after those six payments can Brown-Maclay component values be a same-object target."
