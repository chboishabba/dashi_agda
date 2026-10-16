module DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact as Host

------------------------------------------------------------------------
-- SELECTED SU(2) QFT STRESS -> CANONICAL ELECTROMAGNETIC U(1) RESTRICTION
--
-- Brown-Maclay is an electromagnetic U(1) stress.  The full stress tensor of a
-- non-abelian selected SU(2) sector is therefore NOT the Brown-Maclay target.
-- The missing object is the stress obtained after restricting that SAME sector
-- to the canonical Cartan/U(1) electromagnetic subsector and commuting that
-- restriction through the action/metric-variation/renormalisation pipeline.
--
-- The current repository owns the group/Lie-algebra U(1) embedding and the
-- vanishing bracket on that image, but not a theorem that this restriction of
-- the quantum action/stress is Maxwell/Brown-Maclay.  This owner types exactly
-- that seam without manufacturing it.
------------------------------------------------------------------------

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

    -- Typed semantic payments.  The carrier map above alone is not physics.
    CanonicalCartanU1FieldRestriction : Set
    canonicalCartanU1FieldRestriction : CanonicalCartanU1FieldRestriction

    NonAbelianCommutatorVanishesOnRestrictedField : Set
    nonAbelianCommutatorVanishesOnRestrictedField :
      NonAbelianCommutatorVanishesOnRestrictedField

    YangMillsActionRestrictsToMaxwellAction : Set
    yangMillsActionRestrictsToMaxwellAction :
      YangMillsActionRestrictsToMaxwellAction

    MetricVariationCommutesWithU1Restriction : Set
    metricVariationCommutesWithU1Restriction :
      MetricVariationCommutesWithU1Restriction

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

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FullSelectedSU2StressAutomaticallyEqualsBrownMaclay : Set where
data U1GaugeEmbeddingAutomaticallyClosesStressRestriction : Set where
data VanishingLieBracketAutomaticallyProvesActionRestriction : Set where

fullSelectedSU2StressDoesNotAutomaticallyEqualBrownMaclay :
  FullSelectedSU2StressAutomaticallyEqualsBrownMaclay → ⊥
fullSelectedSU2StressDoesNotAutomaticallyEqualBrownMaclay ()

u1GaugeEmbeddingDoesNotCloseStressRestriction :
  U1GaugeEmbeddingAutomaticallyClosesStressRestriction → ⊥
u1GaugeEmbeddingDoesNotCloseStressRestriction ()

vanishingLieBracketDoesNotProveActionRestriction :
  VanishingLieBracketAutomaticallyProvesActionRestriction → ⊥
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

canonicalCasimirU1RestrictedSelectedQFTStressBoundary :
  CasimirU1RestrictedSelectedQFTStressBoundary
canonicalCasimirU1RestrictedSelectedQFTStressBoundary =
  casimir-u1-restricted-selected-qft-stress-boundary
    true false false
    false false false false false false

casimirU1RestrictedSelectedQFTStressReading : String
casimirU1RestrictedSelectedQFTStressReading =
  "Brown-Maclay targets the canonical electromagnetic U(1)-restricted stress of the selected SU(2) QFT sector, not the full non-abelian SU(2) stress. The repo already owns the U(1) group/Lie-algebra embedding, but the physical restriction still requires the same Cartan field restriction, vanishing non-abelian contribution on that field, YM-action -> Maxwell-action restriction, commutation of restriction with metric variation/stress construction, identification of the restricted quantum stress as Maxwell stress, and the same conducting-plate boundary plus renormalization prescription. Only that restricted stress may subsequently be welded componentwise to Brown-Maclay."
