module DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2Lie
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as U1YM
import DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact as Host

------------------------------------------------------------------------
-- CANONICAL CARTAN-U(1) FIELD IMAGE RECEIPT
--
-- Once a selected Lie-algebra-valued field is proved pointwise to lie in the
-- existing U(1) Cartan image, the non-abelian bracket term vanishes by the
-- already-proved U1AsSU2AbelianRestrictionExact theorem.  No independent
-- commutator-vanishing theorem is then admissible.
------------------------------------------------------------------------

record CanonicalCartanU1FieldImageReceipt
    (SelectedField : Set)
    (selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra) : Set₁ where
  field
    phase : SelectedField → U1YM.U1LieAlgebra
    selectedLieValueIsEmbedded :
      ∀ field →
      selectedLieValue field ≡ U1YM.embedU1Lie (phase field)

open CanonicalCartanU1FieldImageReceipt public

restrictedFieldBracketZero :
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra} →
  (receipt : CanonicalCartanU1FieldImageReceipt SelectedField selectedLieValue) →
  ∀ left right →
  Bracket.lieBracket (selectedLieValue left) (selectedLieValue right)
  ≡ SU2Lie.lieZero
restrictedFieldBracketZero receipt left right =
  trans
    (cong₂ Bracket.lieBracket
      (selectedLieValueIsEmbedded receipt left)
      (selectedLieValueIsEmbedded receipt right))
    (U1YM.u1EmbeddedLieBracketZero
      (phase receipt left)
      (phase receipt right))

------------------------------------------------------------------------
-- U(1)-RESTRICTED SELECTED-QFT STRESS
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

    CanonicalCartanU1FieldRestriction : Set
    canonicalCartanU1FieldRestriction : CanonicalCartanU1FieldRestriction

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
data U1GaugeArchitectureAutomaticallyClosesStressRestriction : Set where
data VanishingLieBracketAutomaticallyProvesActionRestriction : Set where

fullSelectedSU2StressDoesNotAutomaticallyEqualBrownMaclay : FullSelectedSU2StressAutomaticallyEqualsBrownMaclay → ⊥
fullSelectedSU2StressDoesNotAutomaticallyEqualBrownMaclay ()
u1GaugeEmbeddingDoesNotCloseStressRestriction : U1GaugeArchitectureAutomaticallyClosesStressRestriction → ⊥
u1GaugeEmbeddingDoesNotCloseStressRestriction ()
vanishingLieBracketDoesNotProveActionRestriction : VanishingLieBracketAutomaticallyProvesActionRestriction → ⊥
vanishingLieBracketDoesNotProveActionRestriction ()

record CasimirU1RestrictedSelectedQFTStressBoundary : Set where
  constructor casimir-u1-restricted-selected-qft-stress-boundary
  field
    u1RestrictedSelectedQFTStressInterfaceOwned : Bool
    fullSelectedSU2StressIsBrownMaclayTarget : Bool
    u1GaugeEmbeddingAloneClosesStressRestriction : Bool

    canonicalCartanU1FieldImageReceiptOwned : Bool
    restrictedFieldBracketZeroCompilerOwned : Bool
    independentCommutatorPaymentRequiredAfterFieldImage : Bool

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
    true true false
    false false false false false false

data RemainingCanonicalU1StressRestrictionBlocker : Set where
  missingCanonicalCartanU1FieldRestriction : RemainingCanonicalU1StressRestrictionBlocker
  missingYangMillsActionToMaxwellRestriction : RemainingCanonicalU1StressRestrictionBlocker
  missingMetricVariationStressRestriction : RemainingCanonicalU1StressRestrictionBlocker
  missingRestrictedQuantumStressMaxwellIdentification : RemainingCanonicalU1StressRestrictionBlocker
  missingSamePlateBoundaryRenormalization : RemainingCanonicalU1StressRestrictionBlocker

firstU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
firstU1RestrictionBlocker = missingCanonicalCartanU1FieldRestriction
secondU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
secondU1RestrictionBlocker = missingYangMillsActionToMaxwellRestriction
thirdU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
thirdU1RestrictionBlocker = missingMetricVariationStressRestriction
fourthU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
fourthU1RestrictionBlocker = missingRestrictedQuantumStressMaxwellIdentification
fifthU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
fifthU1RestrictionBlocker = missingSamePlateBoundaryRenormalization

casimirU1RestrictedSelectedQFTStressReading : String
casimirU1RestrictedSelectedQFTStressReading =
  "Brown-Maclay targets the canonical electromagnetic U(1)-restricted stress, not the full selected SU(2) stress. The first leaf is now a pointwise same-object field-image receipt into the existing Cartan U(1) embedding. Once that receipt is paid, the existing u1EmbeddedLieBracketZero theorem automatically proves vanishing of the non-abelian bracket on the SAME restricted field; no second commutator theorem is required. The remaining independent restriction leaves are YM-action -> Maxwell, commutation of restriction with metric variation/stress construction, restricted quantum stress -> Maxwell stress, and the same conducting-plate boundary/renormalization weld."
