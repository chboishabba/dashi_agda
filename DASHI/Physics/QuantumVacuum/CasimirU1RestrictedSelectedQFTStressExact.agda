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
-- SAME-OBJECT SELECTED-QFT FIELD REALIZATION
--
-- The field-image theorem above is intentionally generic mathematics.  It does
-- not identify a caller-supplied field with the field of the selected recovered
-- QFT sector.  The current physical payment is therefore indexed by the same
-- unified candidate/candidate/regime/group/host and explicitly carries a
-- same-object witness before the Cartan image receipt may be consumed.
------------------------------------------------------------------------

record SelectedQFTCartanFieldRealization
    (U : Weld.UnifiedCandidate)
    (candidate : Weld.Candidate U)
    (regime : Weld.Regime U)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    (host : Host.CasimirSelectedQFTSU2Host U group) : Set₁ where
  field
    SelectedField : Set
    selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra

    SameSelectedQFTField : Set
    sameSelectedQFTField : SameSelectedQFTField

    cartanImage :
      CanonicalCartanU1FieldImageReceipt SelectedField selectedLieValue

    reading : String

open SelectedQFTCartanFieldRealization public

selectedQFTFieldBracketZero :
  ∀ {U candidate regime group host} →
  (realization :
    SelectedQFTCartanFieldRealization U candidate regime group host) →
  ∀ left right →
  Bracket.lieBracket
    (selectedLieValue realization left)
    (selectedLieValue realization right)
  ≡ SU2Lie.lieZero
selectedQFTFieldBracketZero realization =
  restrictedFieldBracketZero (cartanImage realization)

------------------------------------------------------------------------
-- U(1)-RESTRICTED SELECTED-QFT STRESS
--
-- Compatibility record retained for older downstream consumers.  Its opaque
-- action/variation/boundary Set sockets are no longer the authoritative
-- max-cut: dedicated theorem-bearing action, variation, stress-readout and
-- mode-renormalization owners supersede them.
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
data ArbitraryCartanReceiptAutomaticallyIdentifiesSelectedQFTField : Set where

fullSelectedSU2StressDoesNotAutomaticallyEqualBrownMaclay :
  FullSelectedSU2StressAutomaticallyEqualsBrownMaclay → ⊥
fullSelectedSU2StressDoesNotAutomaticallyEqualBrownMaclay ()

u1GaugeEmbeddingDoesNotCloseStressRestriction :
  U1GaugeArchitectureAutomaticallyClosesStressRestriction → ⊥
u1GaugeEmbeddingDoesNotCloseStressRestriction ()

vanishingLieBracketDoesNotProveActionRestriction :
  VanishingLieBracketAutomaticallyProvesActionRestriction → ⊥
vanishingLieBracketDoesNotProveActionRestriction ()

arbitraryCartanReceiptDoesNotIdentifySelectedQFTField :
  ArbitraryCartanReceiptAutomaticallyIdentifiesSelectedQFTField → ⊥
arbitraryCartanReceiptDoesNotIdentifySelectedQFTField ()

record CasimirU1RestrictedSelectedQFTStressBoundary : Set where
  constructor casimir-u1-restricted-selected-qft-stress-boundary
  field
    u1RestrictedSelectedQFTStressInterfaceOwned : Bool
    fullSelectedSU2StressIsBrownMaclayTarget : Bool
    u1GaugeEmbeddingAloneClosesStressRestriction : Bool

    canonicalCartanU1FieldImageReceiptOwned : Bool
    selectedQFTCartanFieldRealizationInterfaceOwned : Bool
    restrictedFieldBracketZeroCompilerOwned : Bool
    independentCommutatorPaymentRequiredAfterFieldImage : Bool

    legacyOpaqueActionStressSocketsAreAuthoritative : Bool
    dedicatedActionVariationCompilerPreferred : Bool

    selectedQFTCartanFieldRealizationPaid : Bool

    -- Compatibility status retained for older readers.
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
    true true true false
    false true
    false
    false false false false false false

data RemainingCanonicalU1StressRestrictionBlocker : Set where
  missingSelectedQFTCartanFieldRealization : RemainingCanonicalU1StressRestrictionBlocker

  -- Legacy compatibility constructors: downstream theorem-bearing owners now
  -- refine these names, so they are not the authoritative ordering here.
  missingCanonicalCartanU1FieldRestriction : RemainingCanonicalU1StressRestrictionBlocker
  missingYangMillsActionToMaxwellRestriction : RemainingCanonicalU1StressRestrictionBlocker
  missingMetricVariationStressRestriction : RemainingCanonicalU1StressRestrictionBlocker
  missingRestrictedQuantumStressMaxwellIdentification : RemainingCanonicalU1StressRestrictionBlocker
  missingSamePlateBoundaryRenormalization : RemainingCanonicalU1StressRestrictionBlocker

firstU1RestrictionBlocker : RemainingCanonicalU1StressRestrictionBlocker
firstU1RestrictionBlocker = missingSelectedQFTCartanFieldRealization

casimirU1RestrictedSelectedQFTStressReading : String
casimirU1RestrictedSelectedQFTStressReading =
  "The Cartan field-image theorem is generic algebra, not by itself a selected-QFT field theorem. The live payment is now SelectedQFTCartanFieldRealization, indexed by the same unified candidate/candidate/regime/group/host and carrying an explicit same-object witness plus the existing Cartan image receipt. Once supplied, bracket-zero compiles automatically. The older opaque action/variation/stress/boundary Set sockets remain compatibility-only; dedicated action-density, metric-variation, selected-stress-readout and mode-renormalization owners are authoritative."
