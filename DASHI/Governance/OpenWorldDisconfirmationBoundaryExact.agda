module DASHI.Governance.OpenWorldDisconfirmationBoundaryExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION CALIBRATION
--
-- Internal producer pollen:
--   * existing DASHI.Ontology.EpistemicTrit:
--       supported / unresolved / contradicted are distinct epistemic states;
--   * PR #555 / LeanWikidataVerdictBridge:
--       failed/absent observation without a source-matched negative theorem
--       remains unresolved rather than becoming contradiction;
--   * PR #556 / EpistemicAttractorCore:
--       contrary evidence may be reframed, but that transformation requires an
--       explicit reframing witness rather than occurring definitionally;
--   * PR #556 / ContextualCounterpositionEpistemicBridgeExact:
--       local opposition does not imply total worldview inversion.
--
-- No external source is promoted here: this file is a conservative weld of
-- existing repository epistemic semantics.  In particular, a concealment
-- hypothesis is a new proposition requiring its own evidence receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Ontology.EpistemicTrit as Epistemic
import DASHI.Governance.ContextualCounterpositionEpistemicBridgeExact as Counter
import DASHI.Governance.EpistemicAttractorCore as Attractor

------------------------------------------------------------------------
-- Exact trit separation.
------------------------------------------------------------------------

unresolvedIsNotContradicted :
  Epistemic.unresolved ≡ Epistemic.contradicted → ⊥
unresolvedIsNotContradicted ()

unresolvedIsNotSupported :
  Epistemic.unresolved ≡ Epistemic.supported → ⊥
unresolvedIsNotSupported ()

supportedIsNotContradicted :
  Epistemic.supported ≡ Epistemic.contradicted → ⊥
supportedIsNotContradicted ()

------------------------------------------------------------------------
-- Generic open-world verdict.  Absence is not a negative theorem.
------------------------------------------------------------------------

data EvidenceVerdict : Set where
  notObserved certifiedHolds certifiedRefuted : EvidenceVerdict

interpretPositiveProposition : EvidenceVerdict → Epistemic.EpistemicTrit
interpretPositiveProposition notObserved = Epistemic.unresolved
interpretPositiveProposition certifiedHolds = Epistemic.supported
interpretPositiveProposition certifiedRefuted = Epistemic.contradicted

absenceRemainsUnresolved :
  interpretPositiveProposition notObserved ≡ Epistemic.unresolved
absenceRemainsUnresolved = refl

explicitRefutationIsContradicted :
  interpretPositiveProposition certifiedRefuted ≡ Epistemic.contradicted
explicitRefutationIsContradicted = refl

absenceCannotBeReadAsRefutation :
  interpretPositiveProposition notObserved ≡ Epistemic.contradicted → ⊥
absenceCannotBeReadAsRefutation ()

------------------------------------------------------------------------
-- Concealment is a distinct hypothesis.  An absence observation does not
-- manufacture a concealment witness; a downstream case must supply evidence
-- supporting the concealment proposition itself.
------------------------------------------------------------------------

record ConcealmentEvidenceSystem : Set₁ where
  constructor concealmentEvidenceSystem
  field
    Evidence : Set
    supportsConcealment : Evidence → Set

open ConcealmentEvidenceSystem public

record ConcealmentSupport
  (S : ConcealmentEvidenceSystem) : Set₁ where
  constructor concealmentSupport
  field
    evidence : Evidence S
    evidenceSupportsConcealment : supportsConcealment S evidence

-- Constructorless token for the forbidden automatic promotion.
data AbsenceAlonePromotesConcealmentSupport : Set where

absenceAloneDoesNotPromoteToConcealmentSupport :
  AbsenceAlonePromotesConcealmentSupport → ⊥
absenceAloneDoesNotPromoteToConcealmentSupport ()

------------------------------------------------------------------------
-- Cross-check the two existing anti-collapse boundaries.
------------------------------------------------------------------------

localCriticismStillDoesNotBecomeGlobalNegation :
  Counter.ContextualCounterpositionGovernanceBoundary.localCriticismEqualsGlobalNegation
    Counter.canonicalContextualCounterpositionGovernanceBoundary
  ≡ false
localCriticismStillDoesNotBecomeGlobalNegation = refl

contraryEvidenceStillNeedsReframingReceipt :
  Attractor.CausalResolutionBoundary.contraryEvidenceMayBeReframedWithoutReceipt
    Attractor.canonicalCausalResolutionBoundary
  ≡ false
contraryEvidenceStillNeedsReframingReceipt = refl

------------------------------------------------------------------------
-- The self-sealing move can now be isolated exactly as an extra promotion:
--
--   unresolved/absent observation
--          --[new concealment evidence required]-->
--   support for concealment hypothesis.
--
-- It is not part of the epistemic trit semantics itself.
------------------------------------------------------------------------

record OpenWorldDisconfirmationBoundary : Set where
  constructor openWorldDisconfirmationBoundary
  field
    absenceEqualsContradiction : Bool
    unresolvedEqualsNegation : Bool
    absenceAutomaticallySupportsConcealment : Bool
    explicitNegativeEvidenceMayContradict : Bool
    concealmentNeedsOwnEvidence : Bool
    localOppositionEqualsGlobalInversion : Bool

canonicalOpenWorldDisconfirmationBoundary :
  OpenWorldDisconfirmationBoundary
canonicalOpenWorldDisconfirmationBoundary =
  openWorldDisconfirmationBoundary
    false
    false
    false
    true
    true
    false
