module DASHI.Chemistry.AttributedGoldReactionReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.GoldReactionReplaySuiteExact as Gold
import DASHI.Chemistry.LineageCalibrationAttributionEnvelopeExact as Attribution

------------------------------------------------------------------------
-- ATTRIBUTED GOLD REPLAY COMPOSITION
--
-- The replay is a DASHI composition over source-paid coordinates.  It retains
-- source identity and role without transferring authorship of the composition
-- to the source or erasing source ownership of empirical observations.
------------------------------------------------------------------------

record AttributedGoldReplay : Set₁ where
  constructor attributedGoldReplay
  field
    replay : Gold.GoldReactionReplay
    attributionEnvelope : Attribution.ReplayAttributionEnvelope
    replayConstructionOwner : String
    sourceObservationOwnerReference : String
    sourceRoleReference : String
    locatorReference : String
    unpaidResidualReference : String
    sourceOwnsReplayComposition : Bool
    sourceOwnsReplayCompositionIsFalse : sourceOwnsReplayComposition ≡ false
    replayCompositionErasesSourceIdentity : Bool
    replayCompositionErasesSourceIdentityIsFalse : replayCompositionErasesSourceIdentity ≡ false
    replayImportsSourceProof : Bool
    replayImportsSourceProofIsFalse : replayImportsSourceProof ≡ false

open AttributedGoldReplay public

chlorAttributedReplay : AttributedGoldReplay
chlorAttributedReplay =
  attributedGoldReplay
    Gold.chlorAlkaliReplay
    Attribution.chlorEnvelope
    "DASHI.Chemistry.GoldReactionReplaySuiteExact + lineage hyperfabric"
    "Euro Chlor / source-atlas observation ownership retained"
    "technical/institutional process source"
    "process/electrode-reaction locator; exact numeric locator separately payable"
    "plant-specific kinetics, potentials, current density and interfacial structure"
    false refl false refl false refl

pahAttributedReplay : AttributedGoldReplay
pahAttributedReplay =
  attributedGoldReplay
    Gold.pahReplay
    Attribution.pahEnvelope
    "DASHI lineage replay composition"
    "Roberts/Fitzpatrick mechanism review owns review-level mechanism statements"
    "review synthesis"
    "article-level mechanism locator; PAH-specific atom-map locator unpaid"
    "isotope map, catalytic intermediates and assay kinetics"
    false refl false refl false refl

dhprAttributedReplay : AttributedGoldReplay
dhprAttributedReplay =
  attributedGoldReplay
    Gold.dhprReplay
    Attribution.dhprEnvelope
    "DASHI lineage/redox replay composition"
    "BRENDA reaction-identity ownership retained"
    "curated reaction database"
    "EC 1.5.1.34 reaction identity; numeric assay rows unpaid"
    "isotope map, redox potential, kinetic constants and in-vivo flux"
    false refl false refl false refl

pbCaAttributedReplay : AttributedGoldReplay
pbCaAttributedReplay =
  attributedGoldReplay
    Gold.pbCaReplay
    Attribution.pbCaEnvelope
    "DASHI target-relative lineage/discriminator composition"
    "Kirberger/Yang and existing ionic source atlas retain structural observations"
    "primary/source-bounded structural study"
    "article/source-specific coordination observations"
    "same-target affinity, occupancy, kinetics and organism response"
    false refl false refl false refl

carbonAttributedReplay : AttributedGoldReplay
carbonAttributedReplay =
  attributedGoldReplay
    Gold.carbonBondReplay
    Attribution.carbonEnvelope
    "DASHI carbon-vs-alternative reachable-chemistry benchmark"
    "Astrobiology Primer retains broad review/context observations"
    "background primer / review"
    "article-level prebiotic context only"
    "specific reaction identity, yields, atom map, kinetics and matched silicon comparison"
    false refl false refl false refl

canonicalAttributedGoldReplays : List AttributedGoldReplay
canonicalAttributedGoldReplays =
  chlorAttributedReplay
  ∷ pahAttributedReplay
  ∷ dhprAttributedReplay
  ∷ pbCaAttributedReplay
  ∷ carbonAttributedReplay
  ∷ []

record AttributedGoldReplayBoundary : Set where
  constructor attributedGoldReplayBoundary
  field
    sourceOwnsReplayComposition : Bool
    sourceOwnsReplayCompositionIsFalse : sourceOwnsReplayComposition ≡ false
    replayCompositionErasesSourceIdentity : Bool
    replayCompositionErasesSourceIdentityIsFalse : replayCompositionErasesSourceIdentity ≡ false
    replayCompositionCreatesScientificAuthority : Bool
    replayCompositionCreatesScientificAuthorityIsFalse :
      replayCompositionCreatesScientificAuthority ≡ false
    unpaidCoordinatesRemainAttributed : Bool
    unpaidCoordinatesRemainAttributedIsTrue : unpaidCoordinatesRemainAttributed ≡ true
    dashiAndExternalOwnershipRemainDistinct : Bool
    dashiAndExternalOwnershipRemainDistinctIsTrue :
      dashiAndExternalOwnershipRemainDistinct ≡ true

open AttributedGoldReplayBoundary public

canonicalAttributedGoldReplayBoundary : AttributedGoldReplayBoundary
canonicalAttributedGoldReplayBoundary =
  attributedGoldReplayBoundary false refl false refl false refl true refl true refl
