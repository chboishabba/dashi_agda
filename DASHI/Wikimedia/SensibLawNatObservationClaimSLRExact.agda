module DASHI.Wikimedia.SensibLawNatObservationClaimSLRExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Wikimedia.SensibLawBoundaryArtifactMorphismExact as Morph
import DASHI.Wikimedia.SensibLawNatClimateSLRFixtureExact as Nat
import DASHI.Wikimedia.SensibLawNatClimateReviewHandoffExact as Climate
import DASHI.Wikimedia.SLRWikimediaHandoffABIExact as SLR

------------------------------------------------------------------------
-- NAT SOURCE UNIT -> OBSERVATION CLAIM -> SLR
--
-- This is the pre-review-packet ABI.  The observation remains a candidate
-- extracted from bounded anchors; it does not resolve P5991/P14143 equivalence.
------------------------------------------------------------------------

natMigrationObservation : Morph.ObservationClaimPayload
natMigrationObservation =
  Morph.observation-claim-payload
    "nat:p5991-p14143:observation:migration-proposal"
    Nat.natSourceUnit
    ("goal" ∷ "qualifier_family" ∷ "reference_family" ∷ "query_anchor" ∷ [])
    Nat.natSandboxQid
    "candidate migration relation P5991 -> P14143"
    "annual-greenhouse-gas-emissions target semantics remain statement-bundle dependent"
    ("P459" ∷ "P3831" ∷ "P518" ∷ "P580" ∷ "P582" ∷ [])
    Climate.expectedNatReferences
    Morph.unresolvedPolarity
    "candidate observation from a revision-locked user-sandbox proposal; not migration confidence"
    "SensibLaw sl.source_unit.v1 -> ObservationClaimPayload bounded extraction"

natObservationExtraction : Morph.ObservationExtractionReceipt
natObservationExtraction =
  Morph.observation-extraction-receipt
    natMigrationObservation
    Morph.extractObservation
    refl
    true refl
    true refl
    false refl
    "Nat bounded source-unit observation extraction; provenance and anchors preserved"

natObservationCreatesNoWorldTruth :
  Morph.createsWorldTruth natObservationExtraction ≡ false
natObservationCreatesNoWorldTruth = refl

natObservationSlrHandoff : SLR.SlrObservationHandoffReceipt
natObservationSlrHandoff = SLR.observationToSlr natObservationExtraction

natObservationSlrSourceUnitExact :
  SLR.sourceUnitReference natObservationSlrHandoff
  ≡ "unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01"
natObservationSlrSourceUnitExact = refl

natObservationSlrNoAuthority :
  SLR.slrOwnsSourceAuthority natObservationSlrHandoff ≡ false
natObservationSlrNoAuthority = refl

natObservationSlrNoPromotion :
  SLR.slrOwnsSemanticPromotion natObservationSlrHandoff ≡ false
natObservationSlrNoPromotion = refl

-- Extraction gives SLR a deterministic candidate carrier, not a reviewed
-- migration disposition.  Review/promotion remain later governed morphisms.
data ObservationExtractionMeansMigrationSafe : Set where

aObservationDoesNotMeanMigrationSafe : ObservationExtractionMeansMigrationSafe → ⊥
aObservationDoesNotMeanMigrationSafe ()
