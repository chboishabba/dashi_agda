module DASHI.Cognition.ClinicToStreetsSensibLawProvenanceCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Cognition.ClinicToStreetsCausalProvenanceExact as CTS
import DASHI.Cognition.PNF.SensibLawProvenanceSemanticStatusOrthogonalityExact as S

------------------------------------------------------------------------
-- CROSS-POLLINATION: SOURCE PROVENANCE != SEMANTIC TRUTH
--
-- SensibLaw already has the stronger generic rule that external-source
-- provenance and semantic truth/status are independent coordinates.  Reuse it
-- here so the reel/book attribution boundary is not a bespoke exception.
------------------------------------------------------------------------

externalSourceAttributionStillDoesNotAdmitTruth :
  S.ExternalSourceClaimImpliesTruthAdmitted → ⊥
externalSourceAttributionStillDoesNotAdmitTruth =
  S.externalSourceDoesNotAdmitTruth

inheritedProvenanceStatusBoundary :
  S.ProvenanceSemanticStatusOrthogonalityBoundary
inheritedProvenanceStatusBoundary =
  S.canonicalProvenanceSemanticStatusOrthogonalityBoundary

record ClinicToStreetsSensibLawReceipt : Set where
  constructor clinic-to-streets-sensiblaw-receipt
  field
    reelClaimTypedAsAttributed : Bool
    attributionCreatesTruth : Bool
    provenanceAxisRetained : Bool
    semanticStatusAxisIndependent : Bool

canonicalClinicToStreetsSensibLawReceipt : ClinicToStreetsSensibLawReceipt
canonicalClinicToStreetsSensibLawReceipt =
  clinic-to-streets-sensiblaw-receipt true false true true
