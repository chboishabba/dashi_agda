module DASHI.Governance.BoloBoloDerivedScaleEnvelopeExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Bolo

------------------------------------------------------------------------
-- DASHI-DERIVED ARITHMETIC ENVELOPE FROM SOURCE-REPORTED APPROXIMATE SCALES.
--
-- p.m. reports approximate/descriptive design scales: about 500 per bolo,
-- kana around 15-30, about 20 kana per bolo, and tega as possible confederations
-- of roughly 10-20 bolos.  The multiplied ranges below are DASHI arithmetic
-- scenarios from those source numbers; they are not direct quotations, exact
-- population identities, universal human scales, or empirical optima.
------------------------------------------------------------------------

record DerivedScaleEnvelope : Set where
  constructor derivedScaleEnvelope
  field
    sourceAtlas : Bolo.BoloBoloPrimarySourceAtlas
    kanaBundleLower : Nat
    kanaBundleUpper : Nat
    tegaPopulationLower : Nat
    tegaPopulationUpper : Nat

open DerivedScaleEnvelope public

canonicalDerivedScaleEnvelope : DerivedScaleEnvelope
canonicalDerivedScaleEnvelope =
  derivedScaleEnvelope
    Bolo.canonicalBoloBoloPrimarySourceAtlas
    (Bolo.boloApproximateKanaCount Bolo.canonicalBoloBoloPrimarySourceAtlas
      * Bolo.kanaLowerPopulation Bolo.canonicalBoloBoloPrimarySourceAtlas)
    (Bolo.boloApproximateKanaCount Bolo.canonicalBoloBoloPrimarySourceAtlas
      * Bolo.kanaUpperPopulation Bolo.canonicalBoloBoloPrimarySourceAtlas)
    (Bolo.tegaLowerBoloCount Bolo.canonicalBoloBoloPrimarySourceAtlas
      * Bolo.boloApproximatePopulation Bolo.canonicalBoloBoloPrimarySourceAtlas)
    (Bolo.tegaUpperBoloCount Bolo.canonicalBoloBoloPrimarySourceAtlas
      * Bolo.boloApproximatePopulation Bolo.canonicalBoloBoloPrimarySourceAtlas)

record DerivedScaleBoundary : Set where
  constructor derivedScaleBoundary
  field
    derivedEnvelopeQuotedDirectlyFromSource : Bool
    sourceApproximationTreatedAsExactPopulationIdentity : Bool
    derivedEnvelopeProvesOptimalScale : Bool
    derivedEnvelopeProvesCoordinationEfficiency : Bool
    derivedEnvelopeMayParameterizeCounterfactualScenarios : Bool
    sourceNumbersRetainApproximateStatus : Bool

open DerivedScaleBoundary public

canonicalDerivedScaleBoundary : DerivedScaleBoundary
canonicalDerivedScaleBoundary =
  derivedScaleBoundary false false false false true true

canonicalBoloDerivedScaleEnvelopeReceipt : GenericReceipt.GenericReceipt
canonicalBoloDerivedScaleEnvelopeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo derived scale envelope"
    "DASHI.Governance.BoloBoloDerivedScaleEnvelopeExact"
    "canonicalDerivedScaleEnvelope / canonicalDerivedScaleBoundary"
    "derives arithmetic scenario envelopes 300-600 for twenty 15-30-person kana and approximately 5000-10000 for ten-to-twenty approximately-500-person bolos, while retaining the source atlas as the provenance anchor"
    "the multiplied envelopes are DASHI derivations rather than source quotations; approximate source numbers are not exact population identities, empirical optima, or evidence of coordination efficiency, though they may parameterize later counterfactual simulations"
    "agda -i . DASHI/Governance/BoloBoloDerivedScaleEnvelopeRegression.agda"
