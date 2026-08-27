module DASHI.Foundations.Wette1969CompletenessInterpretationBridgeExact where

------------------------------------------------------------------------
-- WETTE 1969 COMPLETENESS CLAIMS -> GENERIC INTERPRETATION GEOMETRY
--
-- Primary source:
-- Eduard Wette, "Definition eines (relativ vollständigen) formalen Systems
-- konstruktiver Arithmetik", 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Secondary audit:
-- G. Kreisel and J. Zucker, JSL 37(1), 1972, pp. 203--204.
-- DOI: 10.2307/2272630
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DeductionIndexedInterpretationExact as Indexed
import DASHI.Foundations.Wette1969PrimaryTextExtractionExact as Primary

------------------------------------------------------------------------
-- Classification, not certification.
------------------------------------------------------------------------

data InterpretationShape : Set where
  formulaIndependentFiniteTranslation : InterpretationShape
  deductionIndexedFiniteReinterpretation : InterpretationShape

shapeOf : Primary.Wette1969CompletenessClaim → InterpretationShape
shapeOf claim with Primary.kind claim
... | Primary.transfiniteCompleteness = formulaIndependentFiniteTranslation
... | Primary.exorbitantCompleteness = deductionIndexedFiniteReinterpretation

hauptsatz1Shape : InterpretationShape
hauptsatz1Shape = shapeOf Primary.hauptsatz1Claim

hauptsatz2Shape : InterpretationShape
hauptsatz2Shape = shapeOf Primary.hauptsatz2Claim

------------------------------------------------------------------------
-- Why Hauptsatz 2 cannot be silently collapsed into the existing formula-only
-- proof-translation interface.
--
-- Wette says on printed p.181 that the substitution domain required for the
-- reinterpretation depends on the Ausgangsdeduktion d<.  Kreisel--Zucker then
-- emphasize that the interpretation of a formula depends on the deduction in
-- which it occurs, and distinguish pointwise success for each deduction from
-- one internal theorem asserting the result uniformly for all deductions.
------------------------------------------------------------------------

record Wette1969CompletenessInterpretationBoundary : Set where
  constructor wette1969CompletenessInterpretationBoundary
  field
    hauptsatz1IsClaimedFiniteDeductionTranslation : Bool
    hauptsatz1IsClaimedFiniteDeductionTranslationIsTrue :
      hauptsatz1IsClaimedFiniteDeductionTranslation ≡ true

    hauptsatz2IsClaimedDeductionIndexedReinterpretation : Bool
    hauptsatz2IsClaimedDeductionIndexedReinterpretationIsTrue :
      hauptsatz2IsClaimedDeductionIndexedReinterpretation ≡ true

    hauptsatz2IsDefinitionallyFormulaOnlyTranslation : Bool
    hauptsatz2IsDefinitionallyFormulaOnlyTranslationIsFalse :
      hauptsatz2IsDefinitionallyFormulaOnlyTranslation ≡ false

    sourceClaimIsAlreadyPointwiseProofCertificate : Bool
    sourceClaimIsAlreadyPointwiseProofCertificateIsFalse :
      sourceClaimIsAlreadyPointwiseProofCertificate ≡ false

    pointwiseHistoricalClaimIsAlreadyUniformInternalization : Bool
    pointwiseHistoricalClaimIsAlreadyUniformInternalizationIsFalse :
      pointwiseHistoricalClaimIsAlreadyUniformInternalization ≡ false

    kreiselZuckerCertifyExactHistoricalInterpretation : Bool
    kreiselZuckerCertifyExactHistoricalInterpretationIsFalse :
      kreiselZuckerCertifyExactHistoricalInterpretation ≡ false

canonicalWette1969CompletenessInterpretationBoundary :
  Wette1969CompletenessInterpretationBoundary
canonicalWette1969CompletenessInterpretationBoundary =
  wette1969CompletenessInterpretationBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Generic owner aliases: these make the architectural destination explicit.
------------------------------------------------------------------------

deductionIndexedSpecOwner : Set₁
deductionIndexedSpecOwner = Indexed.DeductionIndexedInterpretationSpec

certifiedDeductionIndexedOwner : Set₁
certifiedDeductionIndexedOwner = Indexed.DeductionIndexedInterpretation
