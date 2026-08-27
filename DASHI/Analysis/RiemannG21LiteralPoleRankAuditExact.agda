module DASHI.Analysis.RiemannG21LiteralPoleRankAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Literal source audit for the Weil explicit formula used by the #604 source.
--
-- The companion Zeta23/ExplicitFormula.lean defines the pole contribution in
-- literatureRHS as
--
--   h(i/2) + h(-i/2).
--
-- For k = f * g~ it proves
--
--   h_k(z) = h_f(z) * conj(h_g(conj z)).
--
-- Thus the pole contribution is a SUM OF TWO evaluation channels.  It is not
-- justified to assign nuisance rank one unless the selected test family proves
-- those two pole profiles dependent.  This module records that distinction in
-- a carrier-independent way.
------------------------------------------------------------------------

record TwoPoleEvaluationSurface : Set₁ where
  field
    Sample Scalar : Set
    positivePoleProfile : Sample → Scalar
    negativePoleProfile : Sample → Scalar
    combine : Scalar → Scalar → Scalar

    literalPoleResponse : Sample → Scalar
    literalPoleResponseDefinition :
      (x : Sample) →
      literalPoleResponse x
      ≡ combine (positivePoleProfile x) (negativePoleProfile x)

    sourceReading : String

open TwoPoleEvaluationSurface public

------------------------------------------------------------------------
-- Rank-one reduction is EXTRA DATA: one pole profile must factor through the
-- other (or both through a supplied common profile).  The literal two-pole
-- formula by itself does not construct this witness.
------------------------------------------------------------------------

record CommonPoleProfileReduction
    (surface : TwoPoleEvaluationSurface) : Set₁ where
  field
    commonProfile : Sample surface → Scalar surface
    positiveCoefficient negativeCoefficient : Scalar surface
    scale : Scalar surface → Scalar surface → Scalar surface

    positiveFactors :
      (x : Sample surface) →
      positivePoleProfile surface x
      ≡ scale positiveCoefficient (commonProfile x)

    negativeFactors :
      (x : Sample surface) →
      negativePoleProfile surface x
      ≡ scale negativeCoefficient (commonProfile x)

open CommonPoleProfileReduction public

------------------------------------------------------------------------
-- Exact dimension receipts for the two possible architectures.
------------------------------------------------------------------------

record PoleQuotientDimensionCase : Set where
  constructor poleQuotientDimensionCase
  field
    sampleDimension nuisanceRank residualDimension : Nat
    balance : nuisanceRank + residualDimension ≡ sampleDimension

rankOneThreeSampleCase : PoleQuotientDimensionCase
rankOneThreeSampleCase = poleQuotientDimensionCase 3 1 2 refl

genericTwoPoleThreeSampleCase : PoleQuotientDimensionCase
genericTwoPoleThreeSampleCase = poleQuotientDimensionCase 3 2 1 refl

genericTwoPoleFourSampleCase : PoleQuotientDimensionCase
genericTwoPoleFourSampleCase = poleQuotientDimensionCase 4 2 2 refl

threeSamplesNeedRankOneReductionForTwoResidualDimensions :
  residualDimension genericTwoPoleThreeSampleCase ≡ 1
threeSamplesNeedRankOneReductionForTwoResidualDimensions = refl

fourSamplesSupportTwoResidualDimensionsWithoutRankOneReduction :
  residualDimension genericTwoPoleFourSampleCase ≡ 2
fourSamplesSupportTwoResidualDimensionsWithoutRankOneReduction = refl

record LiteralPoleRankBoundary : Set where
  constructor literalPoleRankBoundary
  field
    sourceHasTwoPoleEvaluations : Bool
    sourceHasTwoPoleEvaluationsIsTrue : sourceHasTwoPoleEvaluations ≡ true

    literalFormulaAloneProvesRankOnePole : Bool
    literalFormulaAloneProvesRankOnePoleIsFalse :
      literalFormulaAloneProvesRankOnePole ≡ false

    threeSampleExteriorUnconditional : Bool
    threeSampleExteriorUnconditionalIsFalse :
      threeSampleExteriorUnconditional ≡ false

    fourSampleRankTwoFallbackAvailable : Bool
    fourSampleRankTwoFallbackAvailableIsTrue :
      fourSampleRankTwoFallbackAvailable ≡ true

canonicalLiteralPoleRankBoundary : LiteralPoleRankBoundary
canonicalLiteralPoleRankBoundary =
  literalPoleRankBoundary
    true refl
    false refl
    false refl
    true refl
