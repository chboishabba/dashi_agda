{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonCanonicalDomainApplicabilityExact where

------------------------------------------------------------------------
-- Canonical CMP116 common-domain applicability for the literal Wilson pair.
--
-- On the preferred R338 source, AdmissibleSourcePair is DEFINITIONALLY the
-- canonical SourceCoordinateInside predicate.  Hence no second pair-specific
-- Wilson/J admissibility theorem is required after the R338 source has been
-- aligned to the literal family.
--
-- The same finite normalized demand tuple also constructs one positive common
-- radius and proves first/second Cauchy differentiation use that same radius.
-- What remains physical is therefore only:
--
--   * extraction of the finite normalized CMP116 demand constants from the
--     literal generated family;
--   * alignment/construction of the actual R338 differentiated-localization
--     source theorem on that family.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanCMP116SelectedJPairDomainWeldRound334Exact as R334

canonicalTwoWilsonPairDomainWeld :
  ∀ {Measure Observable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands} →
  (source : R338.CanonicalCommonDomainCMP116Source base demands) →
  R334.SelectedJPairCommonDomainWeld
    base
    (R338.canonicalSourceBuildsGenericPublishedSource source)
    demands
canonicalTwoWilsonPairDomainWeld source = record
  { R334.SelectedJPairCommonDomainWeld.commonSourceCoordinateInsideImpliesSelectedPairAdmissible =
      λ cutoff left right inside → inside
  }

canonicalTwoWilsonPairAdmissible :
  ∀ {Measure Observable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    cutoff left right →
  R334.Source.AdmissibleSourcePair
    (R338.canonicalSourceBuildsGenericPublishedSource source)
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)
    (R334.Cumulant.sourceDirectionOf (R318.meaning base) left)
    (R334.Cumulant.sourceDirectionOf (R318.meaning base) right)
canonicalTwoWilsonPairAdmissible source =
  R334.selectedPairAdmissibleFromCommonDomain
    (canonicalTwoWilsonPairDomainWeld source)

canonicalTwoWilsonCommonRadius :
  ∀ {Scale Volume}
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands) →
  Common.CMP116CommonAnalyticRadius Scale Volume
canonicalTwoWilsonCommonRadius =
  R114.canonicalCMP116CommonDomain

canonicalTwoWilsonFirstSecondDerivativeSameRadius :
  ∀ {Scale Volume}
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands) →
  Common.FirstSecondDerivativeUseSameRadius
    (canonicalTwoWilsonCommonRadius {Scale} {Volume} demands)
canonicalTwoWilsonFirstSecondDerivativeSameRadius =
  R114.canonicalFirstSecondDerivativeSameRadius
