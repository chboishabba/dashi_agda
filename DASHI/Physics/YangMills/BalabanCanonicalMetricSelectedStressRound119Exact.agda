{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact where

------------------------------------------------------------------------
-- ROUND119: ROUND106 METRIC VARIATION USES THE EXACT ROUND114 CMP119 INSERTION
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact as R118
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record CanonicalMetricSelectedStressWeld
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
    (representation : StressRep.CanonicalMetricStressRepresentation domain)
    (coordinate : R114.LiteralStressCoordinate Y group) : Set₁ where
  field
    readoutToRational : StressRep.PairingScalar representation → ℚ

    normalizedSource :
      Chain.Background activity →
      Domain.MetricPerturbation domain →
      R116.NormalizedSourceDerivativeCrossData

    metricFirstVariationCrossNumerator :
      Chain.Background activity →
      Domain.MetricPerturbation domain → ℚ

    localInsertionNumerator :
      Source.LocalInsertionPair
        (R109.source
          (R114.asCMP119Cauchy coordinate (R114.coordinate coordinate))) → ℚ

    finiteFirstVariationReadoutIsCrossNumerator :
      ∀ background perturbation →
      Domain.AdmissibleMetricPerturbation domain perturbation →
      readoutToRational
        (StressRep.firstVariationReadout representation
          (First.substitutedFirstVariation activity background
            (Domain.metricPerturbationToBackgroundTangent
              domain background perturbation)))
      ≡ metricFirstVariationCrossNumerator background perturbation

    metricVariationIsNormalizedCrossNumerator :
      ∀ background perturbation →
      metricFirstVariationCrossNumerator background perturbation
      ≡ R116.sourceDerivativeCrossNumerator
          (normalizedSource background perturbation)

    connectedInsertionIsSelectedCMP119StressInsertion :
      ∀ background perturbation →
      R116.connectedInsertionNumerator
        (normalizedSource background perturbation)
      ≡ localInsertionNumerator
          (Source.pair
            (R109.stressInsertion
              (R114.asCMP119Cauchy coordinate (R114.coordinate coordinate))))
open CanonicalMetricSelectedStressWeld public

asRound118CanonicalMetricWeld :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group} →
  CanonicalMetricSelectedStressWeld
    {C = C} {S = S} {Y = Y} {group = group}
    domain representation coordinate →
  R118.CanonicalMetricCMP119StressWeld domain representation
asRound118CanonicalMetricWeld {coordinate = coordinate} dataSet = record
  { R118.CanonicalMetricCMP119StressWeld.readoutToRational =
      readoutToRational dataSet
  ; R118.CanonicalMetricCMP119StressWeld.normalizedInsertion =
      λ background perturbation → record
        { R116.MetricStressNormalizedInsertionWeld.normalizedSource =
            normalizedSource dataSet background perturbation
        ; R116.MetricStressNormalizedInsertionWeld.metricFirstVariationCrossNumerator =
            metricFirstVariationCrossNumerator dataSet background perturbation
        ; R116.MetricStressNormalizedInsertionWeld.source =
            R109.source
              (R114.asCMP119Cauchy coordinate (R114.coordinate coordinate))
        ; R116.MetricStressNormalizedInsertionWeld.stressInsertion =
            R109.stressInsertion
              (R114.asCMP119Cauchy coordinate (R114.coordinate coordinate))
        ; R116.MetricStressNormalizedInsertionWeld.localInsertionNumerator =
            localInsertionNumerator dataSet
        ; R116.MetricStressNormalizedInsertionWeld.metricVariationIsNormalizedCrossNumerator =
            metricVariationIsNormalizedCrossNumerator dataSet background perturbation
        ; R116.MetricStressNormalizedInsertionWeld.connectedInsertionIsSelectedCMP119StressInsertion =
            connectedInsertionIsSelectedCMP119StressInsertion
              dataSet background perturbation
        }
  ; R118.CanonicalMetricCMP119StressWeld.finiteFirstVariationReadoutIsNormalizedCrossNumerator =
      finiteFirstVariationReadoutIsCrossNumerator dataSet
  }

canonicalMetricVariationIsExactSelectedCMP119StressInsertion :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    (dataSet : CanonicalMetricSelectedStressWeld
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation coordinate) →
  ∀ background perturbation →
  Domain.AdmissibleMetricPerturbation domain perturbation →
  let insertion = R118.normalizedInsertion
        (asRound118CanonicalMetricWeld dataSet) background perturbation
  in
  R118.readoutToRational (asRound118CanonicalMetricWeld dataSet)
    (StressRep.firstVariationReadout representation
      (First.substitutedFirstVariation activity background
        (Domain.metricPerturbationToBackgroundTangent
          domain background perturbation)))
  ≡ R116.cmp119StressInsertionNumerator insertion
canonicalMetricVariationIsExactSelectedCMP119StressInsertion
    dataSet background perturbation admissible =
  R118.finiteCanonicalMetricVariationIsCMP119StressInsertion
    (asRound118CanonicalMetricWeld dataSet)
    background perturbation admissible

canonicalMetricSelectedStressCompilerLevel : ProofLevel
canonicalMetricSelectedStressCompilerLevel = machineChecked

literalCanonicalMetricSelectedStressInstantiationLevel : ProofLevel
literalCanonicalMetricSelectedStressInstantiationLevel = conditional
