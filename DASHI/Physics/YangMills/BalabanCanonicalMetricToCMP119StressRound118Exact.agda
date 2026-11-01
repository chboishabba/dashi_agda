{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact where

------------------------------------------------------------------------
-- ROUND118: CANONICAL CMP116 METRIC VARIATION -> NORMALIZED CMP119 INSERTION
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116

record CanonicalMetricCMP119StressWeld
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
    (representation : StressRep.CanonicalMetricStressRepresentation domain) : Set₁ where
  field
    -- Explicit convention transport: no implicit identification of the stress
    -- pairing scalar with the rational normalized-expectation calculus.
    readoutToRational : StressRep.PairingScalar representation → ℚ

    normalizedInsertion :
      Chain.Background activity →
      Domain.MetricPerturbation domain →
      R116.MetricStressNormalizedInsertionWeld

    finiteFirstVariationReadoutIsNormalizedCrossNumerator :
      ∀ background perturbation →
      Domain.AdmissibleMetricPerturbation domain perturbation →
      let insertion = normalizedInsertion background perturbation
      in
      readoutToRational
        (StressRep.firstVariationReadout representation
          (First.substitutedFirstVariation activity background
            (Domain.metricPerturbationToBackgroundTangent
              domain background perturbation)))
      ≡ R116.metricFirstVariationCrossNumerator insertion
open CanonicalMetricCMP119StressWeld public

finiteCanonicalMetricVariationIsCMP119StressInsertion :
  ∀ {Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (dataSet : CanonicalMetricCMP119StressWeld domain representation) →
  ∀ background perturbation →
  Domain.AdmissibleMetricPerturbation domain perturbation →
  let insertion = normalizedInsertion dataSet background perturbation
  in
  readoutToRational dataSet
    (StressRep.firstVariationReadout representation
      (First.substitutedFirstVariation activity background
        (Domain.metricPerturbationToBackgroundTangent
          domain background perturbation)))
  ≡ R116.cmp119StressInsertionNumerator insertion
finiteCanonicalMetricVariationIsCMP119StressInsertion
    dataSet background perturbation admissible =
  trans
    (finiteFirstVariationReadoutIsNormalizedCrossNumerator
      dataSet background perturbation admissible)
    (R116.metricVariationCrossNumeratorIsCMP119StressInsertion
      (normalizedInsertion dataSet background perturbation))

canonicalMetricCMP119StressCompilerLevel : ProofLevel
canonicalMetricCMP119StressCompilerLevel = machineChecked

literalCanonicalMetricCMP119StressInstantiationLevel : ProofLevel
literalCanonicalMetricCMP119StressInstantiationLevel = conditional
