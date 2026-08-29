{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact where

------------------------------------------------------------------------
-- ROUND118: CANONICAL CMP116 METRIC VARIATION -> NORMALIZED CMP119 INSERTION
--
-- Round106 already owns the exact domain and finite first-variation theorem on
-- (background, admitted metric perturbation).  Round116 owns division-free
-- normalized expectation cancellation.  This file binds them pointwise so the
-- physical source theorem is not a single scalar equality masquerading as a
-- functional identity.
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
    -- The canonical stress representation is read in the same rational scalar
    -- convention as the normalized finite expectation calculus.
    pairingScalarIsRational : StressRep.PairingScalar representation ≡ ℚ

    normalizedInsertion :
      Chain.Background activity →
      Domain.MetricPerturbation domain →
      R116.MetricStressNormalizedInsertionWeld

    -- Literal pointwise source identification on the admitted domain.
    finiteFirstVariationReadoutIsNormalizedCrossNumerator :
      ∀ background perturbation →
      Domain.AdmissibleMetricPerturbation domain perturbation →
      let insertion = normalizedInsertion background perturbation
      in
      StressRep.firstVariationReadout representation
        (First.substitutedFirstVariation activity background
          (Domain.metricPerturbationToBackgroundTangent
            domain background perturbation))
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
  StressRep.firstVariationReadout representation
    (First.substitutedFirstVariation activity background
      (Domain.metricPerturbationToBackgroundTangent
        domain background perturbation))
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

-- Physical source input: instantiate the normalized numerator/denominator
-- derivatives on the SAME finite CMP116 density and prove the surviving
-- connected cross numerator is the selected CMP119 local stress insertion for
-- every admitted (background,h).
literalCanonicalMetricCMP119StressInstantiationLevel : ProofLevel
literalCanonicalMetricCMP119StressInstantiationLevel = conditional
