module DASHI.Physics.YangMills.BalabanCMP109EndpointGaugeRestrictionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Close the ambiguity in the coarse gauge restriction carried by Bałaban's
-- averaged contour.  Equation (0.11), together with the bi-translation law of
-- the group average, says that a contour average with coarse endpoints x,y
-- transforms only by the fine gauge evaluated at those endpoints.
--
-- We make the restriction literal:
--
--     (R g)(x) = g(embed x).
--
-- For a path family whose individual holonomies transform by
--
--     hol^g(path) = g(embed source) hol(path) g(embed target)^-1,
--
-- the already-proved CMP109 group-average covariance now yields
--
--     M(hol^g) = (R g)(source) M(hol) (R g)(target)^-1.
--
-- Thus the `restrictGauge` required by the nonlinear block-average covariance
-- is not a free function on this source-exact contour object: it is endpoint
-- evaluation.  In particular a gauge transformation equal to the identity on
-- all embedded coarse sites acts trivially on every averaged contour.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageAxiomsExact as Average

record CMP109EndpointGaugePathFamily
    (Field FineSite CoarseSite CoarseBond Path Group Lie Scalar : Set)
    (averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar)
    : Set₁ where
  field
    source target : CoarseBond → CoarseSite
    embedCoarseSite : CoarseSite → FineSite

    fineGauge : Field → FineSite → Group

    pathFamily : CoarseBond →
      Average.GaugeCovariantPathFamily
        Field Path Group Lie Scalar averageAxioms

    leftGaugeIsSourceEvaluation : ∀ field bond →
      Average.leftGauge (pathFamily bond) field
      ≡ fineGauge field (embedCoarseSite (source bond))

    rightGaugeIsTargetInverse : ∀ field bond →
      Average.rightGauge (pathFamily bond) field
      ≡ Average.inverse averageAxioms
          (fineGauge field (embedCoarseSite (target bond)))

open CMP109EndpointGaugePathFamily public

restrictedGauge :
  ∀ {Field FineSite CoarseSite CoarseBond Path Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar} →
  CMP109EndpointGaugePathFamily
    Field FineSite CoarseSite CoarseBond Path Group Lie Scalar averageAxioms →
  Field → CoarseSite → Group
restrictedGauge dataSet field coarse =
  fineGauge dataSet field (embedCoarseSite dataSet coarse)

coarseAveragedContour :
  ∀ {Field FineSite CoarseSite CoarseBond Path Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar} →
  CMP109EndpointGaugePathFamily
    Field FineSite CoarseSite CoarseBond Path Group Lie Scalar averageAxioms →
  CoarseBond → Field → Group
coarseAveragedContour dataSet bond =
  Average.averagedContour (pathFamily dataSet bond)

coarseTransformedAveragedContour :
  ∀ {Field FineSite CoarseSite CoarseBond Path Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar} →
  CMP109EndpointGaugePathFamily
    Field FineSite CoarseSite CoarseBond Path Group Lie Scalar averageAxioms →
  CoarseBond → Field → Group
coarseTransformedAveragedContour dataSet bond =
  Average.transformedAveragedContour (pathFamily dataSet bond)

cmp109AveragedContourGaugeRestrictionIsEndpointEvaluation :
  ∀ {Field FineSite CoarseSite CoarseBond Path Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (dataSet : CMP109EndpointGaugePathFamily
      Field FineSite CoarseSite CoarseBond Path Group Lie Scalar averageAxioms)
    field bond →
  coarseTransformedAveragedContour dataSet bond field
  ≡ Average.multiply averageAxioms
      (restrictedGauge dataSet field (source dataSet bond))
      (Average.multiply averageAxioms
        (coarseAveragedContour dataSet bond field)
        (Average.inverse averageAxioms
          (restrictedGauge dataSet field (target dataSet bond))))
cmp109AveragedContourGaugeRestrictionIsEndpointEvaluation
    {averageAxioms = averageAxioms} dataSet field bond =
  trans
    (Average.averagedContourGaugeCovariant
      (pathFamily dataSet bond) field)
    (trans
      (cong
        (λ leftValue →
          Average.multiply averageAxioms leftValue
            (Average.multiply averageAxioms
              (coarseAveragedContour dataSet bond field)
              (Average.rightGauge (pathFamily dataSet bond) field)))
        (leftGaugeIsSourceEvaluation dataSet field bond))
      (cong
        (Average.multiply averageAxioms
          (restrictedGauge dataSet field (source dataSet bond)))
        (cong
          (Average.multiply averageAxioms
            (coarseAveragedContour dataSet bond field))
          (rightGaugeIsTargetInverse dataSet field bond))))

record CMP109GroupIdentityLaws
    {Group Lie Scalar : Set}
    (averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar) : Set₁ where
  field
    multiplyIdentityLeft : ∀ value →
      Average.multiply averageAxioms (Average.identity averageAxioms) value ≡ value
    multiplyIdentityRight : ∀ value →
      Average.multiply averageAxioms value (Average.identity averageAxioms) ≡ value
    inverseIdentity :
      Average.inverse averageAxioms (Average.identity averageAxioms)
      ≡ Average.identity averageAxioms

open CMP109GroupIdentityLaws public

cmp109CoarseAnchoredGaugeFixesAveragedContour :
  ∀ {Field FineSite CoarseSite CoarseBond Path Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (groupLaws : CMP109GroupIdentityLaws averageAxioms)
    (dataSet : CMP109EndpointGaugePathFamily
      Field FineSite CoarseSite CoarseBond Path Group Lie Scalar averageAxioms)
    field →
  (∀ coarse →
    restrictedGauge dataSet field coarse ≡ Average.identity averageAxioms) →
  ∀ bond →
  coarseTransformedAveragedContour dataSet bond field
  ≡ coarseAveragedContour dataSet bond field
cmp109CoarseAnchoredGaugeFixesAveragedContour
    {averageAxioms = averageAxioms} groupLaws dataSet field anchored bond =
  trans
    (cmp109AveragedContourGaugeRestrictionIsEndpointEvaluation
      dataSet field bond)
    (trans
      (cong
        (λ sourceGauge →
          Average.multiply averageAxioms sourceGauge
            (Average.multiply averageAxioms
              (coarseAveragedContour dataSet bond field)
              (Average.inverse averageAxioms
                (restrictedGauge dataSet field (target dataSet bond)))))
        (anchored (source dataSet bond)))
      (trans
        (cong
          (Average.multiply averageAxioms (Average.identity averageAxioms))
          (trans
            (cong
              (Average.multiply averageAxioms
                (coarseAveragedContour dataSet bond field))
              (trans
                (cong (Average.inverse averageAxioms)
                  (anchored (target dataSet bond)))
                (inverseIdentity groupLaws)))
            (multiplyIdentityRight groupLaws
              (coarseAveragedContour dataSet bond field))))
        (multiplyIdentityLeft groupLaws
          (coarseAveragedContour dataSet bond field))))

cmp109EndpointGaugeRestrictionLevel : ProofLevel
cmp109EndpointGaugeRestrictionLevel = machineChecked

cmp109CoarseAnchoredContourInvarianceLevel : ProofLevel
cmp109CoarseAnchoredContourInvarianceLevel = machineChecked
