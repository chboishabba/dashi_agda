module DASHI.Physics.YangMills.BalabanYM4SegmentedBackgroundLocalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the finite integration arithmetic in RG1d.  Once every admissible
-- segment of a background path obeys the same remote-response estimate
--
--      response_i <= localityFactor * step_i,
--
-- the complete polygonal path obeys
--
--      sum response_i <= localityFactor * sum step_i.
--
-- No scale-dependent loss appears while integrating the differentiated KKT
-- response.  The remaining physical theorem is the literal KKT source/support
-- estimate and an admissible path whose total variation is controlled by the
-- endpoint difference.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record LocalitySegment : Set where
  constructor segment
  field
    stepMagnitude responseMagnitude : ℚ

open LocalitySegment public

sumSteps : List LocalitySegment → ℚ
sumSteps [] = 0ℚ
sumSteps (value ∷ values) = stepMagnitude value + sumSteps values

sumResponses : List LocalitySegment → ℚ
sumResponses [] = 0ℚ
sumResponses (value ∷ values) = responseMagnitude value + sumResponses values

record UniformSegmentLocality
    (localityFactor : ℚ) (segments : List LocalitySegment) : Set where
  field
    localityFactorNonnegative : 0ℚ ≤ localityFactor
    pointwiseResponse : ∀ value →
      responseMagnitude value ≤ localityFactor * stepMagnitude value

open UniformSegmentLocality public

segmentedResponseBound :
  ∀ localityFactor segments →
  UniformSegmentLocality localityFactor segments →
  sumResponses segments ≤ localityFactor * sumSteps segments
segmentedResponseBound localityFactor [] bounds = ℚP.≤-refl
segmentedResponseBound localityFactor (value ∷ values) bounds =
  let
    tailBounds : UniformSegmentLocality localityFactor values
    tailBounds = record
      { localityFactorNonnegative = localityFactorNonnegative bounds
      ; pointwiseResponse = pointwiseResponse bounds }

    combined :
      responseMagnitude value + sumResponses values
      ≤ localityFactor * stepMagnitude value
        + localityFactor * sumSteps values
    combined = ℚP.+-mono-≤
      (pointwiseResponse bounds value)
      (segmentedResponseBound localityFactor values tailBounds)

    distributed :
      localityFactor * stepMagnitude value
        + localityFactor * sumSteps values
      ≡ localityFactor * (stepMagnitude value + sumSteps values)
    distributed = ℚRing.solve-∀
      localityFactor (stepMagnitude value) (sumSteps values)
  in
  ℚP.≤-trans combined (ℚP.≤-reflexive distributed)

record EndpointBackgroundLocality
    (localityFactor endpointDifference : ℚ)
    (segments : List LocalitySegment) : Set where
  field
    segmentLocality : UniformSegmentLocality localityFactor segments
    pathLengthControlled : sumSteps segments ≤ endpointDifference

open EndpointBackgroundLocality public

endpointResponseBound :
  ∀ localityFactor endpointDifference segments →
  EndpointBackgroundLocality localityFactor endpointDifference segments →
  sumResponses segments ≤ localityFactor * endpointDifference
endpointResponseBound localityFactor endpointDifference segments data =
  ℚP.≤-trans
    (segmentedResponseBound localityFactor segments (segmentLocality data))
    (Norm.scaleNonnegative
      localityFactor
      (localityFactorNonnegative (segmentLocality data))
      (pathLengthControlled data))

ym4SegmentedBackgroundLocalityLevel : ProofLevel
ym4SegmentedBackgroundLocalityLevel = machineChecked

ym4PhysicalDifferentiatedKKTSourceSupportLevel : ProofLevel
ym4PhysicalDifferentiatedKKTSourceSupportLevel = conditional

ym4PhysicalAdmissiblePathLengthControlLevel : ProofLevel
ym4PhysicalAdmissiblePathLengthControlLevel = conditional
