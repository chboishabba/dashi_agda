module DASHI.Physics.YangMills.BalabanCMP109FederbushMaximalQuarterInvariantBallExact where

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
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- DASHI CONTRIBUTION
--
-- Match G1 to the repository's ALREADY SELECTED quarter-contraction target.
-- On the full centre chart r = 23/768, a quarter contraction leaves three
-- quarters of the ball available for the correction at the reference:
--
--   q = 1/4,
--   (1-q) r = (3/4)(23/768) = 23/1024.
--
-- Therefore
--
--   d(Tx,R) <= d(Tx,TR)+d(TR,R)
--           <= (1/4) d(x,R) + 23/1024
--           <= (1/4)(23/768)+23/1024
--            = 23/768.
--
-- This strictly improves the earlier half-contraction reduction: the literal
-- reference correction may be as large as 23/1024 while the existing quarter
-- contraction machinery can be reused unchanged.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreMaximalChartBudgetExact as Maximal
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

quarter : ℚ
quarter = + 1 / 4

threeQuarters : ℚ
threeQuarters = + 3 / 4

maximalReferenceCorrection : ℚ
maximalReferenceCorrection = + 23 / 1024

threeQuarterRadiusIsReferenceCorrection :
  threeQuarters * Maximal.centreMaximalAllowance
  ≡ maximalReferenceCorrection
threeQuarterRadiusIsReferenceCorrection = ℚRing.solve []

quarterRadiusPlusReferenceCorrectionIsRadius :
  quarter * Maximal.centreMaximalAllowance + maximalReferenceCorrection
  ≡ Maximal.centreMaximalAllowance
quarterRadiusPlusReferenceCorrectionIsRadius = ℚRing.solve []

record DirectFederbushQuarterContractionData (Point : Set) : Set₁ where
  field
    reference : Point
    map : Point → Point
    distance : Point → Point → ℚ

    triangleThroughReferenceImage : ∀ point →
      distance (map point) reference
      ≤ distance (map point) (map reference)
        + distance (map reference) reference

    referenceCorrectionSmall :
      distance (map reference) reference ≤ maximalReferenceCorrection

    quarterContractionFromReference : ∀ point →
      distance (map point) (map reference)
      ≤ quarter * distance point reference

open DirectFederbushQuarterContractionData public

quarterMapPreservesMaximalCentreBall :
  ∀ {Point} (dataSet : DirectFederbushQuarterContractionData Point) point →
  distance dataSet point (reference dataSet)
    ≤ Maximal.centreMaximalAllowance →
  distance dataSet (map dataSet point) (reference dataSet)
    ≤ Maximal.centreMaximalAllowance
quarterMapPreservesMaximalCentreBall dataSet point pointInBall =
  let
    contracted = quarterContractionFromReference dataSet point

    scaledRadius :
      quarter * distance dataSet point (reference dataSet)
      ≤ quarter * Maximal.centreMaximalAllowance
    scaledRadius = Norm.scaleNonnegative
      quarter (ℚP.nonNegative⁻¹ quarter) pointInBall

    firstTerm :
      distance dataSet (map dataSet point) (map dataSet (reference dataSet))
      ≤ quarter * Maximal.centreMaximalAllowance
    firstTerm = ℚP.≤-trans contracted scaledRadius

    summed :
      distance dataSet (map dataSet point) (map dataSet (reference dataSet))
        + distance dataSet (map dataSet (reference dataSet)) (reference dataSet)
      ≤ quarter * Maximal.centreMaximalAllowance + maximalReferenceCorrection
    summed = ℚP.+-mono-≤ firstTerm (referenceCorrectionSmall dataSet)
  in
  ℚP.≤-trans
    (triangleThroughReferenceImage dataSet point)
    (subst
      (λ upper →
        distance dataSet (map dataSet point) (map dataSet (reference dataSet))
          + distance dataSet (map dataSet (reference dataSet)) (reference dataSet)
        ≤ upper)
      quarterRadiusPlusReferenceCorrectionIsRadius
      summed)

cmp109FederbushMaximalQuarterInvariantBallLevel : ProofLevel
cmp109FederbushMaximalQuarterInvariantBallLevel = machineChecked

-- Remaining source-native G1 estimates now align with the repository's quarter
-- budget: prove the actual equation-(0.11) Newton map has quarter Lipschitz
-- factor on the 23/768 ball and reference correction <=23/1024.
cmp109FederbushPhysicalQuarterContractionLevel : ProofLevel
cmp109FederbushPhysicalQuarterContractionLevel = conditional

cmp109FederbushPhysicalReferenceCorrection23Over1024Level : ProofLevel
cmp109FederbushPhysicalReferenceCorrection23Over1024Level = conditional
