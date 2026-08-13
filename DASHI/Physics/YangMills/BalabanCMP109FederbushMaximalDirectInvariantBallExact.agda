module DASHI.Physics.YangMills.BalabanCMP109FederbushMaximalDirectInvariantBallExact where

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
-- Use Round 52's full centre radius 23/768 in the SOURCE-NATIVE Newton route.
-- For a Newton/Federbush map T and reference R, it is enough to prove
--
--   d(T R,R) <= 23/1536,
--   d(T x,T R) <= (1/2) d(x,R).
--
-- Then every x with d(x,R)<=23/768 satisfies
--
--   d(T x,R)
--      <= d(T x,T R)+d(T R,R)
--      <= (1/2)(23/768)+23/1536
--       = 23/768.
--
-- Thus the direct equation-(0.11) route no longer needs the much tighter
-- 3/256 ball.  Its physical leaf is reduced to TWO literal estimates on the
-- actual normalized Federbush Newton map: a half-contraction and a reference
-- correction no larger than 23/1536.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreMaximalChartBudgetExact as Maximal

half : ℚ
half = + 1 / 2

referenceCorrectionAllowance : ℚ
referenceCorrectionAllowance = + 23 / 1536

halfRadiusIsReferenceCorrectionAllowance :
  half * Maximal.centreMaximalAllowance ≡ referenceCorrectionAllowance
halfRadiusIsReferenceCorrectionAllowance = ℚRing.solve []

halfRadiusPlusReferenceCorrectionIsRadius :
  half * Maximal.centreMaximalAllowance + referenceCorrectionAllowance
  ≡ Maximal.centreMaximalAllowance
halfRadiusPlusReferenceCorrectionIsRadius = ℚRing.solve []

record DirectFederbushHalfContractionData (Point : Set) : Set₁ where
  field
    reference : Point
    map : Point → Point
    distance : Point → Point → ℚ

    distanceNonnegative : ∀ left right → 0ℚ ≤ distance left right
    triangleThroughReferenceImage : ∀ point →
      distance (map point) reference
      ≤ distance (map point) (map reference)
        + distance (map reference) reference

    referenceCorrectionSmall :
      distance (map reference) reference ≤ referenceCorrectionAllowance

    halfContractionFromReference : ∀ point →
      distance (map point) (map reference)
      ≤ half * distance point reference

open DirectFederbushHalfContractionData public

mapPreservesMaximalCentreBall :
  ∀ {Point} (dataSet : DirectFederbushHalfContractionData Point) point →
  distance dataSet point (reference dataSet)
    ≤ Maximal.centreMaximalAllowance →
  distance dataSet (map dataSet point) (reference dataSet)
    ≤ Maximal.centreMaximalAllowance
mapPreservesMaximalCentreBall dataSet point pointInBall =
  let
    contraction = halfContractionFromReference dataSet point
    halfScaled :
      half * distance dataSet point (reference dataSet)
      ≤ half * Maximal.centreMaximalAllowance
    halfScaled = ℚP.*-monoˡ-≤-nonNeg half pointInBall

    firstTerm :
      distance dataSet (map dataSet point) (map dataSet (reference dataSet))
      ≤ half * Maximal.centreMaximalAllowance
    firstTerm = ℚP.≤-trans contraction halfScaled

    summed :
      distance dataSet (map dataSet point) (map dataSet (reference dataSet))
        + distance dataSet (map dataSet (reference dataSet)) (reference dataSet)
      ≤ half * Maximal.centreMaximalAllowance + referenceCorrectionAllowance
    summed = ℚP.+-mono-≤ firstTerm (referenceCorrectionSmall dataSet)

    toRadius :
      distance dataSet (map dataSet point) (map dataSet (reference dataSet))
        + distance dataSet (map dataSet (reference dataSet)) (reference dataSet)
      ≤ Maximal.centreMaximalAllowance
    toRadius = subst
      (λ upper →
        distance dataSet (map dataSet point) (map dataSet (reference dataSet))
          + distance dataSet (map dataSet (reference dataSet)) (reference dataSet)
        ≤ upper)
      halfRadiusPlusReferenceCorrectionIsRadius
      summed
  in
  ℚP.≤-trans (triangleThroughReferenceImage dataSet point) toRadius

cmp109FederbushMaximalDirectInvariantBallArithmeticLevel : ProofLevel
cmp109FederbushMaximalDirectInvariantBallArithmeticLevel = machineChecked

-- Exact remaining G1 source-native producer after this reduction:
--   (i)  the actual normalized equation-(0.11) Newton map obeys the half
--        contraction on the 23/768 ball;
--   (ii) its correction at the selected reference is <=23/1536.
cmp109FederbushPhysicalHalfContractionLevel : ProofLevel
cmp109FederbushPhysicalHalfContractionLevel = conditional

cmp109FederbushPhysicalReferenceCorrectionLevel : ProofLevel
cmp109FederbushPhysicalReferenceCorrectionLevel = conditional
