module DASHI.Physics.YangMills.BalabanFiniteHessianRowSumQuadraticBoundExact where

------------------------------------------------------------------------
-- ROUND69: LOCAL HESSIAN ROW SUM -> GLOBAL QUADRATIC-FORM BOUND
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Dominique Bakry, Ivan Gentil and Michel Ledoux,
-- "Analysis and Geometry of Markov Diffusion Operators",
-- Springer, 2014. DOI: 10.1007/978-3-319-00227-9.
--
-- DASHI CONTRIBUTION
--
-- The correct L7 -> L5 coordinate is local, not global oscillation.  This file
-- proves a finite rational Schur/Gershgorin-style estimate tailored to the
-- effective-action Hessian.
--
-- Let H_ij be a symmetric Hessian and M_ij >= 0 an entry magnitude.  Suppose
-- the pointwise Young bound
--
--   H_ij v_i v_j <= (1/2) M_ij (v_i^2 + v_j^2)
--
-- holds and every magnitude row has mass at most rho:
--
--   sum_j M_ij <= rho.
--
-- Then, independently of the number of coordinates,
--
--   sum_ij H_ij v_i v_j <= rho sum_i v_i^2.
--
-- This is exactly the volume-uniform perturbation statement needed by the
-- Round68 Bakry--Emery handoff.  Local finite-range interaction estimates can
-- therefore feed a global curvature margin without paying a factor equal to
-- lattice volume.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Perturb
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

half : ℚ
half = + 1 / 2

record FiniteSymmetricHessianRowBudget (Index : Set) : Set₁ where
  field
    carrier : Matrix.FiniteRationalCoordinates Index
    hessian magnitude : Index → Index → ℚ
    rowBudget : ℚ
    rowBudgetNonnegative : 0ℚ ≤ rowBudget

    magnitudeSymmetric : ∀ i j → magnitude i j ≡ magnitude j i
    magnitudeNonnegative : ∀ i j → 0ℚ ≤ magnitude i j

    rowMagnitudeBound : ∀ i →
      Sums.sumRational (Matrix.coordinates carrier) (magnitude i)
      ≤ rowBudget

    -- Absolute-value/Young work stays local.  It can be proved termwise from
    -- |H_ij| <= M_ij and 2|ab| <= a^2+b^2.
    pointwiseYoungUpper : ∀ (v : Index → ℚ) i j →
      hessian i j * (v i * v j)
      ≤ half * magnitude i j * ((v i * v i) + (v j * v j))

open FiniteSymmetricHessianRowBudget public

quadraticForm : ∀ {Index} →
  FiniteSymmetricHessianRowBudget Index → (Index → ℚ) → ℚ
quadraticForm dataSet v =
  Sums.sumRational (Matrix.coordinates (carrier dataSet)) (λ i →
    Sums.sumRational (Matrix.coordinates (carrier dataSet)) (λ j →
      hessian dataSet i j * (v i * v j)))

vectorNormSq : ∀ {Index} →
  FiniteSymmetricHessianRowBudget Index → (Index → ℚ) → ℚ
vectorNormSq dataSet v =
  Sums.sumRational (Matrix.coordinates (carrier dataSet))
    (λ i → v i * v i)

rowWeightedSquares : ∀ {Index} →
  FiniteSymmetricHessianRowBudget Index → (Index → ℚ) → ℚ
rowWeightedSquares dataSet v =
  Sums.sumRational (Matrix.coordinates (carrier dataSet)) (λ i →
    Sums.sumRational (Matrix.coordinates (carrier dataSet))
      (magnitude dataSet i) * (v i * v i))

pointwiseYoungSummed :
  ∀ {Index} (dataSet : FiniteSymmetricHessianRowBudget Index) v →
  quadraticForm dataSet v
  ≤ rowWeightedSquares dataSet v
pointwiseYoungSummed dataSet v =
  let
    xs = Matrix.coordinates (carrier dataSet)

    nested :
      quadraticForm dataSet v
      ≤ Sums.sumRational xs (λ i →
          Sums.sumRational xs (λ j →
            half * magnitude dataSet i j
              * ((v i * v i) + (v j * v j))))
    nested = Perturb.sumMonotone xs _ _ (λ i →
      Perturb.sumMonotone xs _ _ (pointwiseYoungUpper dataSet v i))

    splitInner : ∀ i →
      Sums.sumRational xs (λ j →
        half * magnitude dataSet i j * ((v i * v i) + (v j * v j)))
      ≡
      Sums.sumRational xs (λ j → half * magnitude dataSet i j * (v i * v i))
      + Sums.sumRational xs (λ j → half * magnitude dataSet i j * (v j * v j))
    splitInner i = trans
      (Sums.sumRationalCong xs _ _ (λ j →
        ℚRing.solve-∀
          (magnitude dataSet i j) (v i) (v j)))
      (Fubini.sumRationalAdd xs
        (λ j → half * magnitude dataSet i j * (v i * v i))
        (λ j → half * magnitude dataSet i j * (v j * v j)))

    splitOuter :
      Sums.sumRational xs (λ i →
        Sums.sumRational xs (λ j →
          half * magnitude dataSet i j * ((v i * v i) + (v j * v j))))
      ≡
      Sums.sumRational xs (λ i →
        Sums.sumRational xs (λ j → half * magnitude dataSet i j * (v i * v i)))
      + Sums.sumRational xs (λ i →
        Sums.sumRational xs (λ j → half * magnitude dataSet i j * (v j * v j)))
    splitOuter = trans
      (Sums.sumRationalCong xs _ _ splitInner)
      (Fubini.sumRationalAdd xs
        (λ i → Sums.sumRational xs
          (λ j → half * magnitude dataSet i j * (v i * v i)))
        (λ i → Sums.sumRational xs
          (λ j → half * magnitude dataSet i j * (v j * v j))))

    firstHalf :
      Sums.sumRational xs (λ i →
        Sums.sumRational xs (λ j → half * magnitude dataSet i j * (v i * v i)))
      ≡ half * rowWeightedSquares dataSet v
    firstHalf = trans
      (Sums.sumRationalCong xs _ _ (λ i →
        trans
          (Sums.sumRationalCong xs _ _ (λ j →
            ℚRing.solve-∀ (magnitude dataSet i j) (v i)))
          (trans
            (Sums.sumRationalScale half xs
              (λ j → magnitude dataSet i j * (v i * v i)))
            (cong (half *_) (Matrix.sumRationalRightScale
              xs (magnitude dataSet i) (v i * v i))))))
      (Sums.sumRationalScale half xs (λ i →
        Sums.sumRational xs (magnitude dataSet i) * (v i * v i)))

    secondToFirst :
      Sums.sumRational xs (λ i →
        Sums.sumRational xs (λ j → half * magnitude dataSet i j * (v j * v j)))
      ≡ half * rowWeightedSquares dataSet v
    secondToFirst = trans
      (Fubini.sumSwap xs xs
        (λ i j → half * magnitude dataSet i j * (v j * v j)))
      (trans
        (Sums.sumRationalCong xs _ _ (λ j →
          trans
            (Sums.sumRationalCong xs _ _ (λ i →
              cong (λ m → half * m * (v j * v j))
                (magnitudeSymmetric dataSet i j)))
            (trans
              (Sums.sumRationalCong xs _ _ (λ i →
                ℚRing.solve-∀ (magnitude dataSet j i) (v j)))
              (trans
                (Sums.sumRationalScale half xs
                  (λ i → magnitude dataSet j i * (v j * v j)))
                (cong (half *_) (Matrix.sumRationalRightScale
                  xs (magnitude dataSet j) (v j * v j)))))))
        (Sums.sumRationalScale half xs (λ j →
          Sums.sumRational xs (magnitude dataSet j) * (v j * v j))))

    twoHalves :
      Sums.sumRational xs (λ i →
        Sums.sumRational xs (λ j →
          half * magnitude dataSet i j * ((v i * v i) + (v j * v j))))
      ≡ rowWeightedSquares dataSet v
    twoHalves = trans splitOuter
      (trans
        (cong₂ _+_ firstHalf secondToFirst)
        (ℚRing.solve-∀ (rowWeightedSquares dataSet v)))
  in
  subst
    (λ upper → quadraticForm dataSet v ≤ upper)
    twoHalves nested

rowWeightedSquaresBound :
  ∀ {Index} (dataSet : FiniteSymmetricHessianRowBudget Index) v →
  rowWeightedSquares dataSet v
  ≤ rowBudget dataSet * vectorNormSq dataSet v
rowWeightedSquaresBound dataSet v =
  let
    xs = Matrix.coordinates (carrier dataSet)

    pointwise : ∀ i →
      Sums.sumRational xs (magnitude dataSet i) * (v i * v i)
      ≤ rowBudget dataSet * (v i * v i)
    pointwise i = Norm.scaleNonnegative
      (v i * v i)
      (FiniteL2.squareNonnegative (v i))
      (rowMagnitudeBound dataSet i)

    summed = Perturb.sumMonotone xs _ _ pointwise

    scaledNorm :
      Sums.sumRational xs (λ i → rowBudget dataSet * (v i * v i))
      ≡ rowBudget dataSet * vectorNormSq dataSet v
    scaledNorm = Sums.sumRationalScale (rowBudget dataSet) xs
      (λ i → v i * v i)
  in
  subst
    (λ upper → rowWeightedSquares dataSet v ≤ upper)
    scaledNorm summed

hessianQuadraticFormBelowUniformRowBudget :
  ∀ {Index} (dataSet : FiniteSymmetricHessianRowBudget Index) v →
  quadraticForm dataSet v
  ≤ rowBudget dataSet * vectorNormSq dataSet v
hessianQuadraticFormBelowUniformRowBudget dataSet v =
  ℚP.≤-trans
    (pointwiseYoungSummed dataSet v)
    (rowWeightedSquaresBound dataSet v)

finiteHessianRowSumQuadraticBoundLevel : ProofLevel
finiteHessianRowSumQuadraticBoundLevel = machineChecked

-- Highest-alpha physical producer for L7/L5 coupling: prove a volume- and
-- cutoff-uniform row bound for the Hessian of the SAME irrelevant/polymer
-- remainder.  Finite range means the row sees only boundedly many neighboring
-- blocks, so this target can remain O(1) as total lattice volume grows.
physicalUnifiedRemainderHessianRowBudgetLevel : ProofLevel
physicalUnifiedRemainderHessianRowBudgetLevel = conditional
