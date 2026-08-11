module DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionNormExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers", RAIRO Analyse Numerique 8 (1974),
-- 129--151. No DOI was assigned to the cited article.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the exact P/C split of the literal 780-row multiplier carrier to a
-- Pythagorean squared-norm identity.  The earlier module proves
--
--   lambda = P lambda + C lambda,
--   <P lambda,C lambda> = <C lambda,P lambda> = 0.
--
-- Exact finite rational summation therefore gives
--
--   ||lambda||^2 = ||P lambda||^2 + ||C lambda||^2,
--
-- and positivity of the complementary square yields
--
--   ||P lambda||^2 <= ||lambda||^2.
--
-- This is the missing norm statement needed to pass a raw average+gauge
-- nonlinear derivative budget through the actual reduced constraint
-- projection without paying an artificial projection constant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionOrthogonalityExact as Projection

RawMultiplier : Set
RawMultiplier = Projection.RawMultiplier

rawMultiplierNormSq : RawMultiplier → ℚ
rawMultiplierNormSq = Rect.finiteNormSq Rows.selectedCombinedConstraintRowCarrier

selectedProjectionPythagoras : ∀ multiplier →
  rawMultiplierNormSq multiplier
  ≡ rawMultiplierNormSq (Projection.selectedReducedProjection multiplier)
    + rawMultiplierNormSq (Projection.selectedConstantComplement multiplier)
selectedProjectionPythagoras multiplier =
  let
    rows = Matrix.coordinates Rows.selectedCombinedConstraintRowCarrier
    projected = Projection.selectedReducedProjection multiplier
    complement = Projection.selectedConstantComplement multiplier

    reconstructSquares :
      rawMultiplierNormSq multiplier
      ≡ Sums.sumRational rows
          (λ row →
            (projected row + complement row)
              * (projected row + complement row))
    reconstructSquares =
      Sums.sumRationalCong rows _ _
        (λ row →
          cong₂ _*_
            (Projection.selectedProjectionComplementReconstruct multiplier row)
            (Projection.selectedProjectionComplementReconstruct multiplier row))

    expandPointwise :
      Sums.sumRational rows
        (λ row →
          (projected row + complement row)
            * (projected row + complement row))
      ≡ Sums.sumRational rows
          (λ row →
            projected row * projected row
            + (projected row * complement row
            + (complement row * projected row
            + complement row * complement row)))
    expandPointwise =
      Sums.sumRationalCong rows _ _
        (λ row → ℚRing.solve-∀ (projected row) (complement row))

    splitSums :
      Sums.sumRational rows
        (λ row →
          projected row * projected row
          + (projected row * complement row
          + (complement row * projected row
          + complement row * complement row)))
      ≡ rawMultiplierNormSq projected
        + (Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
            projected complement
        + (Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
            complement projected
        + rawMultiplierNormSq complement))
    splitSums =
      trans
        (Fubini.sumRationalAdd rows
          (λ row → projected row * projected row)
          (λ row →
            projected row * complement row
            + (complement row * projected row
            + complement row * complement row)))
        (cong
          (rawMultiplierNormSq projected +_)
          (trans
            (Fubini.sumRationalAdd rows
              (λ row → projected row * complement row)
              (λ row →
                complement row * projected row
                + complement row * complement row))
            (cong
              (Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
                projected complement +_)
              (Fubini.sumRationalAdd rows
                (λ row → complement row * projected row)
                (λ row → complement row * complement row)))))

    projectedComplementZero =
      Projection.selectedProjectionComplementOrthogonal multiplier multiplier
    complementProjectedZero =
      Projection.selectedComplementProjectionOrthogonal multiplier multiplier
  in
  trans reconstructSquares
    (trans expandPointwise
      (trans splitSums
        (trans
          (cong
            (λ firstCross →
              rawMultiplierNormSq projected
              + (firstCross
              + (Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
                  complement projected
              + rawMultiplierNormSq complement)))
            projectedComplementZero)
          (trans
            (cong
              (λ secondCross →
                rawMultiplierNormSq projected
                + (0ℚ + (secondCross + rawMultiplierNormSq complement)))
              complementProjectedZero)
            (ℚRing.solve-∀
              (rawMultiplierNormSq projected)
              (rawMultiplierNormSq complement))))))

selectedProjectionNormSqBelowRaw : ∀ multiplier →
  rawMultiplierNormSq (Projection.selectedReducedProjection multiplier)
  ≤ rawMultiplierNormSq multiplier
selectedProjectionNormSqBelowRaw multiplier =
  let
    projectedNorm = rawMultiplierNormSq
      (Projection.selectedReducedProjection multiplier)
    complementNorm = rawMultiplierNormSq
      (Projection.selectedConstantComplement multiplier)
    complementNonnegative = Rect.finiteNormSqNonnegative
      Rows.selectedCombinedConstraintRowCarrier
      (Projection.selectedConstantComplement multiplier)

    belowSum : projectedNorm ≤ projectedNorm + complementNorm
    belowSum =
      subst
        (λ selected → projectedNorm ≤ selected)
        (ℚRing.solve-∀ projectedNorm complementNorm)
        (ℚP.+-mono-≤ ℚP.≤-refl complementNonnegative)
  in
  subst
    (λ upper → projectedNorm ≤ upper)
    (sym (selectedProjectionPythagoras multiplier))
    belowSum

selectedCombinedProjectionPythagorasLevel : ProofLevel
selectedCombinedProjectionPythagorasLevel = machineChecked

selectedCombinedProjectionNormContractionLevel : ProofLevel
selectedCombinedProjectionNormContractionLevel = machineChecked
