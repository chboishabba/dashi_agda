module DASHI.Physics.YangMills.BalabanFourAxisMartingaleExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)

------------------------------------------------------------------------
-- Exact scalar algebra behind the four-coordinate conditional-expectation
-- decomposition.
--
-- For successive averages
--
--   a0, a01, a012, a0123,
--
-- the four martingale differences telescope to x-a0123.  When the global
-- average a0123 vanishes, they reconstruct x exactly.  The variance theorem
-- below then converts the six pairwise orthogonality equations into an exact
-- sum of four squares.  No spectral or analytic premise is hidden here.
------------------------------------------------------------------------

martingale0 : ℚ → ℚ → ℚ
martingale0 x a0 = x - a0

martingale1 : ℚ → ℚ → ℚ
martingale1 a0 a01 = a0 - a01

martingale2 : ℚ → ℚ → ℚ
martingale2 a01 a012 = a01 - a012

martingale3 : ℚ → ℚ → ℚ
martingale3 a012 a0123 = a012 - a0123

fourMartingaleSum : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
fourMartingaleSum x a0 a01 a012 a0123 =
  martingale0 x a0
  + (martingale1 a0 a01
  + (martingale2 a01 a012
  + martingale3 a012 a0123))

fourAxisMartingaleTelescopingRaw : ∀ x a0 a01 a012 a0123 →
  fourMartingaleSum x a0 a01 a012 a0123 ≡ x - a0123
fourAxisMartingaleTelescopingRaw = ℚRing.solve-∀

fourAxisMartingaleDecomposition : ∀ x a0 a01 a012 a0123 →
  a0123 ≡ 0ℚ →
  fourMartingaleSum x a0 a01 a012 a0123 ≡ x
fourAxisMartingaleDecomposition x a0 a01 a012 a0123 globalMeanZero
  rewrite globalMeanZero = ℚRing.solve-∀ x a0 a01 a012

pairCrossSum : ℚ → ℚ → ℚ → ℚ → ℚ
pairCrossSum p0 p1 p2 p3 =
  p0 * p1
  + (p0 * p2
  + (p0 * p3
  + (p1 * p2
  + (p1 * p3 + p2 * p3))))

fourSquareSum : ℚ → ℚ → ℚ → ℚ → ℚ
fourSquareSum p0 p1 p2 p3 =
  sq p0 + (sq p1 + (sq p2 + sq p3))

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

fourSquareExpansionRaw : ∀ p0 p1 p2 p3 →
  sq (p0 + (p1 + (p2 + p3)))
  ≡ fourSquareSum p0 p1 p2 p3
    + twoℚ * pairCrossSum p0 p1 p2 p3
fourSquareExpansionRaw = ℚRing.solve-∀

pairCrossSumZero : ∀ p0 p1 p2 p3 →
  p0 * p1 ≡ 0ℚ →
  p0 * p2 ≡ 0ℚ →
  p0 * p3 ≡ 0ℚ →
  p1 * p2 ≡ 0ℚ →
  p1 * p3 ≡ 0ℚ →
  p2 * p3 ≡ 0ℚ →
  pairCrossSum p0 p1 p2 p3 ≡ 0ℚ
pairCrossSumZero p0 p1 p2 p3
  p01 p02 p03 p12 p13 p23
  rewrite p01 | p02 | p03 | p12 | p13 | p23 =
  ℚRing.solve-∀

fourAxisMartingaleOrthogonalityImpliesVariance :
  ∀ p0 p1 p2 p3 →
  p0 * p1 ≡ 0ℚ →
  p0 * p2 ≡ 0ℚ →
  p0 * p3 ≡ 0ℚ →
  p1 * p2 ≡ 0ℚ →
  p1 * p3 ≡ 0ℚ →
  p2 * p3 ≡ 0ℚ →
  sq (p0 + (p1 + (p2 + p3)))
  ≡ fourSquareSum p0 p1 p2 p3
fourAxisMartingaleOrthogonalityImpliesVariance p0 p1 p2 p3
  p01 p02 p03 p12 p13 p23 =
  trans
    (fourSquareExpansionRaw p0 p1 p2 p3)
    (subst
      (λ cross →
        fourSquareSum p0 p1 p2 p3 + twoℚ * cross
        ≡ fourSquareSum p0 p1 p2 p3)
      (pairCrossSumZero p0 p1 p2 p3 p01 p02 p03 p12 p13 p23)
      (ℚRing.solve-∀
        (fourSquareSum p0 p1 p2 p3)))

fourAxisVarianceDecomposition :
  ∀ x p0 p1 p2 p3 →
  x ≡ p0 + (p1 + (p2 + p3)) →
  p0 * p1 ≡ 0ℚ →
  p0 * p2 ≡ 0ℚ →
  p0 * p3 ≡ 0ℚ →
  p1 * p2 ≡ 0ℚ →
  p1 * p3 ≡ 0ℚ →
  p2 * p3 ≡ 0ℚ →
  sq x ≡ fourSquareSum p0 p1 p2 p3
fourAxisVarianceDecomposition x p0 p1 p2 p3 decomposition
  p01 p02 p03 p12 p13 p23 =
  trans
    (subst
      (λ value → sq x ≡ sq value)
      decomposition
      (ℚRing.solve-∀ x))
    (fourAxisMartingaleOrthogonalityImpliesVariance
      p0 p1 p2 p3 p01 p02 p03 p12 p13 p23)

fourAxisMartingaleTelescopingLevel : ProofLevel
fourAxisMartingaleTelescopingLevel = computed

fourAxisVarianceFromOrthogonalityLevel : ProofLevel
fourAxisVarianceFromOrthogonalityLevel = machineChecked

physicalAxisAverageOrthogonalityLevel : ProofLevel
physicalAxisAverageOrthogonalityLevel = conditional
