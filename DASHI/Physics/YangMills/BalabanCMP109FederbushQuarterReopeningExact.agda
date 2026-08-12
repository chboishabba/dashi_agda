module DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Specialize the repository's finite identity-plus-residual reopening algebra
-- to the one-quarter margin requested by the source-scale CMP109 analysis.
-- No Neumann series is taken in Q.  If
--
--     x + R x = y,
--     ||R x||_1 <= (1/4) ||x||_1,
--
-- then finite triangle algebra gives
--
--     (3/4) ||x||_1 <= ||y||_1,
--     ||x||_1 <= (4/3) ||y||_1.
--
-- This is exactly the reopening constant used after the improved L=13
-- squared Newton ratio is converted from <1/16 to the norm contraction <1/4.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis

oneQuarter threeQuarters fourThirds : ℚ
oneQuarter = + 1 / 4
threeQuarters = + 3 / 4
fourThirds = + 4 / 3

quarterGapExact : 1ℚ - oneQuarter ≡ threeQuarters
quarterGapExact = ℚRing.solve []

fourThirdsTimesThreeQuartersExact :
  fourThirds * threeQuarters ≡ 1ℚ
fourThirdsTimesThreeQuartersExact = ℚRing.solve []

oneQuarterReopeningBound :
  ∀ {Index : Set}
    (indices : List Index)
    (residual : Reopen.Vector Index → Reopen.Vector Index)
    solution source →
  Reopen.IdentityPlusResidualEquation residual solution source →
  L1.vectorL1 indices (residual solution)
    ≤ oneQuarter * L1.vectorL1 indices solution →
  L1.vectorL1 indices solution
    ≤ fourThirds * L1.vectorL1 indices source
oneQuarterReopeningBound
    indices residual solution source equation residualContraction =
  let
    xNorm = L1.vectorL1 indices solution
    yNorm = L1.vectorL1 indices source
    rNorm = L1.vectorL1 indices (residual solution)

    triangle : xNorm ≤ yNorm + rNorm
    triangle = Reopen.solutionL1ReopeningUpper
      indices residual solution source equation

    replaceResidual : yNorm + rNorm ≤ yNorm + oneQuarter * xNorm
    replaceResidual = ℚP.+-monoʳ-≤ yNorm residualContraction

    beforeGap : xNorm ≤ yNorm + oneQuarter * xNorm
    beforeGap = ℚP.≤-trans triangle replaceResidual

    rawGap : (1ℚ - oneQuarter) * xNorm ≤ yNorm
    rawGap = Reopen.reopeningGapBound xNorm yNorm oneQuarter beforeGap

    gap : threeQuarters * xNorm ≤ yNorm
    gap = subst
      (λ lower → lower ≤ yNorm)
      (cong (_* xNorm) quarterGapExact)
      rawGap

    scaled :
      fourThirds * (threeQuarters * xNorm)
      ≤ fourThirds * yNorm
    scaled = Norm.scaleNonnegative fourThirds
      (ℚP.nonNegative⁻¹ fourThirds) gap

    leftExact : fourThirds * (threeQuarters * xNorm) ≡ xNorm
    leftExact = ℚRing.solve-∀ xNorm
  in
  subst
    (λ lower → lower ≤ fourThirds * yNorm)
    leftExact scaled

oneQuarterHomogeneousZeroNorm :
  ∀ {Index : Set}
    (indices : List Index)
    (residual : Reopen.Vector Index → Reopen.Vector Index)
    solution →
  Reopen.IdentityPlusResidualEquation residual solution Reopen.zeroVector →
  L1.vectorL1 indices (residual solution)
    ≤ oneQuarter * L1.vectorL1 indices solution →
  L1.vectorL1 indices solution ≡ 0ℚ
oneQuarterHomogeneousZeroNorm
    indices residual solution equation residualContraction =
  let
    upper = oneQuarterReopeningBound
      indices residual solution Reopen.zeroVector equation residualContraction

    upperZero : L1.vectorL1 indices solution ≤ 0ℚ
    upperZero = subst
      (λ upperBound → L1.vectorL1 indices solution ≤ upperBound)
      (trans
        (cong (fourThirds *_)
          (Reopen.zeroVectorL1Exact indices))
        (ℚRing.solve []))
      upper
  in
  ℚP.≤-antisym upperZero
    (Reopen.vectorL1Nonnegative indices solution)

oneQuarterHomogeneousPointwiseZero :
  ∀ {Index : Set}
    (selector : Basis.FiniteSelector Index)
    (residual : Reopen.Vector Index → Reopen.Vector Index)
    solution →
  Reopen.IdentityPlusResidualEquation residual solution Reopen.zeroVector →
  L1.vectorL1 (Basis.elements selector) (residual solution)
    ≤ oneQuarter * L1.vectorL1 (Basis.elements selector) solution →
  ∀ target → solution target ≡ 0ℚ
oneQuarterHomogeneousPointwiseZero
    selector residual solution equation residualContraction =
  Reopen.finiteSelectorL1ZeroPointwise selector solution
    (oneQuarterHomogeneousZeroNorm
      (Basis.elements selector) residual solution equation residualContraction)

cmp109FederbushQuarterReopeningLevel : ProofLevel
cmp109FederbushQuarterReopeningLevel = machineChecked

cmp109FederbushFourThirdsInverseBoundLevel : ProofLevel
cmp109FederbushFourThirdsInverseBoundLevel = machineChecked
