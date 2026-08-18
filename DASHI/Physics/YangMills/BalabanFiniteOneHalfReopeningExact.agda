module DASHI.Physics.YangMills.BalabanFiniteOneHalfReopeningExact where

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
-- DASHI CONTRIBUTION
--
-- Reuse the generic finite strict-contraction algebra at the coarser constant
-- q=1/2 needed by the physically projected Schur residual.  If
--
--       x + R x = y,
--       ||R x||_1 <= (1/2)||x||_1,
--
-- then exact rational arithmetic gives
--
--       ||x||_1 <= 2 ||y||_1.
--
-- In the homogeneous equation this forces zero l1 norm, and the existing
-- proof-bearing finite selector turns zero l1 norm into pointwise zero.  This
-- is not a new analytic authority: it is the q=1/2 specialization of the same
-- finite triangle/gap argument already used at q=1/6.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Strict
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

oneHalf two : ℚ
oneHalf = + 1 / 2
two = + 2 / 1

oneHalfGapExact : 1ℚ - oneHalf ≡ oneHalf
oneHalfGapExact = ℚRing.solve []

twoTimesOneHalfExact : two * oneHalf ≡ 1ℚ
twoTimesOneHalfExact = ℚRing.solve []

oneHalfReopeningBound :
  ∀ {Index : Set}
    (indices : Agda.Builtin.List.List Index)
    (residual : Strict.Vector Index → Strict.Vector Index)
    solution source →
  Strict.IdentityPlusResidualEquation residual solution source →
  L1.vectorL1 indices (residual solution)
    ≤ oneHalf * L1.vectorL1 indices solution →
  L1.vectorL1 indices solution
    ≤ two * L1.vectorL1 indices source
oneHalfReopeningBound
    indices residual solution source equation residualContraction =
  let
    xNorm = L1.vectorL1 indices solution
    yNorm = L1.vectorL1 indices source
    rNorm = L1.vectorL1 indices (residual solution)

    triangle : xNorm ≤ yNorm + rNorm
    triangle = Strict.solutionL1ReopeningUpper
      indices residual solution source equation

    replaceResidual : yNorm + rNorm ≤ yNorm + oneHalf * xNorm
    replaceResidual = ℚP.+-monoʳ-≤ yNorm residualContraction

    beforeGap : xNorm ≤ yNorm + oneHalf * xNorm
    beforeGap = ℚP.≤-trans triangle replaceResidual

    gapRaw : (1ℚ - oneHalf) * xNorm ≤ yNorm
    gapRaw = Strict.reopeningGapBound xNorm yNorm oneHalf beforeGap

    gap : oneHalf * xNorm ≤ yNorm
    gap = subst
      (λ lower → lower ≤ yNorm)
      (cong (_* xNorm) oneHalfGapExact)
      gapRaw

    scaled : two * (oneHalf * xNorm) ≤ two * yNorm
    scaled = Norm.scaleNonnegative two (ℚP.nonNegative⁻¹ two) gap

    leftExact : two * (oneHalf * xNorm) ≡ xNorm
    leftExact =
      trans
        (ℚRing.solve-∀ two oneHalf xNorm :
          two * (oneHalf * xNorm) ≡ (two * oneHalf) * xNorm)
        (trans
          (cong (_* xNorm) twoTimesOneHalfExact)
          (ℚRing.solve-∀ xNorm))
  in
  subst
    (λ lower → lower ≤ two * yNorm)
    leftExact scaled

oneHalfHomogeneousReopeningZeroNorm :
  ∀ {Index : Set}
    (indices : Agda.Builtin.List.List Index)
    (residual : Strict.Vector Index → Strict.Vector Index)
    solution →
  Strict.IdentityPlusResidualEquation residual solution Strict.zeroVector →
  L1.vectorL1 indices (residual solution)
    ≤ oneHalf * L1.vectorL1 indices solution →
  L1.vectorL1 indices solution ≡ 0ℚ
oneHalfHomogeneousReopeningZeroNorm
    indices residual solution equation residualContraction =
  let
    upper :
      L1.vectorL1 indices solution
      ≤ two * L1.vectorL1 indices Strict.zeroVector
    upper = oneHalfReopeningBound
      indices residual solution Strict.zeroVector equation residualContraction

    upperZero : L1.vectorL1 indices solution ≤ 0ℚ
    upperZero = subst
      (λ right → L1.vectorL1 indices solution ≤ right)
      (trans
        (cong (two *_) (Strict.zeroVectorL1Exact indices))
        (ℚRing.solve []))
      upper
  in
  ℚP.≤-antisym upperZero (Strict.vectorL1Nonnegative indices solution)

oneHalfHomogeneousReopeningPointwiseZero :
  ∀ {Index : Set}
    (selector : Basis.FiniteSelector Index)
    (residual : Strict.Vector Index → Strict.Vector Index)
    solution →
  Strict.IdentityPlusResidualEquation residual solution Strict.zeroVector →
  L1.vectorL1 (Basis.elements selector) (residual solution)
    ≤ oneHalf * L1.vectorL1 (Basis.elements selector) solution →
  ∀ target → solution target ≡ 0ℚ
oneHalfHomogeneousReopeningPointwiseZero
    selector residual solution equation residualContraction =
  Strict.finiteSelectorL1ZeroPointwise selector solution
    (oneHalfHomogeneousReopeningZeroNorm
      (Basis.elements selector) residual solution equation residualContraction)

finiteOneHalfReopeningLevel : ProofLevel
finiteOneHalfReopeningLevel = machineChecked

finiteOneHalfReopeningFactorTwoLevel : ProofLevel
finiteOneHalfReopeningFactorTwoLevel = machineChecked
