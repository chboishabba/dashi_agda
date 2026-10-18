module DASHI.Foundations.BishopPolynomialGeometricRatioConvergenceExact where

------------------------------------------------------------------------
-- POLYNOMIAL x GEOMETRIC SERIES: RATIO-TEST COMPILER
--
-- The vendored Bishop Sequence development already proves Proposition 3.6(1):
-- if eventually
--
--   |a_(n+1)| <= rho |a_n|,     0 < rho < 1,
--
-- then sum a_n converges.
--
-- For the Eisenstein majorants the terms are nonnegative:
--
--   a_n = n^k r^n.
--
-- Therefore the entire analytic problem reduces to the standard eventual
-- successor estimate
--
--   (n+1)^k r^(n+1) <= rho n^k r^n.
--
-- This owner compiles that estimate into an actual Bishop convergence theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- 1. Literal polynomial-geometric term.
------------------------------------------------------------------------

polyGeoTerm :
  Nat → BishopReal.ℝ → Nat → BishopReal.ℝ
polyGeoTerm degree ratio n =
  BishopReal._*_
    (BishopReal.pow (NatReal.natReal n) degree)
    (BishopReal.pow ratio n)

------------------------------------------------------------------------
-- 2. Positivity/nonnegativity authority.
------------------------------------------------------------------------

record PolynomialGeometricNonnegative
    (degree : Nat)
    (ratio : BishopReal.ℝ) : Set₁ where
  field
    termNonnegative :
      (n : Nat) →
      BishopReal._≤_
        BishopReal.0ℝ
        (polyGeoTerm degree ratio n)

    absTermIsTerm :
      (n : Nat) →
      BishopReal._≃_
        (BishopReal.∣_∣ (polyGeoTerm degree ratio n))
        (polyGeoTerm degree ratio n)

open PolynomialGeometricNonnegative public

------------------------------------------------------------------------
-- 3. One eventual ratio inequality is sufficient.
------------------------------------------------------------------------

record PolynomialGeometricRatioTail
    (degree : Nat)
    (ratio : BishopReal.ℝ) : Set₁ where
  field
    contractionRatio : BishopReal.ℝ

    contractionPositive :
      BishopReal._<_ BishopReal.0ℝ contractionRatio

    contractionBelowOne :
      BishopReal._<_ contractionRatio BishopReal.1ℝ

    transitionIndex : Nat

    successorContractive :
      (n : Nat) →
      suc transitionIndex ≤ suc n →
      BishopReal._≤_
        (polyGeoTerm degree ratio (suc n))
        (BishopReal._*_
          contractionRatio
          (polyGeoTerm degree ratio n))

open PolynomialGeometricRatioTail public

------------------------------------------------------------------------
-- 4. Machine-checked ratio-test compiler.
------------------------------------------------------------------------

polynomialGeometricSeriesConvergent :
  ∀ {degree ratio} →
  PolynomialGeometricNonnegative degree ratio →
  (tail : PolynomialGeometricRatioTail degree ratio) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (polyGeoTerm degree ratio))
polynomialGeometricSeriesConvergent positivity tail =
  BishopSequence.proposition-3-6-1
    (contractionPositive tail , contractionBelowOne tail)
    (transitionIndex tail ,
      λ n nAtLeastTransition →
        BishopP.≤-respˡ-≃
          (absTermIsTerm positivity (suc n))
          (BishopP.≤-respʳ-≃
            (BishopP.*-congˡ
              (contractionRatio tail)
              (BishopP.≃-symm
                (absTermIsTerm positivity n)))
            (successorContractive tail n nAtLeastTransition)))

------------------------------------------------------------------------
-- 5. Quartic and sextic specializations used by E4/E6.
------------------------------------------------------------------------

quarticDegree : Nat
quarticDegree = 4

sexticDegree : Nat
sexticDegree = 6

quarticGeometricSeriesConvergent :
  ∀ {ratio} →
  PolynomialGeometricNonnegative quarticDegree ratio →
  PolynomialGeometricRatioTail quarticDegree ratio →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (polyGeoTerm quarticDegree ratio))
quarticGeometricSeriesConvergent =
  polynomialGeometricSeriesConvergent

sexticGeometricSeriesConvergent :
  ∀ {ratio} →
  PolynomialGeometricNonnegative sexticDegree ratio →
  PolynomialGeometricRatioTail sexticDegree ratio →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (polyGeoTerm sexticDegree ratio))
sexticGeometricSeriesConvergent =
  polynomialGeometricSeriesConvergent

------------------------------------------------------------------------
-- 6. Exact remaining leaf.
------------------------------------------------------------------------

record PolynomialGeometricRatioBoundary : Set where
  constructor polynomial-geometric-ratio-boundary
  field
    bishopRatioTestReused : Bool
    quarticConvergenceCompiledFromSuccessorRatio : Bool
    sexticConvergenceCompiledFromSuccessorRatio : Bool
    eventualSuccessorRatioConstructedForEveryZeroLeRBelowOne : Bool

open import Agda.Builtin.Bool using (Bool; true; false)
open PolynomialGeometricRatioBoundary public

canonicalPolynomialGeometricRatioBoundary :
  PolynomialGeometricRatioBoundary
canonicalPolynomialGeometricRatioBoundary =
  polynomial-geometric-ratio-boundary
    true true true false

bishopPolynomialGeometricRatioCompilerLevel : ProofLevel
bishopPolynomialGeometricRatioCompilerLevel = machineChecked

bishopPolynomialGeometricEventualRatioLevel : ProofLevel
bishopPolynomialGeometricEventualRatioLevel = conditional
