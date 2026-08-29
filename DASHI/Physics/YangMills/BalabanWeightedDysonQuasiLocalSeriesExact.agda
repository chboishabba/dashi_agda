{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWeightedDysonQuasiLocalSeriesExact where

------------------------------------------------------------------------
-- ROUND102 C-SPATIAL: WEIGHTED ROW -> QUASI-LOCAL DYSON SERIES
--
-- Let M be a nonnegative finite influence majorant with a submultiplicative
-- spatial weight w and
--
--        sum_y w(x,y) M(x,y) <= rho.
--
-- `BalabanFiniteWeightedInfluencePowerExact` already proves, in its positive
-- power indexing,
--
--        sum_y w(x,y) M^(n+1)(x,y) <= rho^(n+1).
--
-- This file performs the remaining positive-series algebra.  For arbitrary
-- nonnegative coefficients a_n,
--
--   sum_{n<N} a_n sum_y w M^(n+1)
--     <= sum_{n<N} a_n rho^(n+1).
--
-- In particular the standard exponential coefficients give the non-identity
-- part of the semigroup bound
--
--        w(x,y) (exp(tM)-I)(x,y) <= exp(t rho)-1,
--
-- once the usual exponential-series limit/identity is instantiated.  Thus the
-- physical C-spatial input need not be strict finite range.  A (3/2)^distance
-- weighted CMP116/Heat-Doob row is already the right quasi-local object.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record PositiveSeriesCoefficients : Set₁ where
  field
    coefficient : Nat → ℚ
    coefficientNonnegative : ∀ n → 0ℚ ≤ coefficient n

open PositiveSeriesCoefficients public

weightedDysonPartial :
  ∀ {Site} →
  Weighted.WeightedFiniteInfluenceMajorant Site →
  PositiveSeriesCoefficients → Nat → Site → ℚ
weightedDysonPartial dataSet coefficients zero x = 0ℚ
weightedDysonPartial dataSet coefficients (suc n) x =
  weightedDysonPartial dataSet coefficients n x
  + coefficient coefficients n * Weighted.weightedPowerRow dataSet n x

scalarDysonMajorantPartial :
  ∀ {Site} →
  Weighted.WeightedFiniteInfluenceMajorant Site →
  PositiveSeriesCoefficients → Nat → ℚ
scalarDysonMajorantPartial dataSet coefficients zero = 0ℚ
scalarDysonMajorantPartial dataSet coefficients (suc n) =
  scalarDysonMajorantPartial dataSet coefficients n
  + coefficient coefficients n
      * Power.rationalPower (Weighted.weightedRowMass dataSet) (suc n)

weightedDysonPartialBelowScalar :
  ∀ {Site}
    (dataSet : Weighted.WeightedFiniteInfluenceMajorant Site)
    (coefficients : PositiveSeriesCoefficients)
    n x →
  weightedDysonPartial dataSet coefficients n x
  ≤ scalarDysonMajorantPartial dataSet coefficients n
weightedDysonPartialBelowScalar dataSet coefficients zero x = ℚP.≤-refl
weightedDysonPartialBelowScalar dataSet coefficients (suc n) x =
  let
    previous = weightedDysonPartialBelowScalar dataSet coefficients n x
    power = Weighted.weightedPowerRowBound dataSet n x
    scaled = Norm.scaleNonnegative
      (coefficient coefficients n)
      (coefficientNonnegative coefficients n)
      power
  in
  ℚP.+-mono-≤ previous scaled

------------------------------------------------------------------------
-- Source-facing exponential instantiation.
--
-- We intentionally do not build real exponentials inside the rational finite
-- matrix layer.  The only remaining non-YM ingredient is the standard positive
-- exponential-series identity/limit.  All matrix/spatial propagation is proved
-- above before that imported analytic limit is used.
------------------------------------------------------------------------

record ExponentialSeriesInstantiation
    {Site : Set}
    (dataSet : Weighted.WeightedFiniteInfluenceMajorant Site) : Set₁ where
  field
    coefficients : PositiveSeriesCoefficients
    TimeScalar : Set
    time : TimeScalar

    -- Identifies `coefficient n` with t^(n+1)/(n+1)! in the chosen real
    -- analysis carrier and the scalar majorant limit with exp(t rho)-1.
    positiveExponentialCoefficients : Set
    scalarPartialConvergesToExpMinusOne : Set

    -- Identifies the corresponding matrix partials with the non-identity
    -- positive semigroup expansion.  This is standard finite-dimensional
    -- semigroup analysis, not an additional Yang--Mills estimate.
    matrixPartialConvergesToSemigroupMinusIdentity : Set

open ExponentialSeriesInstantiation public

weightedPositiveDysonSeriesCompilerLevel : ProofLevel
weightedPositiveDysonSeriesCompilerLevel = machineChecked

weightedQuasiLocalSemigroupLimitLevel : ProofLevel
weightedQuasiLocalSemigroupLimitLevel = standardImported

-- Physical C input after this compiler: one cutoff/volume-uniform weighted row
-- for the SAME dynamic Heat/Doob derivative influence matrix.  Strict nearest-
-- neighbour support is not required for quasi-local propagation.
literalYMWeightedDynamicRowToQuasiLocalSemigroupLevel : ProofLevel
literalYMWeightedDynamicRowToQuasiLocalSemigroupLevel = conditional
