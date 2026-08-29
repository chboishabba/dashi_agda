module DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Krzysztof Gawedzki and Antti Kupiainen,
-- "A Rigorous Block Spin Approach to Massless Lattice Theories",
-- Communications in Mathematical Physics 77 (1980), 31--64.
-- DOI: 10.1007/BF01205038.
--
-- Krzysztof Gawedzki and Antti Kupiainen,
-- "Massless Lattice phi^4_4 Theory: Rigorous Control of a Renormalizable
-- Asymptotically Free Model",
-- Communications in Mathematical Physics 99 (1985), 197--252.
-- DOI: 10.1007/BF01212281.
--
-- Tadeusz Balaban, John Imbrie and Arthur Jaffe,
-- "Exact Renormalization Group for Gauge Theories",
-- in Progress in Gauge Field Theory, Plenum Press, 1984, pp. 79ff.
-- No DOI is recorded for the proceedings contribution used here.
--
-- DASHI CONTRIBUTION
--
-- Extract the high-alpha continuum mechanism common to the rigorous block-spin
-- literature: do not demand summability of the full massless propagator.
-- Instead prove a summable bound on the change of a renormalized observable
-- from one RG scale to the next.  If
--
--   |O_{n+1}-O_n| <= c (1/4) 2^{-n},
--
-- then every finite tail satisfies the exact Cauchy modulus
--
--   sum_{j=n}^{n+k-1} |O_{j+1}-O_j| <= c (1/2) 2^{-n}.
--
-- The geometric core is reused from the already machine-checked Ursell Cauchy
-- lane.  This module therefore reduces continuum convergence of each physical
-- renormalized observable to one scale-local increment producer, matching the
-- Gawedzki--Kupiainen strategy where the scale fluctuation covariance has
-- exponential falloff even though the full massless covariance is not
-- absolutely summable.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact as Ursell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

record ScaleLocalIncrementMajorant : Set₁ where
  field
    coefficient : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient
    incrementMagnitude : Nat → ℚ
    incrementNonnegative : ∀ depth → 0ℚ ≤ incrementMagnitude depth
    incrementBelowScaleShell : ∀ depth →
      incrementMagnitude depth
      ≤ coefficient * (Ursell.quarter * Geo.halfPower depth)
open ScaleLocalIncrementMajorant public

scaleIncrementTail : ScaleLocalIncrementMajorant → Nat → Nat → ℚ
scaleIncrementTail dataSet start zero = 0ℚ
scaleIncrementTail dataSet start (suc count) =
  incrementMagnitude dataSet start
  + scaleIncrementTail dataSet (suc start) count

scaledGeometricTail : ScaleLocalIncrementMajorant → Nat → Nat → ℚ
scaledGeometricTail dataSet start count =
  coefficient dataSet * Ursell.geometricTailPartial start count

zeroBelowScaledGeometric : ∀ coefficient value →
  0ℚ ≤ coefficient → 0ℚ ≤ value → 0ℚ ≤ coefficient * value
zeroBelowScaledGeometric coefficient value coefficientNonnegative valueNonnegative =
  let
    instance
      coefficientNN : NonNegative coefficient
      coefficientNN = ℚ.nonNegative coefficientNonnegative
      valueNN : NonNegative value
      valueNN = ℚ.nonNegative valueNonnegative
  in
  ℚP.nonNegative⁻¹ (coefficient * value)

incrementTailBelowScaledGeometric :
  (dataSet : ScaleLocalIncrementMajorant) → ∀ start count →
  scaleIncrementTail dataSet start count
  ≤ scaledGeometricTail dataSet start count
incrementTailBelowScaledGeometric dataSet start zero =
  let
    coefficientNN = coefficientNonnegative dataSet
  in
  subst
    (λ upper → 0ℚ ≤ upper)
    (sym (ℚP.*-zeroʳ (coefficient dataSet)))
    (zeroBelowScaledGeometric
      (coefficient dataSet) 0ℚ coefficientNN ℚP.≤-refl)
incrementTailBelowScaledGeometric dataSet start (suc count) =
  let
    headBound = incrementBelowScaleShell dataSet start
    tailBound = incrementTailBelowScaledGeometric dataSet (suc start) count

    summed :
      incrementMagnitude dataSet start
        + scaleIncrementTail dataSet (suc start) count
      ≤ coefficient dataSet * (Ursell.quarter * Geo.halfPower start)
        + coefficient dataSet * Ursell.geometricTailPartial (suc start) count
    summed = ℚP.+-mono-≤ headBound tailBound

    scaleDistributes :
      coefficient dataSet * (Ursell.quarter * Geo.halfPower start)
        + coefficient dataSet * Ursell.geometricTailPartial (suc start) count
      ≡ coefficient dataSet
        * Ursell.geometricTailPartial start (suc count)
    scaleDistributes =
      let
        open import Data.Rational.Tactic.RingSolver as ℚRing
      in
      ℚRing.solve-∀
        (coefficient dataSet)
        Ursell.quarter
        (Geo.halfPower start)
        (Ursell.geometricTailPartial (suc start) count)
  in
  subst
    (λ upper → scaleIncrementTail dataSet start (suc count) ≤ upper)
    scaleDistributes summed

scaleLocalCauchyTail :
  (dataSet : ScaleLocalIncrementMajorant) → ∀ start count →
  scaleIncrementTail dataSet start count
  ≤ coefficient dataSet * (Geo.half * Geo.halfPower start)
scaleLocalCauchyTail dataSet start count =
  let
    geometric = Ursell.geometricTailBelow start count
    scaled = Norm.scaleNonnegative
      (coefficient dataSet)
      (coefficientNonnegative dataSet)
      geometric
  in
  ℚP.≤-trans
    (incrementTailBelowScaledGeometric dataSet start count)
    scaled

------------------------------------------------------------------------
-- Physical observable adapter: once a same-observable difference is bounded
-- by the scale-local increment tail, the Cauchy modulus is automatic.
------------------------------------------------------------------------

record RenormalizedObservableScaleCauchyData : Set₁ where
  field
    majorant : ScaleLocalIncrementMajorant
    scaleDifferenceMagnitude : Nat → Nat → ℚ
    differenceNonnegative : ∀ start count →
      0ℚ ≤ scaleDifferenceMagnitude start count
    differenceBelowIncrementTail : ∀ start count →
      scaleDifferenceMagnitude start count
      ≤ scaleIncrementTail majorant start count
open RenormalizedObservableScaleCauchyData public

renormalizedObservableCauchyModulus :
  (dataSet : RenormalizedObservableScaleCauchyData) → ∀ start count →
  scaleDifferenceMagnitude dataSet start count
  ≤ coefficient (majorant dataSet) * (Geo.half * Geo.halfPower start)
renormalizedObservableCauchyModulus dataSet start count =
  ℚP.≤-trans
    (differenceBelowIncrementTail dataSet start count)
    (scaleLocalCauchyTail (majorant dataSet) start count)

continuumScaleLocalGeometricCauchyLevel : ProofLevel
continuumScaleLocalGeometricCauchyLevel = machineChecked

renormalizedObservableCauchyModulusLevel : ProofLevel
renormalizedObservableCauchyModulusLevel = machineChecked

-- Remaining YM input: instantiate `incrementMagnitude` by the actual change of
-- the same renormalized gauge-invariant Schwinger observable under one physical
-- RG step, uniformly in volume and ultraviolet cutoff.  This is the hard
-- scale-local estimate; generic subsequence extraction is not.
physicalRenormalizedObservableScaleIncrementLevel : ProofLevel
physicalRenormalizedObservableScaleIncrementLevel = conditional
