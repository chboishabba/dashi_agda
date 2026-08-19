module DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact where

------------------------------------------------------------------------
-- ROUND69: EXACT CONTINUUM TAIL MODULUS FROM THE 17/32 ONE-STEP RG BUDGET
--
-- PRIMARY SOURCES / CALIBRATION
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- P. K. Mitter,
-- "The Exact Renormalization Group",
-- Encyclopedia of Mathematical Physics (2006).
-- DOI: 10.1016/B0-12-512666-2/00071-7.
--
-- DASHI CONTRIBUTION
--
-- Round66 proved the all-depth recurrence for theta = 17/32.  The Clay-facing
-- continuum consumers need a Cauchy TAIL modulus, not merely a pointwise bound
-- on K_n.  This module closes that algebra exactly.
--
-- If the physical unified norm gives increments
--
--      d_n <= C theta^n,       theta = 17/32,
--
-- then every finite tail satisfies
--
--      sum_{j=0}^{m-1} d_{N+j}
--        <= (32/15) C theta^N.
--
-- Thus 32/15 is the exact geometric-tail loss.  Once the SAME physical norm
-- establishes the one-step increment estimate, no further summability theorem
-- is required to obtain a common continuum modulus for ordinary observables,
-- composite insertions, connected correlations, and any additional
-- nonexpansive coordinate placed in that norm.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact as Iter

tailFactor : ℚ
tailFactor = + 32 / 15

finiteGeometric : Nat → ℚ
finiteGeometric zero = 0ℚ
finiteGeometric (suc n) = 1ℚ + Iter.theta * finiteGeometric n

finiteGeometricClosedForm : ∀ n →
  (+ 15 / 32) * finiteGeometric n ≡ 1ℚ - Iter.thetaPower n
finiteGeometricClosedForm zero = ℚRing.solve []
finiteGeometricClosedForm (suc n)
  rewrite finiteGeometricClosedForm n =
  ℚRing.solve-∀ (Iter.thetaPower n)

powNonnegative : ∀ n → 0ℚ ≤ Iter.thetaPower n
powNonnegative zero = ℚP.0≤1
powNonnegative (suc n) =
  let
    instance thetaNN : ℚ.NonNegative Iter.theta
    thetaNN = ℚ.nonNegative Iter.thetaNonnegative
    instance powNN : ℚ.NonNegative (Iter.thetaPower n)
    powNN = ℚ.nonNegative (powNonnegative n)
  in
  ℚP.nonNegative⁻¹ (Iter.thetaPower (suc n))

finiteGeometricBelowTailFactor : ∀ n → finiteGeometric n ≤ tailFactor
finiteGeometricBelowTailFactor n =
  let
    powerNN = powNonnegative n
    oneMinusPowerBelowOne : 1ℚ - Iter.thetaPower n ≤ 1ℚ
    oneMinusPowerBelowOne =
      let shifted = ℚP.+-monoˡ-≤ (1ℚ - Iter.thetaPower n) powerNN
      in subst
        (λ right → 1ℚ - Iter.thetaPower n ≤ right)
        (ℚRing.solve-∀ (Iter.thetaPower n)) shifted

    scaled :
      (+ 32 / 15) * ((+ 15 / 32) * finiteGeometric n)
      ≤ (+ 32 / 15) * 1ℚ
    scaled = Norm.scaleNonnegative (+ 32 / 15)
      (ℚP.nonNegative⁻¹ (+ 32 / 15))
      (subst
        (λ left → left ≤ 1ℚ)
        (sym (finiteGeometricClosedForm n))
        oneMinusPowerBelowOne)
  in
  subst
    (λ left → left ≤ tailFactor)
    (ℚRing.solve-∀ (finiteGeometric n))
    (subst
      (λ right → finiteGeometric n ≤ right)
      (ℚRing.solve []) scaled)

shiftedFiniteTail : Nat → Nat → ℚ
shiftedFiniteTail start zero = 0ℚ
shiftedFiniteTail start (suc count) =
  shiftedFiniteTail start count + Iter.thetaPower (start + count)

powAdd : ∀ left right →
  Iter.thetaPower (left + right)
  ≡ Iter.thetaPower left * Iter.thetaPower right
powAdd left zero = sym (ℚP.*-identityʳ (Iter.thetaPower left))
powAdd left (suc right)
  rewrite powAdd left right =
  ℚRing.solve-∀ (Iter.thetaPower left) (Iter.thetaPower right)

shiftedFiniteTailFactorizes : ∀ start count →
  shiftedFiniteTail start count
  ≡ Iter.thetaPower start * finiteGeometric count
shiftedFiniteTailFactorizes start zero = ℚRing.solve-∀ (Iter.thetaPower start)
shiftedFiniteTailFactorizes start (suc count)
  rewrite shiftedFiniteTailFactorizes start count
        | powAdd start count =
  ℚRing.solve-∀
    (Iter.thetaPower start)
    (Iter.thetaPower count)
    (finiteGeometric count)

record GeometricUnifiedIncrementMajorant : Set₁ where
  field
    increment : Nat → ℚ
    amplitude : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude
    incrementBound : ∀ n → increment n ≤ amplitude * Iter.thetaPower n
open GeometricUnifiedIncrementMajorant public

finiteIncrementTail : GeometricUnifiedIncrementMajorant → Nat → Nat → ℚ
finiteIncrementTail dataSet start zero = 0ℚ
finiteIncrementTail dataSet start (suc count) =
  finiteIncrementTail dataSet start count + increment dataSet (start + count)

finiteIncrementTailBelowGeometric :
  (dataSet : GeometricUnifiedIncrementMajorant) →
  ∀ start count →
  finiteIncrementTail dataSet start count
  ≤ amplitude dataSet * shiftedFiniteTail start count
finiteIncrementTailBelowGeometric dataSet start zero =
  subst (λ right → 0ℚ ≤ right) (ℚRing.solve-∀ (amplitude dataSet)) ℚP.≤-refl
finiteIncrementTailBelowGeometric dataSet start (suc count) =
  let
    induction = finiteIncrementTailBelowGeometric dataSet start count
    step = incrementBound dataSet (start + count)
    summed = ℚP.+-mono-≤ induction step
  in
  subst
    (λ right →
      finiteIncrementTail dataSet start count
        + increment dataSet (start + count) ≤ right)
    (ℚRing.solve-∀
      (amplitude dataSet)
      (shiftedFiniteTail start count)
      (Iter.thetaPower (start + count)))
    summed

finiteIncrementTailModulus :
  (dataSet : GeometricUnifiedIncrementMajorant) →
  ∀ start count →
  finiteIncrementTail dataSet start count
  ≤ tailFactor * amplitude dataSet * Iter.thetaPower start
finiteIncrementTailModulus dataSet start count =
  let
    first = finiteIncrementTailBelowGeometric dataSet start count
    factorized :
      amplitude dataSet * shiftedFiniteTail start count
      ≡ amplitude dataSet * Iter.thetaPower start * finiteGeometric count
    factorized rewrite shiftedFiniteTailFactorizes start count =
      ℚRing.solve-∀
        (amplitude dataSet)
        (Iter.thetaPower start)
        (finiteGeometric count)

    scaleNN : 0ℚ ≤ amplitude dataSet * Iter.thetaPower start
    scaleNN =
      let
        instance aNN : ℚ.NonNegative (amplitude dataSet)
        aNN = ℚ.nonNegative (amplitudeNonnegative dataSet)
        instance pNN : ℚ.NonNegative (Iter.thetaPower start)
        pNN = ℚ.nonNegative (powNonnegative start)
      in ℚP.nonNegative⁻¹ (amplitude dataSet * Iter.thetaPower start)

    second :
      amplitude dataSet * Iter.thetaPower start * finiteGeometric count
      ≤ amplitude dataSet * Iter.thetaPower start * tailFactor
    second = Norm.scaleNonnegative
      (amplitude dataSet * Iter.thetaPower start)
      scaleNN
      (finiteGeometricBelowTailFactor count)
  in
  ℚP.≤-trans
    (subst
      (λ right → finiteIncrementTail dataSet start count ≤ right)
      factorized first)
    (subst
      (λ right →
        amplitude dataSet * Iter.thetaPower start * finiteGeometric count
        ≤ right)
      (ℚRing.solve-∀
        tailFactor (amplitude dataSet) (Iter.thetaPower start))
      second)

seventeenThirtySecondTailModulusLevel : ProofLevel
seventeenThirtySecondTailModulusLevel = machineChecked

-- Physical input remains ONE same-object statement: the unified Yang--Mills
-- norm increment at scale n is bounded by C theta^n uniformly in volume and
-- cutoff.  This module then gives the exact common Cauchy modulus downstream.
physicalUnifiedGeometricIncrementMajorantLevel : ProofLevel
physicalUnifiedGeometricIncrementMajorantLevel = conditional
