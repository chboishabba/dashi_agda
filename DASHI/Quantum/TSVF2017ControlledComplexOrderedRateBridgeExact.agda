{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVF2017ControlledComplexOrderedRateBridgeExact where

------------------------------------------------------------------------
-- P01.L16: original COMPLEX ABL -> ordered rational robustness rate,
-- no Nat-scale calibration proxy and no replacement probability theory.
--
-- Each actual site comes from the existing pointer-controlled isometric
-- rotation on C^2. Its wrong Born overlap is computed from the emitted
-- Hermitian record; the selected per-site certificate is the physical
-- checkable inequality 2 * normSquare(overlap) <= 1.
--
-- The selected arbitrary complex disturbance gammas enter ONLY via the
-- ORIGINAL norm-square of the complex gamma product. Conditional on its
-- Born weight <= 1, a heterogeneous list of separately certified pulses
-- yields the normalized original ABL cross bound:
--
--     (2^k+1) * numerator(wrong ABL) <= denominator(right ABL).
--
-- This does not assume a globally independent physical environment:
-- emitted records here form the source's finite tensor product, while
-- correlated Bell-type examples in CorrelatedEnvironmentMarginalNoGo
-- demonstrate that marginal data alone cannot justify this step.
--
-- The original denominator is positive because its right Born mass is 1.
-- No division or probability-from-complex-amplitude shortcut.
-- Actual physical many-body preparation, nonfactorizing correlations,
-- disturbance-source dynamics, final cosmological postselection, and
-- strongly continuous observer/OS same-generator identity remain OPEN.
--
-- Attribution: Aharonov/Bergmann/Lebowitz, Aharonov/Vaidman,
-- Aharonov/Cohen/Landsberger (2017); existing DASHI complex and ABL owners.
-- SOURCE WRITTEN; Agda kernel receipt pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (cong; subst; subst₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order
import DASHI.Quantum.TSVF2017ControlledPointerRecordUnitaryExact as Pulse
import DASHI.Quantum.TSVF2017HeterogeneousEnvironmentABLExact as Hetero
import DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact as Env
import DASHI.Quantum.TSVF2017OriginalComplexABLSelectedExact as ABL
import DASHI.Quantum.TSVFComplexGammaProductBornExact as Gamma
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as C

two : ℚ
two = 1ℚ + 1ℚ

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = ℚP.0≤∣p∣ 1ℚ

twoNonnegative : 0ℚ ≤ two
twoNonnegative = Order.addNonnegative oneNonnegative oneNonnegative

productNonnegative :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
productNonnegative {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

record CalibratedControlledPulse : Set where
  constructor calibratedControlledPulse
  field
    pulse : Pulse.CertifiedRotation
    actualBornHalfBound :
      two * Hetero.siteBorn (Pulse.emittedEnvironmentSite pulse) ≤ 1ℚ

open CalibratedControlledPulse public

emittedSites : List CalibratedControlledPulse → List Hetero.EnvironmentSite
emittedSites [] = []
emittedSites (site ∷ sites) =
  Pulse.emittedEnvironmentSite (pulse site) ∷ emittedSites sites

count : List CalibratedControlledPulse → Nat
count [] = zero
count (_ ∷ sites) = suc (count sites)

powerTwo : List CalibratedControlledPulse → ℚ
powerTwo [] = 1ℚ
powerTwo (_ ∷ sites) = two * powerTwo sites

-- Exactly the original rational power convention, not a new 2^k.
powerTwoIsOriginalRationalPower :
  (sites : List CalibratedControlledPulse) →
  powerTwo sites ≡ Env.rationalPower two (count sites)
powerTwoIsOriginalRationalPower [] = refl
powerTwoIsOriginalRationalPower (_ ∷ sites) =
  cong (two *_) (powerTwoIsOriginalRationalPower sites)

bornProduct : List CalibratedControlledPulse → ℚ
bornProduct [] = 1ℚ
bornProduct (site ∷ sites) =
  Hetero.siteBorn (Pulse.emittedEnvironmentSite (pulse site))
    * bornProduct sites

emittedBornProductIsOriginal :
  (sites : List CalibratedControlledPulse) →
  Hetero.tensorBornProduct (emittedSites sites) ≡ bornProduct sites
emittedBornProductIsOriginal [] = refl
emittedBornProductIsOriginal (site ∷ sites) =
  cong
    (Hetero.siteBorn (Pulse.emittedEnvironmentSite (pulse site)) *_)
    (emittedBornProductIsOriginal sites)

siteBornNonnegative :
  (site : CalibratedControlledPulse) →
  0ℚ ≤ Hetero.siteBorn (Pulse.emittedEnvironmentSite (pulse site))
siteBornNonnegative site =
  Env.complexBornNonnegative
    (Hetero.siteOverlap (Pulse.emittedEnvironmentSite (pulse site)))

powerTwoNonnegative :
  (sites : List CalibratedControlledPulse) →
  0ℚ ≤ powerTwo sites
powerTwoNonnegative [] = oneNonnegative
powerTwoNonnegative (_ ∷ sites) =
  productNonnegative twoNonnegative (powerTwoNonnegative sites)

bornProductNonnegative :
  (sites : List CalibratedControlledPulse) →
  0ℚ ≤ bornProduct sites
bornProductNonnegative [] = oneNonnegative
bornProductNonnegative (site ∷ sites) =
  productNonnegative
    (siteBornNonnegative site)
    (bornProductNonnegative sites)

-- Actual rational squared Hermitian overlaps, NOT arbitrary Nat weights.
controlledHeterogeneousRate :
  (sites : List CalibratedControlledPulse) →
  powerTwo sites * bornProduct sites ≤ 1ℚ
controlledHeterogeneousRate [] =
  subst (λ value → value ≤ 1ℚ)
    (sym (ℚP.*-identityʳ 1ℚ))
    ℚP.≤-refl
controlledHeterogeneousRate (site ∷ sites) =
  let
    born = Hetero.siteBorn (Pulse.emittedEnvironmentSite (pulse site))
    tailPower = powerTwo sites
    tailBorn = bornProduct sites

    step :
      (two * born) * (tailPower * tailBorn) ≤ 1ℚ * 1ℚ
    step =
      Order.nonnegativeProductMonotone
        (productNonnegative twoNonnegative (siteBornNonnegative site))
        (productNonnegative
          (powerTwoNonnegative sites) (bornProductNonnegative sites))
        oneNonnegative oneNonnegative
        (actualBornHalfBound site)
        (controlledHeterogeneousRate sites)

    stepOne :
      (two * born) * (tailPower * tailBorn) ≤ 1ℚ
    stepOne =
      subst (λ bound → (two * born) * (tailPower * tailBorn) ≤ bound)
        (ℚP.*-identityʳ 1ℚ) step

    regroup :
      (two * tailPower) * (born * tailBorn)
      ≡ (two * born) * (tailPower * tailBorn)
    regroup = ℚRing.solve-∀ two tailPower born tailBorn
  in
  subst (λ value → value ≤ 1ℚ) (sym regroup) stepOne

gammaBornNonnegative :
  (gammas : List C.RationalComplex) →
  0ℚ ≤ Gamma.complexGammaBornWeight gammas
gammaBornNonnegative gammas =
  subst
    (λ value → 0ℚ ≤ value)
    (Gamma.complexGammaBornWeightIsNormOfProduct gammas)
    (Env.complexBornNonnegative (Gamma.complexGammaProduct gammas))

originalWrongABLFromControlledPulses :
  (gammas : List C.RationalComplex)
  (sites : List CalibratedControlledPulse) →
  ABL.numerator (Hetero.wrongABL gammas (emittedSites sites))
  ≡ Gamma.complexGammaBornWeight gammas * bornProduct sites
originalWrongABLFromControlledPulses gammas sites =
  trans
    (Hetero.heterogeneousOriginalABLHasCorrectBornFactor
      gammas (emittedSites sites))
    (cong (Gamma.complexGammaBornWeight gammas *_)
      (emittedBornProductIsOriginal sites))

-- The exact rational bridge from actual complex Born weights to the
-- rate comparison, without any Nat/raw-denominator calibration axiom.
originalControlledWrongRate :
  (gammas : List C.RationalComplex)
  (sites : List CalibratedControlledPulse) →
  Gamma.complexGammaBornWeight gammas ≤ 1ℚ →
  powerTwo sites
    * ABL.numerator (Hetero.wrongABL gammas (emittedSites sites))
  ≤ 1ℚ
originalControlledWrongRate gammas sites gammaBound =
  let
    gamma = Gamma.complexGammaBornWeight gammas
    product = bornProduct sites
    power = powerTwo sites

    monotone :
      gamma * (power * product) ≤ 1ℚ * 1ℚ
    monotone =
      Order.nonnegativeProductMonotone
        (gammaBornNonnegative gammas)
        (productNonnegative
          (powerTwoNonnegative sites) (bornProductNonnegative sites))
        oneNonnegative oneNonnegative
        gammaBound (controlledHeterogeneousRate sites)

    underOne : gamma * (power * product) ≤ 1ℚ
    underOne =
      subst (λ bound → gamma * (power * product) ≤ bound)
        (ℚP.*-identityʳ 1ℚ) monotone

    regroup : power * (gamma * product) ≡ gamma * (power * product)
    regroup = ℚRing.solve-∀ power gamma product

    factorized : power * (gamma * product) ≤ 1ℚ
    factorized = subst (λ value → value ≤ 1ℚ)
      (sym regroup) underOne
  in
  subst
    (λ wrong → power * wrong ≤ 1ℚ)
    (sym (originalWrongABLFromControlledPulses gammas sites))
    factorized

-- Same ORIGINAL Q.ablProbability numerator and denominator; positivity
-- is carried by Hetero.positiveHeterogeneousTotal. No invented ratio.
originalControlledABLExponentialCrossBound :
  (gammas : List C.RationalComplex)
  (sites : List CalibratedControlledPulse) →
  Gamma.complexGammaBornWeight gammas ≤ 1ℚ →
  (powerTwo sites + 1ℚ)
    * ABL.numerator (Hetero.wrongABL gammas (emittedSites sites))
  ≤ ABL.denominator (Hetero.rightABL gammas (emittedSites sites))
originalControlledABLExponentialCrossBound gammas sites gammaBound
  rewrite Hetero.wrongABLNumerator gammas (emittedSites sites)
        | Hetero.rightABLDenominator gammas (emittedSites sites) =
  let
    wrong = Hetero.selectedWrongBorn gammas (emittedSites sites)
    power = powerTwo sites
    fromWrong :
      power * wrong ≤ 1ℚ
    fromWrong =
      subst
        (λ original → power * original ≤ 1ℚ)
        (Hetero.wrongABLNumerator gammas (emittedSites sites))
        (originalControlledWrongRate gammas sites gammaBound)

    addition :
      power * wrong + wrong ≤ 1ℚ + wrong
    addition = ℚP.+-mono-≤ fromWrong ℚP.≤-refl

    expand :
      (power + 1ℚ) * wrong ≡ power * wrong + wrong
    expand = ℚRing.solve-∀ power wrong
  in
  subst (λ value → value ≤ 1ℚ + wrong) (sym expand) addition

-- The source's actual (3/5,4/5) unitary has Born overlap 9/25.
-- Its 2*(9/25) <= 1 site certificate is exact decidable rational order.
threeFourControlledCertified : CalibratedControlledPulse
threeFourControlledCertified =
  calibratedControlledPulse Pulse.threeFourPulse
    (subst
      (λ value → two * value ≤ 1ℚ)
      (sym Pulse.threeFourPulseBornNineTwentyFifths)
      (toWitness
        {a? = two * Pulse.nineTwentyFifths ≤? 1ℚ} _))

replicateThreeFour : Nat → List CalibratedControlledPulse
replicateThreeFour zero = []
replicateThreeFour (suc k) =
  threeFourControlledCertified ∷ replicateThreeFour k

-- All k, actual complex 3/5 pulse records, original selected ABL,
-- and empty disturbance product (Gamma=1) give the same bound.
originalRepeatedUnitaryABLExponentialCrossBound :
  (k : Nat) →
  (powerTwo (replicateThreeFour k) + 1ℚ)
    * ABL.numerator
        (Hetero.wrongABL [] (emittedSites (replicateThreeFour k)))
  ≤ ABL.denominator
      (Hetero.rightABL [] (emittedSites (replicateThreeFour k)))
originalRepeatedUnitaryABLExponentialCrossBound k =
  originalControlledABLExponentialCrossBound
    [] (replicateThreeFour k) ℚP.≤-refl

------------------------------------------------------------------------
-- Correlated-state ERROR branch: exact correction to the independent
-- product bound, NOT a claim that local marginals bound global overlap.
--
-- A physical source must furnish the actual whole-environment amplitude
-- and the additive Born comparison below. The existing Bell marginal
-- no-go shows why those data cannot be inferred from one-site densities.
------------------------------------------------------------------------

record ControlledCorrelationBornError
    (gammas : List C.RationalComplex)
    (sites : List CalibratedControlledPulse) : Set where
  constructor controlledCorrelationBornError
  field
    actualGlobalWrongAmplitude : C.RationalComplex
    errorBorn : ℚ
    errorNonnegative : 0ℚ ≤ errorBorn
    correlatedBornUpper :
      C.complexNormSq actualGlobalWrongAmplitude
      ≤ ABL.numerator (Hetero.wrongABL gammas (emittedSites sites))
          + errorBorn

open ControlledCorrelationBornError public

-- Even with correlated records, if a physical source bounds the
-- GLOBAL Born deviation by delta, 2^k W_actual <= 1+2^k delta.
-- No product factorization is asserted for actualGlobalWrongAmplitude.
correlatedWrongRateWithError :
  (gammas : List C.RationalComplex)
  (sites : List CalibratedControlledPulse) →
  Gamma.complexGammaBornWeight gammas ≤ 1ℚ →
  (errorData : ControlledCorrelationBornError gammas sites) →
  powerTwo sites
    * C.complexNormSq (actualGlobalWrongAmplitude errorData)
  ≤ 1ℚ + powerTwo sites * errorBorn errorData
correlatedWrongRateWithError gammas sites gammaBound errorData =
  let
    power = powerTwo sites
    actual = C.complexNormSq (actualGlobalWrongAmplitude errorData)
    independent =
      ABL.numerator (Hetero.wrongABL gammas (emittedSites sites))
    delta = errorBorn errorData

    instance
      powerNN : NonNegative power
      powerNN = nonNegative (powerTwoNonnegative sites)

    first :
      power * actual ≤ power * (independent + delta)
    first =
      ℚP.*-monoˡ-≤-nonNeg power (correlatedBornUpper errorData)

    distribute :
      power * (independent + delta)
      ≡ power * independent + power * delta
    distribute = ℚRing.solve-∀ power independent delta

    second :
      power * independent + power * delta
      ≤ 1ℚ + power * delta
    second =
      ℚP.+-mono-≤
        (originalControlledWrongRate gammas sites gammaBound)
        ℚP.≤-refl
  in
  ℚP.≤-trans first
    (subst
      (λ lhs → lhs ≤ 1ℚ + power * delta)
      (sym distribute)
      second)

-- Corrected two-channel cross inequality, intentionally not named an
-- original ABL probability for the unconstructed correlated postselection.
-- The actual numerator is a real Born norm, not a new independent label.
correlatedTwoChannelCrossWithError :
  (gammas : List C.RationalComplex)
  (sites : List CalibratedControlledPulse) →
  Gamma.complexGammaBornWeight gammas ≤ 1ℚ →
  (errorData : ControlledCorrelationBornError gammas sites) →
  (powerTwo sites + 1ℚ)
    * C.complexNormSq (actualGlobalWrongAmplitude errorData)
  ≤ 1ℚ
    + C.complexNormSq (actualGlobalWrongAmplitude errorData)
    + powerTwo sites * errorBorn errorData
correlatedTwoChannelCrossWithError gammas sites gammaBound errorData =
  let
    power = powerTwo sites
    actual = C.complexNormSq (actualGlobalWrongAmplitude errorData)
    delta = errorBorn errorData

    raw :
      power * actual + actual
      ≤ (1ℚ + power * delta) + actual
    raw = ℚP.+-mono-≤
      (correlatedWrongRateWithError gammas sites gammaBound errorData)
      ℚP.≤-refl

    expand :
      (power + 1ℚ) * actual ≡ power * actual + actual
    expand = ℚRing.solve-∀ power actual

    rearrange :
      (1ℚ + power * delta) + actual
      ≡ 1ℚ + actual + power * delta
    rearrange = ℚRing.solve-∀ power actual delta
  in
  subst₂ _≤_ (sym expand) rearrange raw

