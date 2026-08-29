{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4BetaResponseKernelSummationExact where

------------------------------------------------------------------------
-- ROW A BIDI RESPONSE-KERNEL COMPILER
--
-- BACKWARD target:
-- shooting only needs a cutoff-uniform Lipschitz constant for the cumulative
-- beta history response.
--
-- FORWARD source shape:
-- a contractive irrelevant/polymer response obeys the one-step inequality
--
--       r_(n+1) <= C s_n + (1/2) r_n,
--
-- where s_n is the direct sensitivity injected at shell n.  Instead of opening
-- a triangular double sum, use the exact potential
--
--       P_n = sum_{j<n} r_j + 2 r_n.
--
-- Then
--
--       P_(n+1) <= P_n + 2 C s_n,
--
-- so, for r_0 = 0 and nonnegative responses,
--
--       sum_{j<n} r_j <= 2 C sum_{j<n} s_j.
--
-- Hence any cutoff-uniform direct-source budget sum s_j <= S_tot gives
--
--       cumulative history sensitivity <= 2 C S_tot.
--
-- This is the same high-alpha structure used by the parallel Lean response
-- kernel lane, but stated without conflating the marginal coupling with the
-- contracting irrelevant coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

sum₀ : (Nat → ℚ) → Nat → ℚ
sum₀ f zero = 0ℚ
sum₀ f (suc n) = sum₀ f n + f n

sum₀Nonnegative :
  (f : Nat → ℚ) → (∀ n → 0ℚ ≤ f n) → ∀ K → 0ℚ ≤ sum₀ f K
sum₀Nonnegative f fNN zero = ℚP.≤-refl
sum₀Nonnegative f fNN (suc n) =
  ℚP.+-mono-≤ (sum₀Nonnegative f fNN n) (fNN n)

record GeometricBetaResponseKernel : Set₁ where
  field
    responseCoefficient : ℚ
    responseCoefficientNonnegative : 0ℚ ≤ responseCoefficient

    sourceSensitivity responseSensitivity : Nat → ℚ
    sourceSensitivityNonnegative : ∀ n → 0ℚ ≤ sourceSensitivity n
    responseSensitivityNonnegative : ∀ n → 0ℚ ≤ responseSensitivity n

    responseAtZero : responseSensitivity zero ≡ 0ℚ

    oneStepResponse : ∀ n →
      responseSensitivity (suc n)
      ≤ responseCoefficient * sourceSensitivity n
        + Geo.half * responseSensitivity n

open GeometricBetaResponseKernel public

responsePotential : GeometricBetaResponseKernel → Nat → ℚ
responsePotential dataSet n =
  sum₀ (responseSensitivity dataSet) n
    + Geo.twoℚ * responseSensitivity dataSet n

responsePotentialAtZero :
  (dataSet : GeometricBetaResponseKernel) →
  responsePotential dataSet zero ≡ 0ℚ
responsePotentialAtZero dataSet
  rewrite responseAtZero dataSet =
  ℚRing.solve []

potentialStep :
  (dataSet : GeometricBetaResponseKernel) → ∀ n →
  responsePotential dataSet (suc n)
  ≤ responsePotential dataSet n
    + Geo.twoℚ * responseCoefficient dataSet * sourceSensitivity dataSet n
potentialStep dataSet n =
  let
    r = responseSensitivity dataSet n
    rNext = responseSensitivity dataSet (suc n)
    C = responseCoefficient dataSet
    s = sourceSensitivity dataSet n

    twoNN : 0ℚ ≤ Geo.twoℚ
    twoNN = ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof

    scaledStep :
      Geo.twoℚ * rNext
      ≤ Geo.twoℚ * (C * s + Geo.half * r)
    scaledStep = Norm.scaleNonnegative Geo.twoℚ twoNN (oneStepResponse dataSet n)

    lifted = ℚP.+-mono-≤ ℚP.≤-refl scaledStep
  in
  subst
    (λ left → left ≤
      responsePotential dataSet n + Geo.twoℚ * C * s)
    (ℚRing.solve-∀
      (sum₀ (responseSensitivity dataSet) n) r rNext)
    (subst
      (λ right →
        sum₀ (responseSensitivity dataSet) n + r
          + Geo.twoℚ * rNext ≤ right)
      (ℚRing.solve-∀
        (sum₀ (responseSensitivity dataSet) n)
        r C s Geo.twoℚ Geo.half)
      lifted)

sourceBudgetScaled :
  (dataSet : GeometricBetaResponseKernel) → Nat → ℚ
sourceBudgetScaled dataSet K =
  Geo.twoℚ * responseCoefficient dataSet
    * sum₀ (sourceSensitivity dataSet) K

potentialBelowScaledSource :
  (dataSet : GeometricBetaResponseKernel) → ∀ K →
  responsePotential dataSet K ≤ sourceBudgetScaled dataSet K
potentialBelowScaledSource dataSet zero =
  subst
    (λ left → left ≤ sourceBudgetScaled dataSet zero)
    (responsePotentialAtZero dataSet)
    ℚP.≤-refl
potentialBelowScaledSource dataSet (suc n) =
  let
    previous = potentialBelowScaledSource dataSet n
    step = potentialStep dataSet n
    chained = ℚP.≤-trans step
      (ℚP.+-mono-≤ previous ℚP.≤-refl)
  in
  subst
    (λ right → responsePotential dataSet (suc n) ≤ right)
    (ℚRing.solve-∀
      Geo.twoℚ
      (responseCoefficient dataSet)
      (sum₀ (sourceSensitivity dataSet) n)
      (sourceSensitivity dataSet n))
    chained

cumulativeResponseBelowPotential :
  (dataSet : GeometricBetaResponseKernel) → ∀ K →
  sum₀ (responseSensitivity dataSet) K ≤ responsePotential dataSet K
cumulativeResponseBelowPotential dataSet K =
  let
    twoNN : 0ℚ ≤ Geo.twoℚ
    twoNN = ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof
    tailNN : 0ℚ ≤ Geo.twoℚ * responseSensitivity dataSet K
    tailNN =
      let
        instance
          twoNonnegative : NonNegative Geo.twoℚ
          twoNonnegative = ℚ.nonNegative twoNN
          responseNonnegative : NonNegative (responseSensitivity dataSet K)
          responseNonnegative =
            ℚ.nonNegative (responseSensitivityNonnegative dataSet K)
      in
      ℚP.nonNegative⁻¹
        (Geo.twoℚ * responseSensitivity dataSet K)
  in
  subst
    (λ left → left ≤ responsePotential dataSet K)
    (ℚP.+-identityʳ (sum₀ (responseSensitivity dataSet) K))
    (ℚP.+-monoʳ-≤
      (sum₀ (responseSensitivity dataSet) K) tailNN)

cumulativeResponseBelowScaledSource :
  (dataSet : GeometricBetaResponseKernel) → ∀ K →
  sum₀ (responseSensitivity dataSet) K
  ≤ Geo.twoℚ * responseCoefficient dataSet
      * sum₀ (sourceSensitivity dataSet) K
cumulativeResponseBelowScaledSource dataSet K =
  ℚP.≤-trans
    (cumulativeResponseBelowPotential dataSet K)
    (potentialBelowScaledSource dataSet K)

record UniformSourceSensitivityBudget
    (kernel : GeometricBetaResponseKernel) : Set where
  field
    totalSourceSensitivity : ℚ
    totalSourceSensitivityNonnegative : 0ℚ ≤ totalSourceSensitivity
    sourcePartialBelowTotal : ∀ K →
      sum₀ (sourceSensitivity kernel) K ≤ totalSourceSensitivity

open UniformSourceSensitivityBudget public

uniformCumulativeResponse :
  ∀ {kernel}
    (budget : UniformSourceSensitivityBudget kernel) K →
  sum₀ (responseSensitivity kernel) K
  ≤ Geo.twoℚ * responseCoefficient kernel
      * totalSourceSensitivity budget
uniformCumulativeResponse {kernel} budget K =
  let
    coefficientNN :
      0ℚ ≤ Geo.twoℚ * responseCoefficient kernel
    coefficientNN =
      let
        twoNN = ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof
        instance
          twoNonnegative : NonNegative Geo.twoℚ
          twoNonnegative = ℚ.nonNegative twoNN
          cNonnegative : NonNegative (responseCoefficient kernel)
          cNonnegative = ℚ.nonNegative (responseCoefficientNonnegative kernel)
      in
      ℚP.nonNegative⁻¹
        (Geo.twoℚ * responseCoefficient kernel)

    scaled = Norm.scaleNonnegative
      (Geo.twoℚ * responseCoefficient kernel)
      coefficientNN
      (sourcePartialBelowTotal budget K)
  in
  ℚP.≤-trans
    (cumulativeResponseBelowScaledSource kernel K)
    scaled

betaResponseKernelPotentialLevel : ProofLevel
betaResponseKernelPotentialLevel = machineChecked

betaResponseKernelUniformSummationLevel : ProofLevel
betaResponseKernelUniformSummationLevel = machineChecked

-- Physical source seam: instantiate `sourceSensitivity` by the literal direct
-- preceding-coupling response and `responseSensitivity` by the propagated
-- irrelevant/polymer contribution on the same CMP109/CMP119 trajectory.  A
-- source-native geometric response inequality and one uniform direct-source
-- sensitivity budget then replace a monolithic cumulative q assumption.
literalBetaResponseKernelAndSourceBudgetLevel : ProofLevel
literalBetaResponseKernelAndSourceBudgetLevel = conditional
