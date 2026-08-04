module DASHI.Physics.Closure.NSTriadKNLuoFiniteSmoothHardMultiplierFactorExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prove the finite smooth/hard multiplier step rather than recording a
-- multiplier receipt.  Pointwise symbol factorization is lifted to the full
-- finite Fourier fold.  Separately, nonnegative factor and hard magnitudes are
-- combined into a finite Young estimate with one explicit kernel-L1 constant.
-- The same constant is then transported through an arbitrary finite terminal
-- time window.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; subst; sym; trans)
open Eq.≡-Reasoning

sumList :
  ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumList [] value = 0ℚ
sumList (x ∷ xs) value = value x + sumList xs value

sumListExtensional :
  ∀ {A : Set}
    (xs : List A)
    (left right : A → ℚ) →
  ((x : A) → left x ≡ right x) →
  sumList xs left ≡ sumList xs right
sumListExtensional [] left right pointwise = refl
sumListExtensional (x ∷ xs) left right pointwise
  rewrite pointwise x
        | sumListExtensional xs left right pointwise = refl

sumListMonotone :
  ∀ {A : Set}
    (xs : List A)
    (lower upper : A → ℚ) →
  ((x : A) → lower x ≤ upper x) →
  sumList xs lower ≤ sumList xs upper
sumListMonotone [] lower upper pointwise = ℚₚ.≤-refl
sumListMonotone (x ∷ xs) lower upper pointwise =
  ℚₚ.+-mono-≤
    (pointwise x)
    (sumListMonotone xs lower upper pointwise)

sumListScaleLeft :
  ∀ {A : Set}
    (scale : ℚ)
    (xs : List A)
    (value : A → ℚ) →
  sumList xs (λ x → scale * value x)
  ≡ scale * sumList xs value
sumListScaleLeft scale [] value = solve (scale ∷ [])
sumListScaleLeft scale (x ∷ xs) value
  rewrite sumListScaleLeft scale xs value =
  solve (scale ∷ value x ∷ sumList xs value ∷ [])

sumListScaleRight :
  ∀ {A : Set}
    (scale : ℚ)
    (xs : List A)
    (value : A → ℚ) →
  sumList xs (λ x → value x * scale)
  ≡ sumList xs value * scale
sumListScaleRight scale [] value = solve (scale ∷ [])
sumListScaleRight scale (x ∷ xs) value
  rewrite sumListScaleRight scale xs value =
  solve (scale ∷ value x ∷ sumList xs value ∷ [])

record FiniteSmoothHardSymbolFactorization (Mode : Set) : Set where
  field
    modes : List Mode
    smoothSymbol hardSymbol factorSymbol coefficient : Mode → ℚ

    smoothFactorsThroughHard :
      (mode : Mode) →
      smoothSymbol mode ≡ factorSymbol mode * hardSymbol mode

open FiniteSmoothHardSymbolFactorization public

smoothCoefficient :
  ∀ {Mode} → FiniteSmoothHardSymbolFactorization Mode → Mode → ℚ
smoothCoefficient data mode =
  smoothSymbol data mode * coefficient data mode

factorAppliedToHardCoefficient :
  ∀ {Mode} → FiniteSmoothHardSymbolFactorization Mode → Mode → ℚ
factorAppliedToHardCoefficient data mode =
  factorSymbol data mode
  * (hardSymbol data mode * coefficient data mode)

smoothCoefficientFactorsPointwise :
  ∀ {Mode}
    (data : FiniteSmoothHardSymbolFactorization Mode)
    (mode : Mode) →
  smoothCoefficient data mode
  ≡ factorAppliedToHardCoefficient data mode
smoothCoefficientFactorsPointwise data mode
  rewrite smoothFactorsThroughHard data mode =
  solve
    ( factorSymbol data mode
    ∷ hardSymbol data mode
    ∷ coefficient data mode
    ∷ []
    )

smoothFourierFoldFactorsThroughHard :
  ∀ {Mode}
    (data : FiniteSmoothHardSymbolFactorization Mode) →
  sumList (modes data) (smoothCoefficient data)
  ≡ sumList (modes data) (factorAppliedToHardCoefficient data)
smoothFourierFoldFactorsThroughHard data =
  sumListExtensional
    (modes data)
    (smoothCoefficient data)
    (factorAppliedToHardCoefficient data)
    (smoothCoefficientFactorsPointwise data)

record FiniteSmoothHardMagnitudeData (Mode : Set) : Set where
  field
    modes : List Mode

    factorMagnitude kernelMagnitude hardMagnitude : Mode → ℚ
    hardSup kernelL1 : ℚ

    factorNonnegative :
      (mode : Mode) → 0ℚ ≤ factorMagnitude mode
    kernelNonnegative :
      (mode : Mode) → 0ℚ ≤ kernelMagnitude mode
    hardNonnegative :
      (mode : Mode) → 0ℚ ≤ hardMagnitude mode
    hardSupNonnegative : 0ℚ ≤ hardSup

    factorBelowKernel :
      (mode : Mode) → factorMagnitude mode ≤ kernelMagnitude mode
    hardBelowSup :
      (mode : Mode) → hardMagnitude mode ≤ hardSup

    kernelL1Bound :
      sumList modes kernelMagnitude ≤ kernelL1

open FiniteSmoothHardMagnitudeData public

smoothMagnitude :
  ∀ {Mode} → FiniteSmoothHardMagnitudeData Mode → Mode → ℚ
smoothMagnitude data mode =
  factorMagnitude data mode * hardMagnitude data mode

smoothMagnitudeNonnegative :
  ∀ {Mode}
    (data : FiniteSmoothHardMagnitudeData Mode)
    (mode : Mode) →
  0ℚ ≤ smoothMagnitude data mode
smoothMagnitudeNonnegative data mode =
  let
    instance
      factorIsNonnegative =
        nonNegative (factorNonnegative data mode)
      hardIsNonnegative =
        nonNegative (hardNonnegative data mode)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (factorMagnitude data mode)
          (hardMagnitude data mode)
  in
  ℚₚ.nonNegative⁻¹ (smoothMagnitude data mode)

smoothMagnitudePointwiseYoung :
  ∀ {Mode}
    (data : FiniteSmoothHardMagnitudeData Mode)
    (mode : Mode) →
  smoothMagnitude data mode
  ≤ kernelMagnitude data mode * hardSup data
smoothMagnitudePointwiseYoung data mode =
  let
    first :
      factorMagnitude data mode * hardMagnitude data mode
      ≤ kernelMagnitude data mode * hardMagnitude data mode
    first =
      let instance hardIsNonnegative =
        nonNegative (hardNonnegative data mode)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (hardMagnitude data mode)
        (factorBelowKernel data mode)

    second :
      kernelMagnitude data mode * hardMagnitude data mode
      ≤ kernelMagnitude data mode * hardSup data
    second =
      let instance kernelIsNonnegative =
        nonNegative (kernelNonnegative data mode)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (kernelMagnitude data mode)
        (hardBelowSup data mode)
  in
  ℚₚ.≤-trans first second

finiteSmoothHardYoungBound :
  ∀ {Mode}
    (data : FiniteSmoothHardMagnitudeData Mode) →
  sumList (modes data) (smoothMagnitude data)
  ≤ kernelL1 data * hardSup data
finiteSmoothHardYoungBound data =
  let
    pointwiseSum :
      sumList (modes data) (smoothMagnitude data)
      ≤ sumList (modes data)
          (λ mode → kernelMagnitude data mode * hardSup data)
    pointwiseSum =
      sumListMonotone
        (modes data)
        (smoothMagnitude data)
        (λ mode → kernelMagnitude data mode * hardSup data)
        (smoothMagnitudePointwiseYoung data)

    scaledKernel :
      sumList (modes data)
        (λ mode → kernelMagnitude data mode * hardSup data)
      ≡ sumList (modes data) (kernelMagnitude data) * hardSup data
    scaledKernel =
      sumListScaleRight
        (hardSup data)
        (modes data)
        (kernelMagnitude data)

    scaledL1 :
      sumList (modes data) (kernelMagnitude data) * hardSup data
      ≤ kernelL1 data * hardSup data
    scaledL1 =
      let instance hardSupIsNonnegative =
        nonNegative (hardSupNonnegative data)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (hardSup data)
        (kernelL1Bound data)
  in
  ℚₚ.≤-trans
    pointwiseSum
    (subst
      (λ lower → lower ≤ kernelL1 data * hardSup data)
      (sym scaledKernel)
      scaledL1)

record FiniteTerminalSmoothHardFamily (Time Mode : Set) : Set where
  field
    times : List Time
    spatialData : Time → FiniteSmoothHardMagnitudeData Mode
    commonKernelConstant : ℚ

    commonKernelMeaning :
      (time : Time) →
      kernelL1 (spatialData time) ≡ commonKernelConstant

open FiniteTerminalSmoothHardFamily public

terminalSmoothMagnitude :
  ∀ {Time Mode} →
  FiniteTerminalSmoothHardFamily Time Mode → Time → ℚ
terminalSmoothMagnitude family time =
  sumList
    (modes (spatialData family time))
    (smoothMagnitude (spatialData family time))

terminalHardSup :
  ∀ {Time Mode} →
  FiniteTerminalSmoothHardFamily Time Mode → Time → ℚ
terminalHardSup family time = hardSup (spatialData family time)

terminalPointwiseSameConstant :
  ∀ {Time Mode}
    (family : FiniteTerminalSmoothHardFamily Time Mode)
    (time : Time) →
  terminalSmoothMagnitude family time
  ≤ commonKernelConstant family * terminalHardSup family time
terminalPointwiseSameConstant family time =
  subst
    (λ constant →
      terminalSmoothMagnitude family time
      ≤ constant * terminalHardSup family time)
    (commonKernelMeaning family time)
    (finiteSmoothHardYoungBound (spatialData family time))

finiteTerminalSmoothHardYoungBound :
  ∀ {Time Mode}
    (family : FiniteTerminalSmoothHardFamily Time Mode) →
  sumList (times family) (terminalSmoothMagnitude family)
  ≤ commonKernelConstant family
      * sumList (times family) (terminalHardSup family)
finiteTerminalSmoothHardYoungBound family =
  let
    summedPointwise :
      sumList (times family) (terminalSmoothMagnitude family)
      ≤ sumList (times family)
          (λ time →
            commonKernelConstant family * terminalHardSup family time)
    summedPointwise =
      sumListMonotone
        (times family)
        (terminalSmoothMagnitude family)
        (λ time →
          commonKernelConstant family * terminalHardSup family time)
        (terminalPointwiseSameConstant family)
  in
  subst
    (λ upper →
      sumList (times family) (terminalSmoothMagnitude family) ≤ upper)
    (sumListScaleLeft
      (commonKernelConstant family)
      (times family)
      (terminalHardSup family))
    summedPointwise
