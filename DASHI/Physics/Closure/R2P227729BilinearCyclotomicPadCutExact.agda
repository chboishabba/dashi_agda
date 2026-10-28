module DASHI.Physics.Closure.R2P227729BilinearCyclotomicPadCutExact where

------------------------------------------------------------------------
-- 27×27 INTEGER FREQUENCY BILINEAR CONVOLUTION, arbitrary coefficients.
--
-- A source-written POLYMORPHIC finite aggregation theorem: no ring
-- axioms are needed merely to transport the SAME 729 contributions
-- through either correct retained 4-grid or full-output 5-grid index
-- observation. This works for any supplied zero/add/mul operations.
--
-- Instantiated below with the ORIGINAL exact Q(omega) cyclotomic carrier
-- of DASHI.Biology.Physical.C3CubeCyclotomicFourierExact, and a genuine
-- pair of INDEPENDENT 27-mode coefficient functions (f,g), not u^2 only.
--
-- IMPORTANT: No 4- or 5-point FFT or sample-space field product is
-- built. Our operation is the explicit integer-Fourier bilinear pair
-- aggregation with exact output-frequency classification. It is the
-- correct combinatorial operator the later padded-FFT must reproduce.
--
-- Orszag/Patterson dealiasing prior art; Lambert/Reneuve/Augier 2026.
-- Inherited source authors own the cyclotomic carrier and original
-- C3^3 DFT/Parseval and cyclic-convolution theorem. No Monster action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_,_)

import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as Pairs
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full
import DASHI.Physics.Closure.R2P227729FourGridRetainedQuadraticParetoExact as Four
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as C3

record CoefficientOps (A : Set) : Set₁ where
  field
    zero : A
    add : A → A → A
    multiply : A → A → A

sumUsing :
  ∀ {A : Set} → (ops : CoefficientOps A) →
  (xs : List Pairs.ModePair729) →
  (term : Pairs.ModePair729 → A) → A
sumUsing ops [] term = CoefficientOps.zero ops
sumUsing ops (p ∷ ps) term =
  CoefficientOps.add ops (term p) (sumUsing ops ps term)

sumUsingCong :
  ∀ {A : Set} →
  (ops : CoefficientOps A) →
  (xs : List Pairs.ModePair729) →
  (f g : Pairs.ModePair729 → A) →
  ((pair : Pairs.ModePair729) → f pair ≡ g pair) →
  sumUsing ops xs f ≡ sumUsing ops xs g
sumUsingCong ops [] f g agree = refl
sumUsingCong ops (p ∷ ps) f g agree
  rewrite agree p
        | sumUsingCong ops ps f g agree = refl

choose : ∀ {A : Set} → A → Bool → A → A
choose zero true x = x
choose zero false x = zero

exactContribution :
  ∀ {A : Set} → (ops : CoefficientOps A) →
  (f g : Pairs.ModeCube27 → A) →
  (target : Full.WideCube125) →
  Pairs.ModePair729 → A
exactContribution ops f g target (p , q) =
  choose (CoefficientOps.zero ops)
    (Full.eqWideCube (Full.exactPairOutput p q) target)
    (CoefficientOps.multiply ops (f p) (g q))

fourGridContribution :
  ∀ {A : Set} → (ops : CoefficientOps A) →
  (f g : Pairs.ModeCube27 → A) →
  (target : Pairs.ModeCube27) →
  Pairs.ModePair729 → A
fourGridContribution ops f g target (p , q) =
  choose (CoefficientOps.zero ops)
    (Four.eqFourCube
      (Four.wideToFourGrid (Full.exactPairOutput p q))
      (Four.wideToFourGrid (Full.retainedToWide target)))
    (CoefficientOps.multiply ops (f p) (g q))

fiveGridContribution :
  ∀ {A : Set} → (ops : CoefficientOps A) →
  (f g : Pairs.ModeCube27 → A) →
  (target : Full.WideCube125) →
  Pairs.ModePair729 → A
fiveGridContribution ops f g target (p , q) =
  choose (CoefficientOps.zero ops)
    (Full.eqWideCube
      (Full.fiveGridToWide
        (Full.wideToFiveGrid (Full.exactPairOutput p q)))
      target)
    (CoefficientOps.multiply ops (f p) (g q))

fourGridTermIsTrueRetainedTerm :
  ∀ {A : Set} →
  (ops : CoefficientOps A) (f g : Pairs.ModeCube27 → A) →
  (target : Pairs.ModeCube27) (pair : Pairs.ModePair729) →
  fourGridContribution ops f g target pair
    ≡ exactContribution ops f g (Full.retainedToWide target) pair
fourGridTermIsTrueRetainedTerm ops f g target (p , q)
  rewrite Four.fourGridRetainedCubeMembership
    (Full.exactPairOutput p q) target = refl

fiveGridTermIsTrueFullTerm :
  ∀ {A : Set} →
  (ops : CoefficientOps A) (f g : Pairs.ModeCube27 → A) →
  (target : Full.WideCube125) (pair : Pairs.ModePair729) →
  fiveGridContribution ops f g target pair
    ≡ exactContribution ops f g target pair
fiveGridTermIsTrueFullTerm ops f g target (p , q)
  rewrite Full.pairOutputFivePointRecovered p q = refl

trueBilinearConvolutionAt :
  ∀ {A : Set} → (ops : CoefficientOps A) →
  (f g : Pairs.ModeCube27 → A) →
  Full.WideCube125 → A
trueBilinearConvolutionAt ops f g target =
  sumUsing ops Pairs.pair729 (exactContribution ops f g target)

fourGridBilinearRetainedAt :
  ∀ {A : Set} → (ops : CoefficientOps A) →
  (f g : Pairs.ModeCube27 → A) →
  Pairs.ModeCube27 → A
fourGridBilinearRetainedAt ops f g target =
  sumUsing ops Pairs.pair729 (fourGridContribution ops f g target)

fiveGridBilinearFullAt :
  ∀ {A : Set} → (ops : CoefficientOps A) →
  (f g : Pairs.ModeCube27 → A) →
  Full.WideCube125 → A
fiveGridBilinearFullAt ops f g target =
  sumUsing ops Pairs.pair729 (fiveGridContribution ops f g target)

-- Stronger than the prior "u squared" result: independent f and g,
-- arbitrary A, and zero/add/multiply operations supplied as arguments.
fourGridBilinearRecoversAllRetainedCoefficients :
  ∀ {A : Set} (ops : CoefficientOps A)
  (f g : Pairs.ModeCube27 → A) (target : Pairs.ModeCube27) →
  fourGridBilinearRetainedAt ops f g target
    ≡ trueBilinearConvolutionAt ops f g (Full.retainedToWide target)
fourGridBilinearRecoversAllRetainedCoefficients ops f g target =
  sumUsingCong ops Pairs.pair729
    (fourGridContribution ops f g target)
    (exactContribution ops f g (Full.retainedToWide target))
    (fourGridTermIsTrueRetainedTerm ops f g target)

fiveGridBilinearRecoversAllFullCoefficients :
  ∀ {A : Set} (ops : CoefficientOps A)
  (f g : Pairs.ModeCube27 → A) (target : Full.WideCube125) →
  fiveGridBilinearFullAt ops f g target
    ≡ trueBilinearConvolutionAt ops f g target
fiveGridBilinearRecoversAllFullCoefficients ops f g target =
  sumUsingCong ops Pairs.pair729
    (fiveGridContribution ops f g target)
    (exactContribution ops f g target)
    (fiveGridTermIsTrueFullTerm ops f g target)

------------------------------------------------------------------------
-- Instantiation from source-owned actual cyclotomic rational amplitudes.
-- Unlike Nat values, these support signed and complex-like coefficients.
------------------------------------------------------------------------

cyclotomicOps : CoefficientOps C3.Cyclotomic3
cyclotomicOps = record
  { zero = C3.zeroC
  ; add = C3._+C_
  ; multiply = C3._*C_
  }

cyclotomicFourGridRetainedBilinearExact :
  (f g : Pairs.ModeCube27 → C3.Cyclotomic3)
  (target : Pairs.ModeCube27) →
  fourGridBilinearRetainedAt cyclotomicOps f g target
    ≡ trueBilinearConvolutionAt cyclotomicOps f g
        (Full.retainedToWide target)
cyclotomicFourGridRetainedBilinearExact =
  fourGridBilinearRecoversAllRetainedCoefficients cyclotomicOps

cyclotomicFiveGridFullBilinearExact :
  (f g : Pairs.ModeCube27 → C3.Cyclotomic3)
  (target : Full.WideCube125) →
  fiveGridBilinearFullAt cyclotomicOps f g target
    ≡ trueBilinearConvolutionAt cyclotomicOps f g target
cyclotomicFiveGridFullBilinearExact =
  fiveGridBilinearRecoversAllFullCoefficients cyclotomicOps
