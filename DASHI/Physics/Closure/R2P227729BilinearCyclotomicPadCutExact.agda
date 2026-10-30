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
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

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
      (Four.fourGridGroupSum (Four.inputToFourGrid p) (Four.inputToFourGrid q))
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
        (Full.fiveGridGroupSum (Full.inputToFiveGrid p)
          (Full.inputToFiveGrid q)))
      target)
    (CoefficientOps.multiply ops (f p) (g q))

fourGridTermIsTrueRetainedTerm :
  ∀ {A : Set} →
  (ops : CoefficientOps A) (f g : Pairs.ModeCube27 → A) →
  (target : Pairs.ModeCube27) (pair : Pairs.ModePair729) →
  fourGridContribution ops f g target pair
    ≡ exactContribution ops f g (Full.retainedToWide target) pair
fourGridTermIsTrueRetainedTerm ops f g target (p , q)
  rewrite Four.fourGridGroupSumMatchesIntegerPair p q
        | Four.fourGridRetainedCubeMembership
            (Full.exactPairOutput p q) target = refl

fiveGridTermIsTrueFullTerm :
  ∀ {A : Set} →
  (ops : CoefficientOps A) (f g : Pairs.ModeCube27 → A) →
  (target : Full.WideCube125) (pair : Pairs.ModePair729) →
  fiveGridContribution ops f g target pair
    ≡ exactContribution ops f g target pair
fiveGridTermIsTrueFullTerm ops f g target (p , q)
  rewrite Full.fiveGridGroupSumMatchesIntegerPair p q
        | Full.pairOutputFivePointRecovered p q = refl

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


------------------------------------------------------------------------
-- GENERIC EXACT FINITE SEMIRING SUM CALCULUS (YANG--MILLS/NS REUSE).
--
-- Explicit source-method owners:
--   YangMills.BalabanFiniteSumFubiniExact (rational sum swap and fold laws)
--   Closure.NSTriadKNLuoFiniteFourierParsevalFromInversionExact
--   Closure.NSTriadKNFiniteConvolutionReconstruction
--
-- Earlier authors own their Q-valued / ordered-scalar proofs. This is the
-- coefficient-polymorphic version needed by Q(i), Q(zeta5), and Q(omega)
-- Fourier products. No new scalar carrier or unproved ring coercion.
-- Source-written Agda pending kernel verification.
------------------------------------------------------------------------

record FiniteSumAlgebra {A : Set} (ops : CoefficientOps A) : Set where
  field
    sumAddAssoc :
      (x y z : A) →
      CoefficientOps.add ops (CoefficientOps.add ops x y) z
        ≡ CoefficientOps.add ops x (CoefficientOps.add ops y z)
    sumAddComm :
      (x y : A) →
      CoefficientOps.add ops x y ≡ CoefficientOps.add ops y x
    sumAddZeroLeft :
      (x : A) →
      CoefficientOps.add ops (CoefficientOps.zero ops) x ≡ x
    sumMulDistributesLeft :
      (x y z : A) →
      CoefficientOps.multiply ops x (CoefficientOps.add ops y z)
        ≡ CoefficientOps.add ops
            (CoefficientOps.multiply ops x y)
            (CoefficientOps.multiply ops x z)
    sumMulDistributesRight :
      (x y z : A) →
      CoefficientOps.multiply ops (CoefficientOps.add ops x y) z
        ≡ CoefficientOps.add ops
            (CoefficientOps.multiply ops x z)
            (CoefficientOps.multiply ops y z)
    sumMulZeroLeft :
      (x : A) →
      CoefficientOps.multiply ops (CoefficientOps.zero ops) x
        ≡ CoefficientOps.zero ops
    sumMulZeroRight :
      (x : A) →
      CoefficientOps.multiply ops x (CoefficientOps.zero ops)
        ≡ CoefficientOps.zero ops

sumAll :
  ∀ {X A : Set} (ops : CoefficientOps A) →
  List X → (X → A) → A
sumAll ops [] term = CoefficientOps.zero ops
sumAll ops (x ∷ xs) term =
  CoefficientOps.add ops (term x) (sumAll ops xs term)

sumAllCong :
  ∀ {X A : Set} (ops : CoefficientOps A)
  (xs : List X) (f g : X → A) →
  ((x : X) → f x ≡ g x) →
  sumAll ops xs f ≡ sumAll ops xs g
sumAllCong ops [] f g eq = refl
sumAllCong ops (x ∷ xs) f g eq =
  cong₂ (CoefficientOps.add ops)
    (eq x) (sumAllCong ops xs f g eq)

sumAllZero :
  ∀ {X A : Set} (ops : CoefficientOps A)
  (laws : FiniteSumAlgebra ops) (xs : List X) →
  sumAll ops xs (λ _ → CoefficientOps.zero ops)
    ≡ CoefficientOps.zero ops
sumAllZero ops laws [] = refl
sumAllZero ops laws (_ ∷ xs)
  rewrite sumAllZero ops laws xs =
  FiniteSumAlgebra.sumAddZeroLeft laws (CoefficientOps.zero ops)

sumShuffle4 :
  ∀ {A : Set} (ops : CoefficientOps A)
  (laws : FiniteSumAlgebra ops) (a b c d : A) →
  CoefficientOps.add ops
    (CoefficientOps.add ops a b)
    (CoefficientOps.add ops c d)
  ≡ CoefficientOps.add ops
    (CoefficientOps.add ops a c)
    (CoefficientOps.add ops b d)
sumShuffle4 ops laws a b c d =
  let
    infixl 6 _⊕_
    _⊕_ = CoefficientOps.add ops
    assoc = FiniteSumAlgebra.sumAddAssoc laws
    comm = FiniteSumAlgebra.sumAddComm laws
  in
  trans
    (assoc a b (c ⊕ d))
    (trans
      (cong (a ⊕_) (sym (assoc b c d)))
      (trans
        (cong (λ x → a ⊕ (x ⊕ d)) (comm b c))
        (trans
          (cong (a ⊕_) (assoc c b d))
          (sym (assoc a c (b ⊕ d))))))

sumAllAdd :
  ∀ {X A : Set} (ops : CoefficientOps A)
  (laws : FiniteSumAlgebra ops)
  (xs : List X) (f g : X → A) →
  sumAll ops xs (λ x → CoefficientOps.add ops (f x) (g x))
  ≡ CoefficientOps.add ops (sumAll ops xs f) (sumAll ops xs g)
sumAllAdd ops laws [] f g =
  sym (FiniteSumAlgebra.sumAddZeroLeft laws (CoefficientOps.zero ops))
sumAllAdd ops laws (x ∷ xs) f g =
  trans
    (cong (CoefficientOps.add ops
      (CoefficientOps.add ops (f x) (g x)))
      (sumAllAdd ops laws xs f g))
    (sumShuffle4 ops laws
      (f x) (g x) (sumAll ops xs f) (sumAll ops xs g))

sumAllSwap :
  ∀ {X Y A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (xs : List X) (ys : List Y) (f : X → Y → A) →
  sumAll ops xs (λ x → sumAll ops ys (f x))
  ≡ sumAll ops ys (λ y → sumAll ops xs (λ x → f x y))
sumAllSwap ops laws [] ys f = sym (sumAllZero ops laws ys)
sumAllSwap ops laws (x ∷ xs) ys f =
  trans
    (cong (CoefficientOps.add ops (sumAll ops ys (f x)))
      (sumAllSwap ops laws xs ys f))
    (sym (sumAllAdd ops laws ys
      (f x) (λ y → sumAll ops xs (λ z → f z y))))

sumAllScaleLeft :
  ∀ {X A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (scale : A) (xs : List X) (f : X → A) →
  sumAll ops xs (λ x → CoefficientOps.multiply ops scale (f x))
    ≡ CoefficientOps.multiply ops scale (sumAll ops xs f)
sumAllScaleLeft ops laws scale [] f =
  sym (FiniteSumAlgebra.sumMulZeroRight laws scale)
sumAllScaleLeft ops laws scale (x ∷ xs) f =
  trans
    (cong (CoefficientOps.add ops
      (CoefficientOps.multiply ops scale (f x)))
      (sumAllScaleLeft ops laws scale xs f))
    (sym (FiniteSumAlgebra.sumMulDistributesLeft laws
      scale (f x) (sumAll ops xs f)))

sumAllScaleRight :
  ∀ {X A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (xs : List X) (f : X → A) (scale : A) →
  sumAll ops xs (λ x → CoefficientOps.multiply ops (f x) scale)
    ≡ CoefficientOps.multiply ops (sumAll ops xs f) scale
sumAllScaleRight ops laws [] f scale =
  sym (FiniteSumAlgebra.sumMulZeroLeft laws scale)
sumAllScaleRight ops laws (x ∷ xs) f scale =
  trans
    (cong (CoefficientOps.add ops
      (CoefficientOps.multiply ops (f x) scale))
      (sumAllScaleRight ops laws xs f scale))
    (sym (FiniteSumAlgebra.sumMulDistributesRight laws
      (f x) (sumAll ops xs f) scale))

-- Above are genuine finite-sum algebraic bridge candidates. Instantiation
-- into the existing C4/C5 operator owners avoids copying Yang--Mills
-- rational Fubini onto a different field or silently asserting FFT product
-- equals 729-term group convolution.
