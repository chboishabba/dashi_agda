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
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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
    sumMulAssociative :
      (x y z : A) →
      CoefficientOps.multiply ops (CoefficientOps.multiply ops x y) z
      ≡ CoefficientOps.multiply ops x (CoefficientOps.multiply ops y z)
    sumMulCommutative :
      (x y : A) →
      CoefficientOps.multiply ops x y
      ≡ CoefficientOps.multiply ops y x
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


------------------------------------------------------------------------
-- TRUE BILINEAR EXPANSION INTO THE ORIGINAL 729 ORDERED INPUT PAIRS.
--
-- Reuses exactly the existing Pairs.cube27, Pairs.pair729, mapL,
-- concatMapL and CoefficientOps. This is the source-identical
-- distributive/Fubini bridge from two arbitrary 27-mode Fourier sums
-- to 729 symbolic pair products, independent of the C4/C5 root field.
------------------------------------------------------------------------

sumAllAppend :
  ∀ {X A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (xs ys : List X) (term : X → A) →
  sumAll ops (Pairs._++L_ xs ys) term
  ≡ CoefficientOps.add ops
      (sumAll ops xs term) (sumAll ops ys term)
sumAllAppend ops laws [] ys term =
  sym (FiniteSumAlgebra.sumAddZeroLeft laws (sumAll ops ys term))
sumAllAppend ops laws (x ∷ xs) ys term =
  trans
    (cong (CoefficientOps.add ops (term x))
      (sumAllAppend ops laws xs ys term))
    (sym (FiniteSumAlgebra.sumAddAssoc laws
      (term x) (sumAll ops xs term) (sumAll ops ys term)))

sumAllMap :
  ∀ {X Y A : Set} (ops : CoefficientOps A)
  (reindex : X → Y) (xs : List X) (term : Y → A) →
  sumAll ops (Pairs.mapL reindex xs) term
  ≡ sumAll ops xs (λ x → term (reindex x))
sumAllMap ops reindex [] term = refl
sumAllMap ops reindex (x ∷ xs) term =
  cong (CoefficientOps.add ops (term (reindex x)))
    (sumAllMap ops reindex xs term)

sumAllConcatMap :
  ∀ {X Y A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (expand : X → List Y) (xs : List X)
  (term : Y → A) →
  sumAll ops (Pairs.concatMapL expand xs) term
  ≡ sumAll ops xs (λ x → sumAll ops (expand x) term)
sumAllConcatMap ops laws expand [] term = refl
sumAllConcatMap ops laws expand (x ∷ xs) term =
  trans
    (sumAllAppend ops laws (expand x)
      (Pairs.concatMapL expand xs) term)
    (cong (CoefficientOps.add ops (sumAll ops (expand x) term))
      (sumAllConcatMap ops laws expand xs term))

sumAllPair729AsDouble :
  ∀ {A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (term : Pairs.ModePair729 → A) →
  sumAll ops Pairs.pair729 term
  ≡ sumAll ops Pairs.cube27
      (λ p → sumAll ops Pairs.cube27 (λ q → term (p , q)))
sumAllPair729AsDouble ops laws term =
  trans
    (sumAllConcatMap ops laws
      (λ p → Pairs.mapL (λ q → p , q) Pairs.cube27)
      Pairs.cube27 term)
    (sumAllCong ops Pairs.cube27
      (λ p → sumAll ops
        (Pairs.mapL (λ q → p , q) Pairs.cube27) term)
      (λ p → sumAll ops Pairs.cube27
        (λ q → term (p , q)))
      (λ p → sumAllMap ops (λ q → p , q) Pairs.cube27 term))

sumAllDoubleProduct :
  ∀ {X Y A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (xs : List X) (ys : List Y)
  (f : X → A) (g : Y → A) →
  CoefficientOps.multiply ops
    (sumAll ops xs f) (sumAll ops ys g)
  ≡ sumAll ops xs
      (λ x → sumAll ops ys
        (λ y → CoefficientOps.multiply ops (f x) (g y)))
sumAllDoubleProduct ops laws xs ys f g =
  trans
    (sym (sumAllScaleRight ops laws xs f (sumAll ops ys g)))
    (sumAllCong ops xs
      (λ x → CoefficientOps.multiply ops (f x) (sumAll ops ys g))
      (λ x → sumAll ops ys
        (λ y → CoefficientOps.multiply ops (f x) (g y)))
      (λ x → sym (sumAllScaleLeft ops laws (f x) ys g)))

-- The 729 products here are literal ordered pairs of the original
-- cube27, not a parallel 729 index or an orbit-counting surrogate.
source729ProductExpansion :
  ∀ {A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (f g : Pairs.ModeCube27 → A) →
  CoefficientOps.multiply ops
    (sumAll ops Pairs.cube27 f)
    (sumAll ops Pairs.cube27 g)
  ≡ sumAll ops Pairs.pair729
      (λ pair → CoefficientOps.multiply ops
        (f (proj₁ pair))
        (g (proj₂ pair)))
source729ProductExpansion ops laws f g =
  trans
    (sumAllDoubleProduct ops laws
      Pairs.cube27 Pairs.cube27 f g)
    (sym
      (sumAllPair729AsDouble ops laws
        (λ pair → CoefficientOps.multiply ops
          (f (proj₁ pair))
          (g (proj₂ pair)))))



------------------------------------------------------------------------
-- Exact phase-pair permutation, analogous to additive sumShuffle4.
-- This is needed to regroup the six one-axis characters in C4^3/C5^3.
------------------------------------------------------------------------

productShuffle4 :
  ∀ {A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (a b c d : A) →
  CoefficientOps.multiply ops
    (CoefficientOps.multiply ops a b)
    (CoefficientOps.multiply ops c d)
  ≡ CoefficientOps.multiply ops
    (CoefficientOps.multiply ops a c)
    (CoefficientOps.multiply ops b d)
productShuffle4 ops laws a b c d =
  let
    infixl 7 _⊗_
    _⊗_ = CoefficientOps.multiply ops
    assoc = FiniteSumAlgebra.sumMulAssociative laws
    comm = FiniteSumAlgebra.sumMulCommutative laws
  in
  trans
    (assoc a b (c ⊗ d))
    (trans
      (cong (a ⊗_) (sym (assoc b c d)))
      (trans
        (cong (λ x → a ⊗ (x ⊗ d)) (comm b c))
        (trans
          (cong (a ⊗_) (assoc c b d))
          (sym (assoc a c (b ⊗ d))))))

productShuffleSix :
  ∀ {A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (a b c d e f : A) →
  CoefficientOps.multiply ops
    (CoefficientOps.multiply ops
      (CoefficientOps.multiply ops a b)
      (CoefficientOps.multiply ops c d))
    (CoefficientOps.multiply ops e f)
  ≡ CoefficientOps.multiply ops
    (CoefficientOps.multiply ops
      (CoefficientOps.multiply ops a c) e)
    (CoefficientOps.multiply ops
      (CoefficientOps.multiply ops b d) f)
productShuffleSix ops laws a b c d e f =
  trans
    (cong
      (λ x → CoefficientOps.multiply ops x
        (CoefficientOps.multiply ops e f))
      (productShuffle4 ops laws a b c d))
    (productShuffle4 ops laws
      (CoefficientOps.multiply ops a c)
      (CoefficientOps.multiply ops b d) e f)


------------------------------------------------------------------------
-- EXACT FINITE FOURIER COEFFICIENT-EXTRACTION REDUCTION.
--
-- Reuses, rather than re-proves, sumAllSwap and sumAllScaleLeft on the
-- original 729 pair list. The ONLY premise not obtained from abstract
-- semiring laws is the actual normalized character resolution.
-- Do NOT interpret supplying this premise as discharging it.
--
-- Source genealogy: BalabanFiniteSumFubiniExact (YM) and
-- NSTriadKNLuoFiniteFourierInversionFromResolutionExact (Grafakos).
-- This version is coefficient-polymorphic, not a false rational-only
-- coercion to Q(i) or Q(zeta5). Source-written; kernel pending.
------------------------------------------------------------------------

finiteFourierExtractionFromOriginal729GivenResolution :
  ∀ {Sample A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (samples : List Sample)
  (one : A)
  (rightUnit :
    (value : A) →
    CoefficientOps.multiply ops value one ≡ value)
  (coefficient : Pairs.ModePair729 → A)
  (phase : Pairs.ModePair729 → Sample → A)
  (selected : Pairs.ModePair729 → Bool)
  (resolution :
    (pair : Pairs.ModePair729) →
    sumAll ops samples (phase pair)
    ≡ choose (CoefficientOps.zero ops) (selected pair) one) →
  sumAll ops samples
    (λ sample →
      sumAll ops Pairs.pair729
        (λ pair →
          CoefficientOps.multiply ops
            (coefficient pair) (phase pair sample)))
  ≡ sumAll ops Pairs.pair729
      (λ pair →
        choose (CoefficientOps.zero ops)
          (selected pair) (coefficient pair))
finiteFourierExtractionFromOriginal729GivenResolution
  ops laws samples one rightUnit coefficient phase selected resolution =
  trans
    (sumAllSwap ops laws samples Pairs.pair729
      (λ sample pair →
        CoefficientOps.multiply ops
          (coefficient pair) (phase pair sample)))
    (sumAllCong ops Pairs.pair729
      (λ pair →
        sumAll ops samples
          (λ sample →
            CoefficientOps.multiply ops
              (coefficient pair) (phase pair sample)))
      (λ pair →
        choose (CoefficientOps.zero ops)
          (selected pair) (coefficient pair))
      (λ pair →
        trans
          (sumAllScaleLeft ops laws
            (coefficient pair) samples (phase pair))
          (trans
            (cong (CoefficientOps.multiply ops (coefficient pair))
              (resolution pair))
            (selectByResolution pair (selected pair)))))
  where
  selectByResolution :
    (pair : Pairs.ModePair729) (flag : Bool) →
    CoefficientOps.multiply ops (coefficient pair)
      (choose (CoefficientOps.zero ops) flag one)
    ≡ choose (CoefficientOps.zero ops) flag (coefficient pair)
  selectByResolution pair true = rightUnit (coefficient pair)
  selectByResolution pair false =
    FiniteSumAlgebra.sumMulZeroRight laws (coefficient pair)

-- The exact remaining C4/C5 'payment' is a proof of resolution
-- for the ACTUAL sample list, normalized character kernel and
-- retained/full output selection. No postulate or extracted oracle.


------------------------------------------------------------------------
-- THE ORIGINAL TRIPLE CARTESIAN ENUMERATION / PRODUCT FACTORIZATION.
--
-- Reuse source mapL/concatMapL and existing Fubini and finite scaling,
-- not a new Cube64/Cube125 enumeration or another scalar ontology.
-- The three axes may be of different types and different lengths.
-- In particular this can be instantiated to original Nyquist 4^3/5^3.
------------------------------------------------------------------------

sourceCartesianTripleSumAsNested :
  ∀ {X Y Z A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (xs : List X) (ys : List Y) (zs : List Z)
  (f : X → Y → Z → A) →
  sumAll ops
    (Pairs.concatMapL (λ x →
      Pairs.concatMapL (λ y →
        Pairs.mapL (λ z → x , (y , z)) zs) ys) xs)
    (λ { (x , (y , z)) → f x y z })
  ≡ sumAll ops xs
      (λ x → sumAll ops ys
        (λ y → sumAll ops zs (λ z → f x y z)))
sourceCartesianTripleSumAsNested ops laws xs ys zs f =
  trans
    (sumAllConcatMap ops laws
      (λ x → Pairs.concatMapL (λ y →
        Pairs.mapL (λ z → x , (y , z)) zs) ys)
      xs
      (λ { (x , (y , z)) → f x y z }))
    (sumAllCong ops xs
      (λ x → sumAll ops
        (Pairs.concatMapL (λ y →
          Pairs.mapL (λ z → x , (y , z)) zs) ys)
        (λ { (a , (d , c)) → f a d c }))
      (λ x → sumAll ops ys
        (λ y → sumAll ops zs (λ z → f x y z)))
      (λ x →
        trans
          (sumAllConcatMap ops laws
            (λ y → Pairs.mapL (λ z → x , (y , z)) zs)
            ys
            (λ { (a , (d , c)) → f a d c }))
          (sumAllCong ops ys
            (λ y → sumAll ops
              (Pairs.mapL (λ z → x , (y , z)) zs)
              (λ { (a , (d , c)) → f a d c }))
            (λ y → sumAll ops zs (λ z → f x y z))
            (λ y → sumAllMap ops
              (λ z → x , (y , z)) zs
              (λ { (a , (d , c)) → f a d c })))))

nestedTripleProductFactors :
  ∀ {X Y Z A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (xs : List X) (ys : List Y) (zs : List Z)
  (fx : X → A) (fy : Y → A) (fz : Z → A) →
  sumAll ops xs
    (λ x → sumAll ops ys
      (λ y → sumAll ops zs
        (λ z →
          CoefficientOps.multiply ops
            (CoefficientOps.multiply ops (fx x) (fy y)) (fz z))))
  ≡ CoefficientOps.multiply ops
      (CoefficientOps.multiply ops
        (sumAll ops xs fx) (sumAll ops ys fy))
      (sumAll ops zs fz)
nestedTripleProductFactors ops laws xs ys zs fx fy fz =
  let
    infixl 7 _⊗_
    _⊗_ = CoefficientOps.multiply ops
    xsum = sumAll ops xs fx
    ysum = sumAll ops ys fy
    zsum = sumAll ops zs fz

    inside x =
      trans
        (sumAllCong ops ys
          (λ y → sumAll ops zs
            (λ z → (fx x ⊗ fy y) ⊗ fz z))
          (λ y → (fx x ⊗ fy y) ⊗ zsum)
          (λ y → sumAllScaleLeft ops laws
            (fx x ⊗ fy y) zs fz))
        (trans
          (sumAllScaleRight ops laws ys
            (λ y → fx x ⊗ fy y) zsum)
          (cong (_⊗ zsum)
            (sumAllScaleLeft ops laws (fx x) ys fy)))
  in
  trans
    (sumAllCong ops xs
      (λ x → sumAll ops ys
        (λ y → sumAll ops zs
          (λ z → (fx x ⊗ fy y) ⊗ fz z)))
      (λ x → (fx x ⊗ ysum) ⊗ zsum)
      inside)
    (trans
      (sumAllScaleRight ops laws xs
        (λ x → fx x ⊗ ysum) zsum)
      (cong (_⊗ zsum)
        (sumAllScaleRight ops laws xs fx ysum)))

sourceCartesianTripleProductFactors :
  ∀ {X Y Z A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (xs : List X) (ys : List Y) (zs : List Z)
  (fx : X → A) (fy : Y → A) (fz : Z → A) →
  sumAll ops
    (Pairs.concatMapL (λ x →
      Pairs.concatMapL (λ y →
        Pairs.mapL (λ z → x , (y , z)) zs) ys) xs)
    (λ { (x , (y , z)) →
      CoefficientOps.multiply ops
        (CoefficientOps.multiply ops (fx x) (fy y)) (fz z) })
  ≡ CoefficientOps.multiply ops
      (CoefficientOps.multiply ops
        (sumAll ops xs fx) (sumAll ops ys fy))
      (sumAll ops zs fz)
sourceCartesianTripleProductFactors ops laws xs ys zs fx fy fz =
  trans
    (sourceCartesianTripleSumAsNested ops laws xs ys zs
      (λ x y z →
        CoefficientOps.multiply ops
          (CoefficientOps.multiply ops (fx x) (fy y)) (fz z)))
    (nestedTripleProductFactors ops laws xs ys zs fx fy fz)

-- Agda kernel checking is mandatory: no new postulate, unsafe solver
-- or declaration that the 3D normalized Fourier equation is complete.


------------------------------------------------------------------------
-- PARAMETRIC CARTESIAN TRIPLE ENUMERATION.  Takes the SOURCE cube
-- constructor (e.g. Four.fourCube / Full.gridCube), so the actual
-- Nyquist 64/125 sample lists can reuse exactly the same sum proof.
------------------------------------------------------------------------

sourceCartesianTripleSumWith :
  ∀ {X Y Z W A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (xs : List X) (ys : List Y) (zs : List Z)
  (mk : X → Y → Z → W) (term : W → A) →
  sumAll ops
    (Pairs.concatMapL (λ x →
      Pairs.concatMapL (λ y →
        Pairs.mapL (λ z → mk x y z) zs) ys) xs) term
  ≡ sumAll ops xs
      (λ x → sumAll ops ys
        (λ y → sumAll ops zs (λ z → term (mk x y z))))
sourceCartesianTripleSumWith ops laws xs ys zs mk term =
  trans
    (sumAllConcatMap ops laws
      (λ x → Pairs.concatMapL (λ y →
        Pairs.mapL (λ z → mk x y z) zs) ys)
      xs term)
    (sumAllCong ops xs
      (λ x → sumAll ops
        (Pairs.concatMapL (λ y →
          Pairs.mapL (λ z → mk x y z) zs) ys) term)
      (λ x → sumAll ops ys
        (λ y → sumAll ops zs (λ z → term (mk x y z))))
      (λ x →
        trans
          (sumAllConcatMap ops laws
            (λ y → Pairs.mapL (λ z → mk x y z) zs)
            ys term)
          (sumAllCong ops ys
            (λ y → sumAll ops
              (Pairs.mapL (λ z → mk x y z) zs) term)
            (λ y → sumAll ops zs (λ z → term (mk x y z)))
            (λ y → sumAllMap ops (mk x y) zs term))))

sourceCartesianTripleProductFactorsWith :
  ∀ {X Y Z W A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (xs : List X) (ys : List Y) (zs : List Z)
  (mk : X → Y → Z → W)
  (fx : X → A) (fy : Y → A) (fz : Z → A)
  (interpret : W → A)
  (agreement :
    (x : X) (y : Y) (z : Z) →
    interpret (mk x y z)
    ≡ CoefficientOps.multiply ops
        (CoefficientOps.multiply ops (fx x) (fy y))
        (fz z)) →
  sumAll ops
    (Pairs.concatMapL (λ x →
      Pairs.concatMapL (λ y →
        Pairs.mapL (λ z → mk x y z) zs) ys) xs)
    interpret
  ≡ CoefficientOps.multiply ops
      (CoefficientOps.multiply ops
        (sumAll ops xs fx) (sumAll ops ys fy))
      (sumAll ops zs fz)
sourceCartesianTripleProductFactorsWith
  ops laws xs ys zs mk fx fy fz interpret agreement =
  trans
    (sourceCartesianTripleSumWith
      ops laws xs ys zs mk interpret)
    (trans
      (sumAllCong ops xs
        (λ x → sumAll ops ys (λ y → sumAll ops zs
          (λ z → interpret (mk x y z))))
        (λ x → sumAll ops ys (λ y → sumAll ops zs
          (λ z → CoefficientOps.multiply ops
            (CoefficientOps.multiply ops (fx x) (fy y))
            (fz z))))
        (λ x → sumAllCong ops ys
          (λ y → sumAll ops zs (λ z → interpret (mk x y z)))
          (λ y → sumAll ops zs (λ z →
            CoefficientOps.multiply ops
              (CoefficientOps.multiply ops (fx x) (fy y))
              (fz z)))
          (λ y → sumAllCong ops zs
            (λ z → interpret (mk x y z))
            (λ z → CoefficientOps.multiply ops
              (CoefficientOps.multiply ops (fx x) (fy y))
              (fz z))
            (agreement x y))))
      (nestedTripleProductFactors ops laws xs ys zs fx fy fz))

-- A source cube is merely the constructor mk here. No claim that its
-- actual Fourier character splits into 1D factors until an owner
-- supplies the explicit pointwise agreement at this exact carrier.


------------------------------------------------------------------------
-- SOURCE Boolean Cartesian selector product.  This is exactly the
-- equality predicate convention of the source C4/C5 cubes:
--   (eqAxis0 &&B eqAxis1) &&B eqAxis2.
-- Proof does not assume a data-induced ranking, synthetic QID, or
-- excluded middle on arbitrary propositions: only concrete Bool.
------------------------------------------------------------------------

sourceChooseProduct :
  ∀ {A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (one : A)
  (unitOne : CoefficientOps.multiply ops one one ≡ one)
  (a b : Bool) →
  CoefficientOps.multiply ops
    (choose (CoefficientOps.zero ops) a one)
    (choose (CoefficientOps.zero ops) b one)
  ≡ choose (CoefficientOps.zero ops) (Full._&&B_ a b) one
sourceChooseProduct ops laws one unitOne true true = unitOne
sourceChooseProduct ops laws one unitOne true false =
  FiniteSumAlgebra.sumMulZeroRight laws one
sourceChooseProduct ops laws one unitOne false true =
  FiniteSumAlgebra.sumMulZeroLeft laws one
sourceChooseProduct ops laws one unitOne false false =
  FiniteSumAlgebra.sumMulZeroLeft laws (CoefficientOps.zero ops)

sourceChooseProductTriple :
  ∀ {A : Set}
  (ops : CoefficientOps A) (laws : FiniteSumAlgebra ops)
  (one : A)
  (unitOne : CoefficientOps.multiply ops one one ≡ one)
  (a b c : Bool) →
  CoefficientOps.multiply ops
    (CoefficientOps.multiply ops
      (choose (CoefficientOps.zero ops) a one)
      (choose (CoefficientOps.zero ops) b one))
    (choose (CoefficientOps.zero ops) c one)
  ≡ choose (CoefficientOps.zero ops)
      (Full._&&B_ (Full._&&B_ a b) c) one
sourceChooseProductTriple ops laws one unitOne a b c =
  trans
    (cong
      (λ first → CoefficientOps.multiply ops first
        (choose (CoefficientOps.zero ops) c one))
      (sourceChooseProduct ops laws one unitOne a b))
    (sourceChooseProduct ops laws one unitOne
      (Full._&&B_ a b) c)
