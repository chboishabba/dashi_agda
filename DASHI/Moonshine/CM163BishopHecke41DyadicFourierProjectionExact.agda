module DASHI.Moonshine.CM163BishopHecke41DyadicFourierProjectionExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- Finite signed dyadic Fourier projection on ACTUAL upper half-plane
-- points, using existing exact positive/negative half-sheets.
-- No new primitive-root enumeration, contour integral or compactness.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Product.Base using (_,_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41UniformSeriesContinuityExact as Uniform
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; powC; scaleC)
open Comp using (complexTrans; complexSym)
open Uniform using (complexPrefix)

Point = U.BishopUpperHalfPlanePoint
Func = Point → BishopComplex
left = Phase.left
right = Phase.right Phase.positive


halfSame : ∀ x → scaleC Phase.half (x +C x) ≈C x
halfSame x = (let open P.ℝ-Solver in solve 2 (λ xr xi →
    (Κ (+ 1 / 2) ⊗ (xr ⊕ xr)) ⊜ xr) P.≃-refl (C.re x) (C.im x)) ,
  (let open P.ℝ-Solver in solve 2 (λ xr xi →
    (Κ (+ 1 / 2) ⊗ (xi ⊕ xi)) ⊜ xi) P.≃-refl (C.re x) (C.im x))

halfOpposite : ∀ x y → scaleC Phase.half ((x *C y) +C (Gen.negC x *C y)) ≈C A.zeroC
halfOpposite x y = (let open P.ℝ-Solver in solve 4 (λ xr xi yr yi →
    (Κ (+ 1 / 2) ⊗ (((xr ⊗ yr) ⊖ (xi ⊗ yi)) ⊕ (((⊝ xr) ⊗ yr) ⊖ ((⊝ xi) ⊗ yi)))) ⊜ Κ 0ℚᵘ) P.≃-refl (C.re x) (C.im x) (C.re y) (C.im y)) ,
  (let open P.ℝ-Solver in solve 4 (λ xr xi yr yi →
    (Κ (+ 1 / 2) ⊗ (((xr ⊗ yi) ⊕ (xi ⊗ yr)) ⊕ (((⊝ xr) ⊗ yi) ⊕ ((⊝ xi) ⊗ yr)))) ⊜ Κ 0ℚᵘ) P.≃-refl (C.re x) (C.im x) (C.re y) (C.im y))

negProduct : ∀ x y → (Gen.negC x *C Gen.negC y) ≈C (x *C y)
negProduct x y = (let open P.ℝ-Solver in solve 4 (λ xr xi yr yi →
    (((⊝ xr) ⊗ (⊝ yr)) ⊖ ((⊝ xi) ⊗ (⊝ yi))) ⊜ ((xr ⊗ yr) ⊖ (xi ⊗ yi))) P.≃-refl (C.re x) (C.im x) (C.re y) (C.im y)) ,
  (let open P.ℝ-Solver in solve 4 (λ xr xi yr yi →
    (((⊝ xr) ⊗ (⊝ yi)) ⊕ ((⊝ xi) ⊗ (⊝ yr))) ⊜ ((xr ⊗ yi) ⊕ (xi ⊗ yr))) P.≃-refl (C.re x) (C.im x) (C.re y) (C.im y))

meanAddStep : ∀ x y z w → scaleC Phase.half ((x +C y) +C (z +C w)) ≈C
  (scaleC Phase.half (x +C z) +C scaleC Phase.half (y +C w))
meanAddStep x y z w = (let open P.ℝ-Solver in solve 8 (λ xr xi yr yi zr zi wr wi →
    (Κ (+ 1 / 2) ⊗ ((xr ⊕ yr) ⊕ (zr ⊕ wr))) ⊜ ((Κ (+ 1 / 2) ⊗ (xr ⊕ zr)) ⊕ (Κ (+ 1 / 2) ⊗ (yr ⊕ wr)))) P.≃-refl (C.re x) (C.im x) (C.re y) (C.im y) (C.re z) (C.im z) (C.re w) (C.im w)) ,
  (let open P.ℝ-Solver in solve 8 (λ xr xi yr yi zr zi wr wi →
    (Κ (+ 1 / 2) ⊗ ((xi ⊕ yi) ⊕ (zi ⊕ wi))) ⊜ ((Κ (+ 1 / 2) ⊗ (xi ⊕ zi)) ⊕ (Κ (+ 1 / 2) ⊗ (yi ⊕ wi)))) P.≃-refl (C.re x) (C.im x) (C.re y) (C.im y) (C.re z) (C.im z) (C.re w) (C.im w))

meanMulStep : ∀ v x y → scaleC Phase.half ((v *C x) +C (v *C y)) ≈C
  (v *C scaleC Phase.half (x +C y))
meanMulStep v x y = (let open P.ℝ-Solver in solve 6 (λ vr vi xr xi yr yi →
    (Κ (+ 1 / 2) ⊗ (((vr ⊗ xr) ⊖ (vi ⊗ xi)) ⊕ ((vr ⊗ yr) ⊖ (vi ⊗ yi)))) ⊜ ((vr ⊗ (Κ (+ 1 / 2) ⊗ (xr ⊕ yr))) ⊖ (vi ⊗ (Κ (+ 1 / 2) ⊗ (xi ⊕ yi))))) P.≃-refl (C.re v) (C.im v) (C.re x) (C.im x) (C.re y) (C.im y)) ,
  (let open P.ℝ-Solver in solve 6 (λ vr vi xr xi yr yi →
    (Κ (+ 1 / 2) ⊗ (((vr ⊗ xi) ⊕ (vi ⊗ xr)) ⊕ ((vr ⊗ yi) ⊕ (vi ⊗ yr)))) ⊜ ((vr ⊗ (Κ (+ 1 / 2) ⊗ (xi ⊕ yi))) ⊕ (vi ⊗ (Κ (+ 1 / 2) ⊗ (xr ⊕ yr))))) P.≃-refl (C.re v) (C.im v) (C.re x) (C.im x) (C.re y) (C.im y))


pair : Func → Func
pair f p = scaleC Phase.half (f (left p) +C f (right p))

-- Fold the innermost pair first. This evaluates the full 2^k sample
-- tree, but the symbolic proof costs only k induction steps.
mean : Nat → Func → Func
mean zero f = f
mean (suc k) f = mean k (pair f)

pairCong : ∀ {f g} → (∀ p → f p ≈C g p) → ∀ p → pair f p ≈C pair g p
pairCong h p = A.scaleCCongruent (A.addCCongruent (h (left p)) (h (right p))) P.≃-refl

meanCong : ∀ k {f g} → (∀ p → f p ≈C g p) → ∀ p → mean k f p ≈C mean k g p
meanCong zero h p = h p
meanCong (suc k) h p = meanCong k (pairCong h) p

meanConst : ∀ k z p → mean k (λ _ → z) p ≈C z
meanConst zero z p = C.≈C-refl _
meanConst (suc k) z p = complexTrans (meanCong k (λ _ → halfSame z) p) (meanConst k z p)

meanAdd : ∀ k f g p → mean k (λ p → f p +C g p) p ≈C (mean k f p +C mean k g p)
meanAdd zero f g p = C.≈C-refl _
meanAdd (suc k) f g p = complexTrans
  (meanCong k (λ p → meanAddStep (f (left p)) (g (left p)) (f (right p)) (g (right p))) p)
  (meanAdd k (pair f) (pair g) p)

meanMul : ∀ k v f p → mean k (λ p → v *C f p) p ≈C (v *C mean k f p)
meanMul zero v f p = C.≈C-refl _
meanMul (suc k) v f p = complexTrans
  (meanCong k (λ p → meanMulStep v (f (left p)) (f (right p))) p)
  (meanMul k v (pair f) p)

-- Natural parity decomposition avoids division of signed degrees.
data Parity : Nat → Set where
  even : ∀ n → Parity (n * 2)
  odd : ∀ n → Parity (suc (n * 2))

parity : ∀ n → Parity n
parity zero = even zero
parity (suc zero) = odd zero
parity (suc (suc n)) with parity n
... | even k = even (suc k)
... | odd k = odd (suc k)

halfBound : ∀ a k → a * 2 ≤ suc k → a ≤ k
halfBound zero k h = z≤n
halfBound (suc a) k (s≤s h) = NP.≤-trans (s≤s (NP.m≤m*n a 1)) h

module At (inputs : Round11.BishopCutset) where
  module Rm = Ram.At inputs
  module Ph = Rm.Ph
  q = Ph.q
  nz = Rm.G.qNonzero

  iq : Func
  iq p = Rec.reciprocalC (q p) (nz p)

  mono : Nat → Nat → Func
  mono m n p = powC (q p) m *C powC (iq p) n

  leftSquare : ∀ p → powC (q (left p)) 2 ≈C q p
  leftSquare p = complexTrans (complexSym (Power.powTwo (q (left p)))) (Ph.squareQ p)

  rightNeg : ∀ p → q (right p) ≈C Gen.negC (q (left p))
  rightNeg p = Ph.signedQ Phase.positive p

  rightSquare : ∀ p → powC (q (right p)) 2 ≈C q p
  rightSquare p = complexTrans (complexSym (Power.powTwo (q (right p))))
    (complexTrans (A.mulCCongruent (rightNeg p) (rightNeg p))
      (complexTrans (negProduct (q (left p)) (q (left p))) (Ph.squareQ p)))

  inverseSquare : ∀ p child → powC (q child) 2 ≈C q p →
    powC (iq child) 2 ≈C iq p
  inverseSquare p child h = complexSym (Gen.reciprocalUnique (q p) (nz p) _
    (complexTrans (A.mulCCongruent (complexSym h) (C.≈C-refl _))
      (complexTrans (complexSym (Gen.powProduct (q child) (iq child) 2))
        (complexTrans (A.powCCongruent (Rec.multiplyReciprocal (q child) (nz child)) 2)
          (Power.powUnit 2)))))

  inverseNeg : ∀ p → iq (right p) ≈C Gen.negC (iq (left p))
  inverseNeg p = Gen.reciprocalUnique (q (right p)) (nz (right p)) _
    (complexTrans (A.mulCCongruent (rightNeg p) (C.≈C-refl _))
      (complexTrans (negProduct (q (left p)) (iq (left p)))
        (Rec.multiplyReciprocal (q (left p)) (nz (left p)))))

  evenMono : ∀ p child m n → powC (q child) 2 ≈C q p →
    mono (m * 2) (n * 2) child ≈C mono m n p
  evenMono p child m n h = A.mulCCongruent
    (complexTrans (complexSym (Ram.powPow (q child) 2 m)) (A.powCCongruent h m))
    (complexTrans (complexSym (Ram.powPow (iq child) 2 n))
      (A.powCCongruent (inverseSquare p child h) n))

  oddOdd : ∀ p child m n → powC (q child) 2 ≈C q p →
    mono (suc (m * 2)) (suc (n * 2)) child ≈C mono m n p
  oddOdd p child m n h =
    complexTrans (Gen.shuffle (q child) (powC (q child) (m * 2))
      (iq child) (powC (iq child) (n * 2)))
      (complexTrans (A.mulCCongruent (Rec.multiplyReciprocal (q child) (nz child))
        (evenMono p child m n h)) (L.complexMultiplyLeftIdentity _))

  oddEven : ∀ p child m n → powC (q child) 2 ≈C q p →
    mono (suc (m * 2)) (n * 2) child ≈C (q child *C mono m n p)
  oddEven p child m n h =
    complexTrans (L.complexMultiplyAssociative (q child) _ _)
      (A.mulCCongruent (C.≈C-refl _) (evenMono p child m n h))

  evenOdd : ∀ p child m n → powC (q child) 2 ≈C q p →
    mono (m * 2) (suc (n * 2)) child ≈C (iq child *C mono m n p)
  evenOdd p child m n h =
    complexTrans (complexSym (L.complexMultiplyAssociative _ _ _))
      (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative _ _) (C.≈C-refl _))
        (complexTrans (L.complexMultiplyAssociative _ _ _)
          (A.mulCCongruent (C.≈C-refl _) (evenMono p child m n h))))

  pairEven : ∀ m n p → pair (mono (m * 2) (n * 2)) p ≈C mono m n p
  pairEven m n p = complexTrans
    (A.scaleCCongruent (A.addCCongruent
      (evenMono p (left p) m n (leftSquare p))
      (evenMono p (right p) m n (rightSquare p))) P.≃-refl)
    (halfSame (mono m n p))

  pairOddOdd : ∀ m n p → pair (mono (suc (m * 2)) (suc (n * 2))) p ≈C mono m n p
  pairOddOdd m n p = complexTrans
    (A.scaleCCongruent (A.addCCongruent
      (oddOdd p (left p) m n (leftSquare p))
      (oddOdd p (right p) m n (rightSquare p))) P.≃-refl)
    (halfSame (mono m n p))

  pairOddEven : ∀ m n p → pair (mono (suc (m * 2)) (n * 2)) p ≈C A.zeroC
  pairOddEven m n p = complexTrans
    (A.scaleCCongruent (A.addCCongruent
      (oddEven p (left p) m n (leftSquare p))
      (complexTrans (oddEven p (right p) m n (rightSquare p))
        (A.mulCCongruent (rightNeg p) (C.≈C-refl _)))) P.≃-refl)
    (halfOpposite (q (left p)) (mono m n p))

  pairEvenOdd : ∀ m n p → pair (mono (m * 2) (suc (n * 2))) p ≈C A.zeroC
  pairEvenOdd m n p = complexTrans
    (A.scaleCCongruent (A.addCCongruent
      (evenOdd p (left p) m n (leftSquare p))
      (complexTrans (evenOdd p (right p) m n (rightSquare p))
        (A.mulCCongruent (inverseNeg p) (C.≈C-refl _)))) P.≃-refl)
    (halfOpposite (iq (left p)) (mono m n p))

  diag : ∀ n p → mono n n p ≈C A.oneC
  diag n p = complexTrans (complexSym (Gen.powProduct (q p) (iq p) n))
    (complexTrans (A.powCCongruent (Rec.multiplyReciprocal (q p) (nz p)) n) (Power.powUnit n))

  meanDiag : ∀ k n p → mean k (mono n n) p ≈C A.oneC
  meanDiag k n p = complexTrans (meanCong k (diag n) p) (meanConst k A.oneC p)

  -- Linear-depth bound is deliberately conservative: k≥m,n
  -- implies there are enough binary sheets to distinguish both.
  meanOff : ∀ k m n → m ≤ k → n ≤ k → (m ≡ n → ⊥) →
    ∀ p → mean k (mono m n) p ≈C A.zeroC
  meanOff zero (suc m) n () hn h p
  meanOff zero zero (suc n) hm () h p
  meanOff zero zero zero hm hn h p = ⊥-elim (h refl)
  meanOff (suc k) m n hm hn h p with parity m | parity n
  ... | even a | even b = complexTrans (meanCong k (pairEven a b) p)
    (meanOff k a b (halfBound a k hm) (halfBound b k hn)
      (λ e → h (cong (λ t → t * 2) e)) p)
  ... | odd a | odd b = complexTrans (meanCong k (pairOddOdd a b) p)
    (meanOff k a b (halfBound a k (NP.≤-trans (NP.n≤1+n (a * 2)) hm)) (halfBound b k (NP.≤-trans (NP.n≤1+n (b * 2)) hn))
      (λ e → h (cong (λ t → suc (t * 2)) e)) p)
  ... | odd a | even b = complexTrans (meanCong k (pairOddEven a b) p) (meanConst k A.zeroC p)
  ... | even a | odd b = complexTrans (meanCong k (pairEvenOdd a b) p) (meanConst k A.zeroC p)

  selected : (Nat → BishopComplex) → Nat → Nat → BishopComplex
  selected f n j with j NP.≟ n
  ... | yes e = f j
  ... | no h = A.zeroC

  termProjection : ∀ k f n j → n ≤ k → j ≤ k → ∀ p →
    mean k (λ v → f j *C mono j n v) p ≈C selected f n j
  termProjection k f n j hn hj p with j NP.≟ n
  ... | yes refl = complexTrans (meanMul k (f n) (mono n n) p)
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (meanDiag k n p))
      (L.complexMultiplyRightIdentity _))
  ... | no neq = complexTrans (meanMul k (f j) (mono j n) p)
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (meanOff k j n hj hn neq p))
      (L.complexMultiplyRightZero _))

  -- Exact extraction for every finite prefix, no quadrature error.
  prefixProjection : ∀ k f n m → n ≤ k → m ≤ suc k → ∀ p →
    mean k (λ v → complexPrefix (λ j → f j *C mono j n v) m) p ≈C
      complexPrefix (selected f n) m
  prefixProjection k f n zero hn hm p = meanConst k A.zeroC p
  prefixProjection k f n (suc m) hn (s≤s hm) p =
    complexTrans (meanAdd k (λ v → complexPrefix (λ j → f j *C mono j n v) m)
      (λ v → f m *C mono m n v) p)
      (A.addCCongruent (prefixProjection k f n m hn (NP.≤-step hm) p)
        (termProjection k f n m hn hm p))
