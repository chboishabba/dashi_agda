module DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact where

-- SOURCE-WRITTEN, UNCOMPILED. Fixed nonpole directional limit.
-- The actual scaled gap inverse is obtained from the disk guard, and
-- convergence is proved from the pinned Bishop epsilon extraction.
-- No inverse-continuity postulate, no global uniform tail assumption.
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Data.Nat.Properties as NP
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact as Eps
import DASHI.Foundations.BishopSquareNonnegativeExact as Sq
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopComplexOriginQuadraticRemainderExact as O
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; scaleC)
open Comp using (complexTrans; complexSym)
open Completion using (original-bishop-pointwise-complex-converges; realConverges; imaginaryConverges)

two : ℝ
two = (+ 2 / 1) ⋆

normNN : ∀ z → R.NonNegative (Norm.normSqC z)
normNN (C.complex a b) =
  P.nonNegx,y⇒nonNegx+y (Sq.bishopSquareNonnegative a) (Sq.bishopSquareNonnegative b)

mulR : ∀ {f g : Nat → ℝ} {a b} →
  Seq._ConvergesTo_ f a → Seq._ConvergesTo_ g b →
  Seq._ConvergesTo_ (λ n → f n * g n) (a * b)
mulR {a = a} {b} f g = Seq.xₙyₙ→x₀y₀ (a , f) (b , g)

addR : ∀ {f g : Nat → ℝ} {a b} →
  Seq._ConvergesTo_ f a → Seq._ConvergesTo_ g b →
  Seq._ConvergesTo_ (λ n → f n + g n) (a + b)
addR {a = a} {b} f g = Seq.xₙ+yₙ→x₀+y₀ (a , f) (b , g)

subR : ∀ {f g : Nat → ℝ} {a b} →
  Seq._ConvergesTo_ f a → Seq._ConvergesTo_ g b →
  Seq._ConvergesTo_ (λ n → f n - g n) (a - b)
subR {a = a} {b} f g = addR f (Seq.-xₙ→-x₀ (b , g))

mulConv : ∀ {f g : Nat → BishopComplex} {a b} →
  Lim.Conv f a → Lim.Conv g b → Lim.Conv (λ n → f n *C g n) (a *C b)
mulConv f g = original-bishop-pointwise-complex-converges
  (subR (mulR (realConverges f) (realConverges g)) (mulR (imaginaryConverges f) (imaginaryConverges g)))
  (addR (mulR (realConverges f) (imaginaryConverges g)) (mulR (imaginaryConverges f) (realConverges g)))

scaleConv : ∀ {f : Nat → ℝ} {g : Nat → BishopComplex} {a b} →
  Seq._ConvergesTo_ f a → Lim.Conv g b → Lim.Conv (λ n → scaleC (f n) (g n)) (scaleC a b)
scaleConv f g = original-bishop-pointwise-complex-converges
  (mulR f (realConverges g)) (mulR f (imaginaryConverges g))

conjConv : ∀ {f : Nat → BishopComplex} {z} →
  Lim.Conv f z → Lim.Conv (λ n → Rec.conjugateC (f n)) (Rec.conjugateC z)
conjConv {z = z} f = original-bishop-pointwise-complex-converges
  (realConverges f) (Seq.-xₙ→-x₀ (C.im z , imaginaryConverges f))

normConv : ∀ {f : Nat → BishopComplex} {z} →
  Lim.Conv f z → Seq._ConvergesTo_ (λ n → Norm.normSqC (f n)) (Norm.normSqC z)
normConv f = addR (mulR (realConverges f) (realConverges f))
  (mulR (imaginaryConverges f) (imaginaryConverges f))

normInverse : ∀ z v → (z *C v) ≈C A.oneC →
  (Norm.normSqC z * Norm.normSqC v) ≃ R.1ℝ
normInverse z v e = P.≃-trans (P.≃-symm (Norm.normSqMultiply z v))
  (P.≃-trans (D.normCong e) Norm.normSqOne)

-- Use both components of the original complex cross; do not identify
-- a squared norm with the original signed complex number.
inverseRead : ∀ z v → (z *C v) ≈C A.oneC →
  scaleC (Norm.normSqC v) (Rec.conjugateC z) ≈C v
inverseRead (C.complex a b) (C.complex c d) (re , im) =
  (P.≃-trans
    (let open P.ℝ-Solver in solve 4
      (λ a b c d → (c ⊗ c ⊕ d ⊗ d) ⊗ a
        ⊜ c ⊗ (a ⊗ c ⊖ b ⊗ d) ⊕ d ⊗ (a ⊗ d ⊕ b ⊗ c)) P.≃-refl a b c d)
    (P.≃-trans (P.+-cong (P.*-congˡ re) (P.*-congˡ im))
      (let open P.ℝ-Solver in solve 2
        (λ c d → c ⊗ Κ 1ℚᵘ ⊕ d ⊗ Κ 0ℚᵘ ⊜ c) P.≃-refl c d)))
  ,
  (P.≃-trans
    (let open P.ℝ-Solver in solve 4
      (λ a b c d → (c ⊗ c ⊕ d ⊗ d) ⊗ (⊝ b)
        ⊜ d ⊗ (a ⊗ c ⊖ b ⊗ d) ⊖ c ⊗ (a ⊗ d ⊕ b ⊗ c)) P.≃-refl a b c d)
    (P.≃-trans (P.+-cong (P.*-congˡ re) (P.-‿cong (P.*-congˡ im)))
      (let open P.ℝ-Solver in solve 2
        (λ c d → d ⊗ Κ 1ℚᵘ ⊖ c ⊗ Κ 0ℚᵘ ⊜ d) P.≃-refl c d)))

-- Positive real inverse pairs: no choice of a reciprocal at zero.
-- The supplied products come from the actual guarded complex inverse.
module PositivePairs (a b : ℝ) (aPositive : R._<_ R.0ℝ a)
  (bNN : R.NonNegative b) (ab : (a * b) ≃ R.1ℝ)
  (f g : Nat → ℝ) (fConv : Seq._ConvergesTo_ f a)
  (gNN : ∀ n → R.NonNegative (g n))
  (pair : ∀ n → (f n * g n) ≃ R.1ℝ) where

  halfA = D.half * a
  halfAPos : R.Positive halfA
  halfAPos = P.posx,y⇒posx*y (P.0<x⇒posx D.halfPositive) (P.0<x⇒posx aPositive)
  close = Seq.fast-ε-from-convergence (a , fConv) halfA halfAPos

  doubleLower : ∀ n → ∣ (f n - a) ∣ ≤ halfA → a ≤ two * f n
  doubleLower n bound =
    let low = Bounds.absLower bound
        raw = P.+-mono-≤ low P.≤-refl
        eqL = let open P.ℝ-Solver in solve 1
          (λ a → (⊝ (Κ (+ 1 / 2) ⊗ a)) ⊕ a ⊜ Κ (+ 1 / 2) ⊗ a) P.≃-refl a
        eqR = let open P.ℝ-Solver in solve 2
          (λ f a → (f ⊖ a) ⊕ a ⊜ f) P.≃-refl (f n) a
        lower = P.≤-respʳ-≃ eqR (P.≤-respˡ-≃ (P.≃-symm eqL) raw)
    in P.≤-respˡ-≃
      (let open P.ℝ-Solver in solve 1
        (λ a → a ⊜ Κ (+ 2 / 1) ⊗ (Κ (+ 1 / 2) ⊗ a)) P.≃-refl a)
      (P.*-monoˡ-≤-nonNeg lower Bounds.twoNN)

  inverseBound : ∀ n → a ≤ two * f n → g n ≤ two * b
  inverseBound n lower =
    let raw = P.*-monoʳ-≤-nonNeg
          (P.*-monoʳ-≤-nonNeg lower (gNN n)) bNN
        left = P.≃-trans
          (let open P.ℝ-Solver in solve 3
            (λ a g b → (a ⊗ g) ⊗ b ⊜ (a ⊗ b) ⊗ g) P.≃-refl a (g n) b)
          (P.≃-trans (P.*-congʳ ab) (P.*-identityˡ (g n)))
        right = P.≃-trans
          (let open P.ℝ-Solver in solve 3
            (λ f g b → (Κ (+ 2 / 1) ⊗ f) ⊗ g ⊗ b
              ⊜ (Κ (+ 2 / 1) ⊗ (f ⊗ g)) ⊗ b) P.≃-refl (f n) (g n) b)
          (P.≃-trans (P.*-congʳ (P.*-congˡ (pair n)))
            (P.*-congʳ (P.*-identityʳ two)))
    in P.≤-respʳ-≃ right (P.≤-respˡ-≃ (P.≃-symm left) raw)

  inverseDifference : ∀ n → (g n - b) ≃ ((g n * b) * (a - f n))
  inverseDifference n = P.≃-symm
    (P.≃-trans
      (let open P.ℝ-Solver in solve 4
        (λ g b a f → (g ⊗ b) ⊗ (a ⊖ f) ⊜ g ⊗ (a ⊗ b) ⊖ b ⊗ (f ⊗ g))
        P.≃-refl (g n) b a (f n))
      (P.≃-trans (P.+-cong (P.*-congˡ ab) (P.-‿cong (P.*-congˡ (pair n))))
        (P.+-cong (P.*-identityʳ (g n)) (P.-‿cong (P.*-identityʳ b)))))

  budget = (two * b) * b
  error : Nat → ℝ
  error n = budget * (a - f n)

  errorNull : Seq._ConvergesTo_ error R.0ℝ
  errorNull = Seq.xₙ→x∧x≃y⇒xₙ→y
    (mulR (Power.constantConverges budget) (subR (Power.constantConverges a) fConv))
    (let open P.ℝ-Solver in solve 2
      (λ b a → b ⊗ (a ⊖ a) ⊜ Κ 0ℚᵘ) P.≃-refl budget a)

  quantitative : ∀ n → g n ≤ two * b → ∣ (g n - b) ∣ ≤ ∣ error n ∣
  quantitative n upper =
    P.≤-respˡ-≃ (P.≃-trans (P.∣-∣-cong (inverseDifference n))
      (P.∣x*y∣≃∣x∣*∣y∣ (g n * b) (a - f n)))
      (P.≤-respʳ-≃ (P.≃-symm (P.∣x*y∣≃∣x∣*∣y∣ budget (a - f n)))
        (P.*-monoʳ-≤-nonNeg
          (P.≤-respʳ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x
              (P.nonNegx,y⇒nonNegx*y (P.nonNegx,y⇒nonNegx*y Bounds.twoNN bNN) bNN)))
            (P.≤-respˡ-≃ (P.nonNegx⇒∣x∣≃x (P.nonNegx,y⇒nonNegx*y (gNN n) bNN))
              (P.*-monoʳ-≤-nonNeg upper bNN)))
          (P.nonNeg∣x∣ (a - f n))))

  inverseConverges : Seq._ConvergesTo_ g b
  inverseConverges = Seq.con* λ { (suc k) →
    let eps = (+ 1 / suc k) ⋆
        e = Seq.fast-ε-from-convergence (R.0ℝ , errorNull) eps (Eps.reciprocalNatPositive k)
        cutoff = proj₁ close NP.⊔ proj₁ e
    in cutoff , λ n large →
      let closeN = P.<⇒≤ (proj₂ close n (NP.≤-trans (NP.m≤m⊔n (proj₁ close) (proj₁ e)) large))
          boundN = quantitative n (inverseBound n (doubleLower n closeN))
          errN = P.<⇒≤ (proj₂ e n (NP.≤-trans (NP.m≤n⊔m (proj₁ close) (proj₁ e)) large))
      in P.≤-trans boundN
        (P.≤-respˡ-≃ (P.∣-∣-cong
          (let open P.ℝ-Solver in solve 1 (λ x → x ⊜ x ⊖ Κ 0ℚᵘ) P.≃-refl (error n))) errN) }

inverseLimit : ∀ {f g : Nat → BishopComplex} {z} (nz : Rec.BishopComplexNonzero z) →
  Lim.Conv f z → (∀ n → (f n *C g n) ≈C A.oneC) →
  Lim.Conv g (Rec.reciprocalC z nz)
inverseLimit {f} {g} {z} nz cv cross =
  let v = Rec.reciprocalC z nz
      module Pair = PositivePairs (Norm.normSqC z) (Norm.normSqC v)
        (Rec.normSquarePositive nz) (normNN v) (normInverse z v (Rec.multiplyReciprocal z nz))
        (λ n → Norm.normSqC (f n)) (λ n → Norm.normSqC (g n))
        (normConv cv) (λ n → normNN (g n)) (λ n → normInverse (f n) (g n) (cross n))
  in Lim.convTransport (λ n → inverseRead (f n) (g n) (cross n))
    (Lim.limitTransport (inverseRead z v (Rec.multiplyReciprocal z nz))
      (scaleConv Pair.inverseConverges (conjConv cv)))

gapFromIncrement : ∀ h q d → (q -C A.oneC) ≈C scaleC h d →
  Row.gapMinus q ≈C scaleC (R.- h) d
gapFromIncrement h (C.complex a b) (C.complex c d) (re , im) =
  (P.≃-trans
    (let open P.ℝ-Solver in solve 1 (λ a → Κ 1ℚᵘ ⊖ a ⊜ ⊝ (a ⊖ Κ 1ℚᵘ)) P.≃-refl a)
    (P.≃-trans (P.-‿cong re)
      (let open P.ℝ-Solver in solve 2 (λ h c → ⊝ (h ⊗ c) ⊜ (⊝ h) ⊗ c) P.≃-refl h c)))
  ,
  (P.≃-trans
    (let open P.ℝ-Solver in solve 1 (λ b → Κ 0ℚᵘ ⊖ b ⊜ ⊝ (b ⊖ Κ 0ℚᵘ)) P.≃-refl b)
    (P.≃-trans (P.-‿cong im)
      (let open P.ℝ-Solver in solve 2 (λ h d → ⊝ (h ⊗ d) ⊜ (⊝ h) ⊗ d) P.≃-refl h d)))

scaleCross : ∀ h d v → (d *C scaleC h v) ≈C (scaleC h d *C v)
scaleCross h (C.complex a b) (C.complex c d) =
  (let open P.ℝ-Solver in solve 5
    (λ h a b c d → a ⊗ (h ⊗ c) ⊖ b ⊗ (h ⊗ d)
      ⊜ (h ⊗ a) ⊗ c ⊖ (h ⊗ b) ⊗ d) P.≃-refl h a b c d)
  ,
  (let open P.ℝ-Solver in solve 5
    (λ h a b c d → a ⊗ (h ⊗ d) ⊕ b ⊗ (h ⊗ c)
      ⊜ (h ⊗ a) ⊗ d ⊕ (h ⊗ b) ⊗ c) P.≃-refl h a b c d)

-- Same q and same gap guard as the actual Fourier row; h is not divided.
module AtDirection (T : Cartesian.BishopSetoidComplexTranscendentals)
  (z : BishopComplex) (nz : Rec.BishopComplexNonzero z)
  (M : ℝ) (upper : Upper.BishopComplexNormSquareUpperRadius z M)
  (h : Nat → ℝ) (small : ∀ n → ∣ h n ∣ ≤ R.1ℝ)
  (null : Seq._ConvergesTo_ h R.0ℝ)
  (guard : ∀ n → Rec.BishopComplexNonzero
    (Row.gapMinus (Weld.originalBishopExpOnSeries T (scaleC (h n) z)))) where
  module Origin = O.AtDirection z M upper
  module Along = Origin.Along h small null
  q : Nat → BishopComplex
  q n = Weld.originalBishopExpOnSeries T (scaleC (h n) z)
  d = Along.slopeSeq
  v : Nat → BishopComplex
  v n = scaleC (R.- (h n)) (Rec.reciprocalC (Row.gapMinus (q n)) (guard n))

  cancels : ∀ n → (d n *C v n) ≈C A.oneC
  cancels n = complexTrans (scaleCross (R.- (h n)) (d n) _)
    (complexTrans (A.mulCCongruent
      (complexSym (gapFromIncrement (h n) (q n) (d n)
        (Origin.AtStep.incrementFactor (h n) (small n) T))) (C.≈C-refl _))
      (Rec.multiplyReciprocal (Row.gapMinus (q n)) (guard n)))

  reciprocalConverges : Lim.Conv v (Rec.reciprocalC z nz)
  reciprocalConverges = inverseLimit nz Along.slopeConverges cancels

  qRead : ∀ n → q n ≈C (A.oneC +C scaleC (h n) (d n))
  qRead n = complexTrans
    ((let open P.ℝ-Solver in solve 1 (λ a → a ⊜ Κ 1ℚᵘ ⊕ (a ⊖ Κ 1ℚᵘ)) P.≃-refl (C.re (q n))) ,
     (let open P.ℝ-Solver in solve 1 (λ b → b ⊜ Κ 0ℚᵘ ⊕ (b ⊖ Κ 0ℚᵘ)) P.≃-refl (C.im (q n))))
    (A.addCCongruent (C.≈C-refl _) (Origin.AtStep.incrementFactor (h n) (small n) T))

  qConverges : Lim.Conv q A.oneC
  qConverges = Lim.convTransport (λ n → complexSym (qRead n))
    (Lim.limitTransport (L.complexAddRightIdentity A.oneC)
      (Lim.addConv (Lim.constantC A.oneC)
        (Lim.limitTransport
          ((let open P.ℝ-Solver in solve 1 (λ x → Κ 0ℚᵘ ⊗ x ⊜ Κ 0ℚᵘ) P.≃-refl (C.re z)) ,
           (let open P.ℝ-Solver in solve 1 (λ x → Κ 0ℚᵘ ⊗ x ⊜ Κ 0ℚᵘ) P.≃-refl (C.im z)))
          (scaleConv null Along.slopeConverges))))
