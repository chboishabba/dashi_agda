module DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact where

-- SOURCE-WRITTEN, kernel pending. The original Bishop absolute
-- Cauchy theorem is used on the *same* twisted complex coefficient
-- ring. Sparse expansion preserves actual limits, with explicit
-- stride-41 convergence modulus on every cutoff (not just a subsequence).
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; s≤s; _<_)
open import Data.Nat.DivMod using (_%_; _/_; m%n<n; m≡m%n+[m/n]*n; m*n/n≡m; /-monoˡ-≤)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
import Real as R
open R using (ℝ; _≃_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopRamanujanComplexReadoutExact as Read
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.CM163BishopHecke41SparseRingExact as S
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Actual
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_*C_; _-C_; powC; scaleC)
open N using (SeriesC; _≈cs_; _⊗c_; twist)
open Comp using (complexTrans; complexSym)
open R41 using (stride; restrict; Sector)
open G using (Series; _≈s_; _⊗s_; _⊖s_)

prefixAny : ∀ f → Sector f → ∀ n →
  Seq.SeriesOf f (suc n) ≃ Seq.SeriesOf (restrict f) (suc (n / 41))
prefixAny f hf n =
  P.≃-trans
    (subst (λ k → Seq.SeriesOf f (suc n) ≃ Seq.SeriesOf f (suc k))
      (m≡m%n+[m/n]*n n 41) P.≃-refl)
    (P.≃-trans (R41.skip f hf (n / 41) (n % 41) (m%n<n n 41))
      (R41.prefixStride f hf (n / 41)))

quotLower : ∀ n N0 → stride N0 ≤ n → N0 ≤ n / 41
quotLower n N0 h = subst (λ k → k ≤ n / 41) (m*n/n≡m N0 41) (/-monoˡ-≤ 41 h)

sparseConverges : ∀ f → Sector f → ∀ v →
  Seq._ConvergesTo_ (Seq.SeriesOf (restrict f)) v →
  Seq._ConvergesTo_ (Seq.SeriesOf f) v
sparseConverges f hf v (Seq.con* cv) = Seq.con* λ { (suc k) →
  stride (proj₁ (cv (suc k))) , λ
    { (suc n) (s≤s past) →
      P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong (P.+-cong (prefixAny f hf n) P.≃-refl)))
        (proj₂ (cv (suc k)) (suc (n / 41))
          (s≤s (quotLower n (proj₁ (cv (suc k))) past))) } }

absSector : ∀ f → Sector f → Sector (λ n → ∣ f n ∣)
absSector f hf n hn = P.≃-trans (P.∣-∣-cong (hf n hn))
  (P.nonNegx⇒∣x∣≃x P.nonNeg0)

sparseAbsolute : ∀ f → Sector f →
  Seq.SeriesOf_ConvergesAbsolutely (restrict f) → Seq.SeriesOf_ConvergesAbsolutely f
sparseAbsolute f hf h = proj₁ h ,
  sparseConverges (λ n → ∣ f n ∣) (absSector f hf) (proj₁ h) (proj₂ h)

record Eval (t : BishopComplex) (f : SeriesC) : Set where
  field
    value : BishopComplex
    absolute : C.ComponentwiseAbsoluteSeriesConvergent (twist t f)
    converges : C.ComplexSeriesConvergesTo (twist t f) value
open Eval public

termTransport : ∀ {t f} {g : SeriesC} → (twist t f) ≈cs g → Eval t f →
  C.ComponentwiseAbsoluteSeriesConvergent g
termTransport h ev = CP.complexAbsTransport h (absolute ev)

transport : ∀ {t f g} → f ≈cs g → Eval t f → Eval t g
transport {t} h ev = record
  { value = value ev
  ; absolute = CP.complexAbsTransport (N.twistCong t h) (absolute ev)
  ; converges = CP.complexLimitTransport (N.twistCong t h) (converges ev) }

product : ∀ {t f g} → Eval t f → Eval t g → Eval t (f ⊗c g)
product {t} {f} {g} a b = record
  { value = value a *C value b
  ; absolute = CP.complexAbsTransport (N.twistMul t f g)
      (CP.productAbsolute _ _ (absolute a) (absolute b))
  ; converges = CP.complexLimitTransport (N.twistMul t f g)
      (CP.productLimit _ _ _ _ (absolute a) (absolute b) (converges a) (converges b)) }

realWeight : ∀ t f n → Read.weight t f n ≈C twist t (E.lift f) n
realWeight t f n =
  (let open P.ℝ-Solver in solve 3 (λ a x y → a ⊗ x ⊜ a ⊗ x ⊖ Κ 0ℚᵘ ⊗ y)
    P.≃-refl (f n) (C.re (powC t n)) (C.im (powC t n))) ,
  (let open P.ℝ-Solver in solve 3 (λ a x y → a ⊗ y ⊜ a ⊗ y ⊕ Κ 0ℚᵘ ⊗ x)
    P.≃-refl (f n) (C.re (powC t n)) (C.im (powC t n)))

fromReal : ∀ {t f} → Read.Readout t f → Eval t (E.lift f)
fromReal {t} {f} ev = record
  { value = Read.value ev
  ; absolute = CP.complexAbsTransport (realWeight t f) (Read.absolute ev)
  ; converges = CP.complexLimitTransport (realWeight t f) (Read.converges ev) }

toReal : ∀ {t f} → Eval t (E.lift f) → Read.Readout t f
toReal {t} {f} ev = record
  { value = value ev
  ; absolute = CP.complexAbsTransport (λ n → complexSym (realWeight t f n)) (absolute ev)
  ; converges = CP.complexLimitTransport (λ n → complexSym (realWeight t f n)) (converges ev) }

phase : ∀ {t w q f} → q ≈C (w *C t) → Eval q f → Eval t (twist w f)
phase {t} {w} {q} {f} h ev =
  let eq = N.transCs (N.twistPhaseCong h f) (N.symCs (N.twistCompose t w f))
  in record { value = value ev ; absolute = CP.complexAbsTransport eq (absolute ev)
    ; converges = CP.complexLimitTransport eq (converges ev) }

unit : ∀ t → Eval t N.unit
unit t = fromReal (Read.constantRead t R.1ℝ)

monoRead : ∀ t k → Read.Readout t (S.mono k)
monoRead t zero = Read.constantRead t R.1ℝ
monoRead t (suc k) = Read.transport (S.monoMul 1 (S.mono k))
  (Read.product (Read.monomialRead t) (monoRead t k))

delayRead : ∀ {t f} → (k : Nat) → Read.Readout t f → Read.Readout t (Actual.delay k f)
delayRead {t} {f} k ev = Read.transport (S.monoMul k f) (Read.product (monoRead t k) ev)

monoValue : ∀ t k → Read.value (monoRead t k) ≈C powC t k
monoValue t zero = C.≈C-refl _
monoValue t (suc k) = A.mulCCongruent (C.≈C-refl _) (monoValue t k)

delayValue : ∀ {t f} k (ev : Read.Readout t f) →
  Read.value (delayRead k ev) ≈C (powC t k *C Read.value ev)
delayValue {t} k ev = A.mulCCongruent (monoValue t k) (C.≈C-refl _)

-- Absolute sparse expansion: every original cutoff is compared with
-- the exact smaller prefix, including the forty zero coefficients.
expandRead : ∀ {t q f} → powC t 41 ≈C q →
  Read.Readout q f → Read.Readout t (Actual.expand f)
expandRead {t} {q} {f} h ev =
  let terms = Read.weight t (Actual.expand f)
      a = C.realTerms terms
      b = C.imagTerms terms
      ha : Sector a
      ha n hn = P.≃-trans (P.*-congʳ (S.sectorExpand f n hn)) (P.*-zeroˡ _)
      hb : Sector b
      hb n hn = P.≃-trans (P.*-congʳ (S.sectorExpand f n hn)) (P.*-zeroˡ _)
      read : ∀ n → Read.weight q f n ≈C terms (stride n)
      read n = complexTrans
        (A.scaleCCongruent (complexTrans (A.powCCongruent (complexSym h) n) (Ram.powPow t 41 n)) (f n))
        (P.*-congʳ (P.≃-symm (S.restrictExpand f n)) , P.*-congʳ (P.≃-symm (S.restrictExpand f n)))
      ab = CP.complexAbsTransport read (Read.absolute ev)
      cv = CP.complexLimitTransport read (Read.converges ev)
  in record
    { value = Read.value ev
    ; absolute = C.componentwise-absolute-series-convergent
        (sparseAbsolute a ha (C.realAbsolute ab)) (sparseAbsolute b hb (C.imagAbsolute ab))
    ; converges = C.complex-series-converges-to
        (sparseConverges a ha _ (C.realConverges cv))
        (sparseConverges b hb _ (C.imagConverges cv)) }
