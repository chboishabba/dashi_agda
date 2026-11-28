module DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact where

-- SOURCE-WRITTEN, kernel pending. Extend the existing parity reindex
-- to the actual Hecke stride, retaining all signed complementary indices.
-- Only off-sector zeros of the FIRST factor are required for the
-- on-sector Cauchy read. No analytic convergence premise.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_; _≤_; z≤n; s≤s; _∸_)
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_; _/_; [m+kn]%n≡m%n; m<n⇒m%n≡m; m*n%n≡0; m*n/n≡m; m≡m%n+[m/n]*n)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Data.Fin.Base using (toℕ)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst; trans)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_)
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FS
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP

stride : Nat → Nat
stride n = n * 41

Sector : (Nat → ℝ) → Set
Sector f = ∀ n → (n % 41 ≡ zero → ⊥) → f n ≃ R.0ℝ

offsetResidue : ∀ n k → k < 41 → (k + stride n) % 41 ≡ k
offsetResidue n k hk = trans ([m+kn]%n≡m%n k n 41) (m<n⇒m%n≡m hk)

offsetNonzero : ∀ n k → suc k < 41 → (suc k + stride n) % 41 ≡ zero → ⊥
offsetNonzero n k hk h with trans (sym (offsetResidue n (suc k) hk)) h
... | ()

-- Skip the zero wing after the first retained degree of a block.
skip : ∀ f → Sector f → ∀ n k → k < 41 →
  Seq.SeriesOf f (suc k + stride n) ≃ Seq.SeriesOf f (suc (stride n))
skip f hf n zero hk = P.≃-refl
skip f hf n (suc k) hk =
  P.≃-trans (P.+-cong (skip f hf n k (NP.<-trans (NP.n<1+n k) hk))
    (hf (suc k + stride n) (offsetNonzero n k hk)))
    (P.+-identityʳ _)

prefixStride : ∀ f → Sector f → ∀ n →
  Seq.SeriesOf f (suc (stride n)) ≃ Seq.SeriesOf (λ k → f (stride k)) (suc n)
prefixStride f hf zero = P.≃-refl
prefixStride f hf (suc n) =
  P.+-cong
    (P.≃-trans (skip f hf n 40 NP.≤-refl)
      (prefixStride f hf n))
    P.≃-refl

-- Degree complement is EXACT even when the natural subtraction is
-- truncated. No division of the coefficient values.
complement : ∀ n k → stride n ∸ stride k ≡ stride (n ∸ k)
complement n k = sym (NP.*-distribʳ-∸ 41 n k)

restrict : (Nat → ℝ) → Nat → ℝ
restrict f n = f (stride n)

reduceRow : ∀ a b → Sector a → ∀ n →
  Row.cauchyCoefficient a b (stride n) ≃
    Row.cauchyCoefficient (restrict a) (restrict b) n
reduceRow a b ha n =
  let f = λ k → R._*_ (a k) (b (stride n ∸ k))
      g = λ k → R._*_ (a (stride k)) (b (stride (n ∸ k)))
      hz : Sector f
      hz k hk = P.≃-trans (P.*-congʳ (ha k hk)) (P.*-zeroˡ _)
      hc : ∀ k → f (stride k) ≃ g k
      hc k rewrite complement n k = P.≃-refl
      prefixCong : ∀ m → Seq.SeriesOf (λ k → f (stride k)) m ≃ Seq.SeriesOf g m
      prefixCong zero = P.≃-refl
      prefixCong (suc m) = P.+-cong (prefixCong m) (hc m)
  in P.≃-trans (FS.finSumIsSeriesOf f (suc (stride n)))
    (P.≃-trans (prefixStride f hz n)
      (P.≃-trans (prefixCong (suc n)) (P.≃-symm (FS.finSumIsSeriesOf g (suc n)))))

SectorC : N.SeriesC → Set
SectorC f = ∀ n → (n % 41 ≡ zero → ⊥) → C._≈C_ (f n) A.zeroC

restrictC : N.SeriesC → N.SeriesC
restrictC f n = f (stride n)

reduceComplex : ∀ a b → SectorC a → ∀ n →
  C._≈C_ (N._⊗c_ a b (stride n)) (N._⊗c_ (restrictC a) (restrictC b) n)
reduceComplex a b ha n =
  let ar = C.realTerms a; ai = C.imagTerms a
      br = C.realTerms b; bi = C.imagTerms b
      hr : Sector ar
      hr k hk = proj₁ (ha k hk)
      hi : Sector ai
      hi k hk = proj₂ (ha k hk)
  in P.+-cong (reduceRow ar br hr n) (P.-‿cong (reduceRow ai bi hi n)) ,
     P.+-cong (reduceRow ar bi hr n) (reduceRow ai br hi n)

-- Full coefficient reconstruction is literal: no information survives
-- on a discarded sector. This is the reverse direction of restriction.
expandC : N.SeriesC → N.SeriesC
expandC f n with n % 41 NP.≟ zero
... | yes _ = f (n / 41)
... | no _ = A.zeroC

expandStride : ∀ f n → C._≈C_ (expandC f (stride n)) (f n)
expandStride f n rewrite m*n%n≡0 n 41 | m*n/n≡m n 41 = C.≈C-refl _

reconstruct : ∀ f → SectorC f → N._≈cs_ (expandC (restrictC f)) f
reconstruct f hf n with n % 41 NP.≟ zero
... | no h = (P.≃-symm (proj₁ (hf n h))) , (P.≃-symm (proj₂ (hf n h)))
... | yes h =
  let eq : n ≡ stride (n / 41)
      eq = trans (m≡m%n+[m/n]*n n 41) (cong (λ k → k + stride (n / 41)) h)
  in subst (λ k → C._≈C_ (f (stride (n / 41))) (f k)) (sym eq) (C.≈C-refl _)
