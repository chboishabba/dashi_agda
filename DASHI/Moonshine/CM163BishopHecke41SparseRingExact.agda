module DASHI.Moonshine.CM163BishopHecke41SparseRingExact where

-- SOURCE-WRITTEN, kernel pending. Exact stride-41 subring. The
-- complementary index proof is inherited from the original finite
-- Cauchy row; no cancellation of a nonzero formal series is assumed.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; _∸_)
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_; _/_; m*n%n≡0; m*n/n≡m; m≡m%n+[m/n]*n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Fin.Properties as FP
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; subst)
import Real as R
open R using (ℝ; _≃_; _*_; _+_)
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FS
import DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact as T
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Actual
open G
open R41 using (stride; restrict; Sector)
open Actual using (expand; delay)

zeroPrefix : ∀ f n → (∀ k → k ≤ n → f k ≃ R.0ℝ) → Seq.SeriesOf f (suc n) ≃ R.0ℝ
zeroPrefix f zero h = U.add0 P.≃-refl (h zero z≤n)
zeroPrefix f (suc n) h = U.add0 (zeroPrefix f n (λ k hk → h k (NP.≤-step hk))) (h (suc n) NP.≤-refl)

multiple : ∀ n → n % 41 ≡ zero → n ≡ stride (n / 41)
multiple n h = trans (m≡m%n+[m/n]*n n 41) (cong (λ k → k + stride (n / 41)) h)

sumMultiple : ∀ a b → a % 41 ≡ zero → b % 41 ≡ zero → (a + b) % 41 ≡ zero
sumMultiple a b ha hb =
  trans (cong (λ n → n % 41) (cong₂ _+_ (multiple a ha) (multiple b hb)))
    (trans (cong (λ n → n % 41) (sym (NP.*-distribʳ-+ 41 (a / 41) (b / 41))))
      (m*n%n≡0 ((a / 41) + (b / 41)) 41))

sectorProduct : ∀ f g → Sector f → Sector g → Sector (f ⊗s g)
sectorProduct f g hf hg n hn =
  let term = λ k → f k * g (n ∸ k)
      termZero : ∀ k → k ≤ n → term k ≃ R.0ℝ
      termZero k hk with k % 41 NP.≟ zero | (n ∸ k) % 41 NP.≟ zero
      ... | no h | _ = P.≃-trans (P.*-congʳ (hf k h)) (P.*-zeroˡ _)
      ... | yes _ | no h = U.right0 (hg (n ∸ k) h)
      ... | yes h | yes j = ⊥-elim (hn (trans
        (cong (λ m → m % 41) (sym (T.indexPlusTruncatedComplement n k hk)))
        (sumMultiple k (n ∸ k) h j)))
  in P.≃-trans (FS.finSumIsSeriesOf term (suc n)) (zeroPrefix term n termZero)

sectorExpand : ∀ f → Sector (expand f)
sectorExpand f n hn with n % 41 NP.≟ zero
... | yes h = ⊥-elim (hn h)
... | no _ = P.≃-refl

restrictExpand : ∀ f → restrict (expand f) ≈s f
restrictExpand f n rewrite m*n%n≡0 n 41 | m*n/n≡m n 41 = P.≃-refl

sectorZero : Sector H.zeroSeries
sectorZero n hn = P.≃-refl

sectorUnit : Sector H.unitSeries
sectorUnit zero h = ⊥-elim (h refl)
sectorUnit (suc n) h = P.≃-refl

sectorScale : ∀ a f → Sector f → Sector (scale a f)
sectorScale a f hf n hn = U.right0 (hf n hn)

sectorAdd : ∀ f g → Sector f → Sector g → Sector (f ⊕s g)
sectorAdd f g hf hg n hn = U.add0 (hf n hn) (hg n hn)

sectorSub : ∀ f g → Sector f → Sector g → Sector (f ⊖s g)
sectorSub f g hf hg n hn = U.sub0 (hf n hn) (hg n hn)

sectorPower : ∀ f → Sector f → ∀ n → Sector (H.power f n)
sectorPower f hf zero = sectorUnit
sectorPower f hf (suc n) = sectorProduct f (H.power f n) hf (sectorPower f hf n)

restrictPower : ∀ f → Sector f → ∀ n → restrict (H.power f n) ≈s H.power (restrict f) n
restrictPower f hf zero zero = P.≃-refl
restrictPower f hf zero (suc n) = P.≃-refl
restrictPower f hf (suc n) = transS (R41.reduceRow f (H.power f n) hf)
  (mulCong reflS (restrictPower f hf n))

mono : Nat → Series
mono k = delay k H.unitSeries

monoAway : ∀ k n → (n ≡ k → ⊥) → mono k n ≃ R.0ℝ
monoAway zero zero h = ⊥-elim (h refl)
monoAway zero (suc n) h = P.≃-refl
monoAway (suc k) zero h = P.≃-refl
monoAway (suc k) (suc n) h = monoAway k n (λ e → h (cong suc e))

monoAt : ∀ n → mono n n ≃ R.1ℝ
monoAt zero = P.≃-refl
monoAt (suc n) = monoAt n

monoSector : ∀ k → Sector (mono (stride k))
monoSector k n hn = monoAway (stride k) n
  (λ e → hn (trans (cong (λ m → m % 41) e) (m*n%n≡0 k 41)))

monoMul : ∀ k f → (mono k ⊗s f) ≈s delay k f
monoMul zero f = Ring.rowUnitLeft f
monoMul (suc k) f zero = P.≃-trans (Row.cauchyCoefficientZero (mono (suc k)) f) (P.*-zeroˡ _)
monoMul (suc k) f (suc n) = P.≃-trans (U.zeroHead (mono (suc k)) f P.≃-refl n) (monoMul k f n)

sectorDelay : ∀ k f → Sector f → Sector (delay (stride k) f)
sectorDelay k f hf n hn = P.≃-trans (P.≃-symm (monoMul (stride k) f n))
  (sectorProduct (mono (stride k)) f (monoSector k) hf n hn)

dropDelay : ∀ k l f n → delay (k + l) f (k + n) ≃ delay l f n
dropDelay zero l f n = P.≃-refl
dropDelay (suc k) l f n = dropDelay k l f n

restrictDelay : ∀ k f → restrict (delay (stride k) f) ≈s delay k (restrict f)
restrictDelay zero f n = P.≃-refl
restrictDelay (suc k) f zero = P.≃-refl
restrictDelay (suc k) f (suc n) = P.≃-trans
  (dropDelay 41 (stride k) f (stride n)) (restrictDelay k f n)

constantSector : ∀ a → Sector (G.constant a)
constantSector a zero h = ⊥-elim (h refl)
constantSector a (suc n) h = P.≃-refl

restrictConstant : ∀ a → restrict (G.constant a) ≈s G.constant a
restrictConstant a zero = P.≃-refl
restrictConstant a (suc n) = P.≃-refl
