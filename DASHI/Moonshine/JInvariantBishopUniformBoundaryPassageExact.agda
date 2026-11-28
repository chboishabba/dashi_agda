module DASHI.Moonshine.JInvariantBishopUniformBoundaryPassageExact where

-- Source-written, kernel pending. RH donor: the original
-- BishopDirichletUniformBaselTailsExact limit-order proof and the
-- shifted-prefix discipline of BishopOriginalEtaPairBlockTelescopingExact.
-- Here the majorant is arbitrary but convergent, so a scaled Basel
-- budget is not confused with the unscaled coefficient.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as N
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _-_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as RH
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopCenteredDyadicDominatedSumExact as Cof
open Cof using (prefix)

-- Exact same finite-tail indexing as the RH original Dirichlet owner.
finiteTail : ∀ f K L → (prefix f L - prefix f K) ≃ Seq.∑ f K L
finiteTail = RH.partialMinusIsFiniteTail

shift : ∀ (f : Nat → ℝ) v → Seq._ConvergesTo_ f v → ∀ K →
  Seq._ConvergesTo_ (λ n → f (n + K)) v
shift f v cv K = Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
  (Seq.subseq* ((λ n → n + K) , (λ n → P.≃-refl) ,
    (λ n → N.n<1+n (n + K)))) (v , cv)

-- Uniform error from an original convergent series, by passing the
-- finite-tail inequality to its actual limit. No uniform convergence
-- premise is supplied.
limitTail : ∀ f b v B K →
  Seq._ConvergesTo_ (prefix f) v →
  Seq._ConvergesTo_ (prefix b) B →
  (∀ k → K ≤ k → R._≤_ ∣ f k ∣ (b k)) →
  R._≤_ ∣ v - prefix f K ∣ (B - prefix b K)
limitTail f b v B K cv cb bound =
  let fcv = Inv.subR (shift (prefix f) v cv K) (Power.constantConverges (prefix f K))
      bcv = Inv.subR (shift (prefix b) B cb K) (Power.constantConverges (prefix b K))
  in Seq.xₙ≤yₙ⇒limxₙ≤limyₙ
    (λ n → Cof.tailBound f b K (n + K) (N.m≤n+m K n)
      (λ i Ki _ → bound i Ki))
    (∣ v - prefix f K ∣ , Seq.∣xₙ∣→∣x₀∣ (_ , fcv))
    (B - prefix b K , bcv)

-- The boundary limit is determined from fixed finite heads, with no
-- choice of an infinite sum on the boundary needed in the premises.
module Passage
  (f : Nat → Nat → ℝ) (g b row : Nat → ℝ) (target B : ℝ)
  (fixed : ∀ k → Seq._ConvergesTo_ (λ n → f n k) (g k))
  (rows : ∀ n → Seq._ConvergesTo_ (prefix (f n)) (row n))
  (rowLimit : Seq._ConvergesTo_ row target)
  (majorant : Seq._ConvergesTo_ (prefix b) B)
  (bound : ∀ n k → R._≤_ ∣ f n k ∣ (b k)) where

  error : Nat → ℝ
  error K = B - prefix b K

  errorNull : Seq._ConvergesTo_ error R.0ℝ
  errorNull = Seq.xₙ→x∧x≃y⇒xₙ→y
    (Inv.subR (Power.constantConverges B) majorant) (P.+-inverseʳ B)

  boundaryTail : ∀ K → R._≤_ ∣ target - prefix g K ∣ (error K)
  boundaryTail K =
    let cv = Inv.subR rowLimit (Cof.prefixConv f g fixed K)
    in Seq.xₙ≤y⇒limxₙ≤y
      (λ n → limitTail (f n) b (row n) B K (rows n) majorant (λ k _ → bound n k))
      (∣ target - prefix g K ∣ , Seq.∣xₙ∣→∣x₀∣ (_ , cv))

  boundaryConverges : Seq._ConvergesTo_ (prefix g) target
  boundaryConverges = Vanish.vanishingDifferenceConvergence
    (Power.constantConverges target) errorNull
    (λ K → P.≤-respˡ-≃ (P.∣x-y∣≃∣y-x∣ (prefix g K) target)
      (P.≤-trans (boundaryTail K) P.x≤∣x∣))
