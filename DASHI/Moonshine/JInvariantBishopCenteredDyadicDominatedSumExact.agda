module DASHI.Moonshine.JInvariantBishopCenteredDyadicDominatedSumExact where

-- Source-written, uncompiled. Direct cofinal convergence from a
-- conserved moving sum: no assumed convergence of the target row.
-- Fix an interior prefix, use its actual pointwise convergence, and
-- bound the moving complement by a convergent nonnegative series.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base as N using (_⊔_; _<_; z≤n; s≤s⁻¹) renaming (_≤_ to _≤N_)
import Data.Nat.Properties as NP
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact as Eps
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopCenteredDyadicFoldReindexExact as Re
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Sum
import DASHI.Moonshine.JInvariantBishopCenteredDyadicAddressExact as Addr
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Codec

-- SeriesOf uses an empty zero prefix and adds term n at suc n.
prefix : (Nat → ℝ) → Nat → ℝ
prefix = Seq.SeriesOf

prefixConv : ∀ (f : Nat → Nat → ℝ) (g : Nat → ℝ) →
  (∀ k → Seq._ConvergesTo_ (λ n → f n k) (g k)) →
  ∀ K → Seq._ConvergesTo_ (λ n → prefix (f n) K) (prefix g K)
prefixConv f g cv zero = Power.constantConverges R.0ℝ
prefixConv f g cv (suc K) = Inv.addR (prefixConv f g cv K) (cv K)

-- The finite complement is compared with the SAME original majorant
-- prefix, with its sign intact; no absolute value of a total is used
-- as a surrogate for the total of absolute residuals.
tailBound : ∀ (f b : Nat → ℝ) K L → K ≤N L →
  (∀ i → K ≤N i → i < L → ∣ f i ∣ ≤ b i) →
  ∣ prefix f L - prefix f K ∣ ≤ prefix b L - prefix b K
tailBound f b zero zero N.z≤n h =
  P.≤-respˡ-≃ (P.∣-∣-cong (P.+-inverseʳ R.0ℝ))
    (P.≤-respˡ-≃ (P.nonNegx⇒∣x∣≃x P.nonNeg0)
      (P.≤-respʳ-≃ (P.≃-symm (P.+-inverseʳ R.0ℝ)) P.≤-refl))
tailBound f b K (suc L) KL h with NP.m≤n⇒m<n∨m≡n KL
... | inj₂ eq = equalCase eq
  where
  equalCase : K ≡ suc L →
    ∣ prefix f (suc L) - prefix f K ∣ ≤ prefix b (suc L) - prefix b K
  equalCase refl =
    P.≤-respˡ-≃ (P.∣-∣-cong (P.+-inverseʳ (prefix f (suc L))))
      (P.≤-respˡ-≃ (P.nonNegx⇒∣x∣≃x P.nonNeg0)
        (P.≤-respʳ-≃ (P.≃-symm (P.+-inverseʳ (prefix b (suc L)))) P.≤-refl))
... | inj₁ lt =
  let old = tailBound f b K L (N.s≤s⁻¹ lt)
        (λ i Ki iL → h i Ki (NP.<-trans iL (NP.n<1+n L)))
      step = h L (N.s≤s⁻¹ lt) (NP.n<1+n L)
      eqF = let open P.ℝ-Solver in solve 3
        (λ a c d → (a ⊕ c) ⊖ d ⊜ (a ⊖ d) ⊕ c) P.≃-refl
        (prefix f L) (f L) (prefix f K)
      eqB = let open P.ℝ-Solver in solve 3
        (λ a c d → (a ⊖ d) ⊕ c ⊜ (a ⊕ c) ⊖ d) P.≃-refl
        (prefix b L) (b L) (prefix b K)
  in P.≤-respˡ-≃ (P.∣-∣-cong eqF)
    (P.≤-respʳ-≃ eqB (Bounds.boundAdd old step))

-- Generic constructive cofinal passage with literal dyadic cardinal.
-- The only analytic inputs are fixed-term convergence and summable
-- moving-tail domination, not convergence of the desired endpoint.
module Cofinal
  (f : Nat → Nat → ℝ) (g b : Nat → ℝ) (target B : ℝ)
  (fixed : ∀ k → Seq._ConvergesTo_ (λ n → f n k) (g k))
  (majorant : Seq._ConvergesTo_ (prefix b) B)
  (depth cut : Nat)
  (bound : ∀ n k → depth ≤N n → cut ≤N k → k < Codec.bitCardinality n →
    ∣ f n k ∣ ≤ b k)
  (conserved : ∀ n → prefix (f n) (Codec.bitCardinality n) ≃ target)
  where

  -- At every sufficiently large FIXED interior cutoff K, select a
  -- depth n constructively after obtaining that prefix's modulus.
  -- The moving finite sum is constant, so this proves convergence of
  -- the actual fixed-prefix sequence to target.
  converges : Seq._ConvergesTo_ (prefix g) target
  converges = Seq.con* λ { (suc k) →
    let eps = (+ 1 / suc k) ⋆
        quarter = (+ 1 / 4) ⋆
        delta = quarter * eps
        dp = P.posx,y⇒posx*y (Eps.reciprocalNatPositive 3) (Eps.reciprocalNatPositive k)
        maj = Seq.fast-ε-from-convergence (B , majorant) delta dp
        cutoff = cut ⊔ proj₁ maj
    in cutoff , λ K past →
      let after = NP.≤-trans (NP.n≤1+n cutoff) past
          Kcut = NP.≤-trans (NP.m≤m⊔n cut (proj₁ maj)) after
          Kmaj = NP.≤-trans (NP.m≤n⊔m cut (proj₁ maj)) after
          head = Seq.fast-ε-from-convergence (prefix g K , prefixConv f g fixed K) delta dp
          n = (depth ⊔ K) ⊔ proj₁ head
          nd = NP.≤-trans (NP.m≤m⊔n depth K) (NP.m≤m⊔n (depth ⊔ K) (proj₁ head))
          Kn = NP.≤-trans (NP.m≤n⊔m depth K) (NP.m≤m⊔n (depth ⊔ K) (proj₁ head))
          nhead = NP.m≤n⊔m (depth ⊔ K) (proj₁ head)
          L = Codec.bitCardinality n
          KL = NP.≤-trans Kn (NP.≤-trans (NP.n≤1+n n) (Addr.cardDominatesDepth n))
          Lmaj = NP.≤-trans Kmaj KL
          errorHead = P.<⇒≤ (proj₂ head n nhead)
          atK = P.<⇒≤ (proj₂ maj K Kmaj)
          atL = P.<⇒≤ (proj₂ maj L Lmaj)
          majDiff = P.≤-respˡ-≃
            (P.∣-∣-cong (let open P.ℝ-Solver in solve 3
              (λ a b c → a ⊖ b ⊜ (a ⊖ c) ⊖ (b ⊖ c)) P.≃-refl (prefix b L) (prefix b K) B))
            (Bounds.boundSub atL atK)
          tail = P.≤-trans (tailBound (f n) b K L KL
                    (λ i Ki iL → bound n i nd (NP.≤-trans Kcut Ki) iL))
                   (P.≤-trans P.x≤∣x∣ majDiff)
          targetTail = P.≤-respˡ-≃ (P.∣-∣-cong
            (P.+-cong (P.≃-symm (conserved n)) P.≃-refl)) tail
          signedHead = P.≤-respˡ-≃ (P.∣x-y∣≃∣y-x∣ (prefix g K) (prefix (f n) K)) errorHead
          signedTail = P.≤-respˡ-≃ (P.∣x-y∣≃∣y-x∣ (prefix (f n) K) target) targetTail
          total = P.≤-respˡ-≃ (P.∣-∣-cong
            (let open P.ℝ-Solver in solve 3
              (λ a b c → a ⊖ c ⊜ (a ⊖ b) ⊕ (b ⊖ c)) P.≃-refl (prefix g K) (prefix (f n) K) target))
            (Bounds.boundAdd signedHead signedTail)
          budget = P.≤-respˡ-≃
            (let open P.ℝ-Solver in solve 1
              (λ e → (Κ (+ 1 / 4) ⊗ e) ⊕ ((Κ (+ 1 / 4) ⊗ e) ⊕ (Κ (+ 1 / 4) ⊗ e))
                ⊜ Κ (+ 3 / 4) ⊗ e) P.≃-refl eps)
            (P.≤-respʳ-≃ (P.*-identityˡ eps)
              (P.*-monoʳ-≤-nonNeg
                (P.p≤q⇒p⋆≤q⋆ (+ 3 / 4) (+ 1 / 1) (toWitness {a? = QP._≤?_ (+ 3 / 4) (+ 1 / 1)} _))
                (P.pos⇒nonNeg (Eps.reciprocalNatPositive k))))
      in P.≤-trans total budget }
