{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopUniformLimitSequentialContinuityExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: CONSTRUCTIVE BISHOP UNIFORM-LIMIT THEOREM.
--
-- The theorem consumes an ACTUAL uniform approximation modulus:
-- at every positive rational precision choose one finite cutoff whose
-- error bound holds for all arguments. A single chosen approximant
-- is continuous at the selected limit point, hence the limiting
-- function is sequentially continuous there.
--
-- This is a theorem on the pinned Bishop REAL carrier. The selected
-- zeta/xi function still needs its own uniform-tail receipt and its
-- original exp/log term identification. Those are NOT fields
-- automatically inhabited here.
--
-- Sources: Bishop and Bridges; Cauchy; Murray (2022)/Csimma Bishop
-- (the native Sequence.con* convergence and scalar triangle law).
-- Agda --safe kernel receipt pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Integer.Base using (+_)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Rational.Unnormalised as Rat using (ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as RatP

open import NonReflectiveZ as ZSolver using ()
  renaming
    ( solve to Zsolve
    ; _⊕_ to _:+_
    ; _⊗_ to _:*_
    ; _⊜_ to _:=_
    ; Κ to ZK
    )

import Real as R
import RealProperties as RP
import Sequence as Seq

inversePrecision : (k : Nat) .{{_ : Nat.NonZero k}} → R.ℝ
inversePrecision k = R._⋆ (+ 1 / k)

halfPlusHalf :
  (k : Nat) .{{_ : Nat.NonZero k}} →
  R._≃_
    (R._+_
      (inversePrecision (2 * k))
      (inversePrecision (2 * k)))
    (inversePrecision k)
halfPlusHalf (suc k-1) =
  let
    k = suc k-1
    half = (+ 1 / (2 * k))
  in
  RP.≃-trans
    (RP.≃-symm (RP.⋆-distrib-+ half half))
    (RP.⋆-cong
      (RatP.*≡*
        (Zsolve 1
          (λ q →
            ((ZK (+ 1) :* (ZK (+ 2) :* q)) :+
             (ZK (+ 1) :* (ZK (+ 2) :* q))) :* q
            := ZK (+ 1) :*
               ((ZK (+ 2) :* q) :* (ZK (+ 2) :* q)))
          refl
          (+ k))))

threeLegTriangle :
  (a b c d : R.ℝ) →
  R._≤_
    (R.∣ R._-_ a d ∣)
    (R._+_
      (R.∣ R._-_ a b ∣)
      (R._+_
        (R.∣ R._-_ b c ∣)
        (R.∣ R._-_ c d ∣)))
threeLegTriangle a b c d =
  let open RP.ℝ-Solver
  in
  RP.≤-respˡ-≃
    (RP.∣-∣-cong
      (solve 4
        (λ a′ b′ c′ d′ →
          a′ ⊖ d′
          ⊜ (a′ ⊖ b′) ⊕ ((b′ ⊖ c′) ⊕ (c′ ⊖ d′)))
        RP.≃-refl a b c d))
    (RP.≤-trans
      (RP.∣x+y∣≤∣x∣+∣y∣
        (R._-_ a b)
        (R._+_ (R._-_ b c) (R._-_ c d)))
      (RP.+-monoˡ-≤
        (R.∣ R._-_ a b ∣)
        (RP.∣x+y∣≤∣x∣+∣y∣
          (R._-_ b c)
          (R._-_ c d))))

-- A finite or otherwise selected approximant is sequentially continuous.
SequentiallyContinuous :
  (R.ℝ → R.ℝ) → Set
SequentiallyContinuous f =
  (input : Nat → R.ℝ) →
  (limit : R.ℝ) →
  Seq._ConvergesTo_ input limit →
  Seq._ConvergesTo_ (λ n → f (input n)) (f limit)

-- Uniform approximation is proof relevant: the *same* index must
-- approximate the target function at every Bishop-real argument.
UniformApproximation :
  (Nat → R.ℝ → R.ℝ) →
  (R.ℝ → R.ℝ) →
  Set
UniformApproximation approximation f =
  (k : Nat) .{{_ : Nat.NonZero k}} →
  Σ Nat (λ count →
    (x : R.ℝ) →
    R._≤_
      (R.∣ R._-_ (approximation count x) (f x) ∣)
      (inversePrecision k))

uniformLimitSequentialContinuity :
  (approximation : Nat → R.ℝ → R.ℝ) →
  (f : R.ℝ → R.ℝ) →
  (∀ count → SequentiallyContinuous (approximation count)) →
  UniformApproximation approximation f →
  SequentiallyContinuous f
uniformLimitSequentialContinuity approximation f
    continuous uniform input limit inputConverges =
  Seq.con*
    (λ
      { (suc k-1) →
        let
          k = suc k-1
          fine = 2 * (2 * k)
          uniformReceipt = uniform fine
          m = proj₁ uniformReceipt
          uniformAt = proj₂ uniformReceipt
          approximantConverges =
            continuous m input limit inputConverges
          continuityReceipt =
            Seq.convergence-getter
              (approximation m limit , approximantConverges)
              (2 * k)
          cutoff = suc (proj₁ continuityReceipt)
          quarter = inversePrecision fine
          half = inversePrecision (2 * k)
          whole = inversePrecision k
        in
        proj₁ continuityReceipt ,
        (λ
          { (suc n-1) n≥cutoff →
            let
              n = suc n-1
              atInput = uniformAt (input n)
              atLimit = uniformAt limit
              atMiddle = proj₂ continuityReceipt n n≥cutoff
              reversedFirst =
                RP.≤-respˡ-≃
                  (RP.∣x-y∣≃∣y-x∣
                    (approximation m (input n))
                    (f (input n)))
                  atInput
              open RP.ℝ-Solver
            in
            let open RP.≤-Reasoning
            in begin
              R.∣ R._-_ (f (input n)) (f limit) ∣
                ≤⟨ threeLegTriangle
                      (f (input n))
                      (approximation m (input n))
                      (approximation m limit)
                      (f limit) ⟩
              R._+_
                (R.∣ R._-_ (f (input n))
                  (approximation m (input n)) ∣)
                (R._+_
                  (R.∣ R._-_
                    (approximation m (input n))
                    (approximation m limit) ∣)
                  (R.∣ R._-_ (approximation m limit)
                    (f limit) ∣))
                ≤⟨ RP.+-mono-≤ reversedFirst
                      (RP.+-mono-≤ atMiddle atLimit) ⟩
              R._+_ quarter (R._+_ half quarter)
                ≈⟨ solve 3
                      (λ q h q′ →
                        q ⊕ (h ⊕ q′) ⊜ (q ⊕ q′) ⊕ h)
                      RP.≃-refl quarter half quarter ⟩
              R._+_ (R._+_ quarter quarter) half
                ≈⟨ RP.+-congʳ half (halfPlusHalf (2 * k)) ⟩
              R._+_ half half
                ≈⟨ halfPlusHalf k ⟩
              whole ∎
          })
      })
