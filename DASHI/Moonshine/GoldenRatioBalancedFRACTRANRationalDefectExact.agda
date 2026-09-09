module DASHI.Moonshine.GoldenRatioBalancedFRACTRANRationalDefectExact where

------------------------------------------------------------------------
-- EXACT ℚᵘ DEFECT FOR THE BALANCED-FRACTRAN FIBONACCI RATIOS
--
-- For every positive macro state (p,q), the Nat Cassini/norm-one receipt
--
--   p^2 = p q + q^2 + 1
--
-- is transported through the repository's actual unnormalised-rational
-- representation to
--
--   (p/q)^2 - (p/q) - 1  ~=  1/q^2.
--
-- The proof is deliberately factored into small variable-denominator
-- cross-multiplication lemmas, following the same ℚ.*≡* / Integer-solver idiom
-- already used by FiniteNatSuccessorFractionExact and the Bishop Basel owners.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤSolver)
open ℤSolver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Nat.Base using (NonZero)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using () renaming (solve to solveNat; _:+_ to _:+ₙ_; _:*_ to _:*ₙ_; con to conNat; _:=_ to _:=ₙ_)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; _/_; _+_; _-_; _*_; _≃_; *≡*)
import Data.Rational.Unnormalised.Properties as ℚP
import NonReflectiveQ as ℚSolver

import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANNormOneInvariantExact as Norm

------------------------------------------------------------------------
-- 1. Generic positive-denominator fraction algebra.
------------------------------------------------------------------------

oneQ : ℚᵘ
oneQ = + 1 / 1

ratioQ : (p q : Nat) → .{{_ : NonZero q}} → ℚᵘ
ratioQ p q = + p / q

reciprocalSquareQ : (q : Nat) → .{{_ : NonZero q}} → ℚᵘ
reciprocalSquareQ q = + 1 / (q * q)

canonicalNormFraction :
  (p q : Nat) → .{{_ : NonZero q}} → ℚᵘ
canonicalNormFraction p q =
  + (p * q + q * q + 1) / (q * q)

ratioPlusOneEquivalent :
  (p q : Nat) → .{{_ : NonZero q}} →
  (ratioQ p q ℚ.+ oneQ)
  ℚ.≃
  (+ (p + q) / q)
ratioPlusOneEquivalent p q =
  ℚ.*≡*
    (solve 2
      (λ p′ q′ →
        (((p′ :* con (+ 1)) :+ (con (+ 1) :* q′)) :* q′)
        :=
        ((p′ :+ q′) :* (q′ :* con (+ 1))))
      refl
      (+ p)
      (+ q))

ratioPlusOnePlusReciprocalEquivalent :
  (p q : Nat) → .{{_ : NonZero q}} →
  (((+ (p + q) / q) ℚ.+ reciprocalSquareQ q))
  ℚ.≃
  (+ (((p + q) * q) + 1) / (q * q))
ratioPlusOnePlusReciprocalEquivalent p q =
  ℚ.*≡*
    (solve 2
      (λ p′ q′ →
        ((((p′ :+ q′) :* (q′ :* q′))
          :+ (con (+ 1) :* q′))
          :* (q′ :* q′))
        :=
        ((((p′ :+ q′) :* q′) :+ con (+ 1))
          :* (q′ :* (q′ :* q′))))
      refl
      (+ p)
      (+ q))

expandedCanonicalNumerator :
  (p q : Nat) →
  ((p + q) * q) + 1 ≡ p * q + q * q + 1
expandedCanonicalNumerator =
  solveNat 2
    (λ p q →
      (((p :+ₙ q) :*ₙ q) :+ₙ conNat 1)
      :=ₙ
      (((p :*ₙ q) :+ₙ (q :*ₙ q)) :+ₙ conNat 1))
    refl

ratioPlusOnePlusReciprocalAsCanonical :
  (p q : Nat) → .{{_ : NonZero q}} →
  ((ratioQ p q ℚ.+ oneQ) ℚ.+ reciprocalSquareQ q)
  ℚ.≃ canonicalNormFraction p q
ratioPlusOnePlusReciprocalAsCanonical p q =
  ℚP.≃-trans
    (ℚP.+-cong
      (ratioPlusOneEquivalent p q)
      ℚP.≃-refl)
    (ℚP.≃-trans
      (ratioPlusOnePlusReciprocalEquivalent p q)
      (ℚP.≃-reflexive
        (cong
          (λ numerator → + numerator / (q * q))
          (expandedCanonicalNumerator p q))))

------------------------------------------------------------------------
-- 2. Nat norm-one rewrites the square to that same canonical fraction.
------------------------------------------------------------------------

ratioSquareAsCanonical :
  (p q : Nat) → .{{_ : NonZero q}} →
  Norm.NormOne p q →
  (ratioQ p q ℚ.* ratioQ p q)
  ℚ.≃ canonicalNormFraction p q
ratioSquareAsCanonical p q norm
  rewrite norm =
  ℚ.*≡* refl

ratioSquareBalance :
  (p q : Nat) → .{{_ : NonZero q}} →
  Norm.NormOne p q →
  (ratioQ p q ℚ.* ratioQ p q)
  ℚ.≃
  ((ratioQ p q ℚ.+ oneQ) ℚ.+ reciprocalSquareQ q)
ratioSquareBalance p q norm =
  ℚP.≃-trans
    (ratioSquareAsCanonical p q norm)
    (ℚP.≃-sym (ratioPlusOnePlusReciprocalAsCanonical p q))

------------------------------------------------------------------------
-- 3. Rearrange the paid square balance to the desired quadratic defect.
------------------------------------------------------------------------

defectFromSquareBalance :
  (r s : ℚᵘ) →
  (r ℚ.* r) ℚ.≃ ((r ℚ.+ oneQ) ℚ.+ s) →
  (((r ℚ.* r) ℚ.- r) ℚ.- oneQ) ℚ.≃ s
defectFromSquareBalance r s balance =
  ℚP.≃-trans
    (ℚP.+-congˡ
      (ℚ.- oneQ)
      (ℚP.+-congˡ (ℚ.- r) balance))
    (let open ℚSolver in
     solve 3
       (λ r′ o′ s′ →
         ((((r′ ⊕ o′) ⊕ s′) ⊖ r′) ⊖ o′) ⊜ s′)
       ℚP.≃-refl
       r oneQ s)

normOneRatioDefect :
  (p q : Nat) → .{{_ : NonZero q}} →
  Norm.NormOne p q →
  (((ratioQ p q ℚ.* ratioQ p q) ℚ.- ratioQ p q) ℚ.- oneQ)
  ℚ.≃ reciprocalSquareQ q
normOneRatioDefect p q norm =
  defectFromSquareBalance
    (ratioQ p q)
    (reciprocalSquareQ q)
    (ratioSquareBalance p q norm)

------------------------------------------------------------------------
-- 4. Instantiate on every balanced-FRACTRAN macro state.
------------------------------------------------------------------------

macroRatioDefect :
  (n : Nat) →
  let pair = Ratio.iteratePositiveMacro n
      p = Ratio.positiveHi pair
      q = Ratio.positiveLo pair
  in
  (((Ratio.positiveRatioRational pair ℚ.* Ratio.positiveRatioRational pair)
      ℚ.- Ratio.positiveRatioRational pair)
      ℚ.- oneQ)
  ℚ.≃ reciprocalSquareQ q
macroRatioDefect n =
  normOneRatioDefect
    (Ratio.positiveHi (Ratio.iteratePositiveMacro n))
    (Ratio.positiveLo (Ratio.iteratePositiveMacro n))
    (Norm.balancedMacroNormOne n)

------------------------------------------------------------------------
-- 5. Frontier.
------------------------------------------------------------------------

record RationalDefectFrontier : Set where
  constructor rational-defect-frontier
  field
    natNormOneTransportedToUnnormalisedRational : Bool
    exactReciprocalSquareDefectOnEveryMacroState : Bool
    bishopEmbeddingSameObjectWelded : Bool
    conjugateFactorLowerBoundPaid : Bool

canonicalRationalDefectFrontier : RationalDefectFrontier
canonicalRationalDefectFrontier =
  rational-defect-frontier true true false false
