module DASHI.Physics.Closure.NSPeriodicConcreteCandidateBudgetArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Physics.Closure.NSPeriodicConcreteNorms as Concrete
import DASHI.Physics.Closure.NSPeriodicCanonicalNearYoungAllocation as Near
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact arithmetic extracted from the deterministic candidate constants.
--
-- Near Young payments are 1/16,1/16,2/16 and therefore exactly 1/4.  The
-- selected far-high constant product is eight and the R=8 tail candidate is
-- 1/16, which is strictly stronger than the allotted 1/8.  None of these scalar
-- facts promotes the associated Fourier estimates.
------------------------------------------------------------------------

concreteLowHighDeltaMatches :
  Concrete.nearLowHighDeltaNumerator ≡ Near.lowHighYoungPayment
concreteLowHighDeltaMatches = refl

concreteHighLowDeltaMatches :
  Concrete.nearHighLowDeltaNumerator ≡ Near.highLowYoungPayment
concreteHighLowDeltaMatches = refl

concreteHighHighDeltaMatches :
  Concrete.nearHighHighDeltaNumerator ≡ Near.highHighYoungPayment
concreteHighHighDeltaMatches = refl

concreteNearAllocationIsQuarter :
  Concrete.nearLowHighDeltaNumerator
  + Concrete.nearHighLowDeltaNumerator
  + Concrete.nearHighHighDeltaNumerator
  ≡ Near.oneQuarter
concreteNearAllocationIsQuarter = refl

concreteFarHighConstantProductIsEight :
  Concrete.farHighConstantProduct ≡ 8
concreteFarHighConstantProductIsEight =
  Concrete.farHighConstantProductIsEight

concreteFarHighCandidateIsOneSixteenth :
  Concrete.farHighR8ReducedNumerator ≡ Near.oneSixteenth
concreteFarHighCandidateIsOneSixteenth = refl

concreteFarHighCandidateDenominatorIsSixteen :
  Concrete.farHighR8ReducedDenominator ≡ 16
concreteFarHighCandidateDenominatorIsSixteen =
  Concrete.farHighR8DenominatorIsSixteen

------------------------------------------------------------------------
-- Same-denominator order certificate: 1/16 <= 2/16 = 1/8.
------------------------------------------------------------------------

infix 4 _≤ᴺ_

data _≤ᴺ_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ᴺ n
  suc≤suc : ∀ {m n} → m ≤ᴺ n → suc m ≤ᴺ suc n

one≤two : suc zero ≤ᴺ suc (suc zero)
one≤two = suc≤suc zero≤

farHighCandidateFitsCanonicalEighth :
  Concrete.farHighR8ReducedNumerator ≤ᴺ Near.oneEighth
farHighCandidateFitsCanonicalEighth = one≤two

record ConcreteCandidateBudgetArithmetic : Set where
  field
    near-low-high-share :
      Concrete.nearLowHighDeltaNumerator ≡ Near.lowHighYoungPayment
    near-high-low-share :
      Concrete.nearHighLowDeltaNumerator ≡ Near.highLowYoungPayment
    near-high-high-share :
      Concrete.nearHighHighDeltaNumerator ≡ Near.highHighYoungPayment
    near-total-quarter :
      Concrete.nearLowHighDeltaNumerator
      + Concrete.nearHighLowDeltaNumerator
      + Concrete.nearHighHighDeltaNumerator
      ≡ Near.oneQuarter
    far-high-product-eight : Concrete.farHighConstantProduct ≡ 8
    far-high-one-sixteenth-fits-eighth :
      Concrete.farHighR8ReducedNumerator ≤ᴺ Near.oneEighth

concreteCandidateBudgetArithmetic : ConcreteCandidateBudgetArithmetic
concreteCandidateBudgetArithmetic = record
  { near-low-high-share = concreteLowHighDeltaMatches
  ; near-high-low-share = concreteHighLowDeltaMatches
  ; near-high-high-share = concreteHighHighDeltaMatches
  ; near-total-quarter = concreteNearAllocationIsQuarter
  ; far-high-product-eight = concreteFarHighConstantProductIsEight
  ; far-high-one-sixteenth-fits-eighth =
      farHighCandidateFitsCanonicalEighth
  }

------------------------------------------------------------------------
-- Status: the candidate scalar arithmetic is closed exactly.  The near Fourier
-- product estimates and the far-high Sobolev/geometric-tail inequality remain
-- conditional until proved uniformly in K and the Galerkin cutoff N.
------------------------------------------------------------------------

concreteCandidateBudgetArithmeticLevel : ProofLevel
concreteCandidateBudgetArithmeticLevel = machineChecked
