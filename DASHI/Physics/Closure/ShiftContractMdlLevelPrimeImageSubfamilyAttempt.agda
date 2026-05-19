module DASHI.Physics.Closure.ShiftContractMdlLevelPrimeImageSubfamilyAttempt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState; shiftContractStateTransportedPrimeEmbedding)

------------------------------------------------------------------------
-- Smallest explicit subfamily we can certify on ShiftContractState.
--
-- This is a one-point subfamily around the explicit state
-- `coarseCounterexampleLeft`.  On such a singleton family, equality of the
-- strengthened package `π-mdl-max` forces equality of transported prime
-- image because both members rewrite to the same explicit witness.

MdlLevelPrimeImageSubfamily : Set
MdlLevelPrimeImageSubfamily =
  Σ ShiftContractState (λ x → x ≡ coarseCounterexampleLeft)

subfamilyMember : MdlLevelPrimeImageSubfamily
subfamilyMember = coarseCounterexampleLeft , refl

primeImage-equal-on-subfamily :
  ∀ {x y : MdlLevelPrimeImageSubfamily} →
  π-mdl-max (fst x) ≡ π-mdl-max (fst y) →
  shiftContractStateTransportedPrimeEmbedding (fst x)
    ≡
  shiftContractStateTransportedPrimeEmbedding (fst y)
primeImage-equal-on-subfamily {x = x} {y = y} _ rewrite snd x | snd y = refl

subfamily-π-mdl-max :
  ∀ {x y : MdlLevelPrimeImageSubfamily} →
  π-mdl-max (fst x) ≡ π-mdl-max (fst y)
subfamily-π-mdl-max {x = x} {y = y} rewrite snd x | snd y = refl

subfamily-prime-image :
  ∀ {x y : MdlLevelPrimeImageSubfamily} →
  shiftContractStateTransportedPrimeEmbedding (fst x)
    ≡
  shiftContractStateTransportedPrimeEmbedding (fst y)
subfamily-prime-image {x = x} {y = y} rewrite snd x | snd y = refl
