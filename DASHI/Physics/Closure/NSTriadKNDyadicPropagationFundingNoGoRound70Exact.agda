module DASHI.Physics.Closure.NSTriadKNDyadicPropagationFundingNoGoRound70Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND 70 / CONCRETE DYADIC DEGRADATION FALSIFIER
--
-- Round62 already proves the exact rational identity
--
--   sum_{j=0}^N 2^(-j) + 2*2^(-(N+1)) = 2,
--
-- hence every finite dyadic partial sum is <=2.
--
-- This file reuses that theorem on the Round70 propagation-funding carrier.
-- If the only guaranteed concentration charge at propagation depth j is
-- 2^(-j), then EVERY finite prefix has an explicit event ledger funded by the
-- single finite budget E=2.  Therefore merely producing arbitrarily many
-- distinct propagated events with dyadically decaying lower bounds cannot give
-- the desired contradiction.
--
-- This does not assert that the physical Navier-Stokes propagation law has
-- dyadic degradation.  It is a sharp quantitative falsifier for any proposed
-- Lemma-4 estimate whose resulting charge floor is bounded by this summable
-- pattern.  A viable barrier mechanism needs non-summable cumulative charge
-- floors (or some stronger contradiction not based on finite funding).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale
import DASHI.Physics.Closure.NSTriadKNHHGoodFourthOrderDyadicL1Round62Exact as DyadicSum
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding
import DASHI.Physics.Closure.NSTriadKNFiniteDisjointConcentrationBudgetRound69Exact as R69

dyadicFloorPrefix : Nat → List ℚ
dyadicFloorPrefix zero = Scale.inverseDyadicScale zero ∷ []
dyadicFloorPrefix (suc n) =
  Scale.inverseDyadicScale (suc n) ∷ dyadicFloorPrefix n

dyadicFloorPrefixSumExact : ∀ n →
  Funding.sumFloors (dyadicFloorPrefix n)
  ≡ DyadicSum.partialDyadicWeight n
dyadicFloorPrefixSumExact zero = refl
dyadicFloorPrefixSumExact (suc n) =
  trans
    (cong (Scale.inverseDyadicScale (suc n) +_)
      (dyadicFloorPrefixSumExact n))
    (ℚP.+-comm
      (Scale.inverseDyadicScale (suc n))
      (DyadicSum.partialDyadicWeight n))

dyadicFloorPrefixNonnegative : ∀ n →
  Funding.AllFloorsNonnegative (dyadicFloorPrefix n)
dyadicFloorPrefixNonnegative zero =
  Funding.nonnegative∷
    (DyadicSum.inverseDyadicScaleNonnegative zero)
    Funding.nonnegative[]
dyadicFloorPrefixNonnegative (suc n) =
  Funding.nonnegative∷
    (DyadicSum.inverseDyadicScaleNonnegative (suc n))
    (dyadicFloorPrefixNonnegative n)

dyadicFloorPrefixBelowTwo : ∀ n →
  Funding.sumFloors (dyadicFloorPrefix n) ≤ Scale.two
dyadicFloorPrefixBelowTwo n =
  subst
    (_≤ Scale.two)
    (sym (dyadicFloorPrefixSumExact n))
    (DyadicSum.partialDyadicWeightBelowTwo n)

dyadicFloorPrefixEvents : Nat → List R69.ConcentrationEvent
dyadicFloorPrefixEvents n =
  Funding.exactFloorEvents
    (dyadicFloorPrefix n)
    (dyadicFloorPrefixNonnegative n)

-- Every finite propagation depth is explicitly compatible with ONE fixed
-- energy budget 2.  Thus event count alone cannot contradict finite energy
-- when the guaranteed charge floor decays dyadically.
dyadicPropagationEveryFinitePrefixFundedByTwo : ∀ n →
  Funding.ScaleDependentConcentrationBudget
    Scale.two
    (dyadicFloorPrefix n)
    (dyadicFloorPrefixEvents n)
dyadicPropagationEveryFinitePrefixFundedByTwo n =
  Funding.summableFloorsAdmitFundedLedger
    (dyadicFloorPrefixNonnegative n)
    (dyadicFloorPrefixBelowTwo n)

round70DyadicPropagationFundingContradictionFalsified : Bool
round70DyadicPropagationFundingContradictionFalsified = true

round70DyadicFloorsOutrunEveryFiniteBudget : Bool
round70DyadicFloorsOutrunEveryFiniteBudget = false

round70DyadicPropagationFundingContradictionFalsifiedIsTrue :
  round70DyadicPropagationFundingContradictionFalsified ≡ true
round70DyadicPropagationFundingContradictionFalsifiedIsTrue = refl

round70DyadicFloorsOutrunEveryFiniteBudgetIsFalse :
  round70DyadicFloorsOutrunEveryFiniteBudget ≡ false
round70DyadicFloorsOutrunEveryFiniteBudgetIsFalse = refl
