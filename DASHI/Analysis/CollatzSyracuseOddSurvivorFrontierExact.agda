module DASHI.Analysis.CollatzSyracuseOddSurvivorFrontierExact where

------------------------------------------------------------------------
-- ODD-ONLY SURVIVOR FRONTIER
--
-- After paying every even start in one literal Syracuse step, the remaining
-- terminal theorem can be organized as a pointwise odd-start frontier.
-- Finite exact search/cylinder arithmetic may pay coverage below any chosen
-- frontier.  Universal stopping still requires the frontiers to be unbounded
-- on the literal odd tail; no density statement is promoted into that fact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_<_; _≤_)
import Data.Product as Product
open Product using (Σ; _×_; _,_)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.Analysis.CollatzSyracuseSurvivorFrontierExact as Frontier
import DASHI.Analysis.CollatzSyracuseOddTailReductionExact as OddTail
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Universal

record OddSurvivorFrontierSource : Set₁ where
  field
    frontier : Nat → Nat

    belowFrontierOddDescends :
      (horizon : Nat) →
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Itinerary.parity x ≡ true →
      Syracuse.toNat x < frontier horizon →
      Frontier.StrictDescentWithin horizon x

    frontierUnboundedOnOddTail :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      Itinerary.parity x ≡ true →
      Σ Nat (λ horizon → Syracuse.toNat x < frontier horizon)

open OddSurvivorFrontierSource public

asOddTailStrictDescentSource :
  OddSurvivorFrontierSource →
  OddTail.OddTailStrictDescentAboveEightSource
asOddTailStrictDescentSource source = record
  { OddTail.oddTailDescend = λ x lower nontrivial odd →
      let
        cover = frontierUnboundedOnOddTail source x lower odd
        horizon = Product.proj₁ cover
        xBelow = Product.proj₂ cover
        witness = belowFrontierOddDescends
          source horizon x lower nontrivial odd xBelow
        k = Product.proj₁ witness
        boundedAndDescent = Product.proj₂ witness
      in
      k , Product.proj₂ boundedAndDescent
  }

asLiteralStrictDescentSource :
  OddSurvivorFrontierSource →
  Universal.LiteralStrictDescentSource
asLiteralStrictDescentSource source =
  OddTail.asLiteralStrictDescentSource
    (asOddTailStrictDescentSource source)

universalStoppingFromOddSurvivorFrontier :
  OddSurvivorFrontierSource →
  (x : Syracuse.PositiveNat) →
  Universal.ReachesOne x
universalStoppingFromOddSurvivorFrontier source =
  OddTail.universalStoppingFromOddTail
    (asOddTailStrictDescentSource source)

record OddSurvivorFrontierBoundary : Set where
  constructor oddSurvivorFrontierBoundary
  field
    evenTailAlreadyRemoved : Nat
    finiteOddHorizonCoverageInterfacePaid : Nat
    oddFrontierCompilerPaid : Nat
    finiteCylinderSearchMayFeedCoverage : Nat
    BernoulliDensityCreatesUnboundedOddFrontier : Nat
    unboundedOddFrontierProducerPaid : Nat
    onlyUnboundedLeafIsOddFrontierGrowth : Nat

canonicalOddSurvivorFrontierBoundary : OddSurvivorFrontierBoundary
canonicalOddSurvivorFrontierBoundary =
  oddSurvivorFrontierBoundary 1 1 1 1 0 0 1
