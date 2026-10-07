module DASHI.Moonshine.OggSSP2BPostBrauerOuterActionBlindSpotExact where

------------------------------------------------------------------------
-- WHY THE B' BRAUER PASS DOES NOT CLOSE C'
--
-- The executed screen compares 2-regular (odd-order) traces.  The sourced
-- Completion10 operator is an involution of M22:2, hence order 2 and therefore
-- 2-singular.  Ordinary Brauer-character equality pays semisimplified content
-- but cannot determine the J2^5 action of this p-singular element.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSP2BTate276M24BrauerRuntimeReceiptExact as Brauer
import DASHI.Moonshine.OggSSP2BM22d2Completion10RuntimeReceiptExact as M22d2
import DASHI.Moonshine.OggSSPP2InertiaBrauerRegularityBoundaryExact as Regularity

completionOuterOrder : Nat
completionOuterOrder = 2

completionOuterOrderIsTwo : completionOuterOrder ≡ 2
completionOuterOrderIsTwo = refl

finiteOuterSourceFound : M22d2.outerJ2x5MatchCount ≡ 2
finiteOuterSourceFound = M22d2.outerJ2x5MatchCountIsTwo

brauerIngressPaid :
  Brauer.semisimplifiedIngressPaid Brauer.canonicalTate276M24BrauerRuntimeReceipt
  ≡ true
brauerIngressPaid = Brauer.semisimplifiedIngressIsPaid

ordinaryBrauerCannotSeeAllP2Sectors :
  Regularity.ordinaryRepresentativeBrauerShortcutRejected
    Regularity.OrdinaryBrauerEvaluationOnEverySectorRepresentativePaysFiveSectorRule
ordinaryBrauerCannotSeeAllP2Sectors = Regularity.ordinaryBrauerRepresentativeShortcutRejected

data BrauerPassDeterminesOuterJ2x5Action : Set where

brauerPassDoesNotDetermineOuterJ2x5Action :
  BrauerPassDeterminesOuterJ2x5Action → ⊥
brauerPassDoesNotDetermineOuterJ2x5Action ()

record PostBrauerOuterActionBoundary : Set where
  constructor post-brauer-outer-action-boundary
  field
    semisimplifiedIngressPaid : Bool
    finiteOuterJ2x5SourcePaid : Bool
    outerElementOrder : Nat
    outerElementVisibleToOrdinaryP2BrauerCharacter : Bool
    actualOuterActionOnSameQPaid : Bool

canonicalPostBrauerOuterActionBoundary : PostBrauerOuterActionBoundary
canonicalPostBrauerOuterActionBoundary =
  post-brauer-outer-action-boundary true true 2 false false
