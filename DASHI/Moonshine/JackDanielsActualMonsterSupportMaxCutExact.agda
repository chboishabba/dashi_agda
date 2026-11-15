module DASHI.Moonshine.JackDanielsActualMonsterSupportMaxCutExact where

------------------------------------------------------------------------
-- JACK DANIEL'S FINITE ACTUAL-MONSTER SUPPORT CAPSTONE
--
-- PURPOSE
--   Close the finite 20-prime control seam without reading the external Ogg
--   label and without importing the repository MonsterPrimeLane/SSP15 list.
--
-- UPSTREAM REPOSITORY THEOREMS
--   * AllPrimeRepresentationFrickeClosureExact constructs the unbiased finite
--     representation/arithmetic Fricke closure predicate.
--   * MonsterBinaryTernaryInformationDepthExact owns the exact published
--     Monster order and its factorisation.
--
-- THIS MODULE
--   Evaluates the actual Monster order modulo each candidate prime and proves
--   that the repo-native representation/Fricke closure predicate agrees with
--   literal Monster-order support on all twenty controls.
--
-- ATTRIBUTION BOUNDARY
--   The Monster order is inherited from the already-attributed repository
--   owner.  No new external scientific source is acquired here.  The finite
--   comparison theorem below is a repository formal reconstruction.
--
-- NON-CLAIMS
--   This finite theorem is not an arbitrary-prime proof, does not construct a
--   Monster element of order p, and does not derive the Monster group itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Nat using (_%_)

import DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact as Closure
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.MonsterBinaryTernaryInformationDepthExact as Monster

------------------------------------------------------------------------
-- 1. Literal actual-order remainder on the unbiased finite candidate domain.
------------------------------------------------------------------------

monsterOrderRemainder : Closure.PrimeCandidateUnder72 -> Nat
monsterOrderRemainder Closure.spinorPrime2 = Monster.monsterOrderExact % 2
monsterOrderRemainder (Closure.oddPrime Matrix.prime3) = Monster.monsterOrderExact % 3
monsterOrderRemainder (Closure.oddPrime Matrix.prime5) = Monster.monsterOrderExact % 5
monsterOrderRemainder (Closure.oddPrime Matrix.prime7) = Monster.monsterOrderExact % 7
monsterOrderRemainder (Closure.oddPrime Matrix.prime11) = Monster.monsterOrderExact % 11
monsterOrderRemainder (Closure.oddPrime Matrix.prime13) = Monster.monsterOrderExact % 13
monsterOrderRemainder (Closure.oddPrime Matrix.prime17) = Monster.monsterOrderExact % 17
monsterOrderRemainder (Closure.oddPrime Matrix.prime19) = Monster.monsterOrderExact % 19
monsterOrderRemainder (Closure.oddPrime Matrix.prime23) = Monster.monsterOrderExact % 23
monsterOrderRemainder (Closure.oddPrime Matrix.prime29) = Monster.monsterOrderExact % 29
monsterOrderRemainder (Closure.oddPrime Matrix.prime31) = Monster.monsterOrderExact % 31
monsterOrderRemainder (Closure.oddPrime Matrix.prime37) = Monster.monsterOrderExact % 37
monsterOrderRemainder (Closure.oddPrime Matrix.prime41) = Monster.monsterOrderExact % 41
monsterOrderRemainder (Closure.oddPrime Matrix.prime43) = Monster.monsterOrderExact % 43
monsterOrderRemainder (Closure.oddPrime Matrix.prime47) = Monster.monsterOrderExact % 47
monsterOrderRemainder (Closure.oddPrime Matrix.prime53) = Monster.monsterOrderExact % 53
monsterOrderRemainder (Closure.oddPrime Matrix.prime59) = Monster.monsterOrderExact % 59
monsterOrderRemainder (Closure.oddPrime Matrix.prime61) = Monster.monsterOrderExact % 61
monsterOrderRemainder (Closure.oddPrime Matrix.prime67) = Monster.monsterOrderExact % 67
monsterOrderRemainder (Closure.oddPrime Matrix.prime71) = Monster.monsterOrderExact % 71

isZero : Nat -> Bool
isZero zero = true
isZero (suc _) = false

actualMonsterOrderSupport : Closure.PrimeCandidateUnder72 -> Bool
actualMonsterOrderSupport candidate = isZero (monsterOrderRemainder candidate)

------------------------------------------------------------------------
-- 2. Exact control values.  The five negative controls are not hard-coded as
--    labels: these are reductions of the actual published Monster order.
------------------------------------------------------------------------

prime37ActualRemainder :
  monsterOrderRemainder (Closure.oddPrime Matrix.prime37) ≡ 21
prime37ActualRemainder = refl

prime43ActualRemainder :
  monsterOrderRemainder (Closure.oddPrime Matrix.prime43) ≡ 13
prime43ActualRemainder = refl

prime53ActualRemainder :
  monsterOrderRemainder (Closure.oddPrime Matrix.prime53) ≡ 36
prime53ActualRemainder = refl

prime61ActualRemainder :
  monsterOrderRemainder (Closure.oddPrime Matrix.prime61) ≡ 47
prime61ActualRemainder = refl

prime67ActualRemainder :
  monsterOrderRemainder (Closure.oddPrime Matrix.prime67) ≡ 14
prime67ActualRemainder = refl

------------------------------------------------------------------------
-- 3. The finite Jack Daniel's weld.
------------------------------------------------------------------------

representationFrickeClosureMatchesActualMonsterSupport :
  (candidate : Closure.PrimeCandidateUnder72) ->
  Closure.representationArithmeticFrickeClosed candidate
  ≡ actualMonsterOrderSupport candidate
representationFrickeClosureMatchesActualMonsterSupport Closure.spinorPrime2 = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime3) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime5) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime7) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime11) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime13) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime17) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime19) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime23) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime29) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime31) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime37) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime41) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime43) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime47) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime53) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime59) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime61) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime67) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime71) = refl

------------------------------------------------------------------------
-- 4. Promotion boundary.
------------------------------------------------------------------------

allTwentyActualSupportComparisonsPaid : Bool
allTwentyActualSupportComparisonsPaid = true

externalOggLabelUsedInCapstone : Bool
externalOggLabelUsedInCapstone = false

monsterPrimeLaneUsedInCapstone : Bool
monsterPrimeLaneUsedInCapstone = false

data FiniteControlCreatesArbitraryPrimeTheorem : Set where
data FiniteSupportCreatesMonsterElement : Set where

finiteControlDoesNotCreateArbitraryPrimeTheorem :
  FiniteControlCreatesArbitraryPrimeTheorem -> ⊥
finiteControlDoesNotCreateArbitraryPrimeTheorem ()

finiteSupportDoesNotConstructMonsterElement :
  FiniteSupportCreatesMonsterElement -> ⊥
finiteSupportDoesNotConstructMonsterElement ()

record JackDanielsActualMonsterSupportBoundary : Set where
  field
    actualPublishedMonsterOrderUsed : Bool
    representationFrickeClosureReused : Bool
    allTwentyActualSupportComparisons : Bool
    externalOggLabelUsed : Bool
    MonsterPrimeLaneUsed : Bool
    arbitraryPrimeTheoremClaimed : Bool
    MonsterElementConstructed : Bool
    attributionFirewallPreserved : Bool

canonicalJackDanielsActualMonsterSupportBoundary :
  JackDanielsActualMonsterSupportBoundary
canonicalJackDanielsActualMonsterSupportBoundary = record
  { actualPublishedMonsterOrderUsed = true
  ; representationFrickeClosureReused = true
  ; allTwentyActualSupportComparisons = allTwentyActualSupportComparisonsPaid
  ; externalOggLabelUsed = externalOggLabelUsedInCapstone
  ; MonsterPrimeLaneUsed = monsterPrimeLaneUsedInCapstone
  ; arbitraryPrimeTheoremClaimed = false
  ; MonsterElementConstructed = false
  ; attributionFirewallPreserved = true
  }
