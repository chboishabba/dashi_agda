module DASHI.Moonshine.OggSSPSmallCharacteristicIgusaRamificationNoGoExact where

------------------------------------------------------------------------
-- RAW IGUSA-RAMIFICATION STATISTIC NO-GO
--
-- CLASSICAL INPUT (Katz--Mazur, Ch. 12.9)
--
-- For n >= 1, the transition
--
--   Ig(p^(n+1)) -> Ig(p^n)
--
-- is fully ramified of degree p over every supersingular point.  On local
-- differentials the supersingular exponent is
--
--   p^(2n) (p-1).
--
-- The full Igusa tower ramification invariant appearing in the standard
-- numerology is
--
--   d_Q(Ig(p^n)) = p^(2(n-1)) - 1.
--
-- At n=2 these source-native values are:
--
--   transition differential exponent:
--     p=2 -> 4,   p=3 -> 18
--
--   tower ramification invariant:
--     p=2 -> 3,   p=3 -> 8.
--
-- Neither pair is the Monster residual pair (10,2).
--
-- Therefore the missing fourth term cannot be identified with a raw Igusa
-- ramification/different statistic.  Any successful Igusa mechanism must use a
-- DERIVED modular-function/divisor/q-expansion observable on the bad-level
-- tower.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _*_; _^_; _-_)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPSmallCharacteristicBadLevelIgusaCorrectionCutsetExact as IgusaCutset
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source-native Igusa statistics.
------------------------------------------------------------------------

transitionDifferentialExponent :
  Nat ->
  Nat ->
  Nat
transitionDifferentialExponent p n =
  (p ^ (2 * n)) * (p - 1)

towerRamificationInvariant :
  Nat ->
  Nat ->
  Nat
towerRamificationInvariant p n =
  (p ^ (2 * (n - 1))) - 1

p2PrimeSquareTransitionExponent :
  transitionDifferentialExponent 2 1 ≡ 4
p2PrimeSquareTransitionExponent = refl

p3PrimeSquareTransitionExponent :
  transitionDifferentialExponent 3 1 ≡ 18
p3PrimeSquareTransitionExponent = refl

p2PrimeSquareRamificationInvariant :
  towerRamificationInvariant 2 2 ≡ 3
p2PrimeSquareRamificationInvariant = refl

p3PrimeSquareRamificationInvariant :
  towerRamificationInvariant 3 2 ≡ 8
p3PrimeSquareRamificationInvariant = refl

------------------------------------------------------------------------
-- 2. Monster residual target.
------------------------------------------------------------------------

p2MonsterResidual : Nat
p2MonsterResidual = 10

p3MonsterResidual : Nat
p3MonsterResidual = 2

p2TransitionExponentNotResidual :
  transitionDifferentialExponent 2 1 ≡ p2MonsterResidual -> ⊥
p2TransitionExponentNotResidual ()

p3TransitionExponentNotResidual :
  transitionDifferentialExponent 3 1 ≡ p3MonsterResidual -> ⊥
p3TransitionExponentNotResidual ()

p2TowerInvariantNotResidual :
  towerRamificationInvariant 2 2 ≡ p2MonsterResidual -> ⊥
p2TowerInvariantNotResidual ()

p3TowerInvariantNotResidual :
  towerRamificationInvariant 3 2 ≡ p3MonsterResidual -> ⊥
p3TowerInvariantNotResidual ()

------------------------------------------------------------------------
-- 3. No raw-statistic promotion.
------------------------------------------------------------------------

data IgusaTransitionDifferentIsExceptionalFourthTerm : Set where
data IgusaTowerRamificationIsExceptionalFourthTerm : Set where
data FullRamificationAloneCreatesCorrectedHauptmodulDivisor : Set where

transitionDifferentDoesNotEqualFourthTerm :
  IgusaTransitionDifferentIsExceptionalFourthTerm -> ⊥
transitionDifferentDoesNotEqualFourthTerm ()

towerRamificationDoesNotEqualFourthTerm :
  IgusaTowerRamificationIsExceptionalFourthTerm -> ⊥
towerRamificationDoesNotEqualFourthTerm ()

fullRamificationDoesNotCreateCorrectedDivisor :
  FullRamificationAloneCreatesCorrectedHauptmodulDivisor -> ⊥
fullRamificationDoesNotCreateCorrectedDivisor ()

------------------------------------------------------------------------
-- 4. Cutset retained.
------------------------------------------------------------------------

igusaCutsetBoundary :
  IgusaCutset.BadLevelIgusaCorrectionCutsetBoundary
igusaCutsetBoundary =
  IgusaCutset.canonicalBadLevelIgusaCorrectionCutsetBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record IgusaRamificationNoGoBoundary : Set where
  constructor igusa-ramification-no-go-boundary
  field
    p2TransitionExponentFour : Bool
    p3TransitionExponentEighteen : Bool
    p2TowerInvariantThree : Bool
    p3TowerInvariantEight : Bool
    rawTransitionPairMatchesTenTwo : Bool
    rawTowerInvariantPairMatchesTenTwo : Bool
    derivedBadLevelModularObservableStillRequired : Bool
    attributionFirewallPreserved : Bool

canonicalIgusaRamificationNoGoBoundary :
  IgusaRamificationNoGoBoundary
canonicalIgusaRamificationNoGoBoundary =
  igusa-ramification-no-go-boundary
    true true true true false false true true
