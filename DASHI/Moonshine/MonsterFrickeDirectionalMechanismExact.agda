module DASHI.Moonshine.MonsterFrickeDirectionalMechanismExact where

------------------------------------------------------------------------
-- DIRECTIONAL MECHANISM FOR THE MONSTER / FRICKE PRIME THEOREM
--
-- Forward direction:
--   Conway--Norton / Borcherds monstrous moonshine.
--
--     p | |M|
--       -> a prime-order Monster class has moonshine group Gamma_0(p)^+
--       -> its McKay--Thompson series is a Hauptmodul
--       -> Gamma_0(p)^+ has genus zero.
--
-- Converse direction:
--   Ogg / Duncan--Ono classification-equivalence authority.
--
--     g(X_0^+(p)) = 0
--       -> p | |M|.
--
-- This is strictly more explanatory than using the Ogg/Duncan--Ono
-- supersingular equivalence for both arrows.  The moonshine proof explains the
-- PRESENCE of Monster prime divisors in the genus-zero set.  It still does not
-- explain why the genus-zero set has no extra primes; that remains the converse
-- classification input.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as OggRoute
import DASHI.Moonshine.MonsterPrimeMoonshineFrickeStandardAuthorityExact as Moonshine

------------------------------------------------------------------------
-- Forward arrow now avoids supersingular rationality entirely.
------------------------------------------------------------------------

monsterPrimeImpliesFrickeGenusZeroConceptually :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  OggRoute.primeFrickeGenus p prime ≡ 0
monsterPrimeImpliesFrickeGenusZeroConceptually =
  Moonshine.monsterPrimeImpliesFrickeGenusZeroViaMoonshine

------------------------------------------------------------------------
-- Converse remains the genuinely classificatory/Ogg side.
------------------------------------------------------------------------

frickeGenusZeroImpliesMonsterPrimeByOgg :
  (p : Nat) → (prime : Prime p) →
  OggRoute.primeFrickeGenus p prime ≡ 0 →
  Monster.PrimeDividesMonsterOrder p
frickeGenusZeroImpliesMonsterPrimeByOgg =
  OggRoute.primeFrickeGenusZeroImpliesMonster

------------------------------------------------------------------------
-- Reassemble the arbitrary-prime equivalence with distinct proof provenance on
-- its two arrows.
------------------------------------------------------------------------

monsterPrimeIffFrickeGenusZeroDirectional :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ OggRoute.primeFrickeGenus p prime ≡ 0
monsterPrimeIffFrickeGenusZeroDirectional p prime =
  monsterPrimeImpliesFrickeGenusZeroConceptually p prime
  , frickeGenusZeroImpliesMonsterPrimeByOgg p prime

------------------------------------------------------------------------
-- Boundary: exactly one arrow still needs the Ogg/Duncan--Ono classification.
------------------------------------------------------------------------

record MonsterFrickeDirectionalMechanismBoundary : Set where
  field
    forwardUsesMonstrousMoonshine : Bool
    forwardUsesSupersingularRationality : Bool
    forwardUsesFiniteMonsterPrimeTable : Bool
    converseUsesOggClassification : Bool
    converseExplainedByMoonshineHere : Bool
    presenceOfMonsterPrimesExplainedByMoonshine : Bool
    absenceOfExtraGenusZeroPrimesExplainedByMoonshine : Bool
    arbitraryPrimeEquivalenceReassembled : Bool

canonicalMonsterFrickeDirectionalMechanismBoundary :
  MonsterFrickeDirectionalMechanismBoundary
canonicalMonsterFrickeDirectionalMechanismBoundary = record
  { forwardUsesMonstrousMoonshine = true
  ; forwardUsesSupersingularRationality = false
  ; forwardUsesFiniteMonsterPrimeTable = false
  ; converseUsesOggClassification = true
  ; converseExplainedByMoonshineHere = false
  ; presenceOfMonsterPrimesExplainedByMoonshine = true
  ; absenceOfExtraGenusZeroPrimesExplainedByMoonshine = false
  ; arbitraryPrimeEquivalenceReassembled = true
  }
