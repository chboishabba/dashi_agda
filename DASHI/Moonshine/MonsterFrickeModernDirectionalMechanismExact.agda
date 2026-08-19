module DASHI.Moonshine.MonsterFrickeModernDirectionalMechanismExact where

------------------------------------------------------------------------
-- MODERN DIRECTIONAL MONSTER / FRICKE MECHANISM
--
-- FORWARD DIRECTION -- MONSTROUS MOONSHINE
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bull. London Math. Soc. 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- Richard E. Borcherds,
-- "Monstrous moonshine and monstrous Lie superalgebras",
-- Invent. Math. 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- CONVERSE DIRECTION -- MONSTROUS EXPONENT SUPPORT
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- For p > 3 their Theorem 1.2 detects Monster prime support through the
-- non-rational supersingular locus; the separate low-level authority handles
-- p=2,3 exactly.
--
-- DASHI CONTRIBUTION
--
-- Assemble the arbitrary-prime equivalence with independent directional
-- mechanisms:
--
--   p | |M|  --moonshine-->  g(X_0^+(p)) = 0
--
--   g(X_0^+(p)) = 0  --Duncan--Swisher support-->  p | |M|.
--
-- The forward route now uses the FACTORED Moonshine authority:
--
--   global Conway--Norton/Borcherds genus-zero theorem (imported once)
--     +
--   p-specific class order + exact Gamma_g = Gamma_0(p)^+ selection
--     =>
--   Fricke genus zero.
--
-- Thus per-prime genus zero is no longer bundled into the class-selection
-- witness.  The older Duncan--Ono/Ogg support-equivalence module is not
-- imported here; it remains an independent historical/cross-check route.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as Fricke
import DASHI.Moonshine.MonsterPrimeMoonshineFrickeFactoredAuthorityExact as Moonshine
import DASHI.Moonshine.DuncanSwisherMonsterFrickeAllPrimesExact as DS

------------------------------------------------------------------------
-- Two different proof mechanisms for the two implications.
------------------------------------------------------------------------

monsterPrimeImpliesFrickeGenusZeroByMoonshine :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  Fricke.primeFrickeGenus p prime ≡ 0
monsterPrimeImpliesFrickeGenusZeroByMoonshine =
  Moonshine.monsterPrimeImpliesFrickeGenusZeroViaFactoredMoonshine

frickeGenusZeroImpliesMonsterPrimeByExponentSupport :
  (p : Nat) → (prime : Prime p) →
  Fricke.primeFrickeGenus p prime ≡ 0 →
  Monster.PrimeDividesMonsterOrder p
frickeGenusZeroImpliesMonsterPrimeByExponentSupport =
  DS.duncanSwisherFrickeGenusZeroImpliesMonsterAllPrimes

monsterPrimeIffFrickeGenusZeroModern :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Fricke.primeFrickeGenus p prime ≡ 0
monsterPrimeIffFrickeGenusZeroModern p prime =
  monsterPrimeImpliesFrickeGenusZeroByMoonshine p prime
  , frickeGenusZeroImpliesMonsterPrimeByExponentSupport p prime

------------------------------------------------------------------------
-- Independent second forward proof from Duncan--Swisher is retained as a
-- cross-check: the two proof routes share the target but not their mechanism.
------------------------------------------------------------------------

duncanSwisherAlsoProvesForward :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  Fricke.primeFrickeGenus p prime ≡ 0
duncanSwisherAlsoProvesForward =
  DS.duncanSwisherMonsterImpliesFrickeGenusZeroAllPrimes

record MonsterFrickeModernDirectionalBoundary : Set where
  field
    forwardMechanismIsMoonshine : Bool
    forwardGenusZeroAuthorityFactoredFromPrimeSelection : Bool
    forwardExactClassGroupEqualityIsLoadBearing : Bool
    converseMechanismIsExponentSupport : Bool
    DuncanOnoSupportEquivalenceImported : Bool
    MonsterPrimeLaneImported : Bool
    finiteUnder72FrickeTableImported : Bool
    independentDuncanSwisherForwardCrossCheckRetained : Bool
    arbitraryPrimeEquivalenceDerived : Bool

canonicalMonsterFrickeModernDirectionalBoundary :
  MonsterFrickeModernDirectionalBoundary
canonicalMonsterFrickeModernDirectionalBoundary = record
  { forwardMechanismIsMoonshine = true
  ; forwardGenusZeroAuthorityFactoredFromPrimeSelection = true
  ; forwardExactClassGroupEqualityIsLoadBearing = true
  ; converseMechanismIsExponentSupport = true
  ; DuncanOnoSupportEquivalenceImported = false
  ; MonsterPrimeLaneImported = false
  ; finiteUnder72FrickeTableImported = false
  ; independentDuncanSwisherForwardCrossCheckRetained = true
  ; arbitraryPrimeEquivalenceDerived = true
  }
