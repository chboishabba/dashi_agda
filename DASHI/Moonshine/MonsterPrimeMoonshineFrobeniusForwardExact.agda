module DASHI.Moonshine.MonsterPrimeMoonshineFrobeniusForwardExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Pierre Deligne and Michael Rapoport,
-- "Les schemas de modules de courbes elliptiques", LNM 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- DASHI CONTRIBUTION
--
-- Expose the conceptual FORWARD Monster -> supersingular theorem without using
-- Duncan--Swisher or the older Duncan--Ono/Ogg support equivalence:
--
--   p | |M|
--     -> selected prime-order Monster class has Gamma_g = Gamma_0(p)^+
--     -> Monstrous Moonshine gives g(X_0^+(p)) = 0
--     -> Deligne--Rapoport/Fricke geometry gives pointwise-fixed coarse
--        supersingular Frobenius.
--
-- The theorem is stated for p >= 5 because that is the prime-level geometric
-- authority surface currently used for the actual supersingular carrier.  The
-- low primes 2,3 have separate genus authority and are not silently folded into
-- this geometric statement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.MonsterPrimeMoonshineFrickeFactoredAuthorityExact as Moonshine
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as All
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Published

------------------------------------------------------------------------
-- On a syntactic 5+n prime, the all-prime Fricke genus carrier is literally
-- the prime-pinned Deligne--Rapoport genus carrier.
------------------------------------------------------------------------

moonshineGenusZeroAtFivePlus :
  (n : Nat) →
  (prime : Prime (5 + n)) →
  Monster.PrimeDividesMonsterOrder (5 + n) →
  Published.genericFrickeGenus
    (Published.publishedAuthorityAt
      (5 + n) prime (NatP.m≤m+n 5 n)) ≡ 0
moonshineGenusZeroAtFivePlus n prime divides =
  Moonshine.monsterPrimeImpliesFrickeGenusZeroViaFactoredMoonshine
    (5 + n) prime divides

------------------------------------------------------------------------
-- Direct Moonshine -> geometric fixedness.
------------------------------------------------------------------------

monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p →
  Published.PublishedFrobeniusFullyFixed p prime ge5
monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine 0 prime () divides
monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine 1 prime () divides
monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine 2 prime () divides
monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine 3 prime () divides
monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine 4 prime () divides
monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine
  (suc (suc (suc (suc (suc n))))) prime ge5 divides =
  let
    canonicalGe5 : 5 ≤ 5 + n
    canonicalGe5 = NatP.m≤m+n 5 n

    genusZero :
      Published.genericFrickeGenus
        (Published.publishedAuthorityAt (5 + n) prime canonicalGe5) ≡ 0
    genusZero = moonshineGenusZeroAtFivePlus n prime divides

    fixedIffGenus =
      Published.publishedFrobeniusFullyFixedIffFrickeGenusZero
        (5 + n) prime canonicalGe5
  in
  -- The target proof may carry a different proof term ge5.  The proposition
  -- depends only on p and the pinned authority; proof irrelevance is avoided by
  -- constructing the canonical branch directly, which is definitionally the
  -- same p=5+n source lane used by PublishedFrobeniusFullyFixed.
  proj₂ fixedIffGenus genusZero

------------------------------------------------------------------------
-- Residual form: Moonshine kills the nonfixed Frobenius-pair coordinate.
------------------------------------------------------------------------

monsterPrimeImpliesZeroFrobeniusPairResidualByMoonshine :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p →
  DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact.pairedCount
    (DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact.supersingularFrobenius
      (Published.publishedAuthorityAt p prime ge5)) ≡ 0
monsterPrimeImpliesZeroFrobeniusPairResidualByMoonshine p prime ge5 divides =
  let
    fixed = monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine
      p prime ge5 divides
    pairIffFixed =
      DASHI.Moonshine.DuncanSwisherMonsterFrobeniusFixedExact.pairResidualZeroIffFullyFixed
        p prime ge5
  in
  proj₂ pairIffFixed fixed

------------------------------------------------------------------------
-- Boundary: Duncan--Swisher is not part of the forward genus-zero mechanism.
-- The residual helper currently reuses its already-derived generic equivalence
-- between pair-zero and fixedness; that equivalence itself is geometric, but a
-- future cleanup may move it to a neutral owner.
------------------------------------------------------------------------

record MonsterPrimeMoonshineFrobeniusForwardBoundary : Set where
  field
    forwardClassGroupMechanismIsMoonshine : Bool
    exactGammaGEqualsPrimeFrickeConsumed : Bool
    genusZeroTransportedFromGlobalMoonshine : Bool
    DeligneRapoportGeometryConsumed : Bool
    DuncanSwisherSupportUsedToDeriveGenusZero : Bool
    oldDuncanOnoSupportEquivalenceImported : Bool
    MonsterPrimeLaneEnumerationImported : Bool
    directMonsterToFrobeniusFixednessDerived : Bool

canonicalMonsterPrimeMoonshineFrobeniusForwardBoundary :
  MonsterPrimeMoonshineFrobeniusForwardBoundary
canonicalMonsterPrimeMoonshineFrobeniusForwardBoundary = record
  { forwardClassGroupMechanismIsMoonshine = true
  ; exactGammaGEqualsPrimeFrickeConsumed = true
  ; genusZeroTransportedFromGlobalMoonshine = true
  ; DeligneRapoportGeometryConsumed = true
  ; DuncanSwisherSupportUsedToDeriveGenusZero = false
  ; oldDuncanOnoSupportEquivalenceImported = false
  ; MonsterPrimeLaneEnumerationImported = false
  ; directMonsterToFrobeniusFixednessDerived = true
  }
