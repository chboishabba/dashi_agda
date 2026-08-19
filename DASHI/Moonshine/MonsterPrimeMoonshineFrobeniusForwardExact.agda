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
-- The theorem is stated on the canonical p=5+n source lane.  This avoids
-- treating proof terms of 5<=p as interchangeable data; the underlying prime
-- is still arbitrary above three.  Low primes 2,3 retain their separate source
-- lane and are not silently folded into this geometric statement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Nat.Properties as NatP
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.MonsterPrimeMoonshineFrickeFactoredAuthorityExact as Moonshine
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Published

------------------------------------------------------------------------
-- On a syntactic 5+n prime, the all-prime Fricke genus carrier reduces to the
-- prime-pinned Deligne--Rapoport genus carrier used below.
------------------------------------------------------------------------

moonshineGenusZeroAtFivePlus :
  (n : Nat) →
  (prime : Prime (5 + n)) →
  Monster.PrimeDividesMonsterOrder (5 + n) →
  Selector.genericFrickeGenus
    (Published.publishedAuthorityAt
      (5 + n) prime (NatP.m≤m+n 5 n)) ≡ 0
moonshineGenusZeroAtFivePlus n prime divides =
  Moonshine.monsterPrimeImpliesFrickeGenusZeroViaFactoredMoonshine
    (5 + n) prime divides

------------------------------------------------------------------------
-- Direct Moonshine -> geometric fixedness.
------------------------------------------------------------------------

monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine :
  (n : Nat) →
  (prime : Prime (5 + n)) →
  Monster.PrimeDividesMonsterOrder (5 + n) →
  Published.PublishedFrobeniusFullyFixed
    (5 + n) prime (NatP.m≤m+n 5 n)
monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine n prime divides =
  let
    ge5 = NatP.m≤m+n 5 n
    genusZero = moonshineGenusZeroAtFivePlus n prime divides
    fixedIffGenus =
      Published.publishedFrobeniusFullyFixedIffFrickeGenusZero
        (5 + n) prime ge5
  in
  proj₂ fixedIffGenus genusZero

------------------------------------------------------------------------
-- Boundary: the direct forward theorem is genuinely asymmetric.  It uses
-- Moonshine for Monster -> genus zero and Deligne--Rapoport geometry for genus
-- zero -> Frobenius fixedness.  Duncan--Swisher belongs to the converse lane.
------------------------------------------------------------------------

record MonsterPrimeMoonshineFrobeniusForwardBoundary : Set where
  field
    forwardClassGroupMechanismIsMoonshine : Bool
    exactGammaGEqualsPrimeFrickeConsumed : Bool
    genusZeroTransportedFromGlobalMoonshine : Bool
    DeligneRapoportGeometryConsumed : Bool
    DuncanSwisherSupportImportedHere : Bool
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
  ; DuncanSwisherSupportImportedHere = false
  ; oldDuncanOnoSupportEquivalenceImported = false
  ; MonsterPrimeLaneEnumerationImported = false
  ; directMonsterToFrobeniusFixednessDerived = true
  }
