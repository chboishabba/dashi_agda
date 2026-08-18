module DASHI.Moonshine.MonsterPrimeMoonshineFrickeStandardAuthorityExact where

------------------------------------------------------------------------
-- STANDARD MONSTROUS-MOONSHINE AUTHORITY: MONSTER PRIME -> FRICKE GENUS ZERO
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- Richard E. Borcherds,
-- "Monstrous moonshine and monstrous Lie superalgebras",
-- Inventiones Mathematicae 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- SOURCE ROLE
--
-- Monstrous moonshine gives the conceptual FORWARD explanation of Ogg's prime
-- coincidence.  For every prime p dividing |M| there is a prime-order Monster
-- class whose moonshine group is the Fricke group Gamma_0(p)^+.  The associated
-- McKay--Thompson function is a Hauptmodul, so that group has genus zero.
--
-- This explains
--
--   p | |M|  ==>  g(X_0^+(p)) = 0.
--
-- It does NOT explain the converse, i.e. why there are no additional primes p
-- for which Gamma_0(p)^+ has genus zero.  Duncan--Ono explicitly emphasizes
-- this asymmetry.  The converse/classification remains a separate Ogg input in
-- the current repository.
--
-- DASHI DISCIPLINE
--
-- Reuse the existing MoonshineGroupDatum genus-zero field rather than creating
-- another moonshine-group or Hauptmodul datatype.  The only imported authority
-- below is the prime-divisor -> prime Fricke class/group identification.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MoonshineGroupBase as GroupBase
import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as Fricke

------------------------------------------------------------------------
-- A source-shaped prime-order moonshine witness.
------------------------------------------------------------------------

record PrimeMonsterFrickeMoonshineWitness
    (p : Nat) (prime : Prime p) : Set₁ where
  field
    MonsterClass : Set
    FuchsianGroup : Set

    actsOnUpperHalfPlane : FuchsianGroup → Set
    discrete : FuchsianGroup → Set
    finiteCovolume : FuchsianGroup → Set
    genusZero : FuchsianGroup → Set
    cuspData : FuchsianGroup → Set

    primeMonsterClass : MonsterClass
    primeFrickeGroup : FuchsianGroup

    moonshineDatum :
      GroupBase.MoonshineGroupDatum
        MonsterClass FuchsianGroup
        actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData

    datumUsesPrimeClass :
      GroupBase.MoonshineGroupDatum.monsterClass moonshineDatum
      ≡ primeMonsterClass

    -- The load-bearing Conway--Norton/Borcherds class-group identification:
    -- the moonshine group for the selected prime-order class is Gamma_0(p)^+.
    datumGroupIsPrimeFricke :
      GroupBase.MoonshineGroupDatum.group moonshineDatum
      ≡ primeFrickeGroup

    -- Same modular curve/genus carrier as the arbitrary-prime Fricke theorem.
    primeFrickeGroupGenusZeroMeansCurveGenusZero :
      genusZero primeFrickeGroup →
      Fricke.primeFrickeGenus p prime ≡ 0

open PrimeMonsterFrickeMoonshineWitness public

------------------------------------------------------------------------
-- Standard source boundary: for every actual prime divisor of the Monster
-- order, choose the corresponding prime-order Fricke moonshine class.
------------------------------------------------------------------------

postulate
  publishedPrimeMonsterFrickeMoonshineWitness :
    (p : Nat) → (prime : Prime p) →
    Monster.PrimeDividesMonsterOrder p →
    PrimeMonsterFrickeMoonshineWitness p prime

------------------------------------------------------------------------
-- Locally derive the forward genus-zero theorem from the existing genus-zero
-- field carried by MoonshineGroupDatum.
------------------------------------------------------------------------

moonshineWitnessPrimeFrickeGroupGenusZero :
  (p : Nat) → (prime : Prime p) →
  (W : PrimeMonsterFrickeMoonshineWitness p prime) →
  genusZero W (primeFrickeGroup W)
moonshineWitnessPrimeFrickeGroupGenusZero p prime W =
  subst
    (genusZero W)
    (datumGroupIsPrimeFricke W)
    (GroupBase.MoonshineGroupDatum.groupGenusZero (moonshineDatum W))

monsterPrimeImpliesFrickeGenusZeroViaMoonshine :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  Fricke.primeFrickeGenus p prime ≡ 0
monsterPrimeImpliesFrickeGenusZeroViaMoonshine p prime divides =
  let
    W = publishedPrimeMonsterFrickeMoonshineWitness p prime divides
  in
  primeFrickeGroupGenusZeroMeansCurveGenusZero W
    (moonshineWitnessPrimeFrickeGroupGenusZero p prime W)

------------------------------------------------------------------------
-- Boundary: this is a conceptual replacement for the FORWARD Ogg/Duncan--Ono
-- arrow only.  It intentionally does not assert the converse.
------------------------------------------------------------------------

record MonsterPrimeMoonshineFrickeAuthorityBoundary : Set where
  field
    ConwayNortonPrimeFrickeClassAuthorityImported : Bool
    BorcherdsGenusZeroMoonshineAuthorityImported : Bool
    existingMoonshineGroupDatumReused : Bool
    MonsterPrimeLaneEnumerationImported : Bool
    supersingularRationalityUsedInForwardProof : Bool
    forwardMonsterPrimeToFrickeGenusZeroDerived : Bool
    converseFrickeGenusZeroToMonsterPrimeDerivedHere : Bool
    absenceOfExtraOggPrimesExplainedHere : Bool

canonicalMonsterPrimeMoonshineFrickeAuthorityBoundary :
  MonsterPrimeMoonshineFrickeAuthorityBoundary
canonicalMonsterPrimeMoonshineFrickeAuthorityBoundary = record
  { ConwayNortonPrimeFrickeClassAuthorityImported = true
  ; BorcherdsGenusZeroMoonshineAuthorityImported = true
  ; existingMoonshineGroupDatumReused = true
  ; MonsterPrimeLaneEnumerationImported = false
  ; supersingularRationalityUsedInForwardProof = false
  ; forwardMonsterPrimeToFrickeGenusZeroDerived = true
  ; converseFrickeGenusZeroToMonsterPrimeDerivedHere = false
  ; absenceOfExtraOggPrimesExplainedHere = false
  }
