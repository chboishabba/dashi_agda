module DASHI.Moonshine.MonsterPrimeMoonshineFrickeFactoredAuthorityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- DASHI CONTRIBUTION
--
-- Factor the conceptual Monster-prime -> Fricke-genus-zero mechanism into its
-- two genuinely different authority roles.
--
-- GLOBAL MOONSHINE AUTHORITY (imported ONCE):
--   every Monster class has its Conway--Norton/Borcherds moonshine group,
--   and that group is genus zero.
--
-- PRIME-SPECIFIC CLASSIFICATION AUTHORITY:
--   for p dividing |M|, select a Monster class of order p whose moonshine group
--   is EXACTLY the prime Fricke group Gamma_0(p)^+.
--
-- The second statement is the only p-indexed classification input.  Genus zero
-- is then transported from the global Moonshine theorem through the exact group
-- identification; it is not imported again for each prime.
--
-- This sharpens MonsterPrimeMoonshineFrickeStandardAuthorityExact without
-- changing its mathematical conclusion.  The equality of groups remains
-- load-bearing: shared genus zero or shared prime label is not enough.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import DASHI.Core.Prelude
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MoonshineGroupBase as GroupBase
import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as Fricke

------------------------------------------------------------------------
-- One global Conway--Norton/Borcherds universe.
------------------------------------------------------------------------

record ConwayNortonGenusZeroUniverse : Setω where
  field
    MonsterClass : Set
    FuchsianGroup : Set

    actsOnUpperHalfPlane : FuchsianGroup → Set
    discrete : FuchsianGroup → Set
    finiteCovolume : FuchsianGroup → Set
    genusZero : FuchsianGroup → Set
    cuspData : FuchsianGroup → Set

    classOrder : MonsterClass → Nat

    moonshineDatumForClass :
      MonsterClass →
      GroupBase.MoonshineGroupDatum
        MonsterClass FuchsianGroup
        actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData

    datumClassExact :
      (g : MonsterClass) →
      GroupBase.MoonshineGroupDatum.monsterClass (moonshineDatumForClass g)
      ≡ g

    -- One concrete prime-Fricke group family in the SAME Fuchsian-group
    -- carrier as the Conway--Norton class groups.
    primeFrickeGroup : Nat → FuchsianGroup

    -- Same genus coordinate as the arbitrary-prime Fricke theorem.
    primeFrickeGroupGenusBridge :
      (p : Nat) → (prime : Prime p) →
      genusZero (primeFrickeGroup p) →
      Fricke.primeFrickeGenus p prime ≡ 0

open ConwayNortonGenusZeroUniverse public

postulate
  publishedConwayNortonGenusZeroUniverse : ConwayNortonGenusZeroUniverse

------------------------------------------------------------------------
-- The ONLY p-specific source input: choose the appropriate prime-order class
-- and identify its class Moonshine group with Gamma_0(p)^+.
------------------------------------------------------------------------

record PrimeFrickeClassSelection
    (U : ConwayNortonGenusZeroUniverse)
    (p : Nat) : Set where
  field
    selectedClass : MonsterClass U
    selectedClassHasOrderP : classOrder U selectedClass ≡ p

    classGroupIsPrimeFricke :
      GroupBase.MoonshineGroupDatum.classMoonshineGroup
        (moonshineDatumForClass U selectedClass)
      ≡ primeFrickeGroup U p

open PrimeFrickeClassSelection public

postulate
  publishedPrimeFrickeClassSelection :
    (p : Nat) → (prime : Prime p) →
    Monster.PrimeDividesMonsterOrder p →
    PrimeFrickeClassSelection publishedConwayNortonGenusZeroUniverse p

------------------------------------------------------------------------
-- Global Moonshine supplies genus zero for the selected class group.
------------------------------------------------------------------------

selectedClassGroupGenusZero :
  (U : ConwayNortonGenusZeroUniverse) →
  (p : Nat) →
  (S : PrimeFrickeClassSelection U p) →
  genusZero U
    (GroupBase.MoonshineGroupDatum.classMoonshineGroup
      (moonshineDatumForClass U (selectedClass S)))
selectedClassGroupGenusZero U p S =
  let
    D = moonshineDatumForClass U (selectedClass S)
  in
  subst
    (genusZero U)
    (sym (GroupBase.MoonshineGroupDatum.groupIdentification D))
    (GroupBase.MoonshineGroupDatum.groupGenusZero D)

selectedPrimeFrickeGroupGenusZero :
  (U : ConwayNortonGenusZeroUniverse) →
  (p : Nat) →
  (S : PrimeFrickeClassSelection U p) →
  genusZero U (primeFrickeGroup U p)
selectedPrimeFrickeGroupGenusZero U p S =
  subst
    (genusZero U)
    (classGroupIsPrimeFricke S)
    (selectedClassGroupGenusZero U p S)

------------------------------------------------------------------------
-- Conceptual forward theorem with the authority factorization visible.
------------------------------------------------------------------------

monsterPrimeImpliesFrickeGenusZeroViaFactoredMoonshine :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  Fricke.primeFrickeGenus p prime ≡ 0
monsterPrimeImpliesFrickeGenusZeroViaFactoredMoonshine p prime divides =
  let
    U = publishedConwayNortonGenusZeroUniverse
    S = publishedPrimeFrickeClassSelection p prime divides
  in
  primeFrickeGroupGenusBridge U p prime
    (selectedPrimeFrickeGroupGenusZero U p S)

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record MonsterPrimeMoonshineFrickeFactoredBoundary : Set where
  field
    globalConwayNortonGenusZeroAuthorityImportedOnce : Bool
    primeSpecificClassOrderSelectionImported : Bool
    exactClassGroupEqualsPrimeFrickeImported : Bool
    perPrimeGenusZeroImportedSeparately : Bool
    supersingularRationalityUsedInForwardProof : Bool
    MonsterPrimeLaneEnumerationImported : Bool
    forwardMonsterPrimeToFrickeGenusZeroDerived : Bool
    groupEqualityReplacedBySharedGenusOnly : Bool

canonicalMonsterPrimeMoonshineFrickeFactoredBoundary :
  MonsterPrimeMoonshineFrickeFactoredBoundary
canonicalMonsterPrimeMoonshineFrickeFactoredBoundary = record
  { globalConwayNortonGenusZeroAuthorityImportedOnce = true
  ; primeSpecificClassOrderSelectionImported = true
  ; exactClassGroupEqualsPrimeFrickeImported = true
  ; perPrimeGenusZeroImportedSeparately = false
  ; supersingularRationalityUsedInForwardProof = false
  ; MonsterPrimeLaneEnumerationImported = false
  ; forwardMonsterPrimeToFrickeGenusZeroDerived = true
  ; groupEqualityReplacedBySharedGenusOnly = false
  }
