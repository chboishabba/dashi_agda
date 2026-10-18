module DASHI.Moonshine.OggSSPSmallCharacteristicIgusaOsculationHasseCutsetExact where

------------------------------------------------------------------------
-- IGUSA HASSE / OSCULATION CUTSET
--
-- EXTERNAL SOURCE
--
-- Liedtke--Schroeer, "The Neron model over the Igusa curves" (JNT 2010):
--
--   * for rational p-division sections the osculation filtration is closely
--     controlled by the Hasse invariant / Frobenius-Verschiebung structure;
--   * their small-characteristic analysis treats p=2 and p=3 separately,
--     precisely because wild ramification and stacky phenomena intervene;
--   * iterated Frobenius pullback produces examples with arbitrary osculation
--     number n.
--
-- CONSEQUENCE
--
-- Osculation/Hasse depth is a genuine source-native derived LOCAL coordinate
-- on bad-level Igusa geometry, stronger than raw ramification degree alone.
--
-- But because arbitrary osculation depth can occur under Frobenius pullback,
-- the bare osculation number cannot canonically equal the fixed Monster gaps
-- 10 and 2.  A valid fourth-term theorem must combine it with the specific
-- bad-level object, branch/inertia marking, Fricke/Hauptmodul observable and
-- q-expansion/divisor valuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallCharacteristicBadLevelIgusaCorrectionCutsetExact as Igusa
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

liedtkeSchroeer : Source.AttributedSource
liedtkeSchroeer =
  Source.mkDOISource
    "Christian Liedtke and Stefan Schroeer"
    "The Neron model over the Igusa curves"
    "Journal of Number Theory 130(10), 2157-2197"
    "2010"
    "10.1016/j.jnt.2010.03.016"
    "https://doi.org/10.1016/j.jnt.2010.03.016"
    Source.academicArticleSource
    "source for Hasse-invariant/osculation control of rational p-division sections, Frobenius-pullback effects, and dedicated characteristic-2/3 Igusa geometry; not a Monster-exponent or Hauptmodul-correction theorem"
    Source.publicAttribution

igusaOsculationSourceAtlas : Source.AttributedSourceAtlas
igusaOsculationSourceAtlas =
  Source.mkSourceAtlas
    "small-characteristic Igusa Hasse/osculation source atlas"
    "DASHI.Moonshine.OggSSPSmallCharacteristicIgusaOsculationHasseCutsetExact"
    (liedtkeSchroeer ∷ [])
    "external source supplies the bad-level local geometric coordinate; all Monster/Hauptmodul transfer claims remain DASHI obligations"

------------------------------------------------------------------------
-- 1. Source-native local-coordinate schema.
------------------------------------------------------------------------

record HasseOsculationDatum : Set where
  constructor hasse-osculation-datum
  field
    hasseVanishingDepth : Nat
    osculationNumber : Nat
    frobeniusPullbackDepth : Nat

open HasseOsculationDatum public

------------------------------------------------------------------------
-- 2. Arbitrary osculation depth prevents a canonical raw 10/2 rule.
------------------------------------------------------------------------

datumAtOsculation :
  Nat ->
  HasseOsculationDatum
datumAtOsculation n =
  hasse-osculation-datum n n n

datumAtOsculationCorrect :
  (n : Nat) ->
  osculationNumber (datumAtOsculation n) ≡ n
datumAtOsculationCorrect n = refl

p2RawOsculationCandidate : HasseOsculationDatum
p2RawOsculationCandidate =
  datumAtOsculation 10

p3RawOsculationCandidate : HasseOsculationDatum
p3RawOsculationCandidate =
  datumAtOsculation 2

alternateP2Osculation : HasseOsculationDatum
alternateP2Osculation =
  datumAtOsculation 1

alternateP3Osculation : HasseOsculationDatum
alternateP3Osculation =
  datumAtOsculation 3

p2RawOsculationNotForcedToTen :
  osculationNumber alternateP2Osculation ≡ 10 -> ⊥
p2RawOsculationNotForcedToTen ()

p3RawOsculationNotForcedToTwo :
  osculationNumber alternateP3Osculation ≡ 2 -> ⊥
p3RawOsculationNotForcedToTwo ()

data RawOsculationCanonicallyEqualsP2Gap : Set where
data RawOsculationCanonicallyEqualsP3Gap : Set where

rawOsculationDoesNotCanonicallyEqualP2Gap :
  RawOsculationCanonicallyEqualsP2Gap -> ⊥
rawOsculationDoesNotCanonicallyEqualP2Gap ()

rawOsculationDoesNotCanonicallyEqualP3Gap :
  RawOsculationCanonicallyEqualsP3Gap -> ⊥
rawOsculationDoesNotCanonicallyEqualP3Gap ()

------------------------------------------------------------------------
-- 3. Refined bad-level authority: osculation is input, not answer.
------------------------------------------------------------------------

record HasseOsculationBadLevelAuthority
    (p : Igusa.BadLevelPrime) : Set₁ where
  field
    igusaAuthority :
      Igusa.BadLevelIgusaCorrectionAuthority p

    localHasseOsculationDatum :
      HasseOsculationDatum

    datumComesFromTheSameBadLevelObject :
      Bool
    datumComesFromTheSameBadLevelObjectIsTrue :
      datumComesFromTheSameBadLevelObject ≡ true

    frobeniusPullbackCompatibilityOwned :
      Bool
    frobeniusPullbackCompatibilityOwnedIsTrue :
      frobeniusPullbackCompatibilityOwned ≡ true

    hasseRootCompatibilityOwned :
      Bool
    hasseRootCompatibilityOwnedIsTrue :
      hasseRootCompatibilityOwned ≡ true

    correctedDivisorUsesOsculationDatum :
      Bool
    correctedDivisorUsesOsculationDatumIsTrue :
      correctedDivisorUsesOsculationDatum ≡ true

    analyticFrickeCompatibilityOwned :
      Bool
    analyticFrickeCompatibilityOwnedIsTrue :
      analyticFrickeCompatibilityOwned ≡ true

open HasseOsculationBadLevelAuthority public

------------------------------------------------------------------------
-- 4. Firewalls.
------------------------------------------------------------------------

data HasseOsculationSourceProvesMonsterGap : Set where
data ArbitraryOsculationCreatesPreferredTenTwo : Set where
data LocalOsculationAloneCreatesHauptmodulValuation : Set where

sourceDoesNotProveMonsterGap :
  HasseOsculationSourceProvesMonsterGap -> ⊥
sourceDoesNotProveMonsterGap ()

arbitraryOsculationDoesNotCreatePreferredTenTwo :
  ArbitraryOsculationCreatesPreferredTenTwo -> ⊥
arbitraryOsculationDoesNotCreatePreferredTenTwo ()

localOsculationAloneDoesNotCreateHauptmodulValuation :
  LocalOsculationAloneCreatesHauptmodulValuation -> ⊥
localOsculationAloneDoesNotCreateHauptmodulValuation ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record IgusaOsculationHasseCutsetBoundary : Set where
  constructor igusa-osculation-hasse-cutset-boundary
  field
    liedtkeSchroeerSourceAttached : Bool
    hasseOsculationRelationSourced : Bool
    characteristicTwoThreeSpecificGeometrySourced : Bool
    arbitraryFrobeniusOsculationDepthSourced : Bool
    osculationRetainedAsBadLevelLocalCoordinate : Bool
    rawOsculationPromotedToP2Gap : Bool
    rawOsculationPromotedToP3Gap : Bool
    refinedBadLevelAuthoritySpecified : Bool
    attributionFirewallPreserved : Bool

canonicalIgusaOsculationHasseCutsetBoundary :
  IgusaOsculationHasseCutsetBoundary
canonicalIgusaOsculationHasseCutsetBoundary =
  igusa-osculation-hasse-cutset-boundary
    true true true true true false false true true
