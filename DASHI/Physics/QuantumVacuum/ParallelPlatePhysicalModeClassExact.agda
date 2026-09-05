module DASHI.Physics.QuantumVacuum.ParallelPlatePhysicalModeClassExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.QuantumVacuum.PerfectConductorTETMGenerationCompletenessBidiExact as Legacy
import DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceAuthorityExact as Source

------------------------------------------------------------------------
-- PHYSICAL MODE CLASSIFICATION FOR TWO PERFECTLY CONDUCTING PARALLEL PLATES
--
-- MIT Chapter 13 identifies TM0 as the TEM mode and excludes TE n=0 because
-- it has zero amplitude.  Encode that directly:
--
--   TEM
--   TE_(n+1)
--   TM_(n+1)
--
-- Hence there is no constructor for TE0 or a separate physical TM0.
------------------------------------------------------------------------

data PlateModeClass : Set where
  TEM : PlateModeClass
  TE+ : Nat → PlateModeClass
  TM+ : Nat → PlateModeClass

longitudinalIndex : PlateModeClass → Nat
longitudinalIndex TEM = zero
longitudinalIndex (TE+ n) = suc n
longitudinalIndex (TM+ n) = suc n

IsTEM IsTE IsTM : PlateModeClass → Set
IsTEM TEM = ⊤
IsTEM (TE+ n) = ⊥
IsTEM (TM+ n) = ⊥

IsTE TEM = ⊥
IsTE (TE+ n) = ⊤
IsTE (TM+ n) = ⊥

IsTM TEM = ⊥
IsTM (TE+ n) = ⊥
IsTM (TM+ n) = ⊤

teIndexPositiveByConstruction :
  ∀ n → longitudinalIndex (TE+ n) ≡ suc n
teIndexPositiveByConstruction n = refl

tmHigherIndexPositiveByConstruction :
  ∀ n → longitudinalIndex (TM+ n) ≡ suc n
tmHigherIndexPositiveByConstruction n = refl

temIsOnlyZeroIndex :
  ∀ c → longitudinalIndex c ≡ zero → c ≡ TEM
temIsOnlyZeroIndex TEM proof = refl
temIsOnlyZeroIndex (TE+ n) ()
temIsOnlyZeroIndex (TM+ n) ()

teAndTmDisjoint : ∀ c → IsTE c → IsTM c → ⊥
teAndTmDisjoint TEM ()
teAndTmDisjoint (TE+ n) te ()
teAndTmDisjoint (TM+ n) ()

temAndTeDisjoint : ∀ c → IsTEM c → IsTE c → ⊥
temAndTeDisjoint TEM tem ()
temAndTeDisjoint (TE+ n) ()
temAndTeDisjoint (TM+ n) ()

temAndTmDisjoint : ∀ c → IsTEM c → IsTM c → ⊥
temAndTmDisjoint TEM tem ()
temAndTmDisjoint (TE+ n) ()
temAndTmDisjoint (TM+ n) ()

------------------------------------------------------------------------
-- Legacy adapter.
--
-- Old DASHI surfaces have only TE/TM plus a zero-sector predicate.  Preserve
-- compatibility by representing TEM as the old TM-zero branch, but keep the
-- semantic distinction explicit and one-way.
------------------------------------------------------------------------

legacyPolarisation : PlateModeClass → Legacy.Polarisation
legacyPolarisation TEM = Legacy.TM
legacyPolarisation (TE+ n) = Legacy.TE
legacyPolarisation (TM+ n) = Legacy.TM

LegacyZeroSector : PlateModeClass → Set
LegacyZeroSector TEM = ⊤
LegacyZeroSector (TE+ n) = ⊥
LegacyZeroSector (TM+ n) = ⊥

legacyZeroSectorExactlyTEM :
  ∀ c → LegacyZeroSector c → IsTEM c
legacyZeroSectorExactlyTEM TEM proof = tt
legacyZeroSectorExactlyTEM (TE+ n) ()
legacyZeroSectorExactlyTEM (TM+ n) ()

------------------------------------------------------------------------
-- Source receipt records why this classification is physically chosen.
------------------------------------------------------------------------

record TEMTETMClassificationSourceReceipt : Set where
  field
    teZeroExcluded :
      Source.teZeroExcludedBecauseZeroAmplitude
        Source.canonicalParallelPlateTETMModeExpansionAuthority
    tmZeroIsTEM :
      Source.tmZeroIdentifiedAsTEM
        Source.canonicalParallelPlateTETMModeExpansionAuthority
    higherModesPositiveIndex :
      Source.positiveIndexHigherModes
        Source.canonicalParallelPlateTETMModeExpansionAuthority
    reading : String

open TEMTETMClassificationSourceReceipt public

canonicalClassificationSourceReceipt : TEMTETMClassificationSourceReceipt
canonicalClassificationSourceReceipt = record
  { teZeroExcluded = tt
  ; tmZeroIsTEM = tt
  ; higherModesPositiveIndex = tt
  ; reading =
      "MIT §13.2: TE n=0 is zero-amplitude and excluded; TM0 is the TEM mode; higher TE/TM modes have positive integer index."
  }

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PhysicalTEZero : Set where
data PhysicalTMZeroDistinctFromTEM : Set where

data LegacyTMTagMeansPhysicalTMInZeroSector : Set where

noPhysicalTEZero : PhysicalTEZero → ⊥
noPhysicalTEZero ()

noSeparatePhysicalTMZero : PhysicalTMZeroDistinctFromTEM → ⊥
noSeparatePhysicalTMZero ()

legacyTagDoesNotEraseTEMSemantics :
  LegacyTMTagMeansPhysicalTMInZeroSector → ⊥
legacyTagDoesNotEraseTEMSemantics ()

record Status : Set where
  field
    temConstructorOwned : Bool
    teZeroUnrepresentable : Bool
    tmZeroCanonicalizedAsTEM : Bool
    higherTEPositiveByConstruction : Bool
    higherTMPositiveByConstruction : Bool
    classDisjointnessOwned : Bool

    temConstructorOwnedIsTrue : temConstructorOwned ≡ true
    teZeroUnrepresentableIsTrue : teZeroUnrepresentable ≡ true
    tmZeroCanonicalizedAsTEMIsTrue : tmZeroCanonicalizedAsTEM ≡ true
    higherTEPositiveByConstructionIsTrue : higherTEPositiveByConstruction ≡ true
    higherTMPositiveByConstructionIsTrue : higherTMPositiveByConstruction ≡ true
    classDisjointnessOwnedIsTrue : classDisjointnessOwned ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { temConstructorOwned = true
  ; teZeroUnrepresentable = true
  ; tmZeroCanonicalizedAsTEM = true
  ; higherTEPositiveByConstruction = true
  ; higherTMPositiveByConstruction = true
  ; classDisjointnessOwned = true
  ; temConstructorOwnedIsTrue = refl
  ; teZeroUnrepresentableIsTrue = refl
  ; tmZeroCanonicalizedAsTEMIsTrue = refl
  ; higherTEPositiveByConstructionIsTrue = refl
  ; higherTMPositiveByConstructionIsTrue = refl
  ; classDisjointnessOwnedIsTrue = refl
  }
