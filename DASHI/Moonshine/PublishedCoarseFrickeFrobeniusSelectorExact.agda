module DASHI.Moonshine.PublishedCoarseFrickeFrobeniusSelectorExact where

------------------------------------------------------------------------
-- Consume the ONE standard imported Deligne--Rapoport/Fricke geometry witness
-- and derive the selector locally.
--
-- Nothing in this file imports the finite Ogg control table or a Monster
-- prime label.  The theorem is purely geometric:
--
--   coarse supersingular Frobenius is pointwise fixed
--      iff
--   g(X_0^+(p)) = 0.
--
-- The imported authority supplies geometry; all logical reduction is the
-- theorem-producing chain already formalized in DASHI.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.DeligneRapoportFrickeStandardAuthority as Authority
import DASHI.Moonshine.FrickeSpecialFibreFrobeniusFixedSelectorExact as Selector
import DASHI.Moonshine.SupersingularFrickeSpecialFibreSelectorExact as Fricke

publishedGeometry :
  (p : Nat) → Prime p → 5 ≤ p → Selector.PrimeFrickeFrobeniusGeometry
publishedGeometry = Authority.publishedCoarseFrickeFrobeniusGeometry

PublishedCoarseFrobeniusFullyFixed :
  (p : Nat) → Prime p → 5 ≤ p → Set
PublishedCoarseFrobeniusFullyFixed p prime ge5 =
  Selector.GeometricallyFullyFixed (publishedGeometry p prime ge5)

publishedCoarseFrobeniusFullyFixedIffFrickeGenusZero :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  PublishedCoarseFrobeniusFullyFixed p prime ge5
  ↔
  Fricke.genericFrickeGenus
    (Selector.specialFibreRealization (publishedGeometry p prime ge5)) ≡ 0
publishedCoarseFrobeniusFullyFixedIffFrickeGenusZero p prime ge5 =
  Selector.frobeniusFullyFixedIffFrickeGenusZero
    (publishedGeometry p prime ge5)

publishedFrickeGenusEqualsCoarseFrobeniusPairDefect :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Fricke.genericFrickeGenus
    (Selector.specialFibreRealization (publishedGeometry p prime ge5))
  ≡
  Fricke.frobeniusPairDefect
    (Selector.specialFibreRealization (publishedGeometry p prime ge5))
publishedFrickeGenusEqualsCoarseFrobeniusPairDefect p prime ge5 =
  Fricke.frickeGenusEqualsFrobeniusPairDefect
    (Selector.specialFibreRealization (publishedGeometry p prime ge5))

record PublishedCoarseFrickeFrobeniusSelectorBoundary : Set where
  field
    publishedGeometryConsumed : Bool
    pairDefectEqualsFrickeGenusDerivedLocally : Bool
    allFixedIffFrickeGenusZeroDerivedLocally : Bool
    finiteOggTableUsed : Bool
    monsterPrimeSetUsed : Bool
    gamma2MarkedCarrierSubstitutedForCoarseCarrier : Bool

canonicalPublishedCoarseFrickeFrobeniusSelectorBoundary :
  PublishedCoarseFrickeFrobeniusSelectorBoundary
canonicalPublishedCoarseFrickeFrobeniusSelectorBoundary = record
  { publishedGeometryConsumed = true
  ; pairDefectEqualsFrickeGenusDerivedLocally = true
  ; allFixedIffFrickeGenusZeroDerivedLocally = true
  ; finiteOggTableUsed = false
  ; monsterPrimeSetUsed = false
  ; gamma2MarkedCarrierSubstitutedForCoarseCarrier = false
  }
