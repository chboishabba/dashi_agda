module DASHI.Moonshine.P11Level44HeckeAlignmentNonUniquenessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Kimball Martin,
-- "The basis problem revisited", Transactions of the American Mathematical
-- Society 373 (2020), 4523--4559. DOI: 10.1090/tran/8077.
-- Martin emphasizes that the classical Jacquet--Langlands map on oldspaces is
-- non-canonical while preserving the unramified Hecke action.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Good-prime Hecke operators act on the d=1,2,4 degeneracy copies of one
-- level-11 eigenform with the same eigenvalue.
--
-- DASHI CONTRIBUTION
--
-- Turn that non-canonicity into an exact finite theorem on the repository's
-- already-constructed Old3 multiplicity module.
--
-- If a Hecke operator acts as a scalar lambda on Old3, then EVERY map commuting
-- with integral scalar multiplication is automatically a Hecke intertwiner.
-- In particular both
--
--   identity : Old3 -> Old3
--   oldR     : Old3 -> Old3
--
-- intertwine the entire scalar Hecke family, but they are distinct maps.
--
-- Therefore no amount of away-from-2 scalar Hecke eigenvalue data can select a
-- canonical identification between the principal-level-2 marked realization
-- and the Gamma_0(4) degeneracy realization.  The missing comparison is
-- genuinely LOCAL AT 2 (or must use equivalent extra local structure).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Old

------------------------------------------------------------------------
-- Scalar Hecke action on the multiplicity space.
------------------------------------------------------------------------

scalarHecke : ℤ → Old.Old3 → Old.Old3
scalarHecke = Old.scaleOld3

record ScalarCompatibleOld3Map : Set where
  field
    mapOld3 : Old.Old3 → Old.Old3
    scalarCompatible :
      (k : ℤ) → (v : Old.Old3) →
      mapOld3 (Old.scaleOld3 k v)
      ≡ Old.scaleOld3 k (mapOld3 v)
open ScalarCompatibleOld3Map public

scalarHeckeIntertwinesEveryCompatibleMap :
  (M : ScalarCompatibleOld3Map) →
  (lambda : ℤ) → (v : Old.Old3) →
  mapOld3 M (scalarHecke lambda v)
  ≡ scalarHecke lambda (mapOld3 M v)
scalarHeckeIntertwinesEveryCompatibleMap M lambda v =
  scalarCompatible M lambda v

------------------------------------------------------------------------
-- Two distinct compatible maps: identity and the genuine three-cycle on the
-- multiplicity coordinates.
------------------------------------------------------------------------

identityOld3Map : ScalarCompatibleOld3Map
identityOld3Map = record
  { mapOld3 = λ v → v
  ; scalarCompatible = λ k v → refl
  }

rotationOld3Map : ScalarCompatibleOld3Map
rotationOld3Map = record
  { mapOld3 = Old.oldR
  ; scalarCompatible = λ k v → rotationCommutesWithScalar k v
  }
  where
  rotationCommutesWithScalar :
    (k : ℤ) → (v : Old.Old3) →
    Old.oldR (Old.scaleOld3 k v)
    ≡ Old.scaleOld3 k (Old.oldR v)
  rotationCommutesWithScalar k (Old.old3 a b c) = refl

identityHeckeIntertwiner :
  (lambda : ℤ) → (v : Old.Old3) →
  mapOld3 identityOld3Map (scalarHecke lambda v)
  ≡ scalarHecke lambda (mapOld3 identityOld3Map v)
identityHeckeIntertwiner =
  scalarHeckeIntertwinesEveryCompatibleMap identityOld3Map

rotationHeckeIntertwiner :
  (lambda : ℤ) → (v : Old.Old3) →
  mapOld3 rotationOld3Map (scalarHecke lambda v)
  ≡ scalarHecke lambda (mapOld3 rotationOld3Map v)
rotationHeckeIntertwiner =
  scalarHeckeIntertwinesEveryCompatibleMap rotationOld3Map

------------------------------------------------------------------------
-- The maps are genuinely distinct.
------------------------------------------------------------------------

data Impossible : Set where

identityBasis1NotRotationBasis1 :
  mapOld3 identityOld3Map Old.oldBasis1
  ≡ mapOld3 rotationOld3Map Old.oldBasis1 → Impossible
identityBasis1NotRotationBasis1 ()

record HeckeAlignmentCollision : Set where
  field
    first second : ScalarCompatibleOld3Map
    witness : Old.Old3
    distinctAtWitness :
      mapOld3 first witness ≡ mapOld3 second witness → Impossible
    bothIntertwineEveryScalarHecke :
      (lambda : ℤ) → (v : Old.Old3) →
      (mapOld3 first (scalarHecke lambda v)
        ≡ scalarHecke lambda (mapOld3 first v))
      ×
      (mapOld3 second (scalarHecke lambda v)
        ≡ scalarHecke lambda (mapOld3 second v))

allGoodPrimeHeckeAlignmentCollision : HeckeAlignmentCollision
allGoodPrimeHeckeAlignmentCollision = record
  { first = identityOld3Map
  ; second = rotationOld3Map
  ; witness = Old.oldBasis1
  ; distinctAtWitness = identityBasis1NotRotationBasis1
  ; bothIntertwineEveryScalarHecke = λ lambda v →
      identityHeckeIntertwiner lambda v , rotationHeckeIntertwiner lambda v
  }

------------------------------------------------------------------------
-- Corrected frontier boundary.
------------------------------------------------------------------------

record P11Level44HeckeAlignmentNonUniquenessBoundary : Set where
  field
    scalarHeckeFamilyOnMultiplicitySpaceConstructed : Bool
    everyScalarCompatibleMapIntertwines : Bool
    twoDistinctAllHeckeIntertwinersConstructed : Bool
    allGoodPrimeHeckeDeterminesLocalAlignment : Bool
    extraTwoAdicLocalStructureRequired : Bool

canonicalP11Level44HeckeAlignmentNonUniquenessBoundary :
  P11Level44HeckeAlignmentNonUniquenessBoundary
canonicalP11Level44HeckeAlignmentNonUniquenessBoundary = record
  { scalarHeckeFamilyOnMultiplicitySpaceConstructed = true
  ; everyScalarCompatibleMapIntertwines = true
  ; twoDistinctAllHeckeIntertwinersConstructed = true
  ; allGoodPrimeHeckeDeterminesLocalAlignment = false
  ; extraTwoAdicLocalStructureRequired = true
  }
