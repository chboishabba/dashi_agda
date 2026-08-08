module DASHI.Physics.Closure.NSTriadKNDependentTaxOwnerPartitionRound28Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 26 stored one owner field in every taxable atom and proved numerical
-- recomposition.  This file strengthens that bookkeeping into a dependent
-- partition: every atom is canonically tagged by the fibre over its unique
-- owner, erasing tags recovers the original atom and list exactly, and both
-- signed and taxable finite totals are unchanged by tagging.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax

OwnedTaxAtom : Tax.TaxOwner → Set
OwnedTaxAtom selected =
  Σ Tax.TaxAtom (λ atom → Tax.owner atom ≡ selected)

TaggedTaxAtom : Set
TaggedTaxAtom = Σ Tax.TaxOwner OwnedTaxAtom

tagTaxAtom : Tax.TaxAtom → TaggedTaxAtom
tagTaxAtom atom = Tax.owner atom , (atom , refl)

eraseTaggedTaxAtom : TaggedTaxAtom → Tax.TaxAtom
eraseTaggedTaxAtom (selected , (atom , ownership)) = atom

eraseTagTaxAtomExact :
  (atom : Tax.TaxAtom) →
  eraseTaggedTaxAtom (tagTaxAtom atom) ≡ atom
eraseTagTaxAtomExact atom = refl

tagTaxAtoms : List Tax.TaxAtom → List TaggedTaxAtom
tagTaxAtoms [] = []
tagTaxAtoms (atom ∷ rest) = tagTaxAtom atom ∷ tagTaxAtoms rest

eraseTaggedTaxAtoms : List TaggedTaxAtom → List Tax.TaxAtom
eraseTaggedTaxAtoms [] = []
eraseTaggedTaxAtoms (atom ∷ rest) =
  eraseTaggedTaxAtom atom ∷ eraseTaggedTaxAtoms rest

dependentPartitionListRoundtrip :
  (atoms : List Tax.TaxAtom) →
  eraseTaggedTaxAtoms (tagTaxAtoms atoms) ≡ atoms
dependentPartitionListRoundtrip [] = refl
dependentPartitionListRoundtrip (atom ∷ rest)
  rewrite dependentPartitionListRoundtrip rest = refl

signedTaggedTotal : List TaggedTaxAtom → ℚ
signedTaggedTotal [] = 0ℚ
signedTaggedTotal (tagged ∷ rest) =
  Tax.signedValue (eraseTaggedTaxAtom tagged)
  + signedTaggedTotal rest

taxableTaggedTotal : List TaggedTaxAtom → ℚ
taxableTaggedTotal [] = 0ℚ
taxableTaggedTotal (tagged ∷ rest) =
  Tax.taxableValue (eraseTaggedTaxAtom tagged)
  + taxableTaggedTotal rest

signedAtomTotal : List Tax.TaxAtom → ℚ
signedAtomTotal [] = 0ℚ
signedAtomTotal (atom ∷ rest) =
  Tax.signedValue atom + signedAtomTotal rest

signedTotalPreservedByDependentPartition :
  (atoms : List Tax.TaxAtom) →
  signedTaggedTotal (tagTaxAtoms atoms) ≡ signedAtomTotal atoms
signedTotalPreservedByDependentPartition [] = refl
signedTotalPreservedByDependentPartition (atom ∷ rest)
  rewrite signedTotalPreservedByDependentPartition rest = refl

taxableTotalPreservedByDependentPartition :
  (atoms : List Tax.TaxAtom) →
  taxableTaggedTotal (tagTaxAtoms atoms) ≡ Tax.totalTax atoms
taxableTotalPreservedByDependentPartition [] = refl
taxableTotalPreservedByDependentPartition (atom ∷ rest)
  rewrite taxableTotalPreservedByDependentPartition rest = refl

record UniqueDependentOwner (atom : Tax.TaxAtom) : Set where
  constructor unique-dependent-owner
  field
    selectedOwner : Tax.TaxOwner
    membership : Tax.owner atom ≡ selectedOwner
    uniqueness : ∀ other →
      Tax.owner atom ≡ other → selectedOwner ≡ other

open UniqueDependentOwner public

canonicalUniqueDependentOwner :
  (atom : Tax.TaxAtom) → UniqueDependentOwner atom
canonicalUniqueDependentOwner atom =
  unique-dependent-owner
    (Tax.owner atom)
    refl
    (λ other proof → proof)

ownedFibreMembershipUnique :
  ∀ {atom first second} →
  Tax.owner atom ≡ first →
  Tax.owner atom ≡ second →
  first ≡ second
ownedFibreMembershipUnique first second = trans first second
  where
  trans : ∀ {A : Set} {x y z : A} → x ≡ y → x ≡ z → y ≡ z
  trans refl refl = refl

dependentTaxOwnerPartitionClosed : Bool
dependentTaxOwnerPartitionClosed = true

listPartitionRoundtripClosed : Bool
listPartitionRoundtripClosed = true

signedAndTaxableTotalsPreserved : Bool
signedAndTaxableTotalsPreserved = true

dependentTaxOwnerPartitionClosedIsTrue :
  dependentTaxOwnerPartitionClosed ≡ true
dependentTaxOwnerPartitionClosedIsTrue = refl
