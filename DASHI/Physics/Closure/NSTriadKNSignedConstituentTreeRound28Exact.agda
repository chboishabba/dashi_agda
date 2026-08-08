module DASHI.Physics.Closure.NSTriadKNSignedConstituentTreeRound28Exact where

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
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- DASHI CONTRIBUTION
--
-- Retain the constituent tree
--
--   physical source -> signed contribution -> compatible owner -> grouped tax
--
-- before introducing a nonnegative majorant.  HH constituents may be assigned
-- only to the good or bad HH owners; LH, HL, CC and Com are forced to their
-- corresponding owners; kernel, tail and cutoff boundary sources are likewise
-- fixed.  A TaxAtom can be constructed only from an owner-homogeneous signed
-- group after a single grouped upper bound has been supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteParaproductRangePartitionExact as Range
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax

data BoundaryStatus : Set where
  lowerCut upperCut : BoundaryStatus

data ExtendedSource : Set where
  physicalSource : Support.FiveSourceCell → ExtendedSource
  kernelSource : ExtendedSource
  tailSource : ExtendedSource
  boundarySource : BoundaryStatus → ExtendedSource

CompatibleOwner : ExtendedSource → Tax.TaxOwner → Set
CompatibleOwner (physicalSource cell) selected
  with Support.fiveSourceClass cell
... | Range.LH = selected ≡ Tax.LH
... | Range.HL = selected ≡ Tax.HL
... | Range.HH =
      (selected ≡ Tax.HH-good) ⊎ (selected ≡ Tax.HH-bad)
... | Range.CC = selected ≡ Tax.CC
... | Range.Com = selected ≡ Tax.Com
CompatibleOwner kernelSource selected = selected ≡ Tax.kernel
CompatibleOwner tailSource selected = selected ≡ Tax.tail
CompatibleOwner (boundarySource status) selected = selected ≡ Tax.boundary

record SignedConstituent : Set where
  constructor signed-constituent
  field
    source : ExtendedSource
    assignedOwner : Tax.TaxOwner
    ownerCompatible : CompatibleOwner source assignedOwner
    signedContribution : ℚ

open SignedConstituent public

signedConstituentTotal : List SignedConstituent → ℚ
signedConstituentTotal [] = 0ℚ
signedConstituentTotal (cell ∷ rest) =
  signedContribution cell + signedConstituentTotal rest

OwnedSignedConstituent : Tax.TaxOwner → Set
OwnedSignedConstituent selected =
  Σ SignedConstituent
    (λ constituent → assignedOwner constituent ≡ selected)

ownedSignedValue :
  ∀ {selected} → OwnedSignedConstituent selected → ℚ
ownedSignedValue (constituent , ownership) =
  signedContribution constituent

ownedSignedTotal :
  ∀ {selected} → List (OwnedSignedConstituent selected) → ℚ
ownedSignedTotal [] = 0ℚ
ownedSignedTotal (constituent ∷ rest) =
  ownedSignedValue constituent + ownedSignedTotal rest

record DelayedPositiveGroup (selected : Tax.TaxOwner) : Set where
  constructor delayed-positive-group
  field
    constituents : List (OwnedSignedConstituent selected)
    groupedSignedValue : ℚ
    groupedSignedMeaning :
      groupedSignedValue ≡ ownedSignedTotal constituents
    groupedTaxableValue : ℚ
    groupedSignedBelowTax : groupedSignedValue ≤ groupedTaxableValue
    groupedTaxNonnegative : 0ℚ ≤ groupedTaxableValue

open DelayedPositiveGroup public

groupToTaxAtom :
  ∀ {selected} → DelayedPositiveGroup selected → Tax.TaxAtom
groupToTaxAtom {selected} group =
  Tax.tax-atom
    selected
    (groupedSignedValue group)
    (groupedTaxableValue group)
    (groupedSignedBelowTax group)
    (groupedTaxNonnegative group)

groupTaxOwnerExact :
  ∀ {selected} (group : DelayedPositiveGroup selected) →
  Tax.owner (groupToTaxAtom group) ≡ selected
groupTaxOwnerExact group = refl

groupTaxSignedValueExact :
  ∀ {selected} (group : DelayedPositiveGroup selected) →
  Tax.signedValue (groupToTaxAtom group)
  ≡ groupedSignedValue group
groupTaxSignedValueExact group = refl

groupTaxableValueExact :
  ∀ {selected} (group : DelayedPositiveGroup selected) →
  Tax.taxableValue (groupToTaxAtom group)
  ≡ groupedTaxableValue group
groupTaxableValueExact group = refl

lhCompatibilityCanonical :
  (cell : Support.FiveSourceCell) →
  Support.fiveSourceClass cell ≡ Range.LH →
  CompatibleOwner (physicalSource cell) Tax.LH
lhCompatibilityCanonical cell proof rewrite proof = refl

hlCompatibilityCanonical :
  (cell : Support.FiveSourceCell) →
  Support.fiveSourceClass cell ≡ Range.HL →
  CompatibleOwner (physicalSource cell) Tax.HL
hlCompatibilityCanonical cell proof rewrite proof = refl

ccCompatibilityCanonical :
  (cell : Support.FiveSourceCell) →
  Support.fiveSourceClass cell ≡ Range.CC →
  CompatibleOwner (physicalSource cell) Tax.CC
ccCompatibilityCanonical cell proof rewrite proof = refl

comCompatibilityCanonical :
  (cell : Support.FiveSourceCell) →
  Support.fiveSourceClass cell ≡ Range.Com →
  CompatibleOwner (physicalSource cell) Tax.Com
comCompatibilityCanonical cell proof rewrite proof = refl

hhGoodCompatibilityCanonical :
  (cell : Support.FiveSourceCell) →
  Support.fiveSourceClass cell ≡ Range.HH →
  CompatibleOwner (physicalSource cell) Tax.HH-good
hhGoodCompatibilityCanonical cell proof rewrite proof = inj₁ refl

hhBadCompatibilityCanonical :
  (cell : Support.FiveSourceCell) →
  Support.fiveSourceClass cell ≡ Range.HH →
  CompatibleOwner (physicalSource cell) Tax.HH-bad
hhBadCompatibilityCanonical cell proof rewrite proof = inj₂ refl

signedConstituentTreeClosed : Bool
signedConstituentTreeClosed = true

delayedPositiveGroupingClosed : Bool
delayedPositiveGroupingClosed = true

physicalTimeDependentConstituentsInstantiated : Bool
physicalTimeDependentConstituentsInstantiated = false

signedConstituentTreeClosedIsTrue : signedConstituentTreeClosed ≡ true
signedConstituentTreeClosedIsTrue = refl

physicalTimeDependentConstituentsInstantiatedIsFalse :
  physicalTimeDependentConstituentsInstantiated ≡ false
physicalTimeDependentConstituentsInstantiatedIsFalse = refl
