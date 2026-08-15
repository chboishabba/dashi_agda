module DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact where

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
-- Round 25 made physical support duplicate-free.  This file applies the same
-- discipline to analytic payment: every taxable positive-production atom has
-- exactly one owner, and erasing ownership reconstructs the original tax
-- total exactly.  The owner partition separates good/bad HH, the other four
-- physical classes, kernel, tail and cutoff-boundary taxes.  No atom can be
-- counted twice by construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

data TaxOwner : Set where
  HH-good HH-bad LH HL CC Com kernel tail boundary : TaxOwner

record TaxAtom : Set where
  constructor tax-atom
  field
    owner : TaxOwner
    signedValue : ℚ
    taxableValue : ℚ
    signedBelowTax : signedValue ≤ taxableValue
    taxNonnegative : 0ℚ ≤ taxableValue

open TaxAtom public

ownerUnique :
  (atom : TaxAtom) →
  ∀ {first second} →
  owner atom ≡ first →
  owner atom ≡ second →
  first ≡ second
ownerUnique atom firstProof secondProof =
  trans (sym firstProof) secondProof

totalTax : List TaxAtom → ℚ
totalTax [] = 0ℚ
totalTax (atom ∷ rest) = taxableValue atom + totalTax rest

hhGoodTax : List TaxAtom → ℚ
hhGoodTax [] = 0ℚ
hhGoodTax (atom ∷ rest) with owner atom
... | HH-good = taxableValue atom + hhGoodTax rest
... | HH-bad = hhGoodTax rest
... | LH = hhGoodTax rest
... | HL = hhGoodTax rest
... | CC = hhGoodTax rest
... | Com = hhGoodTax rest
... | kernel = hhGoodTax rest
... | tail = hhGoodTax rest
... | boundary = hhGoodTax rest

hhBadTax : List TaxAtom → ℚ
hhBadTax [] = 0ℚ
hhBadTax (atom ∷ rest) with owner atom
... | HH-good = hhBadTax rest
... | HH-bad = taxableValue atom + hhBadTax rest
... | LH = hhBadTax rest
... | HL = hhBadTax rest
... | CC = hhBadTax rest
... | Com = hhBadTax rest
... | kernel = hhBadTax rest
... | tail = hhBadTax rest
... | boundary = hhBadTax rest

lhTax : List TaxAtom → ℚ
lhTax [] = 0ℚ
lhTax (atom ∷ rest) with owner atom
... | HH-good = lhTax rest
... | HH-bad = lhTax rest
... | LH = taxableValue atom + lhTax rest
... | HL = lhTax rest
... | CC = lhTax rest
... | Com = lhTax rest
... | kernel = lhTax rest
... | tail = lhTax rest
... | boundary = lhTax rest

hlTax : List TaxAtom → ℚ
hlTax [] = 0ℚ
hlTax (atom ∷ rest) with owner atom
... | HH-good = hlTax rest
... | HH-bad = hlTax rest
... | LH = hlTax rest
... | HL = taxableValue atom + hlTax rest
... | CC = hlTax rest
... | Com = hlTax rest
... | kernel = hlTax rest
... | tail = hlTax rest
... | boundary = hlTax rest

ccTax : List TaxAtom → ℚ
ccTax [] = 0ℚ
ccTax (atom ∷ rest) with owner atom
... | HH-good = ccTax rest
... | HH-bad = ccTax rest
... | LH = ccTax rest
... | HL = ccTax rest
... | CC = taxableValue atom + ccTax rest
... | Com = ccTax rest
... | kernel = ccTax rest
... | tail = ccTax rest
... | boundary = ccTax rest

comTax : List TaxAtom → ℚ
comTax [] = 0ℚ
comTax (atom ∷ rest) with owner atom
... | HH-good = comTax rest
... | HH-bad = comTax rest
... | LH = comTax rest
... | HL = comTax rest
... | CC = comTax rest
... | Com = taxableValue atom + comTax rest
... | kernel = comTax rest
... | tail = comTax rest
... | boundary = comTax rest

kernelTax : List TaxAtom → ℚ
kernelTax [] = 0ℚ
kernelTax (atom ∷ rest) with owner atom
... | HH-good = kernelTax rest
... | HH-bad = kernelTax rest
... | LH = kernelTax rest
... | HL = kernelTax rest
... | CC = kernelTax rest
... | Com = kernelTax rest
... | kernel = taxableValue atom + kernelTax rest
... | tail = kernelTax rest
... | boundary = kernelTax rest

tailTax : List TaxAtom → ℚ
tailTax [] = 0ℚ
tailTax (atom ∷ rest) with owner atom
... | HH-good = tailTax rest
... | HH-bad = tailTax rest
... | LH = tailTax rest
... | HL = tailTax rest
... | CC = tailTax rest
... | Com = tailTax rest
... | kernel = tailTax rest
... | tail = taxableValue atom + tailTax rest
... | boundary = tailTax rest

boundaryTax : List TaxAtom → ℚ
boundaryTax [] = 0ℚ
boundaryTax (atom ∷ rest) with owner atom
... | HH-good = boundaryTax rest
... | HH-bad = boundaryTax rest
... | LH = boundaryTax rest
... | HL = boundaryTax rest
... | CC = boundaryTax rest
... | Com = boundaryTax rest
... | kernel = boundaryTax rest
... | tail = boundaryTax rest
... | boundary = taxableValue atom + boundaryTax rest

ownedTaxTotal : List TaxAtom → ℚ
ownedTaxTotal atoms =
  hhGoodTax atoms
  + hhBadTax atoms
  + lhTax atoms
  + hlTax atoms
  + ccTax atoms
  + comTax atoms
  + kernelTax atoms
  + tailTax atoms
  + boundaryTax atoms

private
  hhGoodTaxSum :
    (a b c d e f g h i j : ℚ) →
    a + (b + c + d + e + f + g + h + i + j)
      ≡ a + b + c + d + e + f + g + h + i + j
  hhGoodTaxSum a b c d e f g h i j = solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ [])

  hhBadTaxSum :
    (a b c d e f g h i j : ℚ) →
    a + (b + c + d + e + f + g + h + i + j)
      ≡ b + (a + c) + d + e + f + g + h + i + j
  hhBadTaxSum a b c d e f g h i j = solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ [])

  lhTaxSum :
    (a b c d e f g h i j : ℚ) →
    a + (b + c + d + e + f + g + h + i + j)
      ≡ b + c + (a + d) + e + f + g + h + i + j
  lhTaxSum a b c d e f g h i j = solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ [])

  hlTaxSum :
    (a b c d e f g h i j : ℚ) →
    a + (b + c + d + e + f + g + h + i + j)
      ≡ b + c + d + (a + e) + f + g + h + i + j
  hlTaxSum a b c d e f g h i j = solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ [])

  ccTaxSum :
    (a b c d e f g h i j : ℚ) →
    a + (b + c + d + e + f + g + h + i + j)
      ≡ b + c + d + e + (a + f) + g + h + i + j
  ccTaxSum a b c d e f g h i j = solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ [])

  comTaxSum :
    (a b c d e f g h i j : ℚ) →
    a + (b + c + d + e + f + g + h + i + j)
      ≡ b + c + d + e + f + (a + g) + h + i + j
  comTaxSum a b c d e f g h i j = solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ [])

  kernelTaxSum :
    (a b c d e f g h i j : ℚ) →
    a + (b + c + d + e + f + g + h + i + j)
      ≡ b + c + d + e + f + g + (a + h) + i + j
  kernelTaxSum a b c d e f g h i j = solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ [])

  tailTaxSum :
    (a b c d e f g h i j : ℚ) →
    a + (b + c + d + e + f + g + h + i + j)
      ≡ b + c + d + e + f + g + h + (a + i) + j
  tailTaxSum a b c d e f g h i j = solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ [])

  boundaryTaxSum :
    (a b c d e f g h i j : ℚ) →
    a + (b + c + d + e + f + g + h + i + j)
      ≡ b + c + d + e + f + g + h + i + (a + j)
  boundaryTaxSum a b c d e f g h i j = solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ [])

duplicateFreeTaxOwnershipExact :
  (atoms : List TaxAtom) →
  totalTax atoms ≡ ownedTaxTotal atoms
duplicateFreeTaxOwnershipExact [] = refl
duplicateFreeTaxOwnershipExact (atom ∷ rest)
  with owner atom
... | HH-good
  rewrite duplicateFreeTaxOwnershipExact rest =
  hhGoodTaxSum (taxableValue atom) (hhGoodTax rest)
    (hhBadTax rest) (lhTax rest) (hlTax rest) (ccTax rest)
    (comTax rest) (kernelTax rest) (tailTax rest) (boundaryTax rest)
... | HH-bad
  rewrite duplicateFreeTaxOwnershipExact rest =
  hhBadTaxSum (taxableValue atom) (hhGoodTax rest)
    (hhBadTax rest) (lhTax rest) (hlTax rest) (ccTax rest)
    (comTax rest) (kernelTax rest) (tailTax rest) (boundaryTax rest)
... | LH
  rewrite duplicateFreeTaxOwnershipExact rest =
  lhTaxSum (taxableValue atom) (hhGoodTax rest)
    (hhBadTax rest) (lhTax rest) (hlTax rest) (ccTax rest)
    (comTax rest) (kernelTax rest) (tailTax rest) (boundaryTax rest)
... | HL
  rewrite duplicateFreeTaxOwnershipExact rest =
  hlTaxSum (taxableValue atom) (hhGoodTax rest)
    (hhBadTax rest) (lhTax rest) (hlTax rest) (ccTax rest)
    (comTax rest) (kernelTax rest) (tailTax rest) (boundaryTax rest)
... | CC
  rewrite duplicateFreeTaxOwnershipExact rest =
  ccTaxSum (taxableValue atom) (hhGoodTax rest)
    (hhBadTax rest) (lhTax rest) (hlTax rest) (ccTax rest)
    (comTax rest) (kernelTax rest) (tailTax rest) (boundaryTax rest)
... | Com
  rewrite duplicateFreeTaxOwnershipExact rest =
  comTaxSum (taxableValue atom) (hhGoodTax rest)
    (hhBadTax rest) (lhTax rest) (hlTax rest) (ccTax rest)
    (comTax rest) (kernelTax rest) (tailTax rest) (boundaryTax rest)
... | kernel
  rewrite duplicateFreeTaxOwnershipExact rest =
  kernelTaxSum (taxableValue atom) (hhGoodTax rest)
    (hhBadTax rest) (lhTax rest) (hlTax rest) (ccTax rest)
    (comTax rest) (kernelTax rest) (tailTax rest) (boundaryTax rest)
... | tail
  rewrite duplicateFreeTaxOwnershipExact rest =
  tailTaxSum (taxableValue atom) (hhGoodTax rest)
    (hhBadTax rest) (lhTax rest) (hlTax rest) (ccTax rest)
    (comTax rest) (kernelTax rest) (tailTax rest) (boundaryTax rest)
... | boundary
  rewrite duplicateFreeTaxOwnershipExact rest =
  boundaryTaxSum (taxableValue atom) (hhGoodTax rest)
    (hhBadTax rest) (lhTax rest) (hlTax rest) (ccTax rest)
    (comTax rest) (kernelTax rest) (tailTax rest) (boundaryTax rest)

------------------------------------------------------------------------
-- Tax coefficients are kept separate from ownership.  Ownership prevents
-- duplication; the still-open analytic work must prove each coefficient and
-- then the strict total margin.
------------------------------------------------------------------------

record OwnedViscosityCoefficients : Set where
  constructor owned-viscosity-coefficients
  field
    etaHHGood etaHHBad etaLH etaHL etaCC etaCom etaKernel etaTail etaBoundary : ℚ

open OwnedViscosityCoefficients public

totalEta : OwnedViscosityCoefficients → ℚ
totalEta E =
  etaHHGood E + etaHHBad E + etaLH E + etaHL E + etaCC E
  + etaCom E + etaKernel E + etaTail E + etaBoundary E
