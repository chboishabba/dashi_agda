module DASHI.Physics.Closure.NSTriadKNAffineResolvedFamilyReduction where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Jean-Michel Bony; DASHI
-- repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators"; "Calcul
-- symbolique et propagation des singularites pour les equations aux derivees
-- partielles non lineaires"; and "Resolved-family reduction of the Stage-3
-- affine coefficient frontier".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Annales
-- scientifiques de l'Ecole Normale Superieure 14 (1981); DASHI formal
-- development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.24033/asens.1404; the repository reduction
-- has no DOI.
-- Uses: the eight-family factorisation of the twenty-one affine rows and the
-- proved constant-unit-weight assignment for the output-relocation family.
-- Relationship: refines the historical 24-slot underdetermination statement.
-- One three-leg family is now fixed to (0,0,0), leaving seven unresolved
-- families and twenty-one numeric slots.  It does not assign any of the other
-- families or claim a positive global epsilon.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Physics.Closure.NSTriadKNAffineRowFactorisation as Factor
import DASHI.Physics.Closure.NSTriadKNAffineCertificateUnderdetermination as Previous
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightCheckA as Unit

originalIndependentFamilyCount : Nat
originalIndependentFamilyCount = Factor.independentFamilyCount

resolvedIndependentFamilyCount : Nat
resolvedIndependentFamilyCount = 1

remainingIndependentFamilyCount : Nat
remainingIndependentFamilyCount = 7

coefficientSlotsPerFamily : Nat
coefficientSlotsPerFamily = 3

resolvedCoefficientSlotCount : Nat
resolvedCoefficientSlotCount =
  resolvedIndependentFamilyCount * coefficientSlotsPerFamily

remainingIndependentCoefficientSlotCount : Nat
remainingIndependentCoefficientSlotCount =
  remainingIndependentFamilyCount * coefficientSlotsPerFamily

familyCountDecomposition :
  resolvedIndependentFamilyCount + remainingIndependentFamilyCount
  ≡ originalIndependentFamilyCount
familyCountDecomposition = refl

resolvedCoefficientSlotCountIs3 :
  resolvedCoefficientSlotCount ≡ 3
resolvedCoefficientSlotCountIs3 = refl

remainingIndependentCoefficientSlotCountIs21 :
  remainingIndependentCoefficientSlotCount ≡ 21
remainingIndependentCoefficientSlotCountIs21 = refl

outputRelocationResolvedFamily : Factor.IndependentCoefficientFamily
outputRelocationResolvedFamily = Factor.outputRelocationFamily

postOutputRelocationAffineOutcome : Previous.AffineCertificateOutcome
postOutputRelocationAffineOutcome =
  Previous.underdetermined remainingIndependentCoefficientSlotCount

postOutputRelocationOutcomeIsUnderdetermined21 :
  postOutputRelocationAffineOutcome ≡ Previous.underdetermined 21
postOutputRelocationOutcomeIsUnderdetermined21 = refl

record ResolvedFamilyReductionReceipt : Set where
  constructor receipt
  field
    historicalOutcomeWasUnderdetermined24 :
      Previous.currentAffineOutcome ≡ Previous.underdetermined 24
    outputRelocationUnitWeightCheckAClosed :
      Unit.outputRelocationUnitWeightSymbolicCheckA ≡ true
    familyResolvedIsOutputRelocation :
      outputRelocationResolvedFamily ≡ Factor.outputRelocationFamily
    oneFamilyResolved : resolvedIndependentFamilyCount ≡ 1
    sevenFamiliesRemain : remainingIndependentFamilyCount ≡ 7
    threeSlotsResolved : resolvedCoefficientSlotCount ≡ 3
    twentyOneSlotsRemain : remainingIndependentCoefficientSlotCount ≡ 21

open ResolvedFamilyReductionReceipt public

resolvedFamilyReductionReceipt : ResolvedFamilyReductionReceipt
resolvedFamilyReductionReceipt = receipt
  Previous.currentOutcomeIsUnderdetermined24
  Unit.outputRelocationUnitWeightSymbolicCheckAIsTrue
  refl refl refl refl refl

outputRelocationAffineFamilyResolved : Bool
outputRelocationAffineFamilyResolved = true

postOutputRelocationAffineOutcomeRefined : Bool
postOutputRelocationAffineOutcomeRefined = true

remainingAffineIndependentSlotCountIsTwentyOne : Bool
remainingAffineIndependentSlotCountIsTwentyOne = true

globalAffineCertificateClosed : Bool
globalAffineCertificateClosed = false

outputRelocationAffineFamilyResolvedIsTrue :
  outputRelocationAffineFamilyResolved ≡ true
outputRelocationAffineFamilyResolvedIsTrue = refl

postOutputRelocationAffineOutcomeRefinedIsTrue :
  postOutputRelocationAffineOutcomeRefined ≡ true
postOutputRelocationAffineOutcomeRefinedIsTrue = refl

remainingAffineIndependentSlotCountIsTwentyOneIsTrue :
  remainingAffineIndependentSlotCountIsTwentyOne ≡ true
remainingAffineIndependentSlotCountIsTwentyOneIsTrue = refl

globalAffineCertificateClosedIsFalse :
  globalAffineCertificateClosed ≡ false
globalAffineCertificateClosedIsFalse = refl
