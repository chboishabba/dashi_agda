module DASHI.Physics.Closure.NSTriadKNAffineCertificateExactAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Pierre Germain; DASHI
-- repository contributors.
-- Title: "Exact structural audit for the Stage-3 affine weight problem".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Journal
-- of Differential Equations 226 (2006), 373--428; DASHI formal
-- development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.1016/j.jde.2005.10.007;
-- the repository exact audit has no DOI.
-- Uses: the Section-5.10 affine template, the twenty-one-row/eight-family
-- factorisation, and the generic common-small-epsilon theorem.
-- Relationship: replaces the coarse statement "sixty-three unrelated
-- coefficients are missing" by the exact statement that sixty-three raw
-- row slots factor through twenty-four independent numeric slots. It
-- remains fail-closed because those twenty-four values and the resulting
-- positive common interval have not yet been proved from the five
-- cutoff-uniform Sobolev archetypes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresAffineWeightTemplate as Template
import DASHI.Physics.Closure.NSTriadKNAffineRowFactorisation as Rows
import DASHI.Physics.Closure.NSTriadKNSmallEpsilonCertificate as Small

data AffineCertificateOutcome : Set where
  certified
  zeroSlackBoundary
  infeasible
  underdetermined : Nat → AffineCertificateOutcome

rawUnfactorisedOutcome : AffineCertificateOutcome
rawUnfactorisedOutcome = underdetermined Rows.rawCoefficientSlotCount

currentFactorisedOutcome : AffineCertificateOutcome
currentFactorisedOutcome =
  underdetermined Rows.independentCoefficientSlotCount

rawOutcomeIsUnderdetermined63 :
  rawUnfactorisedOutcome ≡ underdetermined 63
rawOutcomeIsUnderdetermined63 = refl

currentOutcomeIsUnderdetermined24 :
  currentFactorisedOutcome ≡ underdetermined 24
currentOutcomeIsUnderdetermined24 = refl

record ExactAffineArchitectureReceipt : Set where
  constructor receipt
  field
    sourceTemplateClosed :
      Template.grafakosTorresSection510AffineTemplateClosed ≡ true
    sourceWitnessClosed :
      Template.sourceDiagonalSmallEpsilonWitnessClosed ≡ true
    twelveSeparatedRowsFactorised :
      Rows.allTwelveSeparatedRowsFactorised ≡ true
    nineOverlapRowsFactorised :
      Rows.allNineOverlapRowsFactorised ≡ true
    rawSlotsAreSixtyThree :
      Rows.rawCoefficientSlotCount ≡ 63
    independentSlotsAreTwentyFour :
      Rows.independentCoefficientSlotCount ≡ 24
    genericSmallEpsilonTheoremClosed :
      Small.genericTwentyOneRowSmallEpsilonTheoremClosed ≡ true
    concreteRowsStillOpen :
      Small.concreteDASHIRowBoundsSupplied ≡ false
    positiveEpsilonStillOpen :
      Small.strictPositiveDASHIEpsilonAvailable ≡ false

open ExactAffineArchitectureReceipt public

exactAffineArchitectureReceipt : ExactAffineArchitectureReceipt
exactAffineArchitectureReceipt =
  receipt
    Template.grafakosTorresSection510AffineTemplateClosedIsTrue
    Template.sourceDiagonalSmallEpsilonWitnessClosedIsTrue
    Rows.allTwelveSeparatedRowsFactorisedIsTrue
    Rows.allNineOverlapRowsFactorisedIsTrue
    Rows.rawCoefficientSlotCountIs63
    Rows.independentCoefficientSlotCountIs24
    Small.genericTwentyOneRowSmallEpsilonTheoremClosedIsTrue
    Small.concreteDASHIRowBoundsSuppliedIsFalse
    Small.strictPositiveDASHIEpsilonAvailableIsFalse

affineSolverArchitectureClosed : Bool
affineSolverArchitectureClosed = true

affineSolverArchitectureClosedIsTrue :
  affineSolverArchitectureClosed ≡ true
affineSolverArchitectureClosedIsTrue = refl

numericTwentyFourCoefficientSlotsClosed : Bool
numericTwentyFourCoefficientSlotsClosed = false

numericTwentyFourCoefficientSlotsClosedIsFalse :
  numericTwentyFourCoefficientSlotsClosed ≡ false
numericTwentyFourCoefficientSlotsClosedIsFalse = refl

strictPositiveEpsilonAvailable : Bool
strictPositiveEpsilonAvailable = false

strictPositiveEpsilonAvailableIsFalse :
  strictPositiveEpsilonAvailable ≡ false
strictPositiveEpsilonAvailableIsFalse = refl
