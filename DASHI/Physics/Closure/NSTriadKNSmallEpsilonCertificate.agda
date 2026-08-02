module DASHI.Physics.Closure.NSTriadKNSmallEpsilonCertificate where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Terence Tao; DASHI
-- repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators" and
-- "Multilinear Interpolation Between Adjoint Operators".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Journal
-- of Functional Analysis 199 (2003), 379--385; DASHI formal development,
-- 2026.
-- DOI: 10.1006/jfan.2001.3804;
-- 10.1016/S0022-1236(02)00098-8; the repository certificate has no DOI.
-- Uses: the Section-5.10 strategy of solving the homogeneity equalities
-- first, substituting an affine family in epsilon, and proving every
-- geometric sum strict on one common positive interval.
-- Relationship: gives a reusable theorem converting rowwise lower/upper
-- epsilon bounds into a certificate for all twenty-one DASHI rows. The
-- theorem is closed; the concrete Navier--Stokes row bounds remain an
-- explicit input and are not fabricated.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresAffineWeightTemplate as Template
import DASHI.Physics.Closure.NSTriadKNAffineRowFactorisation as Rows

record SymbolicSmallEpsilonInput {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    zero epsilon : Scalar
    _<_ : Scalar → Scalar → Set s

    rowLowerBound : Rows.AffineRow → Scalar
    rowUpperBound : Rows.AffineRow → Scalar
    rowStrict : Rows.AffineRow → Scalar → Set s

    epsilonPositive : zero < epsilon
    everyLowerBoundBelowEpsilon :
      ∀ row → rowLowerBound row < epsilon
    epsilonBelowEveryUpperBound :
      ∀ row → epsilon < rowUpperBound row

    intervalImpliesRowStrict :
      ∀ row →
      rowLowerBound row < epsilon →
      epsilon < rowUpperBound row →
      rowStrict row epsilon

open SymbolicSmallEpsilonInput public

record SmallEpsilonCertificate {s : Level}
    (input : SymbolicSmallEpsilonInput {s}) : Set (lsuc s) where
  field
    selectedEpsilon : Scalar input
    selectedEpsilonIsInput :
      selectedEpsilon ≡ epsilon input
    selectedEpsilonPositive :
      _<_ input (zero input) selectedEpsilon
    everyRowStrict :
      ∀ row → rowStrict input row selectedEpsilon

open SmallEpsilonCertificate public

deriveSmallEpsilonCertificate :
  ∀ {s} (input : SymbolicSmallEpsilonInput {s}) →
  SmallEpsilonCertificate input
deriveSmallEpsilonCertificate input = record
  { selectedEpsilon = epsilon input
  ; selectedEpsilonIsInput = refl
  ; selectedEpsilonPositive = epsilonPositive input
  ; everyRowStrict = λ row →
      intervalImpliesRowStrict input row
        (everyLowerBoundBelowEpsilon input row)
        (epsilonBelowEveryUpperBound input row)
  }

record AffineSubstitutionReceipt {s : Level}
    (input : SymbolicSmallEpsilonInput {s}) : Set (lsuc s) where
  field
    familyAssignment :
      Rows.FamilyCoefficientAssignment (Scalar input)
    baseExponent :
      Rows.AffineRow → Scalar input
    epsilonSlope :
      Rows.AffineRow → Scalar input
    subtract multiply :
      Scalar input → Scalar input → Scalar input
    substitutedExponent :
      Rows.AffineRow → Scalar input
    substitutionMeaning :
      ∀ row →
      substitutedExponent row
      ≡ subtract
          (baseExponent row)
          (multiply (epsilon input) (epsilonSlope row))
    strictExponentImpliesRowStrict :
      ∀ row → rowStrict input row (epsilon input)

open AffineSubstitutionReceipt public

record ExactCommonIntervalAudit {s : Level}
    (input : SymbolicSmallEpsilonInput {s}) : Set (lsuc s) where
  field
    lowerMaximum upperMinimum : Scalar input
    everyLowerAtMostMaximum : Set s
    minimumAtMostEveryUpper : Set s
    maximumBelowSelectedEpsilon :
      _<_ input lowerMaximum (epsilon input)
    selectedEpsilonBelowMinimum :
      _<_ input (epsilon input) upperMinimum
    activeRowsIdentified : Set s
    rationalAuditAgreesWithSymbolicProof : Set s

open ExactCommonIntervalAudit public

record SourceSmallEpsilonMethodReceipt : Set where
  constructor source-receipt
  field
    section510TemplateClosed :
      Template.grafakosTorresSection510AffineTemplateClosed ≡ true
    diagonalWitnessClosed :
      Template.sourceDiagonalSmallEpsilonWitnessClosed ≡ true
    epsilonPositive :
      Template.PositiveNat Template.sourceEpsilonScaled
    firstTargetMarginPositive :
      Template.PositiveNat
        Template.sourceTargetAboveEpsilonMarginScaled
    firstOrderMarginPositive :
      Template.PositiveNat
        Template.sourceOrderAboveTargetMarginScaled
    sourceDoesNotPopulateDASHIRows :
      Template.sourceCoefficientsAutomaticallyTransferToDASHI ≡ false

open SourceSmallEpsilonMethodReceipt public

sourceSmallEpsilonMethodReceipt : SourceSmallEpsilonMethodReceipt
sourceSmallEpsilonMethodReceipt =
  source-receipt
    Template.grafakosTorresSection510AffineTemplateClosedIsTrue
    Template.sourceDiagonalSmallEpsilonWitnessClosedIsTrue
    Template.sourceEpsilonPositive
    Template.sourceTargetAboveEpsilonMarginPositive
    Template.sourceOrderAboveTargetMarginPositive
    Template.sourceCoefficientsAutomaticallyTransferToDASHIIsFalse

genericTwentyOneRowSmallEpsilonTheoremClosed : Bool
genericTwentyOneRowSmallEpsilonTheoremClosed = true

genericTwentyOneRowSmallEpsilonTheoremClosedIsTrue :
  genericTwentyOneRowSmallEpsilonTheoremClosed ≡ true
genericTwentyOneRowSmallEpsilonTheoremClosedIsTrue = refl

sourceSmallEpsilonConstructionChecked : Bool
sourceSmallEpsilonConstructionChecked = true

sourceSmallEpsilonConstructionCheckedIsTrue :
  sourceSmallEpsilonConstructionChecked ≡ true
sourceSmallEpsilonConstructionCheckedIsTrue = refl

concreteDASHIRowBoundsSupplied : Bool
concreteDASHIRowBoundsSupplied = false

concreteDASHIRowBoundsSuppliedIsFalse :
  concreteDASHIRowBoundsSupplied ≡ false
concreteDASHIRowBoundsSuppliedIsFalse = refl

strictPositiveDASHIEpsilonAvailable : Bool
strictPositiveDASHIEpsilonAvailable = false

strictPositiveDASHIEpsilonAvailableIsFalse :
  strictPositiveDASHIEpsilonAvailable ≡ false
strictPositiveDASHIEpsilonAvailableIsFalse = refl
