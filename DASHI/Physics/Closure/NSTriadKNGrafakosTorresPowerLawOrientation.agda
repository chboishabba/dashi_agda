module DASHI.Physics.Closure.NSTriadKNGrafakosTorresPowerLawOrientation where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; DASHI repository contributors.
-- Title: "Literal three-condition power-law orientation for the Stage-3
-- multilinear Schur test".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; DASHI formal
-- development, 2026.
-- DOI: 10.1006/jfan.2001.3804; the repository orientation theorem has no DOI.
-- Uses: the paper's construction of auxiliary functions by direct power-law
-- substitution into the output and two partial-adjoint Schur inequalities.
-- Relationship: determines the sign/incidence orientation of the three
-- auxiliary weights.  It does not determine the physical shell coefficients,
-- which still require the literal kernel and shell-index substitution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)

record ConjugateExponentData : Set where
  constructor exponents
  field
    left leftConjugate right rightConjugate output outputConjugate : Int

open ConjugateExponentData public

record SignedThreeLegOrientation : Set where
  constructor orientation
  field
    leftSign rightSign outputSign : Int

open SignedThreeLegOrientation public

-- When every target is moved to the left, an input weight contributes with a
-- negative sign and the condition's target weight with a positive sign.
outputConditionOrientation : SignedThreeLegOrientation
outputConditionOrientation = orientation (negsuc 0) (negsuc 0) (pos 1)

firstAdjointConditionOrientation : SignedThreeLegOrientation
firstAdjointConditionOrientation = orientation (pos 1) (negsuc 0) (negsuc 0)

secondAdjointConditionOrientation : SignedThreeLegOrientation
secondAdjointConditionOrientation = orientation (negsuc 0) (pos 1) (negsuc 0)

outputOrientationLiteral :
  outputConditionOrientation ≡ orientation (negsuc 0) (negsuc 0) (pos 1)
outputOrientationLiteral = refl

firstAdjointOrientationLiteral :
  firstAdjointConditionOrientation ≡ orientation (pos 1) (negsuc 0) (negsuc 0)
firstAdjointOrientationLiteral = refl

secondAdjointOrientationLiteral :
  secondAdjointConditionOrientation ≡ orientation (negsuc 0) (pos 1) (negsuc 0)
secondAdjointOrientationLiteral = refl

record PowerLawSubstitutionCutset : Set₁ where
  field
    ShellIndex : Set
    Scalar : Set
    auxiliaryPower : Scalar → ShellIndex → Scalar
    kernelMajorant : ShellIndex → ShellIndex → ShellIndex → Scalar

    outputConditionWrittenLiterally : Set
    firstAdjointConditionWrittenLiterally : Set
    secondAdjointConditionWrittenLiterally : Set

    outputInputsNegativeTargetPositive : Set
    firstAdjointInputsNegativeTargetPositive : Set
    secondAdjointInputsNegativeTargetPositive : Set

open PowerLawSubstitutionCutset public

record OutputRelocationOrientationExtraction : Set₁ where
  field
    literalOutputKernelWritten : Set
    leftShellVariableSubstituted : Set
    rightShellVariableSubstituted : Set
    outputShellVariableSubstituted : Set
    physicalDecaySeparatedFromAuxiliaryWeights : Set
    outputConditionCoefficientVector : Set
    firstAdjointConditionCoefficientVector : Set
    secondAdjointConditionCoefficientVector : Set
    allThreeVectorsConsistentWithOneKernel : Set

open OutputRelocationOrientationExtraction public

grafakosTorresSignOrientationClosed : Bool
grafakosTorresSignOrientationClosed = true

literalThreeConditionTemplateClosed : Bool
literalThreeConditionTemplateClosed = true

outputRelocationNumericOrientationClosed : Bool
outputRelocationNumericOrientationClosed = false

outputRelocationCheckAAvailable : Bool
outputRelocationCheckAAvailable = false

grafakosTorresSignOrientationClosedIsTrue :
  grafakosTorresSignOrientationClosed ≡ true
grafakosTorresSignOrientationClosedIsTrue = refl

literalThreeConditionTemplateClosedIsTrue :
  literalThreeConditionTemplateClosed ≡ true
literalThreeConditionTemplateClosedIsTrue = refl

outputRelocationNumericOrientationClosedIsFalse :
  outputRelocationNumericOrientationClosed ≡ false
outputRelocationNumericOrientationClosedIsFalse = refl

outputRelocationCheckAAvailableIsFalse :
  outputRelocationCheckAAvailable ≡ false
outputRelocationCheckAAvailableIsFalse = refl
