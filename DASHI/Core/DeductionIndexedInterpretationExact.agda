module DASHI.Core.DeductionIndexedInterpretationExact where

------------------------------------------------------------------------
-- DEDUCTION-INDEXED INTERPRETATION
--
-- Generic owner for interpretations whose translated formula / proof object
-- depends on the source deduction in which the formula occurs.  This is
-- strictly more general than a formula-only map.
--
-- Historical calibration: G. Kreisel and J. Zucker, review of Eduard Wette,
-- Journal of Symbolic Logic 37(1), 1972, pp. 203--204.
-- DOI: 10.2307/2272630.
-- The review stresses the difference between:
--   (i) each source deduction d having a target proof of its interpretation;
--   (ii) the target theory proving one formula expressing that (i) holds for
--        all d.
--
-- The 1969 Wette primary text makes an earlier distinction necessary too:
-- stating the interpretation procedure is not yet certifying that every
-- source deduction has a target proof.  Hence this module now separates a
-- DeductionIndexedInterpretationSpec from a proof-bearing
-- DeductionIndexedInterpretation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record DeductionIndexedInterpretationSpec : Set₁ where
  constructor deductionIndexedInterpretationSpec
  field
    SourceDeduction : Set
    TargetFormula : Set
    interpretation : SourceDeduction → TargetFormula

open DeductionIndexedInterpretationSpec public

record DeductionIndexedInterpretation : Set₁ where
  constructor deductionIndexedInterpretation
  field
    SourceDeduction : Set
    TargetFormula : Set
    TargetDerivable : TargetFormula → Set
    interpretation : SourceDeduction → TargetFormula
    pointwiseProof :
      (deduction : SourceDeduction) →
      TargetDerivable (interpretation deduction)

open DeductionIndexedInterpretation public

forgetPointwiseCertificate :
  DeductionIndexedInterpretation →
  DeductionIndexedInterpretationSpec
forgetPointwiseCertificate indexed =
  deductionIndexedInterpretationSpec
    (DeductionIndexedInterpretation.SourceDeduction indexed)
    (DeductionIndexedInterpretation.TargetFormula indexed)
    (DeductionIndexedInterpretation.interpretation indexed)

-- Internalizing the whole pointwise family is additional data.  Nothing in a
-- DeductionIndexedInterpretation manufactures this package.
record UniformInternalization
    (indexed : DeductionIndexedInterpretation) : Set₁ where
  constructor uniformInternalization
  field
    uniformFormula : DeductionIndexedInterpretation.TargetFormula indexed
    ExpressesPointwiseFamily :
      DeductionIndexedInterpretation.TargetFormula indexed → Set
    expressesFamily : ExpressesPointwiseFamily uniformFormula
    uniformProof :
      DeductionIndexedInterpretation.TargetDerivable indexed uniformFormula

open UniformInternalization public

pointwiseInstance :
  (indexed : DeductionIndexedInterpretation) →
  (deduction : DeductionIndexedInterpretation.SourceDeduction indexed) →
  DeductionIndexedInterpretation.TargetDerivable indexed
    (DeductionIndexedInterpretation.interpretation indexed deduction)
pointwiseInstance indexed deduction =
  DeductionIndexedInterpretation.pointwiseProof indexed deduction

record DeductionIndexedInterpretationBoundary : Set where
  constructor deductionIndexedInterpretationBoundary
  field
    deductionDependentInterpretationExplicitlyRepresentable : Bool
    deductionDependentInterpretationExplicitlyRepresentableIsTrue :
      deductionDependentInterpretationExplicitlyRepresentable ≡ true

    interpretationSpecificationIsAlreadyPointwiseProofCertificate : Bool
    interpretationSpecificationIsAlreadyPointwiseProofCertificateIsFalse :
      interpretationSpecificationIsAlreadyPointwiseProofCertificate ≡ false

    pointwiseProofFamilyIsDefinitionallyUniformInternalProof : Bool
    pointwiseProofFamilyIsDefinitionallyUniformInternalProofIsFalse :
      pointwiseProofFamilyIsDefinitionallyUniformInternalProof ≡ false

    formulaOnlyTranslationIsDefinitionallyEnoughForEveryDeductionIndexedInterpretation : Bool
    formulaOnlyTranslationIsDefinitionallyEnoughForEveryDeductionIndexedInterpretationIsFalse :
      formulaOnlyTranslationIsDefinitionallyEnoughForEveryDeductionIndexedInterpretation ≡ false

canonicalDeductionIndexedInterpretationBoundary :
  DeductionIndexedInterpretationBoundary
canonicalDeductionIndexedInterpretationBoundary =
  deductionIndexedInterpretationBoundary
    true refl
    false refl
    false refl
    false refl
