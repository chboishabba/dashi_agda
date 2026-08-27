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
-- The records below formalize that distinction; the cited review is source
-- calibration, not a proof certificate for the generic Agda lemmas.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

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

-- Internalizing the whole pointwise family is additional data.  Nothing in a
-- DeductionIndexedInterpretation manufactures this package.
record UniformInternalization
    (indexed : DeductionIndexedInterpretation) : Set₁ where
  constructor uniformInternalization
  field
    uniformFormula : TargetFormula indexed
    ExpressesPointwiseFamily : TargetFormula indexed → Set
    expressesFamily : ExpressesPointwiseFamily uniformFormula
    uniformProof : TargetDerivable indexed uniformFormula

open UniformInternalization public

pointwiseInstance :
  (indexed : DeductionIndexedInterpretation) →
  (deduction : SourceDeduction indexed) →
  TargetDerivable indexed (interpretation indexed deduction)
pointwiseInstance indexed deduction = pointwiseProof indexed deduction

record DeductionIndexedInterpretationBoundary : Set where
  constructor deductionIndexedInterpretationBoundary
  field
    deductionDependentInterpretationExplicitlyRepresentable : Bool
    deductionDependentInterpretationExplicitlyRepresentableIsTrue :
      deductionDependentInterpretationExplicitlyRepresentable ≡ true

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
