module DASHI.Physics.Closure.NormalisedH0OSPositivity where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.H0SignConventionReceipt as Sign

data NormalisedH0Branch : Set where
  spectralRadiusNormalisationBranch : NormalisedH0Branch
  invertedTransferOperatorBranch : NormalisedH0Branch

canonicalNormalisedH0Branches :
  List NormalisedH0Branch
canonicalNormalisedH0Branches =
  spectralRadiusNormalisationBranch
  ∷ invertedTransferOperatorBranch
  ∷ []

normalisedH0BoundaryStatement : String
normalisedH0BoundaryStatement =
  "Raw H0 fails PSD; an OS branch must first build a contractive transfer matrix, e.g. by spectral-radius normalization or transfer inversion, then check the reflection form."

record NormalisedH0OSPositivityReceipt : Setω where
  field
    signConventionReceipt :
      Sign.H0SignConventionReceipt

    signConventionRequiresNormalisation :
      Sign.h0NormalisationRequired signConventionReceipt ≡ true

    signConventionRequiresInversion :
      Sign.h0InversionRequiredForOS signConventionReceipt ≡ true

    branches :
      List NormalisedH0Branch

    branchesAreCanonical :
      branches ≡ canonicalNormalisedH0Branches

    normalisedTransferMatrixConstructed :
      Bool

    normalisedTransferMatrixConstructedIsFalse :
      normalisedTransferMatrixConstructed ≡ false

    invertedTransferMatrixConstructed :
      Bool

    invertedTransferMatrixConstructedIsFalse :
      invertedTransferMatrixConstructed ≡ false

    reflectionPositiveFormChecked :
      Bool

    reflectionPositiveFormCheckedIsFalse :
      reflectionPositiveFormChecked ≡ false

    h0OSPositiveAfterNormalisation :
      Bool

    h0OSPositiveAfterNormalisationIsFalse :
      h0OSPositiveAfterNormalisation ≡ false

    osPositivityInhabitedUnconditionally :
      Bool

    osPositivityInhabitedUnconditionallyIsFalse :
      osPositivityInhabitedUnconditionally ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ normalisedH0BoundaryStatement

    receiptBoundary :
      List String

open NormalisedH0OSPositivityReceipt public

canonicalNormalisedH0OSPositivityReceipt :
  NormalisedH0OSPositivityReceipt
canonicalNormalisedH0OSPositivityReceipt =
  record
    { signConventionReceipt =
        Sign.canonicalH0SignConventionReceipt
    ; signConventionRequiresNormalisation =
        refl
    ; signConventionRequiresInversion =
        refl
    ; branches =
        canonicalNormalisedH0Branches
    ; branchesAreCanonical =
        refl
    ; normalisedTransferMatrixConstructed =
        false
    ; normalisedTransferMatrixConstructedIsFalse =
        refl
    ; invertedTransferMatrixConstructed =
        false
    ; invertedTransferMatrixConstructedIsFalse =
        refl
    ; reflectionPositiveFormChecked =
        false
    ; reflectionPositiveFormCheckedIsFalse =
        refl
    ; h0OSPositiveAfterNormalisation =
        false
    ; h0OSPositiveAfterNormalisationIsFalse =
        refl
    ; osPositivityInhabitedUnconditionally =
        false
    ; osPositivityInhabitedUnconditionallyIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; boundaryStatement =
        normalisedH0BoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; receiptBoundary =
        "This receipt does not rescue the failed raw matrix branch"
        ∷ "It records the two admissible OS transfer-operator branches that must be computed next"
        ∷ "The reflection-positive form, Wightman reconstruction, and Clay promotion remain false"
        ∷ []
    }

normalisedH0StillOpen :
  h0OSPositiveAfterNormalisation canonicalNormalisedH0OSPositivityReceipt
  ≡
  false
normalisedH0StillOpen =
  refl
