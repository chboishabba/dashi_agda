module DASHI.Physics.Closure.H0SignConventionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.H0ExplicitMatrixReceipt as H0Raw

data H0SignConventionStatus : Set where
  rawTransferEigenvaluesRequireOSRenormalisation :
    H0SignConventionStatus

data H0SignConventionResolutionTarget : Set where
  useOSContractiveTransferOperator :
    H0SignConventionResolutionTarget

  useInvertedTransferOperator :
    H0SignConventionResolutionTarget

canonicalH0SignTargets :
  List H0SignConventionResolutionTarget
canonicalH0SignTargets =
  useOSContractiveTransferOperator
  ∷ useInvertedTransferOperator
  ∷ []

h0SignConventionStatement : String
h0SignConventionStatement =
  "Raw lambda_p=(p+1)/p exceeds 1, so H=-log(lambda_p)/a is negative; an OS transfer operator must be contractive or inverted before a positivity claim."

record H0SignConventionReceipt : Setω where
  field
    rawMatrixReceipt :
      H0Raw.H0ExplicitMatrixReceipt

    rawMatrixNotPSD :
      H0Raw.rawMatrixPositiveSemidefinite rawMatrixReceipt ≡ false

    status :
      H0SignConventionStatus

    signConventionStatement :
      String

    signConventionStatementIsCanonical :
      signConventionStatement ≡ h0SignConventionStatement

    rawLambdaGreaterThanOneRecorded :
      Bool

    rawLambdaGreaterThanOneRecordedIsTrue :
      rawLambdaGreaterThanOneRecorded ≡ true

    rawHamiltonianEnergiesNegative :
      Bool

    rawHamiltonianEnergiesNegativeIsTrue :
      rawHamiltonianEnergiesNegative ≡ true

    h0NormalisationRequired :
      Bool

    h0NormalisationRequiredIsTrue :
      h0NormalisationRequired ≡ true

    h0InversionRequiredForOS :
      Bool

    h0InversionRequiredForOSIsTrue :
      h0InversionRequiredForOS ≡ true

    normalisedOrInvertedOSMatrixChecked :
      Bool

    normalisedOrInvertedOSMatrixCheckedIsFalse :
      normalisedOrInvertedOSMatrixChecked ≡ false

    osPositivityInhabitedUnconditionally :
      Bool

    osPositivityInhabitedUnconditionallyIsFalse :
      osPositivityInhabitedUnconditionally ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    resolutionTargets :
      List H0SignConventionResolutionTarget

    resolutionTargetsAreCanonical :
      resolutionTargets ≡ canonicalH0SignTargets

    receiptBoundary :
      List String

open H0SignConventionReceipt public

canonicalH0SignConventionReceipt :
  H0SignConventionReceipt
canonicalH0SignConventionReceipt =
  record
    { rawMatrixReceipt =
        H0Raw.canonicalH0ExplicitMatrixReceipt
    ; rawMatrixNotPSD =
        refl
    ; status =
        rawTransferEigenvaluesRequireOSRenormalisation
    ; signConventionStatement =
        h0SignConventionStatement
    ; signConventionStatementIsCanonical =
        refl
    ; rawLambdaGreaterThanOneRecorded =
        true
    ; rawLambdaGreaterThanOneRecordedIsTrue =
        refl
    ; rawHamiltonianEnergiesNegative =
        true
    ; rawHamiltonianEnergiesNegativeIsTrue =
        refl
    ; h0NormalisationRequired =
        true
    ; h0NormalisationRequiredIsTrue =
        refl
    ; h0InversionRequiredForOS =
        true
    ; h0InversionRequiredForOSIsTrue =
        refl
    ; normalisedOrInvertedOSMatrixChecked =
        false
    ; normalisedOrInvertedOSMatrixCheckedIsFalse =
        refl
    ; osPositivityInhabitedUnconditionally =
        false
    ; osPositivityInhabitedUnconditionallyIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; resolutionTargets =
        canonicalH0SignTargets
    ; resolutionTargetsAreCanonical =
        refl
    ; receiptBoundary =
        "The raw transfer eigenvalues are not contractive in the OS convention"
        ∷ "The raw H=-log(T)/a branch has negative lane energies and failed the PSD check"
        ∷ "A normalized or inverted transfer-operator branch is now the admissible next finite computation"
        ∷ []
    }

h0SignConventionRequiresNormalisation :
  h0NormalisationRequired canonicalH0SignConventionReceipt ≡ true
h0SignConventionRequiresNormalisation =
  refl
