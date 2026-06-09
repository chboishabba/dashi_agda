module DASHI.Physics.Closure.H0ExplicitMatrixReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.H0OSPositivityBaseCase as H0Selected

data H0ExplicitMatrixStatus : Set where
  rawLogTransferMatrixNotPSD : H0ExplicitMatrixStatus

data H0ExplicitMatrixObstruction : Set where
  negativeRawDiagonalConvention : H0ExplicitMatrixObstruction
  rawP2P3MinorNegative : H0ExplicitMatrixObstruction
  rawP2P5MinorNegative : H0ExplicitMatrixObstruction
  rawP3P5MinorNegative : H0ExplicitMatrixObstruction
  rawP2P5CouplingIncluded : H0ExplicitMatrixObstruction

canonicalH0ExplicitMatrixObstructions :
  List H0ExplicitMatrixObstruction
canonicalH0ExplicitMatrixObstructions =
  negativeRawDiagonalConvention
  ∷ rawP2P3MinorNegative
  ∷ rawP2P5MinorNegative
  ∷ rawP3P5MinorNegative
  ∷ rawP2P5CouplingIncluded
  ∷ []

h0RawMatrixLabel : String
h0RawMatrixLabel =
  "diag(log(2/3),log(3/4),log(5/6)); offdiag(sqrt(3)/2,1/sqrt(2),14/sqrt(24))"

h0RawMinorDiagnosticLabel : String
h0RawMinorDiagnosticLabel =
  "principal minors: M12=-0.6333549574, M13=-0.4260749703, M23=-8.1142160234; determinant=+7.0706136809"

record H0ExplicitMatrixReceipt : Setω where
  field
    selectedBaseCaseReceipt :
      H0Selected.H0OSPositivityBaseCaseReceipt

    selectedBaseCaseStillOpen :
      H0Selected.h0OSPositivityBaseCaseInhabited selectedBaseCaseReceipt
      ≡
      false

    status :
      H0ExplicitMatrixStatus

    rawMatrixStatement :
      String

    rawMatrixStatementIsCanonical :
      rawMatrixStatement ≡ h0RawMatrixLabel

    rawMinorDiagnostic :
      String

    rawMinorDiagnosticIsCanonical :
      rawMinorDiagnostic ≡ h0RawMinorDiagnosticLabel

    p2p3PrincipalMinorNonNegative :
      Bool

    p2p3PrincipalMinorNonNegativeIsFalse :
      p2p3PrincipalMinorNonNegative ≡ false

    p2p5PrincipalMinorNonNegative :
      Bool

    p2p5PrincipalMinorNonNegativeIsFalse :
      p2p5PrincipalMinorNonNegative ≡ false

    p3p5PrincipalMinorNonNegative :
      Bool

    p3p5PrincipalMinorNonNegativeIsFalse :
      p3p5PrincipalMinorNonNegative ≡ false

    determinantNonNegativeInRawConvention :
      Bool

    determinantNonNegativeInRawConventionIsTrue :
      determinantNonNegativeInRawConvention ≡ true

    rawMatrixPositiveSemidefinite :
      Bool

    rawMatrixPositiveSemidefiniteIsFalse :
      rawMatrixPositiveSemidefinite ≡ false

    h0OSPositivityFalseForRawMatrix :
      Bool

    h0OSPositivityFalseForRawMatrixIsTrue :
      h0OSPositivityFalseForRawMatrix ≡ true

    osPositivityInhabitedUnconditionally :
      Bool

    osPositivityInhabitedUnconditionallyIsFalse :
      osPositivityInhabitedUnconditionally ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    obstructions :
      List H0ExplicitMatrixObstruction

    obstructionsAreCanonical :
      obstructions ≡ canonicalH0ExplicitMatrixObstructions

    receiptBoundary :
      List String

open H0ExplicitMatrixReceipt public

canonicalH0ExplicitMatrixReceipt :
  H0ExplicitMatrixReceipt
canonicalH0ExplicitMatrixReceipt =
  record
    { selectedBaseCaseReceipt =
        H0Selected.canonicalH0OSPositivityBaseCaseReceipt
    ; selectedBaseCaseStillOpen =
        refl
    ; status =
        rawLogTransferMatrixNotPSD
    ; rawMatrixStatement =
        h0RawMatrixLabel
    ; rawMatrixStatementIsCanonical =
        refl
    ; rawMinorDiagnostic =
        h0RawMinorDiagnosticLabel
    ; rawMinorDiagnosticIsCanonical =
        refl
    ; p2p3PrincipalMinorNonNegative =
        false
    ; p2p3PrincipalMinorNonNegativeIsFalse =
        refl
    ; p2p5PrincipalMinorNonNegative =
        false
    ; p2p5PrincipalMinorNonNegativeIsFalse =
        refl
    ; p3p5PrincipalMinorNonNegative =
        false
    ; p3p5PrincipalMinorNonNegativeIsFalse =
        refl
    ; determinantNonNegativeInRawConvention =
        true
    ; determinantNonNegativeInRawConventionIsTrue =
        refl
    ; rawMatrixPositiveSemidefinite =
        false
    ; rawMatrixPositiveSemidefiniteIsFalse =
        refl
    ; h0OSPositivityFalseForRawMatrix =
        true
    ; h0OSPositivityFalseForRawMatrixIsTrue =
        refl
    ; osPositivityInhabitedUnconditionally =
        false
    ; osPositivityInhabitedUnconditionallyIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; obstructions =
        canonicalH0ExplicitMatrixObstructions
    ; obstructionsAreCanonical =
        refl
    ; receiptBoundary =
        "The requested raw H0 matrix is not PSD because all three 2x2 principal minors are negative"
        ∷ "This resolves the raw base-case branch negatively; it does not disprove a differently normalised OS transfer-matrix branch"
        ∷ "OS positivity, Wightman reconstruction, and Clay Yang-Mills promotion remain false"
        ∷ []
    }

h0ExplicitRawMatrixNotPSD :
  rawMatrixPositiveSemidefinite canonicalH0ExplicitMatrixReceipt ≡ false
h0ExplicitRawMatrixNotPSD =
  refl

h0ExplicitRawMatrixDoesNotPromoteClay :
  clayYangMillsPromoted canonicalH0ExplicitMatrixReceipt ≡ false
h0ExplicitRawMatrixDoesNotPromoteClay =
  refl
