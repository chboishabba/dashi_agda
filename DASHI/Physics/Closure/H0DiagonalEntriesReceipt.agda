module DASHI.Physics.Closure.H0DiagonalEntriesReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Raw H0 diagonal-entry diagnostic.
--
-- With E_p=-log((p+1)/p), all three diagonal entries are negative.  Therefore
-- the raw matrix cannot be positive semidefinite, before any determinant or
-- off-diagonal analysis is needed.  This receipt resolves the base-case
-- blocker as a sign-convention/normalisation obstruction.

data H0DiagonalEntriesStatus : Set where
  rawDiagonalEntriesObstructPSD :
    H0DiagonalEntriesStatus

data H0PSDObstruction : Set where
  negativeP2PrincipalMinor :
    H0PSDObstruction

  negativeP3PrincipalMinor :
    H0PSDObstruction

  negativeP5PrincipalMinor :
    H0PSDObstruction

  p2p5OffDiagonalStillAmplifiesRawObstruction :
    H0PSDObstruction

canonicalH0PSDObstructions :
  List H0PSDObstruction
canonicalH0PSDObstructions =
  negativeP2PrincipalMinor
  ∷ negativeP3PrincipalMinor
  ∷ negativeP5PrincipalMinor
  ∷ p2p5OffDiagonalStillAmplifiesRawObstruction
  ∷ []

data H0OSPromotion : Set where

h0OSPromotionImpossibleHere :
  H0OSPromotion →
  ⊥
h0OSPromotionImpossibleHere ()

record H0DiagonalEntriesReceipt : Set where
  field
    status :
      H0DiagonalEntriesStatus

    lambdaP2 :
      String

    lambdaP3 :
      String

    lambdaP5 :
      String

    energyP2 :
      String

    energyP3 :
      String

    energyP5 :
      String

    g12 :
      String

    g23 :
      String

    g13 :
      String

    allRawDiagonalsNegative :
      Bool

    allRawDiagonalsNegativeIsTrue :
      allRawDiagonalsNegative ≡ true

    rawOneByOnePrincipalMinorsNonnegative :
      Bool

    rawOneByOnePrincipalMinorsNonnegativeIsFalse :
      rawOneByOnePrincipalMinorsNonnegative ≡ false

    rawH0PositiveSemidefinite :
      Bool

    rawH0PositiveSemidefiniteIsFalse :
      rawH0PositiveSemidefinite ≡ false

    determinantComputationNeededForRawPSD :
      Bool

    determinantComputationNeededForRawPSDIsFalse :
      determinantComputationNeededForRawPSD ≡ false

    signConventionOrNormalisationRequired :
      Bool

    signConventionOrNormalisationRequiredIsTrue :
      signConventionOrNormalisationRequired ≡ true

    h0OSPositivityBaseCase :
      Bool

    h0OSPositivityBaseCaseIsFalse :
      h0OSPositivityBaseCase ≡ false

    obstructions :
      List H0PSDObstruction

    obstructionsAreCanonical :
      obstructions ≡ canonicalH0PSDObstructions

    promotionFlags :
      List H0OSPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open H0DiagonalEntriesReceipt public

canonicalH0DiagonalEntriesReceipt :
  H0DiagonalEntriesReceipt
canonicalH0DiagonalEntriesReceipt =
  record
    { status =
        rawDiagonalEntriesObstructPSD
    ; lambdaP2 =
        "lambda_p2 = |E(F2)|/2 = 3/2"
    ; lambdaP3 =
        "lambda_p3 = |E(F3)|/3 = 4/3"
    ; lambdaP5 =
        "lambda_p5 = |E(F5)|/5 = 6/5"
    ; energyP2 =
        "E_p2 = -log(3/2) = log(2/3) < 0"
    ; energyP3 =
        "E_p3 = -log(4/3) = log(3/4) < 0"
    ; energyP5 =
        "E_p5 = -log(6/5) = log(5/6) < 0"
    ; g12 =
        "g12 = sqrt(3)/2"
    ; g23 =
        "g23 = 14/sqrt(24)"
    ; g13 =
        "g13 = 1/sqrt(2)"
    ; allRawDiagonalsNegative =
        true
    ; allRawDiagonalsNegativeIsTrue =
        refl
    ; rawOneByOnePrincipalMinorsNonnegative =
        false
    ; rawOneByOnePrincipalMinorsNonnegativeIsFalse =
        refl
    ; rawH0PositiveSemidefinite =
        false
    ; rawH0PositiveSemidefiniteIsFalse =
        refl
    ; determinantComputationNeededForRawPSD =
        false
    ; determinantComputationNeededForRawPSDIsFalse =
        refl
    ; signConventionOrNormalisationRequired =
        true
    ; signConventionOrNormalisationRequiredIsTrue =
        refl
    ; h0OSPositivityBaseCase =
        false
    ; h0OSPositivityBaseCaseIsFalse =
        refl
    ; obstructions =
        canonicalH0PSDObstructions
    ; obstructionsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The raw E_p=-log(lambda_p) convention gives negative diagonal entries"
        ∷ "A PSD matrix must have nonnegative one-by-one principal minors"
        ∷ "Therefore raw H0 is not OS-positive before determinant analysis"
        ∷ "A sign convention, inversion, or transfer-matrix normalisation receipt is required next"
        ∷ []
    }

rawH0OSPositivityBaseCaseNotEstablished :
  h0OSPositivityBaseCase canonicalH0DiagonalEntriesReceipt ≡ false
rawH0OSPositivityBaseCaseNotEstablished =
  refl

