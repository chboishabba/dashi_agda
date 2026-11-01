module DASHI.Physics.QFT.SpinorRepresentationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Characteristic-2 spinor-representation receipt.
--
-- This receipt records the elementary toy representation S = F2^2 of
-- Cl(1,1) ~= M2(F2).  The visible gamma0 * gamma1 statistics operator is the
-- swap matrix on the two F2 coordinates.  Because characteristic 2 collapses
-- -1 to +1, this surface does not derive a physical fermion sign.  Any
-- fermionic statistics theorem must lift out of characteristic 2.

data F2 : Set where
  f0 :
    F2

  f1 :
    F2

data F2Vector2 : Set where
  f2vec :
    F2 →
    F2 →
    F2Vector2

record F2Matrix2 : Set where
  constructor matrix2
  field
    a00 :
      F2

    a01 :
      F2

    a10 :
      F2

    a11 :
      F2

open F2Matrix2 public

f2Zero :
  F2
f2Zero =
  f0

f2One :
  F2
f2One =
  f1

spinorModuleF2SquaredLabel : String
spinorModuleF2SquaredLabel =
  "S = F2^2"

cliffordAlgebraM2F2Label : String
cliffordAlgebraM2F2Label =
  "Cl(1,1) over F2 is recorded as M2(F2)"

gamma0Matrix :
  F2Matrix2
gamma0Matrix =
  matrix2 f0 f1 f1 f0

gamma1Matrix :
  F2Matrix2
gamma1Matrix =
  matrix2 f1 f0 f0 f1

swapMatrix :
  F2Matrix2
swapMatrix =
  matrix2 f0 f1 f1 f0

statisticsOperatorLabel : String
statisticsOperatorLabel =
  "gamma0 * gamma1 is the coordinate-swap matrix over F2"

char2NoMinusOneBoundary : String
char2NoMinusOneBoundary =
  "In characteristic 2, -1 = 1, so the swap carries no fermion sign"

record SpinorRepresentationReceipt : Setω where
  field
    spinorModule :
      String

    spinorModuleIsF2Squared :
      spinorModule ≡ spinorModuleF2SquaredLabel

    cliffordAlgebra :
      String

    cliffordAlgebraIsM2F2 :
      cliffordAlgebra ≡ cliffordAlgebraM2F2Label

    gamma0 :
      F2Matrix2

    gamma0IsSwapMatrix :
      gamma0 ≡ swapMatrix

    gamma1 :
      F2Matrix2

    gamma1IsIdentityMatrix :
      gamma1 ≡ matrix2 f1 f0 f0 f1

    statisticsOperator :
      F2Matrix2

    statisticsOperatorIsGamma0Gamma1Swap :
      statisticsOperator ≡ swapMatrix

    statisticsOperatorDescription :
      String

    statisticsOperatorDescriptionIsCanonical :
      statisticsOperatorDescription ≡ statisticsOperatorLabel

    characteristicTwoMinusOneEqualsOne :
      Bool

    characteristicTwoMinusOneEqualsOneIsTrue :
      characteristicTwoMinusOneEqualsOne ≡ true

    noFermionSignBoundary :
      String

    noFermionSignBoundaryIsCanonical :
      noFermionSignBoundary ≡ char2NoMinusOneBoundary

    spinorRepresentationRecorded :
      Bool

    spinorRepresentationRecordedIsTrue :
      spinorRepresentationRecorded ≡ true

    char2CliffordHasNoFermionSign :
      Bool

    char2CliffordHasNoFermionSignIsTrue :
      char2CliffordHasNoFermionSign ≡ true

    cliffordLiftToCharZeroRequired :
      Bool

    cliffordLiftToCharZeroRequiredIsTrue :
      cliffordLiftToCharZeroRequired ≡ true

    fermionicStatisticsDerived :
      Bool

    fermionicStatisticsDerivedIsFalse :
      fermionicStatisticsDerived ≡ false

    exactSMGDHRPromotion :
      Bool

    exactSMGDHRPromotionIsFalse :
      exactSMGDHRPromotion ≡ false

    receiptBoundary :
      List String

open SpinorRepresentationReceipt public

canonicalSpinorRepresentationReceipt :
  SpinorRepresentationReceipt
canonicalSpinorRepresentationReceipt =
  record
    { spinorModule =
        spinorModuleF2SquaredLabel
    ; spinorModuleIsF2Squared =
        refl
    ; cliffordAlgebra =
        cliffordAlgebraM2F2Label
    ; cliffordAlgebraIsM2F2 =
        refl
    ; gamma0 =
        swapMatrix
    ; gamma0IsSwapMatrix =
        refl
    ; gamma1 =
        matrix2 f1 f0 f0 f1
    ; gamma1IsIdentityMatrix =
        refl
    ; statisticsOperator =
        swapMatrix
    ; statisticsOperatorIsGamma0Gamma1Swap =
        refl
    ; statisticsOperatorDescription =
        statisticsOperatorLabel
    ; statisticsOperatorDescriptionIsCanonical =
        refl
    ; characteristicTwoMinusOneEqualsOne =
        true
    ; characteristicTwoMinusOneEqualsOneIsTrue =
        refl
    ; noFermionSignBoundary =
        char2NoMinusOneBoundary
    ; noFermionSignBoundaryIsCanonical =
        refl
    ; spinorRepresentationRecorded =
        true
    ; spinorRepresentationRecordedIsTrue =
        refl
    ; char2CliffordHasNoFermionSign =
        true
    ; char2CliffordHasNoFermionSignIsTrue =
        refl
    ; cliffordLiftToCharZeroRequired =
        true
    ; cliffordLiftToCharZeroRequiredIsTrue =
        refl
    ; fermionicStatisticsDerived =
        false
    ; fermionicStatisticsDerivedIsFalse =
        refl
    ; exactSMGDHRPromotion =
        false
    ; exactSMGDHRPromotionIsFalse =
        refl
    ; receiptBoundary =
        "S = F2^2 is recorded as the characteristic-2 spinor representation"
        ∷ "Cl(1,1) over F2 is recorded as M2(F2)"
        ∷ "gamma0 * gamma1 is the swap matrix on the two F2 coordinates"
        ∷ "Characteristic 2 has -1 = 1, so this receipt derives no fermion sign"
        ∷ "A characteristic-zero Clifford lift is required before fermionic statistics can be claimed"
        ∷ "Exact Standard Model / G_DHR promotion remains false"
        ∷ []
    }

spinorRepresentationRecordedIsCanonicalTrue :
  SpinorRepresentationReceipt.spinorRepresentationRecorded
    canonicalSpinorRepresentationReceipt
  ≡
  true
spinorRepresentationRecordedIsCanonicalTrue =
  SpinorRepresentationReceipt.spinorRepresentationRecordedIsTrue
    canonicalSpinorRepresentationReceipt

char2CliffordHasNoFermionSignIsCanonicalTrue :
  SpinorRepresentationReceipt.char2CliffordHasNoFermionSign
    canonicalSpinorRepresentationReceipt
  ≡
  true
char2CliffordHasNoFermionSignIsCanonicalTrue =
  SpinorRepresentationReceipt.char2CliffordHasNoFermionSignIsTrue
    canonicalSpinorRepresentationReceipt

cliffordLiftToCharZeroRequiredIsCanonicalTrue :
  SpinorRepresentationReceipt.cliffordLiftToCharZeroRequired
    canonicalSpinorRepresentationReceipt
  ≡
  true
cliffordLiftToCharZeroRequiredIsCanonicalTrue =
  SpinorRepresentationReceipt.cliffordLiftToCharZeroRequiredIsTrue
    canonicalSpinorRepresentationReceipt

fermionicStatisticsDerivedIsCanonicalFalse :
  SpinorRepresentationReceipt.fermionicStatisticsDerived
    canonicalSpinorRepresentationReceipt
  ≡
  false
fermionicStatisticsDerivedIsCanonicalFalse =
  SpinorRepresentationReceipt.fermionicStatisticsDerivedIsFalse
    canonicalSpinorRepresentationReceipt

exactSMGDHRPromotionFalse :
  SpinorRepresentationReceipt.exactSMGDHRPromotion
    canonicalSpinorRepresentationReceipt
  ≡
  false
exactSMGDHRPromotionFalse =
  SpinorRepresentationReceipt.exactSMGDHRPromotionIsFalse
    canonicalSpinorRepresentationReceipt
