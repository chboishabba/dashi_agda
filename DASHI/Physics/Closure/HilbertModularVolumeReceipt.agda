module DASHI.Physics.Closure.HilbertModularVolumeReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Hilbert modular volume diagnostic for Q(sqrt(21)).
--
-- This receipt records the exact zeta(-1) arithmetic used by the tempting
-- Hilbert-modular-volume route for K=Q(sqrt(21)).  The Dirichlet character is
-- the primitive quadratic character chi_21 of conductor 21.  A finite
-- Bernoulli computation gives
--
--   sum_{a=1}^{21} chi_21(a) B_2(a/21) = 8/21
--   B_{2,chi_21} = 21 * (8/21) = 8
--   L(-1, chi_21) = - B_{2,chi_21} / 2 = -4
--   zeta_Q(-1) = -1/12
--   zeta_K(-1) = zeta_Q(-1) * L(-1, chi_21) = 1/3
--
-- The Hilbert modular volume formula is recorded only as a diagnostic
-- arithmetic surface.  No natural deg23 normalization is derived here and no
-- terminal/physical promotion is asserted.

record SignedRationalDatum : Set where
  constructor signedRationalDatum
  field
    numerator :
      Nat

    denominator :
      Nat

    positive :
      Bool

open SignedRationalDatum public

oneThirdPositive : SignedRationalDatum
oneThirdPositive =
  signedRationalDatum 1 3 true

minusOneTwelfth : SignedRationalDatum
minusOneTwelfth =
  signedRationalDatum 1 12 false

minusFour : SignedRationalDatum
minusFour =
  signedRationalDatum 4 1 false

eightOverTwentyOne : SignedRationalDatum
eightOverTwentyOne =
  signedRationalDatum 8 21 true

eightPositive : SignedRationalDatum
eightPositive =
  signedRationalDatum 8 1 true

data HilbertModularVolumeStatus : Set where
  hilbertVolumeZetaMinusOneDiagnosticRecorded :
    HilbertModularVolumeStatus

data HilbertModularVolumeBlocker : Set where
  noNaturalDeg23NormalizationDerivedHere :
    HilbertModularVolumeBlocker

  missingHilbertVolumeToCarrierDeg23Bridge :
    HilbertModularVolumeBlocker

  missingPhysicalVcbNormalizationAuthority :
    HilbertModularVolumeBlocker

canonicalHilbertModularVolumeBlockers :
  List HilbertModularVolumeBlocker
canonicalHilbertModularVolumeBlockers =
  noNaturalDeg23NormalizationDerivedHere
  ∷ missingHilbertVolumeToCarrierDeg23Bridge
  ∷ missingPhysicalVcbNormalizationAuthority
  ∷ []

data HilbertModularVolumePromotion : Set where

hilbertModularVolumePromotionImpossibleHere :
  HilbertModularVolumePromotion →
  ⊥
hilbertModularVolumePromotionImpossibleHere ()

chi21PositiveResidues : List Nat
chi21PositiveResidues =
  1 ∷ 4 ∷ 5 ∷ 16 ∷ 17 ∷ 20 ∷ []

chi21NegativeResidues : List Nat
chi21NegativeResidues =
  2 ∷ 8 ∷ 10 ∷ 11 ∷ 13 ∷ 19 ∷ []

chi21ZeroResidues : List Nat
chi21ZeroResidues =
  3 ∷ 6 ∷ 7 ∷ 9 ∷ 12 ∷ 14 ∷ 15 ∷ 18 ∷ 21 ∷ []

hilbertVolumeFormulaLabel : String
hilbertVolumeFormulaLabel =
  "Hilbert modular volume for Q(sqrt(21)) is governed by zeta_K(-1); exact normalization to deg23 is not derived here"

chi21BernoulliComputationLabel : String
chi21BernoulliComputationLabel =
  "sum chi_21(a) B2(a/21)=8/21, so B_{2,chi21}=8 and L(-1,chi21)=-4"

zetaKMinusOneLabel : String
zetaKMinusOneLabel =
  "zeta_{Q(sqrt(21))}(-1)=zeta(-1)*L(-1,chi21)=(-1/12)*(-4)=1/3"

record HilbertModularVolumeReceipt : Set where
  field
    status :
      HilbertModularVolumeStatus

    statusIsDiagnosticRecorded :
      status ≡ hilbertVolumeZetaMinusOneDiagnosticRecorded

    fieldLabel :
      String

    fieldLabelIsQsqrt21 :
      fieldLabel ≡ "Q(sqrt(21))"

    discriminant :
      Nat

    discriminantIsTwentyOne :
      discriminant ≡ 21

    chi21Conductor :
      Nat

    chi21ConductorIsTwentyOne :
      chi21Conductor ≡ 21

    chi21PositiveResidueClasses :
      List Nat

    chi21PositiveResidueClassesAreCanonical :
      chi21PositiveResidueClasses ≡ chi21PositiveResidues

    chi21NegativeResidueClasses :
      List Nat

    chi21NegativeResidueClassesAreCanonical :
      chi21NegativeResidueClasses ≡ chi21NegativeResidues

    chi21ZeroResidueClasses :
      List Nat

    chi21ZeroResidueClassesAreCanonical :
      chi21ZeroResidueClasses ≡ chi21ZeroResidues

    finiteBernoulliWeightedSum :
      SignedRationalDatum

    finiteBernoulliWeightedSumIsEightOverTwentyOne :
      finiteBernoulliWeightedSum ≡ eightOverTwentyOne

    generalizedBernoulliB2Chi21 :
      SignedRationalDatum

    generalizedBernoulliB2Chi21IsEight :
      generalizedBernoulliB2Chi21 ≡ eightPositive

    bernoulliComputation :
      String

    bernoulliComputationIsCanonical :
      bernoulliComputation ≡ chi21BernoulliComputationLabel

    zetaMinusOne :
      SignedRationalDatum

    zetaMinusOneIsMinusOneTwelfth :
      zetaMinusOne ≡ minusOneTwelfth

    lMinusOneChi21 :
      SignedRationalDatum

    lMinusOneChi21IsMinusFour :
      lMinusOneChi21 ≡ minusFour

    zetaKMinusOne :
      SignedRationalDatum

    zetaKMinusOneIsOneThird :
      zetaKMinusOne ≡ oneThirdPositive

    zetaKMinusOneStatement :
      String

    zetaKMinusOneStatementIsCanonical :
      zetaKMinusOneStatement ≡ zetaKMinusOneLabel

    volumeFormulaStatus :
      String

    volumeFormulaStatusIsDiagnostic :
      volumeFormulaStatus ≡ hilbertVolumeFormulaLabel

    hilbertVolumeDiagnosticRecorded :
      Bool

    hilbertVolumeDiagnosticRecordedIsTrue :
      hilbertVolumeDiagnosticRecorded ≡ true

    naturalDeg23NormalizationDerived :
      Bool

    naturalDeg23NormalizationDerivedIsFalse :
      naturalDeg23NormalizationDerived ≡ false

    physicalVcbPromoted :
      Bool

    physicalVcbPromotedIsFalse :
      physicalVcbPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalPromotionConstructed :
      Bool

    terminalPromotionConstructedIsFalse :
      terminalPromotionConstructed ≡ false

    blockers :
      List HilbertModularVolumeBlocker

    blockersAreCanonical :
      blockers ≡ canonicalHilbertModularVolumeBlockers

    promotionFlags :
      List HilbertModularVolumePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open HilbertModularVolumeReceipt public

canonicalHilbertModularVolumeReceipt :
  HilbertModularVolumeReceipt
canonicalHilbertModularVolumeReceipt =
  record
    { status =
        hilbertVolumeZetaMinusOneDiagnosticRecorded
    ; statusIsDiagnosticRecorded =
        refl
    ; fieldLabel =
        "Q(sqrt(21))"
    ; fieldLabelIsQsqrt21 =
        refl
    ; discriminant =
        21
    ; discriminantIsTwentyOne =
        refl
    ; chi21Conductor =
        21
    ; chi21ConductorIsTwentyOne =
        refl
    ; chi21PositiveResidueClasses =
        chi21PositiveResidues
    ; chi21PositiveResidueClassesAreCanonical =
        refl
    ; chi21NegativeResidueClasses =
        chi21NegativeResidues
    ; chi21NegativeResidueClassesAreCanonical =
        refl
    ; chi21ZeroResidueClasses =
        chi21ZeroResidues
    ; chi21ZeroResidueClassesAreCanonical =
        refl
    ; finiteBernoulliWeightedSum =
        eightOverTwentyOne
    ; finiteBernoulliWeightedSumIsEightOverTwentyOne =
        refl
    ; generalizedBernoulliB2Chi21 =
        eightPositive
    ; generalizedBernoulliB2Chi21IsEight =
        refl
    ; bernoulliComputation =
        chi21BernoulliComputationLabel
    ; bernoulliComputationIsCanonical =
        refl
    ; zetaMinusOne =
        minusOneTwelfth
    ; zetaMinusOneIsMinusOneTwelfth =
        refl
    ; lMinusOneChi21 =
        minusFour
    ; lMinusOneChi21IsMinusFour =
        refl
    ; zetaKMinusOne =
        oneThirdPositive
    ; zetaKMinusOneIsOneThird =
        refl
    ; zetaKMinusOneStatement =
        zetaKMinusOneLabel
    ; zetaKMinusOneStatementIsCanonical =
        refl
    ; volumeFormulaStatus =
        hilbertVolumeFormulaLabel
    ; volumeFormulaStatusIsDiagnostic =
        refl
    ; hilbertVolumeDiagnosticRecorded =
        true
    ; hilbertVolumeDiagnosticRecordedIsTrue =
        refl
    ; naturalDeg23NormalizationDerived =
        false
    ; naturalDeg23NormalizationDerivedIsFalse =
        refl
    ; physicalVcbPromoted =
        false
    ; physicalVcbPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalPromotionConstructed =
        false
    ; terminalPromotionConstructedIsFalse =
        refl
    ; blockers =
        canonicalHilbertModularVolumeBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "chi_21 has conductor 21 with six positive, six negative, and nine zero residue classes"
        ∷ "finite Bernoulli computation records sum chi_21(a) B2(a/21)=8/21"
        ∷ "therefore L(-1,chi_21)=-4 and zeta_{Q(sqrt(21))}(-1)=1/3"
        ∷ "the Hilbert modular volume formula is recorded as a diagnostic surface only"
        ∷ "no natural deg23 normalization, physical Vcb, physical CKM, or terminal promotion is derived here"
        ∷ []
    }

hilbertModularVolumeZetaKMinusOneIsOneThird :
  zetaKMinusOne canonicalHilbertModularVolumeReceipt ≡ oneThirdPositive
hilbertModularVolumeZetaKMinusOneIsOneThird =
  refl

hilbertModularVolumeNoNaturalDeg23Normalization :
  naturalDeg23NormalizationDerived canonicalHilbertModularVolumeReceipt
  ≡ false
hilbertModularVolumeNoNaturalDeg23Normalization =
  refl
