module DASHI.Physics.Closure.ZetaK21ComputationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_ ; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23ShimuraApproachReceipt as Shimura

------------------------------------------------------------------------
-- Zeta computation for K = Q(sqrt(21)).
--
-- This receipt records the finite Dirichlet/Bernoulli computation
--
--   zeta_K(-1) = zeta(-1) L(-1, chi_21)
--
-- for the real quadratic field K = Q(sqrt(21)), whose fundamental
-- discriminant is 21.  With conductor f=21 and
--
--   B_2(x) = x^2 - x + 1/6,
--   B_{2,chi} = f * sum_{a=1}^{f} chi(a) B_2(a/f),
--   L(-1,chi) = -B_{2,chi}/2,
--
-- the finite character sums give B_{2,chi_21}=8, hence
-- L(-1,chi_21)=-4 and zeta_K(-1)=1/3.  This is an arithmetic diagnostic
-- only; it does not promote the Shimura/deg23 route or any physical claim.

data K21ZetaComputationStatus : Set where
  k21DirichletBernoulliFiniteSumComputed :
    K21ZetaComputationStatus

chi21NonzeroSupport :
  List Nat
chi21NonzeroSupport =
  1 ∷ 2 ∷ 4 ∷ 5 ∷ 8 ∷ 10 ∷ 11 ∷ 13 ∷ 16 ∷ 17 ∷ 19 ∷ 20 ∷ []

chi21PlusSupport :
  List Nat
chi21PlusSupport =
  1 ∷ 4 ∷ 5 ∷ 16 ∷ 17 ∷ 20 ∷ []

chi21MinusSupport :
  List Nat
chi21MinusSupport =
  2 ∷ 8 ∷ 10 ∷ 11 ∷ 13 ∷ 19 ∷ []

data K21ZetaBlocker : Set where
  shimuraVolumeInterpretationNotDerived :
    K21ZetaBlocker

  deg23PeriodComparisonNotComputed :
    K21ZetaBlocker

  physicalPromotionNotAuthorized :
    K21ZetaBlocker

canonicalK21ZetaBlockers :
  List K21ZetaBlocker
canonicalK21ZetaBlockers =
  shimuraVolumeInterpretationNotDerived
  ∷ deg23PeriodComparisonNotComputed
  ∷ physicalPromotionNotAuthorized
  ∷ []

data K21ZetaPromotion : Set where

k21ZetaPromotionImpossibleHere :
  K21ZetaPromotion →
  ⊥
k21ZetaPromotionImpossibleHere ()

k21FiniteSumFormulaLabel : String
k21FiniteSumFormulaLabel =
  "B_{2,chi_21}=21 * sum_{a=1}^{21} chi_21(a) * B_2(a/21), B_2(x)=x^2-x+1/6"

k21WeightedSquareSumLabel : String
k21WeightedSquareSumLabel =
  "sum chi_21(a)*a^2 over a=1..21 is 168, while sum chi_21(a)=0 and sum chi_21(a)*a=0"

k21ZetaResultLabel : String
k21ZetaResultLabel =
  "zeta_{Q(sqrt(21))}(-1) = zeta(-1)*L(-1,chi_21) = (-1/12)*(-4) = 1/3"

record ZetaK21ComputationReceipt : Setω where
  field
    status :
      K21ZetaComputationStatus

    shimuraContext :
      Shimura.Deg23ShimuraApproachReceipt

    shimuraContextStillDiagnostic :
      Shimura.deg23DerivedHere shimuraContext ≡ false

    fieldLabel :
      String

    fieldLabelIsCanonical :
      fieldLabel ≡ "Q(sqrt(21))"

    fundamentalDiscriminant :
      Nat

    fundamentalDiscriminantIsTwentyOne :
      fundamentalDiscriminant ≡ 21

    dirichletConductor :
      Nat

    dirichletConductorIsTwentyOne :
      dirichletConductor ≡ 21

    nonzeroSupport :
      List Nat

    nonzeroSupportIsCanonical :
      nonzeroSupport ≡ chi21NonzeroSupport

    plusSupport :
      List Nat

    plusSupportIsCanonical :
      plusSupport ≡ chi21PlusSupport

    minusSupport :
      List Nat

    minusSupportIsCanonical :
      minusSupport ≡ chi21MinusSupport

    finiteSumFormula :
      String

    finiteSumFormulaIsCanonical :
      finiteSumFormula ≡ k21FiniteSumFormulaLabel

    chiSumZeroRecorded :
      Bool

    chiSumZeroRecordedIsTrue :
      chiSumZeroRecorded ≡ true

    chiLinearSumZeroRecorded :
      Bool

    chiLinearSumZeroRecordedIsTrue :
      chiLinearSumZeroRecorded ≡ true

    chiWeightedSquareSum :
      Nat

    chiWeightedSquareSumIsOneHundredSixtyEight :
      chiWeightedSquareSum ≡ 168

    weightedSquareSumStatement :
      String

    weightedSquareSumStatementIsCanonical :
      weightedSquareSumStatement ≡ k21WeightedSquareSumLabel

    bernoulliDenominator :
      Nat

    bernoulliDenominatorIsTwentyOne :
      bernoulliDenominator ≡ 21

    generalizedBernoulliNumerator :
      Nat

    generalizedBernoulliNumeratorIsEight :
      generalizedBernoulliNumerator ≡ 8

    generalizedBernoulliValueLabel :
      String

    generalizedBernoulliValueLabelIsCanonical :
      generalizedBernoulliValueLabel ≡ "B_{2,chi_21}=8"

    lMinusOneValueLabel :
      String

    lMinusOneValueLabelIsCanonical :
      lMinusOneValueLabel ≡ "L(-1,chi_21)=-4"

    zetaMinusOneValueLabel :
      String

    zetaMinusOneValueLabelIsCanonical :
      zetaMinusOneValueLabel ≡ "zeta(-1)=-1/12"

    zetaK21MinusOneNumerator :
      Nat

    zetaK21MinusOneNumeratorIsOne :
      zetaK21MinusOneNumerator ≡ 1

    zetaK21MinusOneDenominator :
      Nat

    zetaK21MinusOneDenominatorIsThree :
      zetaK21MinusOneDenominator ≡ 3

    zetaK21MinusOneDecimalMilli :
      Nat

    zetaK21MinusOneDecimalMilliIsAbout333 :
      zetaK21MinusOneDecimalMilli ≡ 333

    zetaResultStatement :
      String

    zetaResultStatementIsCanonical :
      zetaResultStatement ≡ k21ZetaResultLabel

    arithmeticDiagnosticComplete :
      Bool

    arithmeticDiagnosticCompleteIsTrue :
      arithmeticDiagnosticComplete ≡ true

    shimuraVolumeDerived :
      Bool

    shimuraVolumeDerivedIsFalse :
      shimuraVolumeDerived ≡ false

    deg23DerivedFromZeta :
      Bool

    deg23DerivedFromZetaIsFalse :
      deg23DerivedFromZeta ≡ false

    physicalPromotionConstructed :
      Bool

    physicalPromotionConstructedIsFalse :
      physicalPromotionConstructed ≡ false

    blockers :
      List K21ZetaBlocker

    blockersAreCanonical :
      blockers ≡ canonicalK21ZetaBlockers

    promotionFlags :
      List K21ZetaPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ZetaK21ComputationReceipt public

canonicalZetaK21ComputationReceipt :
  ZetaK21ComputationReceipt
canonicalZetaK21ComputationReceipt =
  record
    { status =
        k21DirichletBernoulliFiniteSumComputed
    ; shimuraContext =
        Shimura.canonicalDeg23ShimuraApproachReceipt
    ; shimuraContextStillDiagnostic =
        refl
    ; fieldLabel =
        "Q(sqrt(21))"
    ; fieldLabelIsCanonical =
        refl
    ; fundamentalDiscriminant =
        21
    ; fundamentalDiscriminantIsTwentyOne =
        refl
    ; dirichletConductor =
        21
    ; dirichletConductorIsTwentyOne =
        refl
    ; nonzeroSupport =
        chi21NonzeroSupport
    ; nonzeroSupportIsCanonical =
        refl
    ; plusSupport =
        chi21PlusSupport
    ; plusSupportIsCanonical =
        refl
    ; minusSupport =
        chi21MinusSupport
    ; minusSupportIsCanonical =
        refl
    ; finiteSumFormula =
        k21FiniteSumFormulaLabel
    ; finiteSumFormulaIsCanonical =
        refl
    ; chiSumZeroRecorded =
        true
    ; chiSumZeroRecordedIsTrue =
        refl
    ; chiLinearSumZeroRecorded =
        true
    ; chiLinearSumZeroRecordedIsTrue =
        refl
    ; chiWeightedSquareSum =
        168
    ; chiWeightedSquareSumIsOneHundredSixtyEight =
        refl
    ; weightedSquareSumStatement =
        k21WeightedSquareSumLabel
    ; weightedSquareSumStatementIsCanonical =
        refl
    ; bernoulliDenominator =
        21
    ; bernoulliDenominatorIsTwentyOne =
        refl
    ; generalizedBernoulliNumerator =
        8
    ; generalizedBernoulliNumeratorIsEight =
        refl
    ; generalizedBernoulliValueLabel =
        "B_{2,chi_21}=8"
    ; generalizedBernoulliValueLabelIsCanonical =
        refl
    ; lMinusOneValueLabel =
        "L(-1,chi_21)=-4"
    ; lMinusOneValueLabelIsCanonical =
        refl
    ; zetaMinusOneValueLabel =
        "zeta(-1)=-1/12"
    ; zetaMinusOneValueLabelIsCanonical =
        refl
    ; zetaK21MinusOneNumerator =
        1
    ; zetaK21MinusOneNumeratorIsOne =
        refl
    ; zetaK21MinusOneDenominator =
        3
    ; zetaK21MinusOneDenominatorIsThree =
        refl
    ; zetaK21MinusOneDecimalMilli =
        333
    ; zetaK21MinusOneDecimalMilliIsAbout333 =
        refl
    ; zetaResultStatement =
        k21ZetaResultLabel
    ; zetaResultStatementIsCanonical =
        refl
    ; arithmeticDiagnosticComplete =
        true
    ; arithmeticDiagnosticCompleteIsTrue =
        refl
    ; shimuraVolumeDerived =
        false
    ; shimuraVolumeDerivedIsFalse =
        refl
    ; deg23DerivedFromZeta =
        false
    ; deg23DerivedFromZetaIsFalse =
        refl
    ; physicalPromotionConstructed =
        false
    ; physicalPromotionConstructedIsFalse =
        refl
    ; blockers =
        canonicalK21ZetaBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The Dirichlet/Bernoulli finite sum for K=Q(sqrt(21)) is recorded exactly"
        ∷ "The quadratic character chi_21 has conductor 21 and nonzero support on units modulo 21"
        ∷ "The finite sums give B_{2,chi_21}=8, L(-1,chi_21)=-4, and zeta_K(-1)=1/3"
        ∷ "This is an arithmetic diagnostic only; no Shimura-volume, deg23, CKM, or physical promotion is constructed"
        ∷ []
    }

zetaK21ArithmeticDiagnosticComplete :
  arithmeticDiagnosticComplete canonicalZetaK21ComputationReceipt ≡ true
zetaK21ArithmeticDiagnosticComplete =
  refl

zetaK21MinusOneIsOneThird :
  zetaK21MinusOneNumerator canonicalZetaK21ComputationReceipt ≡ 1
zetaK21MinusOneIsOneThird =
  refl

zetaK21DoesNotPromoteDeg23 :
  deg23DerivedFromZeta canonicalZetaK21ComputationReceipt ≡ false
zetaK21DoesNotPromoteDeg23 =
  refl
