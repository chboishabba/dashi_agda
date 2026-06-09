module DASHI.Physics.Closure.YMWilsonCoefficientRGReceipt where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills Wilson coefficient RG receipt.
--
-- This records the dimensional RG bookkeeping for the cusp-induced
-- dimension-6 Yang-Mills deformation.  The UV scale is identified with the
-- cusp scale Lambda_UV ~ N.  Cusp curvature gives c6(Lambda_UV) ~ N^-2.
-- Since the operator has dimension 6 relative to marginal dimension 4, its
-- coefficient runs as c6(mu) ~ (mu / Lambda_UV)^2 c6(Lambda_UV).  At
-- mu = Lambda_QCD this gives c6(Lambda_QCD) ~ Lambda_QCD^2 / N^4.

data YMWilsonCoefficientRGStatus : Set where
  dimensionSixWilsonRGSuppressionRecorded :
    YMWilsonCoefficientRGStatus

data YMWilsonCoefficientRGFact : Set where
  uvScaleIsCuspScaleN :
    YMWilsonCoefficientRGFact

  cuspCurvatureGivesNUVMinusTwo :
    YMWilsonCoefficientRGFact

  dimensionSixOperatorRunsQuadraticallyBelowUV :
    YMWilsonCoefficientRGFact

  qcdScaleCoefficientSuppressedByNFourth :
    YMWilsonCoefficientRGFact

canonicalYMWilsonCoefficientRGFacts :
  List YMWilsonCoefficientRGFact
canonicalYMWilsonCoefficientRGFacts =
  uvScaleIsCuspScaleN
  ∷ cuspCurvatureGivesNUVMinusTwo
  ∷ dimensionSixOperatorRunsQuadraticallyBelowUV
  ∷ qcdScaleCoefficientSuppressedByNFourth
  ∷ []

uvScaleStatement :
  String
uvScaleStatement =
  "Lambda_UV ~ N (cusp scale)."

cuspCurvatureStatement :
  String
cuspCurvatureStatement =
  "c6(Lambda_UV) ~ N^-2 from cusp curvature."

dimensionSixRunningStatement :
  String
dimensionSixRunningStatement =
  "For a dimension-6 operator relative to marginal dimension 4, c6(mu) ~ (mu/Lambda_UV)^2 c6(Lambda_UV)."

qcdScaleStatement :
  String
qcdScaleStatement =
  "At mu = Lambda_QCD, c6(Lambda_QCD) ~ Lambda_QCD^2/N^4."

wilsonCoefficientAtQCDScaleFormula :
  String
wilsonCoefficientAtQCDScaleFormula =
  "Lambda_QCD^2/N^4"

n31TableLabel :
  String
n31TableLabel =
  "N=31 -> about 4e-8"

n100TableLabel :
  String
n100TableLabel =
  "N=100 -> about 4e-10"

record YMWilsonCoefficientRGReceipt : Set where
  field
    status :
      YMWilsonCoefficientRGStatus

    statusIsCanonical :
      status ≡ dimensionSixWilsonRGSuppressionRecorded

    uvScale :
      String

    uvScaleIsCuspScale :
      uvScale ≡ uvScaleStatement

    lambdaUVScalesAsN :
      Bool

    lambdaUVScalesAsNIsTrue :
      lambdaUVScalesAsN ≡ true

    cuspCurvatureInitialCoefficient :
      String

    cuspCurvatureInitialCoefficientIsCanonical :
      cuspCurvatureInitialCoefficient ≡ cuspCurvatureStatement

    c6AtLambdaUVScalesAsNMinusTwo :
      Bool

    c6AtLambdaUVScalesAsNMinusTwoIsTrue :
      c6AtLambdaUVScalesAsNMinusTwo ≡ true

    operatorDimension :
      Nat

    operatorDimensionIsSix :
      operatorDimension ≡ 6

    marginalDimension :
      Nat

    marginalDimensionIsFour :
      marginalDimension ≡ 4

    rgRunningLaw :
      String

    rgRunningLawIsCanonical :
      rgRunningLaw ≡ dimensionSixRunningStatement

    runningPowerRelativeToMarginal :
      Nat

    runningPowerRelativeToMarginalIsTwo :
      runningPowerRelativeToMarginal ≡ 2

    muEqualsLambdaQCD :
      Bool

    muEqualsLambdaQCDIsTrue :
      muEqualsLambdaQCD ≡ true

    wilsonCoefficientAtQCDScale :
      String

    wilsonCoefficientAtQCDScaleIsLambdaQCDSquaredOverNFourth :
      wilsonCoefficientAtQCDScale ≡ wilsonCoefficientAtQCDScaleFormula

    qcdScaleCoefficientStatement :
      String

    qcdScaleCoefficientStatementIsCanonical :
      qcdScaleCoefficientStatement ≡ qcdScaleStatement

    runningSuppressedByN4 :
      Bool

    runningSuppressedByN4IsTrue :
      runningSuppressedByN4 ≡ true

    runningSuppressedByN^4 :
      Bool

    runningSuppressedByN^4IsTrue :
      runningSuppressedByN^4 ≡ true

    n31 :
      Nat

    n31IsThirtyOne :
      n31 ≡ 31

    n31CoefficientApprox :
      Float

    n31CoefficientApproxLabel :
      String

    n31CoefficientApproxLabelIsCanonical :
      n31CoefficientApproxLabel ≡ n31TableLabel

    n100 :
      Nat

    n100IsOneHundred :
      n100 ≡ 100

    n100CoefficientApprox :
      Float

    n100CoefficientApproxLabel :
      String

    n100CoefficientApproxLabelIsCanonical :
      n100CoefficientApproxLabel ≡ n100TableLabel

    facts :
      List YMWilsonCoefficientRGFact

    factsAreCanonical :
      facts ≡ canonicalYMWilsonCoefficientRGFacts

    receiptBoundary :
      List String

open YMWilsonCoefficientRGReceipt public

canonicalYMWilsonCoefficientRGReceipt :
  YMWilsonCoefficientRGReceipt
canonicalYMWilsonCoefficientRGReceipt =
  record
    { status =
        dimensionSixWilsonRGSuppressionRecorded
    ; statusIsCanonical =
        refl
    ; uvScale =
        uvScaleStatement
    ; uvScaleIsCuspScale =
        refl
    ; lambdaUVScalesAsN =
        true
    ; lambdaUVScalesAsNIsTrue =
        refl
    ; cuspCurvatureInitialCoefficient =
        cuspCurvatureStatement
    ; cuspCurvatureInitialCoefficientIsCanonical =
        refl
    ; c6AtLambdaUVScalesAsNMinusTwo =
        true
    ; c6AtLambdaUVScalesAsNMinusTwoIsTrue =
        refl
    ; operatorDimension =
        6
    ; operatorDimensionIsSix =
        refl
    ; marginalDimension =
        4
    ; marginalDimensionIsFour =
        refl
    ; rgRunningLaw =
        dimensionSixRunningStatement
    ; rgRunningLawIsCanonical =
        refl
    ; runningPowerRelativeToMarginal =
        2
    ; runningPowerRelativeToMarginalIsTwo =
        refl
    ; muEqualsLambdaQCD =
        true
    ; muEqualsLambdaQCDIsTrue =
        refl
    ; wilsonCoefficientAtQCDScale =
        wilsonCoefficientAtQCDScaleFormula
    ; wilsonCoefficientAtQCDScaleIsLambdaQCDSquaredOverNFourth =
        refl
    ; qcdScaleCoefficientStatement =
        qcdScaleStatement
    ; qcdScaleCoefficientStatementIsCanonical =
        refl
    ; runningSuppressedByN4 =
        true
    ; runningSuppressedByN4IsTrue =
        refl
    ; runningSuppressedByN^4 =
        true
    ; runningSuppressedByN^4IsTrue =
        refl
    ; n31 =
        31
    ; n31IsThirtyOne =
        refl
    ; n31CoefficientApprox =
        0.00000004
    ; n31CoefficientApproxLabel =
        n31TableLabel
    ; n31CoefficientApproxLabelIsCanonical =
        refl
    ; n100 =
        100
    ; n100IsOneHundred =
        refl
    ; n100CoefficientApprox =
        0.0000000004
    ; n100CoefficientApproxLabel =
        n100TableLabel
    ; n100CoefficientApproxLabelIsCanonical =
        refl
    ; facts =
        canonicalYMWilsonCoefficientRGFacts
    ; factsAreCanonical =
        refl
    ; receiptBoundary =
        uvScaleStatement
        ∷ cuspCurvatureStatement
        ∷ dimensionSixRunningStatement
        ∷ qcdScaleStatement
        ∷ n31TableLabel
        ∷ n100TableLabel
        ∷ []
    }

wilsonCoefficientAtQCDScaleFlag :
  wilsonCoefficientAtQCDScale canonicalYMWilsonCoefficientRGReceipt
  ≡
  "Lambda_QCD^2/N^4"
wilsonCoefficientAtQCDScaleFlag =
  refl

runningSuppressedByN4Flag :
  runningSuppressedByN4 canonicalYMWilsonCoefficientRGReceipt
  ≡
  true
runningSuppressedByN4Flag =
  refl

runningSuppressedByN^4Flag :
  runningSuppressedByN^4 canonicalYMWilsonCoefficientRGReceipt
  ≡
  true
runningSuppressedByN^4Flag =
  refl

n31CoefficientTableFlag :
  n31CoefficientApproxLabel canonicalYMWilsonCoefficientRGReceipt
  ≡
  "N=31 -> about 4e-8"
n31CoefficientTableFlag =
  refl

n100CoefficientTableFlag :
  n100CoefficientApproxLabel canonicalYMWilsonCoefficientRGReceipt
  ≡
  "N=100 -> about 4e-10"
n100CoefficientTableFlag =
  refl
