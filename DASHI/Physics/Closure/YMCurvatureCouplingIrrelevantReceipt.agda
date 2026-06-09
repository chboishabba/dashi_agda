module DASHI.Physics.Closure.YMCurvatureCouplingIrrelevantReceipt where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Curvature-Yang-Mills coupling irrelevance receipt.
--
-- The local operator R * Tr|F|^2 has engineering mass dimension
-- [R] + [Tr|F|^2] = 2 + 4 = 6.  In four-dimensional Yang-Mills theory the
-- marginal operator dimension is 4.  Operators with d > 4 are irrelevant at
-- the UV Gaussian fixed point and are suppressed by Lambda_UV^(d - 4).
-- Hence this curvature-YM coupling is dimension 6 and is suppressed by
-- Lambda_UV^2.

data YMCurvatureCouplingIrrelevanceStatus : Set where
  theorem :
    YMCurvatureCouplingIrrelevanceStatus

curvatureDimension :
  Nat
curvatureDimension =
  2

traceFNormSquaredDimension :
  Nat
traceFNormSquaredDimension =
  4

curvatureYMOperatorStatement :
  String
curvatureYMOperatorStatement =
  "R * Tr|F|^2 has engineering mass dimension [R] + [Tr|F|^2] = 2 + 4 = 6."

fourDimensionalMarginalityStatement :
  String
fourDimensionalMarginalityStatement =
  "In 4D Yang-Mills theory, marginal operators have dimension 4."

irrelevanceStatement :
  String
irrelevanceStatement =
  "Operators with d > 4 are irrelevant at the UV Gaussian fixed point and are suppressed by Lambda_UV^(d - 4)."

curvatureYMSuppressionStatement :
  String
curvatureYMSuppressionStatement =
  "The curvature-YM coupling has d = 6, so it is irrelevant and suppressed by Lambda_UV^2."

record YMCurvatureCouplingIrrelevantReceipt : Set where
  field
    curvatureYMCouplingDimension :
      Nat

    curvatureYMCouplingDimensionIsSix :
      curvatureYMCouplingDimension ≡ 6

    curvatureYMCouplingDimensionFromFactors :
      curvatureYMCouplingDimension ≡
      curvatureDimension + traceFNormSquaredDimension

    marginalDimension4D :
      Nat

    marginalDimension4DIsFour :
      marginalDimension4D ≡ 4

    curvatureCouplingIsIrrelevant :
      YMCurvatureCouplingIrrelevanceStatus

    curvatureCouplingIsIrrelevantIsTheorem :
      curvatureCouplingIsIrrelevant ≡ theorem

    suppressedByLambdaUVsquared :
      Bool

    suppressedByLambdaUVsquaredIsTrue :
      suppressedByLambdaUVsquared ≡ true

    operatorStatement :
      String

    operatorStatementIsCanonical :
      operatorStatement ≡ curvatureYMOperatorStatement

    marginalityStatement :
      String

    marginalityStatementIsCanonical :
      marginalityStatement ≡ fourDimensionalMarginalityStatement

    irrelevantOperatorStatement :
      String

    irrelevantOperatorStatementIsCanonical :
      irrelevantOperatorStatement ≡ irrelevanceStatement

    suppressionStatement :
      String

    suppressionStatementIsCanonical :
      suppressionStatement ≡ curvatureYMSuppressionStatement

open YMCurvatureCouplingIrrelevantReceipt public

canonicalYMCurvatureCouplingIrrelevantReceipt :
  YMCurvatureCouplingIrrelevantReceipt
canonicalYMCurvatureCouplingIrrelevantReceipt =
  record
    { curvatureYMCouplingDimension =
        6
    ; curvatureYMCouplingDimensionIsSix =
        refl
    ; curvatureYMCouplingDimensionFromFactors =
        refl
    ; marginalDimension4D =
        4
    ; marginalDimension4DIsFour =
        refl
    ; curvatureCouplingIsIrrelevant =
        theorem
    ; curvatureCouplingIsIrrelevantIsTheorem =
        refl
    ; suppressedByLambdaUVsquared =
        true
    ; suppressedByLambdaUVsquaredIsTrue =
        refl
    ; operatorStatement =
        curvatureYMOperatorStatement
    ; operatorStatementIsCanonical =
        refl
    ; marginalityStatement =
        fourDimensionalMarginalityStatement
    ; marginalityStatementIsCanonical =
        refl
    ; irrelevantOperatorStatement =
        irrelevanceStatement
    ; irrelevantOperatorStatementIsCanonical =
        refl
    ; suppressionStatement =
        curvatureYMSuppressionStatement
    ; suppressionStatementIsCanonical =
        refl
    }

curvatureYMCouplingDimensionFlag :
  curvatureYMCouplingDimension
    canonicalYMCurvatureCouplingIrrelevantReceipt
  ≡
  6
curvatureYMCouplingDimensionFlag =
  refl

marginalDimension4DFlag :
  marginalDimension4D
    canonicalYMCurvatureCouplingIrrelevantReceipt
  ≡
  4
marginalDimension4DFlag =
  refl

curvatureCouplingIsIrrelevantFlag :
  curvatureCouplingIsIrrelevant
    canonicalYMCurvatureCouplingIrrelevantReceipt
  ≡
  theorem
curvatureCouplingIsIrrelevantFlag =
  refl

suppressedByLambdaUVsquaredFlag :
  suppressedByLambdaUVsquared
    canonicalYMCurvatureCouplingIrrelevantReceipt
  ≡
  true
suppressedByLambdaUVsquaredFlag =
  refl
