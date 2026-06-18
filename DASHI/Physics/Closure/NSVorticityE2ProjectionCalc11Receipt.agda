module DASHI.Physics.Closure.NSVorticityE2ProjectionCalc11Receipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Calc 11 vorticity-to-e2 projection receipt.
--
-- This module records the exact diagnostic shape only.  It is candidate-
-- only and non-promoting: omega is computed as curl u; the strain
-- eigenframe is recorded as e1/e2/e3; the boundary-layer diagnostic
-- fraction is omega_e2_fraction = |<omega,e2>|^2 / |omega|^2; and the
-- recorded outputs are mean, max, layer_cell_count, and min_g12.
-- No Clay promotion is made.

data NSVorticityE2ProjectionCalc11Status : Set where
  candidateOnlyNonPromoting :
    NSVorticityE2ProjectionCalc11Status

data NSVorticityE2ProjectionCalc11Shape : Set where
  omegaEqualsCurlURecorded :
    NSVorticityE2ProjectionCalc11Shape
  strainEigenframeE1E2E3Recorded :
    NSVorticityE2ProjectionCalc11Shape
  omegaE2FractionBoundaryLayerRecorded :
    NSVorticityE2ProjectionCalc11Shape
  meanOutputRecorded :
    NSVorticityE2ProjectionCalc11Shape
  maxOutputRecorded :
    NSVorticityE2ProjectionCalc11Shape
  layerCellCountRecorded :
    NSVorticityE2ProjectionCalc11Shape
  minG12Recorded :
    NSVorticityE2ProjectionCalc11Shape
  decisionInterpretationsRecorded :
    NSVorticityE2ProjectionCalc11Shape
  noClayPromotionRecorded :
    NSVorticityE2ProjectionCalc11Shape

canonicalNSVorticityE2ProjectionCalc11Shape :
  List NSVorticityE2ProjectionCalc11Shape
canonicalNSVorticityE2ProjectionCalc11Shape =
  omegaEqualsCurlURecorded
  ∷ strainEigenframeE1E2E3Recorded
  ∷ omegaE2FractionBoundaryLayerRecorded
  ∷ meanOutputRecorded
  ∷ maxOutputRecorded
  ∷ layerCellCountRecorded
  ∷ minG12Recorded
  ∷ decisionInterpretationsRecorded
  ∷ noClayPromotionRecorded
  ∷ []

omegaFormulaText : String
omegaFormulaText = "omega = curl u"

strainEigenframeText : String
strainEigenframeText = "strain eigenvectors e1/e2/e3"

omegaE2FractionText : String
omegaE2FractionText =
  "omega_e2_fraction = |<omega,e2>|^2 / |omega|^2 on the boundary layer"

calc11OutputNamesText : List String
calc11OutputNamesText =
  "mean"
  ∷ "max"
  ∷ "layer_cell_count"
  ∷ "min_g12"
  ∷ []

calc11DecisionInterpretationsText : List String
calc11DecisionInterpretationsText =
  "candidate-only boundary-layer diagnostic"
  ∷ "non-promoting evidence lane only"
  ∷ "no Clay promotion follows"
  ∷ []

noClayPromotionText : String
noClayPromotionText = "No Clay promotion is made."

record NSVorticityE2ProjectionCalc11Receipt : Set where
  constructor mkNSVorticityE2ProjectionCalc11Receipt
  field
    status : NSVorticityE2ProjectionCalc11Status
    statusIsCanonical :
      status ≡ candidateOnlyNonPromoting

    diagnosticShape :
      List NSVorticityE2ProjectionCalc11Shape
    diagnosticShapeIsCanonical :
      diagnosticShape ≡ canonicalNSVorticityE2ProjectionCalc11Shape

    omegaFormula :
      String
    omegaFormulaIsCanonical :
      omegaFormula ≡ omegaFormulaText

    strainEigenframe :
      String
    strainEigenframeIsCanonical :
      strainEigenframe ≡ strainEigenframeText

    omegaE2Fraction :
      String
    omegaE2FractionIsCanonical :
      omegaE2Fraction ≡ omegaE2FractionText

    outputNames :
      List String
    outputNamesIsCanonical :
      outputNames ≡ calc11OutputNamesText

    mean :
      String
    meanIsCanonical :
      mean ≡ "candidate-only mean placeholder"

    max :
      String
    maxIsCanonical :
      max ≡ "candidate-only max placeholder"

    decisionInterpretations :
      List String
    decisionInterpretationsIsCanonical :
      decisionInterpretations ≡ calc11DecisionInterpretationsText

    layerCellCount :
      Nat

    minG12 :
      String

    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

    noClayPromotion :
      String
    noClayPromotionIsCanonical :
      noClayPromotion ≡ noClayPromotionText

open NSVorticityE2ProjectionCalc11Receipt public

canonicalNSVorticityE2ProjectionCalc11Receipt :
  NSVorticityE2ProjectionCalc11Receipt
canonicalNSVorticityE2ProjectionCalc11Receipt =
  mkNSVorticityE2ProjectionCalc11Receipt
    candidateOnlyNonPromoting
    refl
    canonicalNSVorticityE2ProjectionCalc11Shape
    refl
    omegaFormulaText
    refl
    strainEigenframeText
    refl
    omegaE2FractionText
    refl
    calc11OutputNamesText
    refl
    "candidate-only mean placeholder"
    refl
    "candidate-only max placeholder"
    refl
    calc11DecisionInterpretationsText
    refl
    0
    "candidate-only boundary-layer min_g12 placeholder"
    false
    refl
    noClayPromotionText
    refl

calc11StatusIsCandidateOnlyNonPromoting :
  status canonicalNSVorticityE2ProjectionCalc11Receipt ≡
  candidateOnlyNonPromoting
calc11StatusIsCandidateOnlyNonPromoting = refl

calc11ClayPromotionStillFalse :
  clayPromotion canonicalNSVorticityE2ProjectionCalc11Receipt ≡ false
calc11ClayPromotionStillFalse = refl
