module DASHI.Physics.Closure.NSVorticityE2ProjectionCalc11ResultReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Calc 11 vorticity-to-e2 result receipt.
--
-- Candidate-only empirical result surface.  This records the user's
-- Calc 11 summary exactly as given: the bottom-5% g12 cells mean
-- omega_e2_fraction is 0.343, the random baseline is 1/3, the full
-- boundary mean is 0.432, the max value is 1.0 in isolated/scattered
-- cells, percentile monotonicity fails, the decision is no_special_alignment,
-- and Clay promotion stays false.

data NSVorticityE2ProjectionCalc11ResultStatus : Set where
  candidateOnlyEmpiricalResultRecorded :
    NSVorticityE2ProjectionCalc11ResultStatus

data NSVorticityE2ProjectionCalc11ResultShape : Set where
  bottom5MeanRecorded :
    NSVorticityE2ProjectionCalc11ResultShape
  randomBaselineRecorded :
    NSVorticityE2ProjectionCalc11ResultShape
  fullBoundaryMeanRecorded :
    NSVorticityE2ProjectionCalc11ResultShape
  maxScatteredRecorded :
    NSVorticityE2ProjectionCalc11ResultShape
  percentileMonotonicityFailureRecorded :
    NSVorticityE2ProjectionCalc11ResultShape
  noSpecialAlignmentDecisionRecorded :
    NSVorticityE2ProjectionCalc11ResultShape
  collapseImpossibleImplicationRecorded :
    NSVorticityE2ProjectionCalc11ResultShape
  hStrainDomImplicationRecorded :
    NSVorticityE2ProjectionCalc11ResultShape
  noClayPromotionRecorded :
    NSVorticityE2ProjectionCalc11ResultShape

canonicalNSVorticityE2ProjectionCalc11ResultShape :
  List NSVorticityE2ProjectionCalc11ResultShape
canonicalNSVorticityE2ProjectionCalc11ResultShape =
  bottom5MeanRecorded
  ∷ randomBaselineRecorded
  ∷ fullBoundaryMeanRecorded
  ∷ maxScatteredRecorded
  ∷ percentileMonotonicityFailureRecorded
  ∷ noSpecialAlignmentDecisionRecorded
  ∷ collapseImpossibleImplicationRecorded
  ∷ hStrainDomImplicationRecorded
  ∷ noClayPromotionRecorded
  ∷ []

bottom5MeanText : String
bottom5MeanText =
  "bottom-5% g12 cells mean omega_e2_fraction = 0.343"

randomBaselineText : String
randomBaselineText =
  "random baseline omega_e2_fraction = 1/3"

fullBoundaryMeanText : String
fullBoundaryMeanText =
  "full boundary mean omega_e2_fraction = 0.432"

maxScatteredText : String
maxScatteredText =
  "max omega_e2_fraction = 1.0, isolated/scattered"

percentileMonotonicityFailureText : String
percentileMonotonicityFailureText =
  "percentile monotonicity failure is recorded: the bottom-5% g12 mean does not drop below the random baseline, while the full-boundary mean stays higher"

noSpecialAlignmentText : String
noSpecialAlignmentText = "no_special_alignment"

collapseImpossibleImplicationText : String
collapseImpossibleImplicationText =
  "collapseImpossible remains unsupported by this Calc 11 receipt."

hStrainDomImplicationText : String
hStrainDomImplicationText =
  "h_strain_dom is empirically consistent with Calc 10/11 but remains unproved by this Calc 11 receipt."

clayPromotionText : String
clayPromotionText = "No Clay promotion is made."

record NSVorticityE2ProjectionCalc11ResultReceipt : Set where
  field
    status :
      NSVorticityE2ProjectionCalc11ResultStatus
    statusIsCanonical :
      status ≡ candidateOnlyEmpiricalResultRecorded

    resultShape :
      List NSVorticityE2ProjectionCalc11ResultShape
    resultShapeIsCanonical :
      resultShape ≡ canonicalNSVorticityE2ProjectionCalc11ResultShape

    bottom5Mean :
      String
    bottom5MeanIsCanonical :
      bottom5Mean ≡ bottom5MeanText

    randomBaseline :
      String
    randomBaselineIsCanonical :
      randomBaseline ≡ randomBaselineText

    fullBoundaryMean :
      String
    fullBoundaryMeanIsCanonical :
      fullBoundaryMean ≡ fullBoundaryMeanText

    maxScattered :
      String
    maxScatteredIsCanonical :
      maxScattered ≡ maxScatteredText

    percentileMonotonicityFailure :
      Bool
    percentileMonotonicityFailureIsTrue :
      percentileMonotonicityFailure ≡ true

    decision :
      String
    decisionIsCanonical :
      decision ≡ noSpecialAlignmentText

    collapseImpossibleImplication :
      String
    collapseImpossibleImplicationIsCanonical :
      collapseImpossibleImplication ≡ collapseImpossibleImplicationText

    hStrainDomImplication :
      String
    hStrainDomImplicationIsCanonical :
      hStrainDomImplication ≡ hStrainDomImplicationText

    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

    receiptBoundary :
      List String

open NSVorticityE2ProjectionCalc11ResultReceipt public

canonicalNSVorticityE2ProjectionCalc11ResultReceipt :
  NSVorticityE2ProjectionCalc11ResultReceipt
canonicalNSVorticityE2ProjectionCalc11ResultReceipt =
  record
    { status =
        candidateOnlyEmpiricalResultRecorded
    ; statusIsCanonical =
        refl
    ; resultShape =
        canonicalNSVorticityE2ProjectionCalc11ResultShape
    ; resultShapeIsCanonical =
        refl
    ; bottom5Mean =
        bottom5MeanText
    ; bottom5MeanIsCanonical =
        refl
    ; randomBaseline =
        randomBaselineText
    ; randomBaselineIsCanonical =
        refl
    ; fullBoundaryMean =
        fullBoundaryMeanText
    ; fullBoundaryMeanIsCanonical =
        refl
    ; maxScattered =
        maxScatteredText
    ; maxScatteredIsCanonical =
        refl
    ; percentileMonotonicityFailure =
        true
    ; percentileMonotonicityFailureIsTrue =
        refl
    ; decision =
        noSpecialAlignmentText
    ; decisionIsCanonical =
        refl
    ; collapseImpossibleImplication =
        collapseImpossibleImplicationText
    ; collapseImpossibleImplicationIsCanonical =
        refl
    ; hStrainDomImplication =
        hStrainDomImplicationText
    ; hStrainDomImplicationIsCanonical =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; receiptBoundary =
        "Calc 11 empirical result is candidate-only and non-promoting"
        ∷ "bottom-5% g12 cells mean omega_e2_fraction = 0.343"
        ∷ "random baseline omega_e2_fraction = 1/3"
        ∷ "full boundary mean omega_e2_fraction = 0.432"
        ∷ "max omega_e2_fraction = 1.0, isolated/scattered"
        ∷ "percentile monotonicity failure is recorded"
        ∷ "decision = no_special_alignment"
        ∷ "collapseImpossible remains unsupported here"
        ∷ "h_strain_dom is empirically consistent but unproved here"
        ∷ "Clay promotion is false"
        ∷ []
    }

calc11ResultStatusIsCandidateOnly :
  status canonicalNSVorticityE2ProjectionCalc11ResultReceipt ≡
  candidateOnlyEmpiricalResultRecorded
calc11ResultStatusIsCandidateOnly = refl

calc11ClayPromotionIsFalse :
  clayPromotion canonicalNSVorticityE2ProjectionCalc11ResultReceipt ≡ false
calc11ClayPromotionIsFalse = refl
