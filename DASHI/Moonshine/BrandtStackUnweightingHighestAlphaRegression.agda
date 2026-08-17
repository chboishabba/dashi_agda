module DASHI.Moonshine.BrandtStackUnweightingHighestAlphaRegression where

open import DASHI.Core.Prelude

import DASHI.Moonshine.BrandtStackUnweightingExact as Stack
import DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact as P11
import DASHI.Moonshine.BrandtStackUnweightingControlsExact as Controls
import DASHI.Moonshine.P37NonOggPositiveHeckeControlExact as P37
import DASHI.Moonshine.P37NonOggPositivePrimeSquareNeighboursExact as P37Square
import DASHI.Moonshine.BrandtStackCrossPrimeSelectorCutsetExact as Cutset

p11StackExplainsFiveStateCount : P11.p11UnweightedStateCount ≡ 5
p11StackExplainsFiveStateCount = P11.p11UnweightedStateCountIsFive

p11MassFormulaClearsExactly : 4 + 6 ≡ 11 - 1
p11MassFormulaClearsExactly = P11.p11MassFormulaCleared

p37SamePrescriptionGivesThree : Controls.p37UnweightedStateCount ≡ 3
p37SamePrescriptionGivesThree = Controls.p37UnweightedStateCountIsThree

p43SamePrescriptionGivesSeven : Controls.p43UnweightedStateCount ≡ 7
p43SamePrescriptionGivesSeven = Controls.p43UnweightedStateCountIsSeven

p43WeightSumFiveIsNotSheetCountSeven :
  Controls.p43MonodromyWeightSum ≡ Controls.p43UnweightedStateCount → ⊥
p43WeightSumFiveIsNotSheetCountSeven = Controls.p43WeightSumIsNotUnweightedCount

p37IsNonOggControl :
  DASHI.Moonshine.CandidateLevelExternalOggPredicateExact.ExternalOggAt 37 → ⊥
p37IsNonOggControl = Controls.p37IsNotExternallyOgg

p43IsNonOggControl :
  DASHI.Moonshine.CandidateLevelExternalOggPredicateExact.ExternalOggAt 43 → ⊥
p43IsNonOggControl = Controls.p43IsNotExternallyOgg

p37PositivePrimeSquareExists :
  P37Square.nonOggControlSurvivesP11PositivityGate
    P37Square.canonicalP37PrimeSquareNeighbourBoundary
  ≡ true
p37PositivePrimeSquareExists =
  P37Square.nonOggControlSurvivesP11PositivityGateIsTrue
    P37Square.canonicalP37PrimeSquareNeighbourBoundary

positiveFeatureCannotBeOggSelector :
  (classify : Cutset.PositiveT2SquareFeature → Bool) →
  classify Cutset.p11PositiveFeature ≡ true →
  classify Cutset.p37PositiveFeature ≡ false →
  ⊥
positiveFeatureCannotBeOggSelector = Cutset.featureOnlyClassifierCannotSeparate

stackUnweightingDoesNotDerivePermutationGenerators :
  P11.particularPermutationGeneratorsDerivedFromMassFormula
    P11.canonicalP11StackUnweightingBoundary
  ≡ false
stackUnweightingDoesNotDerivePermutationGenerators =
  P11.particularPermutationGeneratorsDerivedFromMassFormulaIsFalse
    P11.canonicalP11StackUnweightingBoundary

jointSelectorStillOpen :
  Cutset.jointHeckeFrickeFrobeniusSelectorConstructedHere
    Cutset.canonicalBrandtStackSelectorCutsetBoundary
  ≡ false
jointSelectorStillOpen =
  Cutset.jointHeckeFrickeFrobeniusSelectorConstructedHereIsFalse
    Cutset.canonicalBrandtStackSelectorCutsetBoundary
