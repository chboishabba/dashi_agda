module DASHI.Education.DigitalESDEfSIndependentChallengeRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEfSIndependentDerivationExact as EfS
import DASHI.Education.DigitalESDEfSIndependentChallengeExact as Challenge

systemsMappingRegression :
  EfS.area EfS.systemsThinking ≡ EfS.embracingComplexity
systemsMappingRegression = refl

politicalActionMappingRegression :
  EfS.area EfS.politicalAgency ≡ EfS.actingForSustainability
politicalActionMappingRegression = refl

sourceIndependentRegression :
  EfS.IndependentThemeReceipt.formulatedWithoutDigitalPrinciple EfS.valuesReceipt ≡
  true
sourceIndependentRegression = refl

ecologicalMismatchRegression :
  Challenge.ComparisonReceipt.outcome Challenge.ecologicalComparison ≡
  Challenge.unmatchedEfSRequirement
ecologicalMismatchRegression = refl

collectiveTensionRegression :
  Challenge.ComparisonReceipt.outcome Challenge.collectiveComparison ≡
  Challenge.candidateTension
collectiveTensionRegression = refl

noAutomaticNovelPrincipleRegression :
  Challenge.UnmatchedThemeIsAutomaticallyNewPrinciple → ⊥
noAutomaticNovelPrincipleRegression =
  Challenge.unmatchedDoesNotAutomaticallyDemandNewPrinciple
