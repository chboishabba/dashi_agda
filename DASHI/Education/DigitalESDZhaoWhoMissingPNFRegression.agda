module DASHI.Education.DigitalESDZhaoWhoMissingPNFRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDZhaoWhoMissingPNFExact as Zhao
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Core.IntersectionalNonFactorability as Factors

registeredPopulationRegression : Zhao.registeredDisabledStudentCount ≡ 7188
registeredPopulationRegression = refl

validResponseCountRegression : Zhao.validResponseCount ≡ 124
validResponseCountRegression = refl

strongestPaidImplicationRegression :
  Zhao.strongestPaidImplication ≡ Cone.restatesMeasuredResult
strongestPaidImplicationRegression = refl

responseCountCannotDetermineRepresentationRegression :
  Factors.FactorsThrough Zhao.responseCountProjection Zhao.representationAdequacy → ⊥
responseCountCannotDetermineRepresentationRegression =
  Zhao.responseCountCannotDetermineRepresentationAdequacy
