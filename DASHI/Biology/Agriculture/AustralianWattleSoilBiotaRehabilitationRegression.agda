module DASHI.Biology.Agriculture.AustralianWattleSoilBiotaRehabilitationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianWattleSoilBiotaRehabilitationExact as W

bell2003Pinned : W.bell2003DOI ≡ "10.1071/SB02004"
bell2003Pinned = refl

moreiraGrez2019Pinned : W.moreiraGrez2019DOI ≡ "10.3389/fmicb.2019.01617"
moreiraGrez2019Pinned = refl

kneller2018Pinned : W.kneller2018DOI ≡ "10.1016/j.scitotenv.2017.11.219"
kneller2018Pinned = refl

knellerPMIDPinned : W.kneller2018PMID ≡ "29197793"
knellerPMIDPinned = refl

viabilityNotColonisation : W.inoculumViabilityImpliesFieldColonisation W.canonicalWattleSoilBiotaBoundary ≡ false
viabilityNotColonisation = refl

introducedNotIndigenous : W.introducedInoculumEqualsIndigenousPropagulePool W.canonicalWattleSoilBiotaBoundary ≡ false
introducedNotIndigenous = refl

soilFunctionNotRecruitment : W.soilFunctionImprovementImpliesNativeRecruitment W.canonicalWattleSoilBiotaBoundary ≡ false
soilFunctionNotRecruitment = refl

agriculturalInoculumNotNativeFit : W.agriculturalMicrobialInoculumImpliesNativeSystemFitness W.canonicalWattleSoilBiotaBoundary ≡ false
agriculturalInoculumNotNativeFit = refl
