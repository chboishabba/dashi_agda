{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3SelectedMarkedF2Test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedMarkedF2Exact as P3

noUniversalFamily :
  P3.universalMarkedCurvatureFamilyRequiredForCosmology ≡ false
noUniversalFamily = refl

oneSourceSuffices :
  P3.oneSelectedMarkedF2SourceSuffices ≡ true
oneSourceSuffices = refl

physicalDataRemains :
  P3.remainingSelectedF2SourceWorkIsPhysicalMarkedSourceDataAndSemantics ≡ true
physicalDataRemains = refl
