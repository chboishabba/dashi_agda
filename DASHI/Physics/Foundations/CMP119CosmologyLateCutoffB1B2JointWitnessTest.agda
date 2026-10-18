{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyLateCutoffB1B2JointWitnessTest where

import DASHI.Physics.Foundations.CMP119CosmologyLateCutoffB1B2JointWitnessExact as Joint

lateCutoffSelectionIsCompilerOwnedRegression =
  Joint.lateCutoffSelectionIsCompilerOwned

b1AndB2UseSameChosenCutoffRegression =
  Joint.b1AndB2UseSameChosenCutoff

noHandSelectedCutoffRequiredRegression =
  Joint.noHandSelectedCutoffRequired
