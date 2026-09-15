module DASHI.Environment.WaterHyacinthLESRegression where

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.WaterHyacinthLESExact as Hyacinth

------------------------------------------------------------------------
-- The water-hyacinth fixture retains externality/status axes separately and
-- carries its empirical provenance through the canonical typed source atlas.
------------------------------------------------------------------------

canonicalScenario : Hyacinth.WaterHyacinthInterventionScenario
canonicalScenario = Hyacinth.canonicalWaterHyacinthScenario

controlIsNotRestoration : Hyacinth.ControlRestorationSeparation
controlIsNotRestoration = Hyacinth.canonicalControlRestorationSeparation

statusAxesRemainDistinct : Hyacinth.BiocontrolStatusSeparation
statusAxesRemainDistinct = Hyacinth.canonicalBiocontrolStatusSeparation

sourceBoundary : Hyacinth.WaterHyacinthSourceBoundary
sourceBoundary = Hyacinth.canonicalWaterHyacinthSourceBoundary

typedSourceAtlas : Attribution.AttributedSourceAtlas
typedSourceAtlas = Hyacinth.sourceAtlas canonicalScenario
