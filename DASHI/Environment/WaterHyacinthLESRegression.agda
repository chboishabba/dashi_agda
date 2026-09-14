module DASHI.Environment.WaterHyacinthLESRegression where

import DASHI.Environment.WaterHyacinthLESExact as Hyacinth

------------------------------------------------------------------------
-- RED regression: the water-hyacinth fixture must retain biomass fate,
-- dissolved oxygen, nutrient/seedbank residuals, non-target evidence and
-- restoration state as distinct coordinates rather than a scalar success flag.
------------------------------------------------------------------------

canonicalScenario : Hyacinth.WaterHyacinthInterventionScenario
canonicalScenario = Hyacinth.canonicalWaterHyacinthScenario

controlIsNotRestoration : Hyacinth.ControlRestorationSeparation
controlIsNotRestoration = Hyacinth.canonicalControlRestorationSeparation

statusAxesRemainDistinct : Hyacinth.BiocontrolStatusSeparation
statusAxesRemainDistinct = Hyacinth.canonicalBiocontrolStatusSeparation

sourceBoundary : Hyacinth.WaterHyacinthSourceBoundary
sourceBoundary = Hyacinth.canonicalWaterHyacinthSourceBoundary
