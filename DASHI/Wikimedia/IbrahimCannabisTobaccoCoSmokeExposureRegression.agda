module DASHI.Wikimedia.IbrahimCannabisTobaccoCoSmokeExposureRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RED surface for cannabis + tobacco co-combustion.
------------------------------------------------------------------------

record CoSmokeRegression : Set where
  constructor co-smoke-regression
  field
    cannabisResidueVectorRequired : Bool
    tobaccoResidueVectorRequired : Bool
    cannabisTransferFunctionRequired : Bool
    tobaccoTransferFunctionRequired : Bool
    mixedCombustionInteractionRequired : Bool
    tobaccoBatchPesticidePanelPaidUS : Bool
    tobaccoBatchPesticidePanelPaidAU : Bool
    additiveExposureAssumptionPaid : Bool
open CoSmokeRegression public

expectedCoSmokeRegression : CoSmokeRegression
expectedCoSmokeRegression =
  co-smoke-regression true true true true true false false false
