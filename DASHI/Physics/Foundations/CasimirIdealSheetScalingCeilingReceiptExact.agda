module DASHI.Physics.Foundations.CasimirIdealSheetScalingCeilingReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- IDEAL CASIMIR WEAK-FIELD SCALING CEILING
--
-- Brown-Maclay's ideal perfect-conductor parallel-plate energy density implies
-- an equivalent surface mass density proportional to a^-3. In the Newtonian
-- infinite-sheet proxy the field saturates at 2 pi G |sigma|, so increasing
-- plate radius cannot exceed the fixed-gap ceiling. The inverted femtometre
-- gaps below are diagnostics of the ideal model and are not material/device
-- realizability claims.
------------------------------------------------------------------------

record CasimirIdealSheetScalingReceipt : Set where
  constructor casimir-ideal-sheet-scaling-receipt
  field
    sourceDOI : String
    producer : String
    evidence : String
    referenceGapM : String
    referenceSurfaceMassDensityAbsKgM2 : String
    referenceInfiniteSheetGAbsMS2 : String
    gapFor1eMinus12MS2M : String
    gapFor1eMinus9MS2M : String
    gapFor1eMinus6MS2M : String
    gapFor1gM : String
    numericalScalingReplayPaid : Bool
    finiteMaterialRealizabilityPaid : Bool
    modelValidityAtFemtometreGapPaid : Bool
    measuredGravityPaid : Bool
    macroscopicNegativeMassPaid : Bool
    warpCapabilityPaid : Bool

open CasimirIdealSheetScalingReceipt public

canonicalCasimirIdealSheetScalingReceipt : CasimirIdealSheetScalingReceipt
canonicalCasimirIdealSheetScalingReceipt =
  casimir-ideal-sheet-scaling-receipt
    "10.1103/PhysRev.184.1272"
    "scripts/casimir_ideal_sheet_scaling_ceiling.py"
    "Docs/evidence/casimir_ideal_sheet_scaling_ceiling_2026-10-16.json"
    "1e-07"
    "4.82195004530249e-24"
    "2.0221263984732167e-33"
    "1.2645502728279351e-14"
    "1.2645502728279352e-15"
    "1.2645502728279356e-16"
    "5.907846567783201e-19"
    true false false false false false

record CasimirIdealSheetScalingBoundary : Set where
  constructor casimir-ideal-sheet-scaling-boundary
  field
    brownMaclayIdealScalingSourcePaid : Bool
    fixedGapAreaCeilingNumericallyExecuted : Bool
    inverseGapDiagnosticNumericallyExecuted : Bool
    idealScalingDoesNotCreateFiniteMaterialRealizability : Bool
    idealScalingDoesNotCreateMeasuredGravity : Bool
    idealScalingDoesNotCreateWarpCapability : Bool

open CasimirIdealSheetScalingBoundary public

canonicalCasimirIdealSheetScalingBoundary : CasimirIdealSheetScalingBoundary
canonicalCasimirIdealSheetScalingBoundary =
  casimir-ideal-sheet-scaling-boundary true true true true true true
