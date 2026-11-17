module DASHI.Physics.Foundations.CasimirGravityScalingReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record CasimirGravityScalingReceipt : Set where
  constructor casimir-gravity-scaling-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    brownMaclayDOI : String
    energyDensity100nmJm3 : String
    equivalentMassDensity100nmKgm3 : String
    sheetGravity100nmMs2 : String
    sheetGravity100nmFractionG : String
    assertionsPassed : Bool

open CasimirGravityScalingReceipt public

canonicalCasimirGravityScalingReceipt : CasimirGravityScalingReceipt
canonicalCasimirGravityScalingReceipt =
  casimir-gravity-scaling-receipt
    "scripts/casimir_gravity_scaling.py"
    "Docs/evidence/casimir_gravity_scaling_2026-10-16.json"
    "2327d5479f83757d5337cb79be89b6dd0e6bd72161dfd22f92aad195f3dcecdd"
    "10.1103/PhysRev.184.1272"
    "-4.333752574825845"
    "-4.8219500453024903e-17"
    "-2.0221263984732167e-33"
    "-2.0619950732138056e-34"
    true

record CasimirGravityScalingBoundary : Set where
  constructor casimir-gravity-scaling-boundary
  field
    brownMaclayIdealStressSourcePaid : Bool
    idealStressScalingExecutionPaid : Bool
    equivalentMassDensityDiagnosticPaid : Bool
    weakFieldInfiniteSheetProxyPaid : Bool
    finitePlateGRSolutionPaid : Bool
    measuredGravitationalBackreactionPaid : Bool
    macroscopicScalingDemonstrated : Bool
    warpCapabilityPaid : Bool
    wormholeCapabilityPaid : Bool
    agdaKernelReceiptPaid : Bool

open CasimirGravityScalingBoundary public

canonicalCasimirGravityScalingBoundary : CasimirGravityScalingBoundary
canonicalCasimirGravityScalingBoundary =
  casimir-gravity-scaling-boundary
    true true true true
    false false false false false false

record CasimirGravityScalingAttributionBoundary : Set where
  constructor casimir-gravity-scaling-attribution-boundary
  field
    brownMaclayOwnsIdealRenormalizedStressTheory : Bool
    dashiOwnsScalingAndWeakFieldProxy : Bool
    weakFieldProxyIsNotMeasuredGravity : Bool
    negativeEnergyDoesNotPromoteToWarpCapability : Bool

open CasimirGravityScalingAttributionBoundary public

canonicalCasimirGravityScalingAttributionBoundary : CasimirGravityScalingAttributionBoundary
canonicalCasimirGravityScalingAttributionBoundary =
  casimir-gravity-scaling-attribution-boundary true true true true
