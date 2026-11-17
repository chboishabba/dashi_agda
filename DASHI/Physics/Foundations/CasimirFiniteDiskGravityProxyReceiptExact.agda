module DASHI.Physics.Foundations.CasimirFiniteDiskGravityProxyReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record CasimirFiniteDiskGravityProxyReceipt : Set where
  constructor casimir-finite-disk-gravity-proxy-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    brownMaclayDOI : String
    separationM : String
    diskRadiusM : String
    axisZM : String
    finiteDiskFactor : String
    finiteDiskAccelerationMs2 : String
    finiteDiskFractionG : String
    assertionsPassed : Bool

open CasimirFiniteDiskGravityProxyReceipt public

canonicalCasimirFiniteDiskGravityProxyReceipt : CasimirFiniteDiskGravityProxyReceipt
canonicalCasimirFiniteDiskGravityProxyReceipt =
  casimir-finite-disk-gravity-proxy-receipt
    "scripts/casimir_finite_disk_gravity_proxy.py"
    "Docs/evidence/casimir_finite_disk_gravity_proxy_2026-10-16.json"
    "a951135281bd6fd8e0c49941d25d940300736d3bb7e4595c01960a1538205b7e"
    "10.1103/PhysRev.184.1272"
    "1e-7" "0.01" "0.001"
    "0.9004962809790011"
    "-1.8209173014945933e-33"
    "-1.8568188948260551e-34"
    true

record CasimirFiniteDiskGravityProxyBoundary : Set where
  constructor casimir-finite-disk-gravity-proxy-boundary
  field
    brownMaclayEnergyDensitySourcePaid : Bool
    equivalentSurfaceMassDiagnosticPaid : Bool
    finiteDiskWeakFieldProxyPaid : Bool
    infinitePlaneIdealizationReduced : Bool
    finitePlateGRSolutionPaid : Bool
    measuredGravityPaid : Bool
    macroscopicScalingPaid : Bool
    warpCapabilityPaid : Bool
    wormholeCapabilityPaid : Bool
    agdaKernelReceiptPaid : Bool

open CasimirFiniteDiskGravityProxyBoundary public

canonicalCasimirFiniteDiskGravityProxyBoundary : CasimirFiniteDiskGravityProxyBoundary
canonicalCasimirFiniteDiskGravityProxyBoundary =
  casimir-finite-disk-gravity-proxy-boundary
    true true true true
    false false false false false false

record CasimirFiniteDiskGravityProxyAttributionBoundary : Set where
  constructor casimir-finite-disk-gravity-proxy-attribution-boundary
  field
    brownMaclayOwnsIdealRenormalizedStressTheory : Bool
    dashiOwnsFiniteDiskWeakFieldDiagnostic : Bool
    newtonianDiskProxyIsNotFinitePlateGR : Bool
    numericalProxyIsNotMeasuredGravity : Bool

open CasimirFiniteDiskGravityProxyAttributionBoundary public

canonicalCasimirFiniteDiskGravityProxyAttributionBoundary : CasimirFiniteDiskGravityProxyAttributionBoundary
canonicalCasimirFiniteDiskGravityProxyAttributionBoundary =
  casimir-finite-disk-gravity-proxy-attribution-boundary true true true true
