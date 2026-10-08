{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974MaterialIdentityAndConstitutiveDataExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- HISTORICAL SAME-OBJECT IDENTITY
--
-- NASA-CR-140308 / R-9557 and executive summary R-9557-1 identify the
-- Durability Engine nozzle as WC103 columbium with Vac Hyd silicide coating
-- VH-101, 80-percent bell, attached near epsilon 3:1 and extending to 40:1.
-- This pays the historical alloy/coating identity.  It does not import a
-- modern datasheet as though it were the 1974 article's batch certificate.
------------------------------------------------------------------------

data MaterialIdentity : Set where
  haynes25 wc103Columbium : MaterialIdentity

data DataAuthority : Set where
  sameHistoricalReport modernManufacturerData legacyNASAComparator secondaryDatabase : DataAuthority

record HardwareIdentityReceipt : Set where
  constructor hardware-identity-receipt
  field
    material : MaterialIdentity
    historicalName : String
    coating : String
    nozzleContour : String
    attachAreaRatio : String
    exitAreaRatio : String
    sourceReference : String
    sameObjectIdentityPaid : Bool

wc103NozzleIdentity : HardwareIdentityReceipt
wc103NozzleIdentity =
  hardware-identity-receipt
    wc103Columbium
    "WC103 columbium"
    "Vac Hyd silicide VH-101"
    "80-percent bell; special contour"
    "approximately 3:1"
    "40:1"
    "NASA-CR-140308 R-9557 pp.13,18; R-9557-1 p.9"
    true

wc103IdentityPaid : Bool
wc103IdentityPaid = HardwareIdentityReceipt.sameObjectIdentityPaid wc103NozzleIdentity

vh101CoatingPaid : Bool
vh101CoatingPaid = true

record HistoricalGeometryReceipt : Set where
  constructor historical-geometry-receipt
  field
    characteristicLengthTenthsIn : Nat
    contractionRatio : String
    throatExpansionAngleDeg : Nat
    reportedHeatTransferReductionLowerPercent : Nat
    reportedHeatTransferReductionUpperPercent : Nat
    nozzleAttachRatio : String
    nozzleExitRatio : String
    wallThicknessRecovered : Bool
    localRadiusProfileRecovered : Bool
    sourceReference : String

historicalGeometry : HistoricalGeometryReceipt
historicalGeometry =
  historical-geometry-receipt
    160 "6:1" 42 20 30 "3:1" "40:1"
    false false
    "NASA-CR-140308 R-9557 pp.13,18; Figure 7"

------------------------------------------------------------------------
-- CONSTITUTIVE ANCHORS
--
-- These are bounded external anchors.  They constrain plausibility but are
-- not silently promoted to the exact 1974 nozzle article's constitutive law.
------------------------------------------------------------------------

record TensileAnchor : Set where
  constructor tensile-anchor
  field
    material : MaterialIdentity
    temperatureF : Nat
    yieldStrengthTenthsKsi : Nat
    ultimateStrengthTenthsKsi : Nat
    condition : String
    authority : DataAuthority
    sameHistoricalArticle : Bool
    sourceReference : String

-- Current Haynes International solution-annealed sheet data:
-- 2000 F: 0.2% yield 9.0 ksi, UTS 13.3 ksi.
haynes25At2000F : TensileAnchor
haynes25At2000F =
  tensile-anchor haynes25 2000 90 133
    "solution-annealed sheet"
    modernManufacturerData false
    "Haynes International HAYNES 25 alloy brochure/current alloy page"

-- Plate gives a nearby independent product-form anchor:
-- 2000 F: yield 9.3 ksi, UTS 14.5 ksi.
haynes25PlateAt2000F : TensileAnchor
haynes25PlateAt2000F =
  tensile-anchor haynes25 2000 93 145
    "solution-annealed plate"
    modernManufacturerData false
    "Haynes International HAYNES 25 alloy brochure/current alloy page"

record CreepAnchor : Set where
  constructor creep-anchor
  field
    material : MaterialIdentity
    temperatureC : Nat
    testFamily : String
    authority : DataAuthority
    sameHistoricalArticle : Bool
    sourceReference : String
    admissibleUse : String

c103HistoricalCreepAnchor : CreepAnchor
c103HistoricalCreepAnchor =
  creep-anchor wc103Columbium 1093
    "legacy C-103 creep / stress-rupture test family"
    legacyNASAComparator false
    "NASA NTRS 19800025047, Table I, C-103 creep data"
    "external constitutive comparator only; not a 1974 batch certificate"

record MaterialDataBoundary : Set where
  constructor material-data-boundary
  field
    alloyIdentityRecovered : Bool
    coatingIdentityRecovered : Bool
    exact1974WallThicknessRecovered : Bool
    exact1974HaynesConstitutiveLawRecovered : Bool
    exact1974WC103ConstitutiveLawRecovered : Bool
    modernDataMayBoundPlausibility : Bool
    modernDataEqualsHistoricalArticle : Bool

canonicalMaterialDataBoundary : MaterialDataBoundary
canonicalMaterialDataBoundary =
  material-data-boundary true true false false false true false
