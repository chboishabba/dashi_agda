module DASHI.Physics.Closure.NSSprint127AxisymmetricBoundaryVortexStretchingGate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint126LogGapAuditAndAxisymmetricPivot
  as Sprint126

------------------------------------------------------------------------
-- Sprint127 axisymmetric boundary vortex-stretching gate receipt.
--
-- This module records the axisymmetric boundary route as the live primary
-- Navier-Stokes route after Sprint126.  It closes only the evidence gates
-- supplied for this sprint: Sprint126 is imported, the route is recorded,
-- Hou-Luo scaling compatibility is recorded true from the scaling sampler,
-- and the energy obstruction is recorded absent.  The analytic and Clay
-- gates remain false/open.

sprint127AxisymmetricBoundaryLedgerClosed : Bool
sprint127AxisymmetricBoundaryLedgerClosed = true

sprint126Imported : Bool
sprint126Imported = true

axisymmetricBoundaryRouteRecorded : Bool
axisymmetricBoundaryRouteRecorded = true

axisymmetricBoundaryVortexStretchingGateRecorded : Bool
axisymmetricBoundaryVortexStretchingGateRecorded = true

axisymmetricBoundaryLivePrimaryNSRoute : Bool
axisymmetricBoundaryLivePrimaryNSRoute = true

energyObstructionAbsent : Bool
energyObstructionAbsent = true

EnergyObstructionAbsent : String
EnergyObstructionAbsent = "EnergyObstructionAbsent"

boundaryVorticityAmplificationLawClosed : Bool
boundaryVorticityAmplificationLawClosed = false

boundaryVorticityAmplificationLawRecorded : Bool
boundaryVorticityAmplificationLawRecorded = true

strainAlignmentNearAxisOrBoundaryClosed : Bool
strainAlignmentNearAxisOrBoundaryClosed = false

strainAlignmentNearAxisOrBoundary : Bool
strainAlignmentNearAxisOrBoundary = false

viscousBoundaryLayerDominanceCheckClosed : Bool
viscousBoundaryLayerDominanceCheckClosed = false

viscousBoundaryLayerDominanceCheck : Bool
viscousBoundaryLayerDominanceCheck = false

houLuoScalingCompatibilityRecorded : Bool
houLuoScalingCompatibilityRecorded = true

houLuoScalingCompatibility : Bool
houLuoScalingCompatibility = true

geometricDepletionForAxisymmetricBoundaryClosed : Bool
geometricDepletionForAxisymmetricBoundaryClosed = false

bkmBridgeFromAxisymmetricBoundaryClosed : Bool
bkmBridgeFromAxisymmetricBoundaryClosed = false

bkmBridge : Bool
bkmBridge = false

BKMBridge : String
BKMBridge = "BKMBridge"

globalSmoothDataBoundaryConstructionClosed : Bool
globalSmoothDataBoundaryConstructionClosed = false

navierStokesClayAssemblyClosed : Bool
navierStokesClayAssemblyClosed = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

record Sprint126ImportReceipt : Set where
  constructor sprint126ImportReceipt
  field
    sprint126Receipt :
      Sprint126.NSSprint126LogGapAuditAndAxisymmetricPivot
    sprint126ReceiptIsCanonical :
      sprint126Receipt
      ≡ Sprint126.canonicalNSSprint126LogGapAuditAndAxisymmetricPivot
    sprint126LedgerClosed :
      Sprint126.sprint126LogGapAuditAndAxisymmetricPivotLedgerClosed ≡ true
    sprint126AxisymmetricTarget :
      Sprint126.axisymmetricBoundaryVortexStretchingGateNextTarget ≡ true
    sprint126AxisymmetricGateStillOpen :
      Sprint126.axisymmetricBoundaryVortexStretchingGateClosed ≡ false
    sprint126ClayStillFalse :
      Sprint126.clayNavierStokesPromoted ≡ false
    sprint126ImportedField :
      sprint126Imported ≡ true
    importStatement :
      String
    importStatementIsRequested :
      importStatement ≡ "Sprint127 imports Sprint126 log-gap audit and axisymmetric pivot"

open Sprint126ImportReceipt public

canonicalSprint126ImportReceipt : Sprint126ImportReceipt
canonicalSprint126ImportReceipt =
  sprint126ImportReceipt
    Sprint126.canonicalNSSprint126LogGapAuditAndAxisymmetricPivot
    refl
    refl
    refl
    refl
    refl
    refl
    "Sprint127 imports Sprint126 log-gap audit and axisymmetric pivot"
    refl

record AxisymmetricBoundaryVortexStretchingGate : Set where
  constructor axisymmetricBoundaryVortexStretchingGateReceipt
  field
    gateName :
      String
    gateNameIsRequested :
      gateName ≡ "AxisymmetricBoundaryVortexStretchingGate"
    routeStatement :
      String
    routeStatementIsRequested :
      routeStatement ≡ "axisymmetric boundary route is the live primary Navier-Stokes route"
    routeRecordedField :
      axisymmetricBoundaryRouteRecorded ≡ true
    gateRecordedField :
      axisymmetricBoundaryVortexStretchingGateRecorded ≡ true
    livePrimaryRouteField :
      axisymmetricBoundaryLivePrimaryNSRoute ≡ true
    energyObstructionAbsentField :
      energyObstructionAbsent ≡ true

open AxisymmetricBoundaryVortexStretchingGate public

canonicalAxisymmetricBoundaryVortexStretchingGate :
  AxisymmetricBoundaryVortexStretchingGate
canonicalAxisymmetricBoundaryVortexStretchingGate =
  axisymmetricBoundaryVortexStretchingGateReceipt
    "AxisymmetricBoundaryVortexStretchingGate"
    refl
    "axisymmetric boundary route is the live primary Navier-Stokes route"
    refl
    refl
    refl
    refl
    refl

record BoundaryVorticityAmplificationLaw : Set where
  constructor boundaryVorticityAmplificationLawReceipt
  field
    subgateName :
      String
    subgateNameIsRequested :
      subgateName ≡ "BoundaryVorticityAmplificationLaw"
    statusStatement :
      String
    statusStatementIsRequested :
      statusStatement ≡ "boundary vorticity amplification law is not closed"
    closedField :
      boundaryVorticityAmplificationLawClosed ≡ false

open BoundaryVorticityAmplificationLaw public

canonicalBoundaryVorticityAmplificationLaw :
  BoundaryVorticityAmplificationLaw
canonicalBoundaryVorticityAmplificationLaw =
  boundaryVorticityAmplificationLawReceipt
    "BoundaryVorticityAmplificationLaw"
    refl
    "boundary vorticity amplification law is not closed"
    refl
    refl

record StrainAlignmentNearAxisOrBoundary : Set where
  constructor strainAlignmentNearAxisOrBoundaryReceipt
  field
    subgateName :
      String
    subgateNameIsRequested :
      subgateName ≡ "StrainAlignmentNearAxisOrBoundary"
    statusStatement :
      String
    statusStatementIsRequested :
      statusStatement ≡ "strain alignment near axis or boundary is not closed"
    closedField :
      strainAlignmentNearAxisOrBoundaryClosed ≡ false

open StrainAlignmentNearAxisOrBoundary public

canonicalStrainAlignmentNearAxisOrBoundary :
  StrainAlignmentNearAxisOrBoundary
canonicalStrainAlignmentNearAxisOrBoundary =
  strainAlignmentNearAxisOrBoundaryReceipt
    "StrainAlignmentNearAxisOrBoundary"
    refl
    "strain alignment near axis or boundary is not closed"
    refl
    refl

record ViscousBoundaryLayerDominanceCheck : Set where
  constructor viscousBoundaryLayerDominanceCheckReceipt
  field
    subgateName :
      String
    subgateNameIsRequested :
      subgateName ≡ "ViscousBoundaryLayerDominanceCheck"
    statusStatement :
      String
    statusStatementIsRequested :
      statusStatement ≡ "viscous boundary layer dominance check is not closed"
    closedField :
      viscousBoundaryLayerDominanceCheckClosed ≡ false

open ViscousBoundaryLayerDominanceCheck public

canonicalViscousBoundaryLayerDominanceCheck :
  ViscousBoundaryLayerDominanceCheck
canonicalViscousBoundaryLayerDominanceCheck =
  viscousBoundaryLayerDominanceCheckReceipt
    "ViscousBoundaryLayerDominanceCheck"
    refl
    "viscous boundary layer dominance check is not closed"
    refl
    refl

record HouLuoScalingCompatibility : Set where
  constructor houLuoScalingCompatibilityReceipt
  field
    subgateName :
      String
    subgateNameIsRequested :
      subgateName ≡ "HouLuoScalingCompatibility"
    evidenceStatement :
      String
    evidenceStatementIsRequested :
      evidenceStatement ≡ "HouLuoScalingCompatibility recorded true from scaling sampler"
    recordedField :
      houLuoScalingCompatibilityRecorded ≡ true

open HouLuoScalingCompatibility public

canonicalHouLuoScalingCompatibility : HouLuoScalingCompatibility
canonicalHouLuoScalingCompatibility =
  houLuoScalingCompatibilityReceipt
    "HouLuoScalingCompatibility"
    refl
    "HouLuoScalingCompatibility recorded true from scaling sampler"
    refl
    refl

record GeometricDepletionForAxisymmetricBoundary : Set where
  constructor geometricDepletionForAxisymmetricBoundaryReceipt
  field
    subgateName :
      String
    subgateNameIsRequested :
      subgateName ≡ "GeometricDepletionForAxisymmetricBoundary"
    statusStatement :
      String
    statusStatementIsRequested :
      statusStatement ≡ "geometric depletion comparison is not closed"
    closedField :
      geometricDepletionForAxisymmetricBoundaryClosed ≡ false

open GeometricDepletionForAxisymmetricBoundary public

canonicalGeometricDepletionForAxisymmetricBoundary :
  GeometricDepletionForAxisymmetricBoundary
canonicalGeometricDepletionForAxisymmetricBoundary =
  geometricDepletionForAxisymmetricBoundaryReceipt
    "GeometricDepletionForAxisymmetricBoundary"
    refl
    "geometric depletion comparison is not closed"
    refl
    refl

record BKMBridgeFromAxisymmetricBoundary : Set where
  constructor bkmBridgeFromAxisymmetricBoundaryReceipt
  field
    subgateName :
      String
    subgateNameIsRequested :
      subgateName ≡ "BKMBridgeFromAxisymmetricBoundary"
    statusStatement :
      String
    statusStatementIsRequested :
      statusStatement ≡ "BKM bridge from axisymmetric boundary route is not closed"
    closedField :
      bkmBridgeFromAxisymmetricBoundaryClosed ≡ false

open BKMBridgeFromAxisymmetricBoundary public

canonicalBKMBridgeFromAxisymmetricBoundary :
  BKMBridgeFromAxisymmetricBoundary
canonicalBKMBridgeFromAxisymmetricBoundary =
  bkmBridgeFromAxisymmetricBoundaryReceipt
    "BKMBridgeFromAxisymmetricBoundary"
    refl
    "BKM bridge from axisymmetric boundary route is not closed"
    refl
    refl

record GlobalSmoothDataBoundaryConstruction : Set where
  constructor globalSmoothDataBoundaryConstructionReceipt
  field
    subgateName :
      String
    subgateNameIsRequested :
      subgateName ≡ "GlobalSmoothDataBoundaryConstruction"
    statusStatement :
      String
    statusStatementIsRequested :
      statusStatement ≡ "global smooth data boundary construction is not closed"
    closedField :
      globalSmoothDataBoundaryConstructionClosed ≡ false

open GlobalSmoothDataBoundaryConstruction public

canonicalGlobalSmoothDataBoundaryConstruction :
  GlobalSmoothDataBoundaryConstruction
canonicalGlobalSmoothDataBoundaryConstruction =
  globalSmoothDataBoundaryConstructionReceipt
    "GlobalSmoothDataBoundaryConstruction"
    refl
    "global smooth data boundary construction is not closed"
    refl
    refl

record NavierStokesClayAssembly : Set where
  constructor navierStokesClayAssemblyReceipt
  field
    subgateName :
      String
    subgateNameIsRequested :
      subgateName ≡ "NavierStokesClayAssembly"
    statusStatement :
      String
    statusStatementIsRequested :
      statusStatement ≡ "Navier-Stokes Clay assembly is not closed"
    assemblyClosedField :
      navierStokesClayAssemblyClosed ≡ false
    clayPromotedField :
      clayNavierStokesPromoted ≡ false

open NavierStokesClayAssembly public

canonicalNavierStokesClayAssembly : NavierStokesClayAssembly
canonicalNavierStokesClayAssembly =
  navierStokesClayAssemblyReceipt
    "NavierStokesClayAssembly"
    refl
    "Navier-Stokes Clay assembly is not closed"
    refl
    refl
    refl

record Sprint127GateStatuses : Set where
  constructor sprint127GateStatuses
  field
    sprint127LedgerClosedField :
      sprint127AxisymmetricBoundaryLedgerClosed ≡ true
    sprint126ImportedField :
      sprint126Imported ≡ true
    routeRecordedField :
      axisymmetricBoundaryRouteRecorded ≡ true
    gateRecordedField :
      axisymmetricBoundaryVortexStretchingGateRecorded ≡ true
    livePrimaryRouteField :
      axisymmetricBoundaryLivePrimaryNSRoute ≡ true
    houLuoScalingCompatibilityRecordedField :
      houLuoScalingCompatibilityRecorded ≡ true
    houLuoScalingCompatibilityAuditField :
      houLuoScalingCompatibility ≡ true
    energyObstructionAbsentField :
      energyObstructionAbsent ≡ true
    amplificationLawClosedField :
      boundaryVorticityAmplificationLawClosed ≡ false
    amplificationLawRecordedField :
      boundaryVorticityAmplificationLawRecorded ≡ true
    strainAlignmentClosedField :
      strainAlignmentNearAxisOrBoundaryClosed ≡ false
    strainAlignmentAuditField :
      strainAlignmentNearAxisOrBoundary ≡ false
    viscousDominanceClosedField :
      viscousBoundaryLayerDominanceCheckClosed ≡ false
    viscousDominanceAuditField :
      viscousBoundaryLayerDominanceCheck ≡ false
    depletionComparisonClosedField :
      geometricDepletionForAxisymmetricBoundaryClosed ≡ false
    bkmBridgeClosedField :
      bkmBridgeFromAxisymmetricBoundaryClosed ≡ false
    bkmBridgeAuditField :
      bkmBridge ≡ false
    globalDataClosedField :
      globalSmoothDataBoundaryConstructionClosed ≡ false
    clayAssemblyClosedField :
      navierStokesClayAssemblyClosed ≡ false
    clayPromotedField :
      clayNavierStokesPromoted ≡ false
    statusStatement :
      String
    statusStatementIsRequested :
      statusStatement
      ≡ "Sprint127 records the axisymmetric boundary route and leaves analytic and Clay gates open"

open Sprint127GateStatuses public

canonicalSprint127GateStatuses : Sprint127GateStatuses
canonicalSprint127GateStatuses =
  sprint127GateStatuses
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    "Sprint127 records the axisymmetric boundary route and leaves analytic and Clay gates open"
    refl

record NSSprint127AxisymmetricBoundaryVortexStretchingGate : Set where
  constructor nsSprint127AxisymmetricBoundaryVortexStretchingGateReceipt
  field
    importedSprint126 :
      Sprint126ImportReceipt
    primaryGate :
      AxisymmetricBoundaryVortexStretchingGate
    amplificationLaw :
      BoundaryVorticityAmplificationLaw
    strainAlignment :
      StrainAlignmentNearAxisOrBoundary
    viscousDominance :
      ViscousBoundaryLayerDominanceCheck
    scalingCompatibility :
      HouLuoScalingCompatibility
    geometricDepletion :
      GeometricDepletionForAxisymmetricBoundary
    bkmBridgeReceipt :
      BKMBridgeFromAxisymmetricBoundary
    globalData :
      GlobalSmoothDataBoundaryConstruction
    clayAssembly :
      NavierStokesClayAssembly
    gateStatuses :
      Sprint127GateStatuses
    gateStatusesAreCanonical :
      gateStatuses ≡ canonicalSprint127GateStatuses
    ledgerSummary :
      String
    ledgerSummaryIsRequested :
      ledgerSummary
      ≡ "Sprint127 makes AxisymmetricBoundaryVortexStretchingGate the live primary NS route, records HouLuoScalingCompatibility true from the scaling sampler and energy obstruction absent, while keeping amplification, alignment, viscous dominance, depletion comparison, BKM bridge, global data, and Clay assembly false/open."

open NSSprint127AxisymmetricBoundaryVortexStretchingGate public

canonicalNSSprint127AxisymmetricBoundaryVortexStretchingGate :
  NSSprint127AxisymmetricBoundaryVortexStretchingGate
canonicalNSSprint127AxisymmetricBoundaryVortexStretchingGate =
  nsSprint127AxisymmetricBoundaryVortexStretchingGateReceipt
    canonicalSprint126ImportReceipt
    canonicalAxisymmetricBoundaryVortexStretchingGate
    canonicalBoundaryVorticityAmplificationLaw
    canonicalStrainAlignmentNearAxisOrBoundary
    canonicalViscousBoundaryLayerDominanceCheck
    canonicalHouLuoScalingCompatibility
    canonicalGeometricDepletionForAxisymmetricBoundary
    canonicalBKMBridgeFromAxisymmetricBoundary
    canonicalGlobalSmoothDataBoundaryConstruction
    canonicalNavierStokesClayAssembly
    canonicalSprint127GateStatuses
    refl
    "Sprint127 makes AxisymmetricBoundaryVortexStretchingGate the live primary NS route, records HouLuoScalingCompatibility true from the scaling sampler and energy obstruction absent, while keeping amplification, alignment, viscous dominance, depletion comparison, BKM bridge, global data, and Clay assembly false/open."
    refl

sprint127SubgateReceiptSummary :
  BoundaryVorticityAmplificationLaw
  × StrainAlignmentNearAxisOrBoundary
  × ViscousBoundaryLayerDominanceCheck
  × HouLuoScalingCompatibility
  × GeometricDepletionForAxisymmetricBoundary
  × BKMBridgeFromAxisymmetricBoundary
  × GlobalSmoothDataBoundaryConstruction
  × NavierStokesClayAssembly
sprint127SubgateReceiptSummary =
  canonicalBoundaryVorticityAmplificationLaw ,
  canonicalStrainAlignmentNearAxisOrBoundary ,
  canonicalViscousBoundaryLayerDominanceCheck ,
  canonicalHouLuoScalingCompatibility ,
  canonicalGeometricDepletionForAxisymmetricBoundary ,
  canonicalBKMBridgeFromAxisymmetricBoundary ,
  canonicalGlobalSmoothDataBoundaryConstruction ,
  canonicalNavierStokesClayAssembly

sprint127ClosedEvidenceStatuses :
  (sprint126Imported ≡ true)
  × (axisymmetricBoundaryRouteRecorded ≡ true)
  × (axisymmetricBoundaryVortexStretchingGateRecorded ≡ true)
  × (axisymmetricBoundaryLivePrimaryNSRoute ≡ true)
  × (houLuoScalingCompatibilityRecorded ≡ true)
  × (houLuoScalingCompatibility ≡ true)
  × (energyObstructionAbsent ≡ true)
sprint127ClosedEvidenceStatuses =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl

sprint127OpenAnalyticStatuses :
  (boundaryVorticityAmplificationLawClosed ≡ false)
  × (boundaryVorticityAmplificationLawRecorded ≡ true)
  × (strainAlignmentNearAxisOrBoundaryClosed ≡ false)
  × (strainAlignmentNearAxisOrBoundary ≡ false)
  × (viscousBoundaryLayerDominanceCheckClosed ≡ false)
  × (viscousBoundaryLayerDominanceCheck ≡ false)
  × (geometricDepletionForAxisymmetricBoundaryClosed ≡ false)
  × (bkmBridgeFromAxisymmetricBoundaryClosed ≡ false)
  × (bkmBridge ≡ false)
  × (globalSmoothDataBoundaryConstructionClosed ≡ false)
  × (navierStokesClayAssemblyClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sprint127OpenAnalyticStatuses =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl
