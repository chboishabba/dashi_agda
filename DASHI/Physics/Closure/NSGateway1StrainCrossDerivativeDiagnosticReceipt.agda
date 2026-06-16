module DASHI.Physics.Closure.NSGateway1StrainCrossDerivativeDiagnosticReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS-GW-1 strain cross-derivative diagnostic route.
--
-- This receipt records one diagnostic target and its fail-closed boundary.
-- It does not promote a DNS sign result, a nonlinear Riesz sign condition,
-- Navier-Stokes regularity, or Clay status.

scriptPath : String
scriptPath =
  "scripts/ns_gateway1_strain_cross_derivative_diagnostic.py"

mathematicalGateway : String
mathematicalGateway =
  "T_e1 T_e2 lambda2 sign condition"

record NSGateway1DiagnosticTarget : Set where
  constructor mkNSGateway1DiagnosticTarget
  field
    targetName :
      String
    diagnosticSymbol :
      String
    coordinateFrame :
      String
    fieldSource :
      String
    quantityComputed :
      String
    shellOrDatasetScope :
      String
    promotionAllowed :
      Bool
    dnsSignConfirmed :
      Bool
    nonlinearRieszSignConditionConfirmed :
      Bool
    clayNavierStokesPromoted :
      Bool

canonicalTaylorGreenDiagnostic :
  NSGateway1DiagnosticTarget
canonicalTaylorGreenDiagnostic =
  mkNSGateway1DiagnosticTarget
    "synthetic Taylor-Green diagnostic"
    "∂e1∂e2 λ2"
    "strain eigenframe e1/e2 at enstrophy maximum"
    "Taylor-Green synthetic / DNS NPZ adapter"
    "records ∂e1∂e2 λ2 at enstrophy max"
    "synthetic Taylor-Green diagnostic row; DNS dataset still required"
    false
    false
    false
    false

canonicalPromotionAllowed :
  NSGateway1DiagnosticTarget.promotionAllowed
    canonicalTaylorGreenDiagnostic
    ≡ false
canonicalPromotionAllowed =
  refl

canonicalDNSSignConfirmed :
  NSGateway1DiagnosticTarget.dnsSignConfirmed
    canonicalTaylorGreenDiagnostic
    ≡ false
canonicalDNSSignConfirmed =
  refl

canonicalNonlinearRieszSignConditionConfirmed :
  NSGateway1DiagnosticTarget.nonlinearRieszSignConditionConfirmed
    canonicalTaylorGreenDiagnostic
    ≡ false
canonicalNonlinearRieszSignConditionConfirmed =
  refl

canonicalClayNavierStokesPromoted :
  NSGateway1DiagnosticTarget.clayNavierStokesPromoted
    canonicalTaylorGreenDiagnostic
    ≡ false
canonicalClayNavierStokesPromoted =
  refl

record NSGateway1DiagnosticAggregation : Set where
  constructor mkNSGateway1DiagnosticAggregation
  field
    gateway1DiagnosticRouteRecorded :
      Bool
    numericalDNSStillRequired :
      Bool
    nonlinearRieszSignStillOpen :
      Bool
    clayPromotionStillBlocked :
      Bool
    diagnosticScriptReference :
      String
    gatewayReference :
      String

canonicalAggregation :
  NSGateway1DiagnosticAggregation
canonicalAggregation =
  mkNSGateway1DiagnosticAggregation
    true
    true
    true
    true
    scriptPath
    mathematicalGateway

canonicalGateway1DiagnosticRouteRecorded :
  NSGateway1DiagnosticAggregation.gateway1DiagnosticRouteRecorded
    canonicalAggregation
    ≡ true
canonicalGateway1DiagnosticRouteRecorded =
  refl

canonicalNumericalDNSStillRequired :
  NSGateway1DiagnosticAggregation.numericalDNSStillRequired
    canonicalAggregation
    ≡ true
canonicalNumericalDNSStillRequired =
  refl

canonicalNonlinearRieszSignStillOpen :
  NSGateway1DiagnosticAggregation.nonlinearRieszSignStillOpen
    canonicalAggregation
    ≡ true
canonicalNonlinearRieszSignStillOpen =
  refl

canonicalClayPromotionStillBlocked :
  NSGateway1DiagnosticAggregation.clayPromotionStillBlocked
    canonicalAggregation
    ≡ true
canonicalClayPromotionStillBlocked =
  refl

routeRecordedNotPromoted : Bool
routeRecordedNotPromoted =
  true

dnsSignConfirmedHere : Bool
dnsSignConfirmedHere =
  false

nonlinearRieszSignConditionProvedHere : Bool
nonlinearRieszSignConditionProvedHere =
  false

clayNavierStokesPromotedHere : Bool
clayNavierStokesPromotedHere =
  false

routeRecordedNotPromotedIsTrue :
  routeRecordedNotPromoted ≡ true
routeRecordedNotPromotedIsTrue =
  refl

dnsSignConfirmedHereIsFalse :
  dnsSignConfirmedHere ≡ false
dnsSignConfirmedHereIsFalse =
  refl

nonlinearRieszSignConditionProvedHereIsFalse :
  nonlinearRieszSignConditionProvedHere ≡ false
nonlinearRieszSignConditionProvedHereIsFalse =
  refl

clayNavierStokesPromotedHereIsFalse :
  clayNavierStokesPromotedHere ≡ false
clayNavierStokesPromotedHereIsFalse =
  refl

dnsSignClassificationStillOpen : Bool
dnsSignClassificationStillOpen =
  true

numericalDNSRequiredBeforeAnySignPromotion : Bool
numericalDNSRequiredBeforeAnySignPromotion =
  NSGateway1DiagnosticAggregation.numericalDNSStillRequired
    canonicalAggregation

dnsSignClassificationStillOpenIsTrue :
  dnsSignClassificationStillOpen ≡ true
dnsSignClassificationStillOpenIsTrue =
  refl

numericalDNSRequiredBeforeAnySignPromotionIsTrue :
  numericalDNSRequiredBeforeAnySignPromotion ≡ true
numericalDNSRequiredBeforeAnySignPromotionIsTrue =
  refl

organizationString : String
organizationString =
  "NS-GW-1 diagnostic route boundary receipt"

requirementString : String
requirementString =
  "Record the strain cross-derivative diagnostic target while keeping DNS sign, nonlinear Riesz sign, and Clay promotion fail-closed."

codeArtifactString : String
codeArtifactString =
  scriptPath

stateString : String
stateString =
  "Synthetic Taylor-Green row recorded; numerical DNS evidence remains required."

latticeString : String
latticeString =
  mathematicalGateway

proposalString : String
proposalString =
  "Use the diagnostic script output only as evidence routing until real DNS data and the nonlinear sign condition are checked."

governanceString : String
governanceString =
  "promotionAllowed=false, dnsSignConfirmed=false, nonlinearRieszSignConditionConfirmed=false, clayNavierStokesPromoted=false"

gapString : String
gapString =
  "DNS sign and nonlinear Riesz sign condition remain open; Clay Navier-Stokes promotion is blocked."

record NSGateway1DiagnosticReceipt : Set where
  constructor mkNSGateway1DiagnosticReceipt
  field
    target :
      NSGateway1DiagnosticTarget
    aggregation :
      NSGateway1DiagnosticAggregation
    routeRecorded :
      Bool
    routeRecordedIsTrue :
      routeRecorded ≡ true
    dnsSignConfirmed :
      Bool
    dnsSignConfirmedIsFalse :
      dnsSignConfirmed ≡ false
    nonlinearRieszSignConditionProved :
      Bool
    nonlinearRieszSignConditionProvedIsFalse :
      nonlinearRieszSignConditionProved ≡ false
    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    O :
      String
    R :
      String
    C :
      String
    S :
      String
    L :
      String
    P :
      String
    G :
      String
    F :
      String

canonicalReceipt :
  NSGateway1DiagnosticReceipt
canonicalReceipt =
  mkNSGateway1DiagnosticReceipt
    canonicalTaylorGreenDiagnostic
    canonicalAggregation
    routeRecordedNotPromoted
    routeRecordedNotPromotedIsTrue
    dnsSignConfirmedHere
    dnsSignConfirmedHereIsFalse
    nonlinearRieszSignConditionProvedHere
    nonlinearRieszSignConditionProvedHereIsFalse
    clayNavierStokesPromotedHere
    clayNavierStokesPromotedHereIsFalse
    organizationString
    requirementString
    codeArtifactString
    stateString
    latticeString
    proposalString
    governanceString
    gapString

canonicalReceiptTargetDNSSignConfirmedFalseProjection :
  NSGateway1DiagnosticTarget.dnsSignConfirmed
    (NSGateway1DiagnosticReceipt.target canonicalReceipt)
  ≡ false
canonicalReceiptTargetDNSSignConfirmedFalseProjection =
  refl

canonicalReceiptAggregationNumericalDNSRequiredProjection :
  NSGateway1DiagnosticAggregation.numericalDNSStillRequired
    (NSGateway1DiagnosticReceipt.aggregation canonicalReceipt)
  ≡ true
canonicalReceiptAggregationNumericalDNSRequiredProjection =
  refl

canonicalReceiptDNSSignConfirmedFalseProjection :
  NSGateway1DiagnosticReceipt.dnsSignConfirmed canonicalReceipt
  ≡ false
canonicalReceiptDNSSignConfirmedFalseProjection =
  refl

canonicalReceiptNumericalDNSBeforePromotionProjection :
  numericalDNSRequiredBeforeAnySignPromotion ≡ true
canonicalReceiptNumericalDNSBeforePromotionProjection =
  refl
