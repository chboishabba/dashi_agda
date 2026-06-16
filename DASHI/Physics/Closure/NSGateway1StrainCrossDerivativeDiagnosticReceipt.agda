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
--
-- Current nine-result conclusion: the t=0 synthetic/fixture row is
-- eigenframe-degenerate, so zero/noise cross-derivative values are not sign
-- evidence.  Real DNS snapshots near t≈7-9 are required before any sign
-- promotion can even be considered.  Pressure-Hessian promotion is also
-- held behind an explicit axis-order/incompressibility audit receipt.
--
-- Follow-up FluidSim Re=1600 Taylor-Green runs at t≈9 resolved the first
-- non-degenerate sign ambiguity: N=64 gave a positive under-resolved row,
-- while N=128 gave a negative, non-degenerate row.  This keeps the signed
-- T(b) route empirically live, but it still does not promote the nonlinear
-- Riesz sign condition; an independent external DNS time-window receipt is
-- still required.

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
    t0SyntheticFixture :
      Bool
    eigenframeDegenerate :
      Bool
    zeroOrNoiseCrossDerivativeIsSignEvidence :
      Bool
    realDNSTimeSevenToNineRequired :
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
    true
    true
    false
    true

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

canonicalT0SyntheticFixture :
  NSGateway1DiagnosticTarget.t0SyntheticFixture
    canonicalTaylorGreenDiagnostic
    ≡ true
canonicalT0SyntheticFixture =
  refl

canonicalEigenframeDegenerate :
  NSGateway1DiagnosticTarget.eigenframeDegenerate
    canonicalTaylorGreenDiagnostic
    ≡ true
canonicalEigenframeDegenerate =
  refl

canonicalZeroOrNoiseCrossDerivativeIsNotSignEvidence :
  NSGateway1DiagnosticTarget.zeroOrNoiseCrossDerivativeIsSignEvidence
    canonicalTaylorGreenDiagnostic
    ≡ false
canonicalZeroOrNoiseCrossDerivativeIsNotSignEvidence =
  refl

canonicalRealDNSTimeSevenToNineRequired :
  NSGateway1DiagnosticTarget.realDNSTimeSevenToNineRequired
    canonicalTaylorGreenDiagnostic
    ≡ true
canonicalRealDNSTimeSevenToNineRequired =
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
    degeneracyConclusionRecorded :
      Bool
    zeroNoiseCrossDerivativeSignEvidenceBlocked :
      Bool
    realDNSWindowStillRequired :
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
    true
    true
    true
    scriptPath
    mathematicalGateway

record NSGateway1ResolutionSeriesReceipt : Set where
  constructor mkNSGateway1ResolutionSeriesReceipt
  field
    seriesName :
      String
    n64FieldPath :
      String
    n64Source :
      String
    n64Grid :
      String
    n64Time :
      String
    n64CrossDerivative :
      String
    n64EigenframeDegenerate :
      Bool
    n64EigenframeDegenerateIsFalse :
      n64EigenframeDegenerate ≡ false
    n64Classification :
      String
    n64UnderResolvedAliasingSuspected :
      Bool
    n64UnderResolvedAliasingSuspectedIsTrue :
      n64UnderResolvedAliasingSuspected ≡ true
    n128FieldPath :
      String
    n128Source :
      String
    n128Grid :
      String
    n128Time :
      String
    n128CrossDerivative :
      String
    n128EigenframeDegenerate :
      Bool
    n128EigenframeDegenerateIsFalse :
      n128EigenframeDegenerate ≡ false
    n128MinEigenvalueGap :
      String
    n128Classification :
      String
    n128SignSupportsNonpositiveRule :
      Bool
    n128SignSupportsNonpositiveRuleIsTrue :
      n128SignSupportsNonpositiveRule ≡ true
    n128ResolvesN64SignInversion :
      Bool
    n128ResolvesN64SignInversionIsTrue :
      n128ResolvesN64SignInversion ≡ true
    routeEmpiricallyLive :
      Bool
    routeEmpiricallyLiveIsTrue :
      routeEmpiricallyLive ≡ true
    externalDNSWindowStillRequired :
      Bool
    externalDNSWindowStillRequiredIsTrue :
      externalDNSWindowStillRequired ≡ true
    nonlinearRieszSignPromotedHere :
      Bool
    nonlinearRieszSignPromotedHereIsFalse :
      nonlinearRieszSignPromotedHere ≡ false
    clayPromotionHere :
      Bool
    clayPromotionHereIsFalse :
      clayPromotionHere ≡ false
    analysisConclusion :
      String

canonicalResolutionSeriesReceipt :
  NSGateway1ResolutionSeriesReceipt
canonicalResolutionSeriesReceipt =
  mkNSGateway1ResolutionSeriesReceipt
    "NS-GW-1 FluidSim Taylor-Green Re=1600 t≈9 resolution series"
    "/tmp/tg_re1600_t9_N64_fluidsim.npz"
    "FluidSim ns3d pseudo-spectral Taylor-Green"
    "N=64"
    "t=9.009999999999852"
    "+346.53387265024656"
    false
    refl
    "positive_adverse_to_nonpositive_rule"
    true
    refl
    "/tmp/tg_re1600_t9_N128_fluidsim.npz"
    "FluidSim ns3d pseudo-spectral Taylor-Green"
    "N=128"
    "t=9.009999999999852"
    "-1116.3493344286098"
    false
    refl
    "1.938833755893448"
    "negative_supports_nonpositive_rule"
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    "N=128 is non-degenerate and supports the nonpositive local eigenframe cross-derivative route; this is empirical route evidence only, with external DNS and nonlinear Riesz promotion still fail-closed."

canonicalResolutionSeriesN128SignSupportsRoute :
  NSGateway1ResolutionSeriesReceipt.n128SignSupportsNonpositiveRule
    canonicalResolutionSeriesReceipt
  ≡ true
canonicalResolutionSeriesN128SignSupportsRoute =
  refl

canonicalResolutionSeriesRouteEmpiricallyLive :
  NSGateway1ResolutionSeriesReceipt.routeEmpiricallyLive
    canonicalResolutionSeriesReceipt
  ≡ true
canonicalResolutionSeriesRouteEmpiricallyLive =
  refl

canonicalResolutionSeriesExternalDNSStillRequired :
  NSGateway1ResolutionSeriesReceipt.externalDNSWindowStillRequired
    canonicalResolutionSeriesReceipt
  ≡ true
canonicalResolutionSeriesExternalDNSStillRequired =
  refl

canonicalResolutionSeriesNonlinearRieszStillUnpromoted :
  NSGateway1ResolutionSeriesReceipt.nonlinearRieszSignPromotedHere
    canonicalResolutionSeriesReceipt
  ≡ false
canonicalResolutionSeriesNonlinearRieszStillUnpromoted =
  refl

canonicalResolutionSeriesClayStillUnpromoted :
  NSGateway1ResolutionSeriesReceipt.clayPromotionHere
    canonicalResolutionSeriesReceipt
  ≡ false
canonicalResolutionSeriesClayStillUnpromoted =
  refl

record NSGateway1AxisOrderIncompressibilityAuditReceipt : Set where
  constructor mkNSGateway1AxisOrderIncompressibilityAuditReceipt
  field
    auditName :
      String
    axisOrderAuditRecorded :
      Bool
    axisOrderAuditRecordedIsTrue :
      axisOrderAuditRecorded ≡ true
    incompressibilityAuditRecorded :
      Bool
    incompressibilityAuditRecordedIsTrue :
      incompressibilityAuditRecorded ≡ true
    requiredBeforePressureHessianPromotion :
      Bool
    requiredBeforePressureHessianPromotionIsTrue :
      requiredBeforePressureHessianPromotion ≡ true
    pressureHessianTheoremPromotedHere :
      Bool
    pressureHessianTheoremPromotedHereIsFalse :
      pressureHessianTheoremPromotedHere ≡ false
    clayClaimPromotedHere :
      Bool
    clayClaimPromotedHereIsFalse :
      clayClaimPromotedHere ≡ false
    auditConclusion :
      String

canonicalAxisOrderIncompressibilityAuditReceipt :
  NSGateway1AxisOrderIncompressibilityAuditReceipt
canonicalAxisOrderIncompressibilityAuditReceipt =
  mkNSGateway1AxisOrderIncompressibilityAuditReceipt
    "NS-GW-1 axis-order/incompressibility audit"
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    "Axis-order and incompressibility are recorded as prerequisites before pressure-Hessian promotion; the theorem and Clay claims stay false."

record NSGateway1PressureHessianDiagnosticResult : Set where
  constructor mkNSGateway1PressureHessianDiagnosticResult
  field
    diagnosticName :
      String
    axisOrderIncompressibilityAudit :
      NSGateway1AxisOrderIncompressibilityAuditReceipt
    qcritSign :
      String
    pressureHessianCrossDerivative :
      String
    lambda2CrossDerivative :
      String
    omegaNormSquaredCrossDerivative :
      String
    strainNormSquaredCrossDerivative :
      String
    localDecompositionTail :
      String
    vorticityDominanceMargin :
      String
    vorticityDominance :
      Bool
    vorticityDominanceIsTrue :
      vorticityDominance ≡ true
    pressurePoissonConvention :
      String
    divergenceResidual :
      String
    localToGlobalTheoremPromoted :
      Bool
    localToGlobalTheoremPromotedIsFalse :
      localToGlobalTheoremPromoted ≡ false
    externalDNSRequired :
      Bool
    externalDNSRequiredIsTrue :
      externalDNSRequired ≡ true
    resultPromotedHere :
      Bool
    resultPromotedHereIsFalse :
      resultPromotedHere ≡ false
    diagnosticConclusion :
      String

canonicalPressureHessianDiagnosticResult :
  NSGateway1PressureHessianDiagnosticResult
canonicalPressureHessianDiagnosticResult =
  mkNSGateway1PressureHessianDiagnosticResult
    "NS-GW-1 pressure-Hessian diagnostic result"
    canonicalAxisOrderIncompressibilityAuditReceipt
    "axis-corrected pressure_hessian_e1_e2_at_max positive on local FluidSim N=128 row; pressure-Hessian sign route adverse and unpromoted"
    "15.909006049568312"
    "-690.5589798533151"
    "-132442.67124306824"
    "-53862.34109935466"
    "-12343.085516129893"
    "15.909006049565505"
    true
    refl
    "-Delta p = |S|^2 - 0.5*|omega|^2, zero-mean periodic pressure solve, numpy array axis order z,y,x"
    "divergence_max_abs=2.7533531010703882e-14; divergence_l2_mean=4.363464778751043e-15; xyz_storage_divergence_max_abs=25.896617641470364; pressure_poisson_rhs_mean=-8.673617379884035e-18"
    false
    refl
    true
    refl
    false
    refl
    "Pressure-Hessian Qcrit is negative on the local N=128 FluidSim row, but the proposed vorticity-dominance sufficient condition fails, the divergence/RHS residuals are recorded, local-to-global theorem promotion is false, and external DNS remains required."

canonicalPressureHessianLocalToGlobalTheoremPromotedFalse :
  NSGateway1PressureHessianDiagnosticResult.localToGlobalTheoremPromoted
    canonicalPressureHessianDiagnosticResult
  ≡ false
canonicalPressureHessianLocalToGlobalTheoremPromotedFalse =
  refl

canonicalPressureHessianExternalDNSRequiredTrue :
  NSGateway1PressureHessianDiagnosticResult.externalDNSRequired
    canonicalPressureHessianDiagnosticResult
  ≡ true
canonicalPressureHessianExternalDNSRequiredTrue =
  refl

canonicalPressureHessianResultPromotedHereFalse :
  NSGateway1PressureHessianDiagnosticResult.resultPromotedHere
    canonicalPressureHessianDiagnosticResult
  ≡ false
canonicalPressureHessianResultPromotedHereFalse =
  refl

canonicalPressureHessianVorticityDominanceRecordedTrue :
  NSGateway1PressureHessianDiagnosticResult.vorticityDominance
    canonicalPressureHessianDiagnosticResult
  ≡ true
canonicalPressureHessianVorticityDominanceRecordedTrue =
  refl

canonicalPressureHessianAxisOrderAuditRecordedTrue :
  NSGateway1PressureHessianDiagnosticResult.axisOrderIncompressibilityAudit
    canonicalPressureHessianDiagnosticResult
  ≡ canonicalAxisOrderIncompressibilityAuditReceipt
canonicalPressureHessianAxisOrderAuditRecordedTrue =
  refl

canonicalAxisOrderIncompressibilityAuditRequiredBeforePressureHessianPromotion :
  NSGateway1AxisOrderIncompressibilityAuditReceipt.requiredBeforePressureHessianPromotion
    canonicalAxisOrderIncompressibilityAuditReceipt
  ≡ true
canonicalAxisOrderIncompressibilityAuditRequiredBeforePressureHessianPromotion =
  refl

canonicalAxisOrderIncompressibilityAuditAxisOrderRecordedTrue :
  NSGateway1AxisOrderIncompressibilityAuditReceipt.axisOrderAuditRecorded
    canonicalAxisOrderIncompressibilityAuditReceipt
  ≡ true
canonicalAxisOrderIncompressibilityAuditAxisOrderRecordedTrue =
  refl

canonicalAxisOrderIncompressibilityAuditIncompressibilityRecordedTrue :
  NSGateway1AxisOrderIncompressibilityAuditReceipt.incompressibilityAuditRecorded
    canonicalAxisOrderIncompressibilityAuditReceipt
  ≡ true
canonicalAxisOrderIncompressibilityAuditIncompressibilityRecordedTrue =
  refl

canonicalAxisOrderIncompressibilityAuditPressureHessianTheoremFalse :
  NSGateway1AxisOrderIncompressibilityAuditReceipt.pressureHessianTheoremPromotedHere
    canonicalAxisOrderIncompressibilityAuditReceipt
  ≡ false
canonicalAxisOrderIncompressibilityAuditPressureHessianTheoremFalse =
  refl

canonicalAxisOrderIncompressibilityAuditClayClaimFalse :
  NSGateway1AxisOrderIncompressibilityAuditReceipt.clayClaimPromotedHere
    canonicalAxisOrderIncompressibilityAuditReceipt
  ≡ false
canonicalAxisOrderIncompressibilityAuditClayClaimFalse =
  refl

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

canonicalDegeneracyConclusionRecorded :
  NSGateway1DiagnosticAggregation.degeneracyConclusionRecorded
    canonicalAggregation
    ≡ true
canonicalDegeneracyConclusionRecorded =
  refl

canonicalZeroNoiseCrossDerivativeSignEvidenceBlocked :
  NSGateway1DiagnosticAggregation.zeroNoiseCrossDerivativeSignEvidenceBlocked
    canonicalAggregation
    ≡ true
canonicalZeroNoiseCrossDerivativeSignEvidenceBlocked =
  refl

canonicalRealDNSWindowStillRequired :
  NSGateway1DiagnosticAggregation.realDNSWindowStillRequired
    canonicalAggregation
    ≡ true
canonicalRealDNSWindowStillRequired =
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

t0SyntheticFixtureEigenframeDegenerateHere : Bool
t0SyntheticFixtureEigenframeDegenerateHere =
  true

zeroOrNoiseCrossDerivativeNotSignEvidenceHere : Bool
zeroOrNoiseCrossDerivativeNotSignEvidenceHere =
  true

realDNSTimeSevenToNineRequiredHere : Bool
realDNSTimeSevenToNineRequiredHere =
  true

dnsSignClassificationStillOpenIsTrue :
  dnsSignClassificationStillOpen ≡ true
dnsSignClassificationStillOpenIsTrue =
  refl

numericalDNSRequiredBeforeAnySignPromotionIsTrue :
  numericalDNSRequiredBeforeAnySignPromotion ≡ true
numericalDNSRequiredBeforeAnySignPromotionIsTrue =
  refl

t0SyntheticFixtureEigenframeDegenerateHereIsTrue :
  t0SyntheticFixtureEigenframeDegenerateHere ≡ true
t0SyntheticFixtureEigenframeDegenerateHereIsTrue =
  refl

zeroOrNoiseCrossDerivativeNotSignEvidenceHereIsTrue :
  zeroOrNoiseCrossDerivativeNotSignEvidenceHere ≡ true
zeroOrNoiseCrossDerivativeNotSignEvidenceHereIsTrue =
  refl

realDNSTimeSevenToNineRequiredHereIsTrue :
  realDNSTimeSevenToNineRequiredHere ≡ true
realDNSTimeSevenToNineRequiredHereIsTrue =
  refl

organizationString : String
organizationString =
  "NS-GW-1 diagnostic route boundary receipt"

requirementString : String
requirementString =
  "Record the nine-result degeneracy conclusion while keeping DNS sign, nonlinear Riesz sign, axis-order/incompressibility audit, pressure-Hessian promotion, and Clay promotion fail-closed."

codeArtifactString : String
codeArtifactString =
  scriptPath

stateString : String
stateString =
  "t=0 synthetic/fixture eigenframe_degenerate=true; FluidSim TG Re=1600 t≈9 N=64 positive row is superseded by non-degenerate N=128 negative row; axis-order/incompressibility audit is required before any pressure-Hessian promotion; local sign route is live but unpromoted."

latticeString : String
latticeString =
  mathematicalGateway

proposalString : String
proposalString =
  "Use diagnostic output only as evidence routing; proceed to NS-GW-2a while requiring independent external DNS t≈7-9 before nonlinear Riesz sign promotion and requiring the axis-order/incompressibility audit before any pressure-Hessian promotion."

governanceString : String
governanceString =
  "promotionAllowed=false, dnsSignConfirmed=false, nonlinearRieszSignConditionConfirmed=false, clayNavierStokesPromoted=false, pressureHessianTheoremPromotedHere=false, zeroOrNoiseCrossDerivativeIsSignEvidence=false"

gapString : String
gapString =
  "Independent external DNS t≈7-9, axis-order/incompressibility audit closure, global Riesz-vs-local-cross-derivative extraction, and nonlinear Riesz sign theorem remain open; Clay Navier-Stokes promotion is blocked."

record NSGateway1DiagnosticReceipt : Set where
  constructor mkNSGateway1DiagnosticReceipt
  field
    target :
      NSGateway1DiagnosticTarget
    aggregation :
      NSGateway1DiagnosticAggregation
    resolutionSeries :
      NSGateway1ResolutionSeriesReceipt
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
    t0SyntheticFixtureEigenframeDegenerate :
      Bool
    t0SyntheticFixtureEigenframeDegenerateIsTrue :
      t0SyntheticFixtureEigenframeDegenerate ≡ true
    zeroOrNoiseCrossDerivativeNotSignEvidence :
      Bool
    zeroOrNoiseCrossDerivativeNotSignEvidenceIsTrue :
      zeroOrNoiseCrossDerivativeNotSignEvidence ≡ true
    realDNSTimeSevenToNineRequired :
      Bool
    realDNSTimeSevenToNineRequiredIsTrue :
      realDNSTimeSevenToNineRequired ≡ true
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
    canonicalResolutionSeriesReceipt
    routeRecordedNotPromoted
    routeRecordedNotPromotedIsTrue
    dnsSignConfirmedHere
    dnsSignConfirmedHereIsFalse
    nonlinearRieszSignConditionProvedHere
    nonlinearRieszSignConditionProvedHereIsFalse
    clayNavierStokesPromotedHere
    clayNavierStokesPromotedHereIsFalse
    t0SyntheticFixtureEigenframeDegenerateHere
    t0SyntheticFixtureEigenframeDegenerateHereIsTrue
    zeroOrNoiseCrossDerivativeNotSignEvidenceHere
    zeroOrNoiseCrossDerivativeNotSignEvidenceHereIsTrue
    realDNSTimeSevenToNineRequiredHere
    realDNSTimeSevenToNineRequiredHereIsTrue
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

canonicalReceiptT0SyntheticFixtureEigenframeDegenerateProjection :
  NSGateway1DiagnosticReceipt.t0SyntheticFixtureEigenframeDegenerate
    canonicalReceipt
  ≡ true
canonicalReceiptT0SyntheticFixtureEigenframeDegenerateProjection =
  refl

canonicalReceiptZeroOrNoiseCrossDerivativeNotSignEvidenceProjection :
  NSGateway1DiagnosticReceipt.zeroOrNoiseCrossDerivativeNotSignEvidence
    canonicalReceipt
  ≡ true
canonicalReceiptZeroOrNoiseCrossDerivativeNotSignEvidenceProjection =
  refl

canonicalReceiptRealDNSTimeSevenToNineRequiredProjection :
  NSGateway1DiagnosticReceipt.realDNSTimeSevenToNineRequired
    canonicalReceipt
  ≡ true
canonicalReceiptRealDNSTimeSevenToNineRequiredProjection =
  refl
