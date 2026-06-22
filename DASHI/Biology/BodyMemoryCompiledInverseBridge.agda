module DASHI.Biology.BodyMemoryCompiledInverseBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import Ontology.BrainDNA.BrainDnaRepresentationMap as Map
import Ontology.BrainDNA.BrainWholeChainIntegrationLaw as Whole

------------------------------------------------------------------------
-- Candidate-only compiled inverse bridge.
--
-- This file models a thread-local inverse lane as a compile-time surface:
-- live self/world relation, chart-local inverse self * world^-1_j,
-- residual check, carry j+1, and a body-memory reading that comes from
-- applying the old inverse inside a changed world.
--
-- Hard gates stay closed:
-- - not RSA identity
-- - not factorization
-- - not diagnosis
-- - plus-one is not a cure
-- - no clinical authority

data Never : Set where

data CompiledInverseRoute : Set where
  candidateOnlyCompiledInverseRoute : CompiledInverseRoute
  rsaIdentityRoute : CompiledInverseRoute
  factorizationRoute : CompiledInverseRoute
  diagnosisRoute : CompiledInverseRoute
  cureRoute : CompiledInverseRoute
  clinicalAuthorityRoute : CompiledInverseRoute

AdmissibleCompiledInverseRoute : CompiledInverseRoute → Set
AdmissibleCompiledInverseRoute candidateOnlyCompiledInverseRoute = ⊤
AdmissibleCompiledInverseRoute rsaIdentityRoute = Never
AdmissibleCompiledInverseRoute factorizationRoute = Never
AdmissibleCompiledInverseRoute diagnosisRoute = Never
AdmissibleCompiledInverseRoute cureRoute = Never
AdmissibleCompiledInverseRoute clinicalAuthorityRoute = Never

rsaIdentityRouteRejected :
  AdmissibleCompiledInverseRoute rsaIdentityRoute →
  Never
rsaIdentityRouteRejected impossible = impossible

factorizationRouteRejected :
  AdmissibleCompiledInverseRoute factorizationRoute →
  Never
factorizationRouteRejected impossible = impossible

diagnosisRouteRejected :
  AdmissibleCompiledInverseRoute diagnosisRoute →
  Never
diagnosisRouteRejected impossible = impossible

cureRouteRejected :
  AdmissibleCompiledInverseRoute cureRoute →
  Never
cureRouteRejected impossible = impossible

clinicalAuthorityRouteRejected :
  AdmissibleCompiledInverseRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRouteRejected impossible = impossible

data LiveRelationRole : Set where
  selfRole : LiveRelationRole
  worldRole : LiveRelationRole
  chartLocalInverseRole : LiveRelationRole
  residualCheckRole : LiveRelationRole
  carryRole : LiveRelationRole
  oldInverseInChangedWorldRole : LiveRelationRole
  bodyMemoryResidualRole : LiveRelationRole

data ResidualKind : Set where
  chartResidualKind : ResidualKind
  changedWorldResidualKind : ResidualKind
  oldInverseResidualKind : ResidualKind
  carryResidualKind : ResidualKind
  bodyMemoryResidualKind : ResidualKind

data GateKind : Set where
  noRsaIdentityGate : GateKind
  noFactorizationGate : GateKind
  noDiagnosisGate : GateKind
  plusOneNotCureGate : GateKind
  noClinicalAuthorityGate : GateKind

canonicalResidualKinds : List ResidualKind
canonicalResidualKinds =
  chartResidualKind
  ∷ changedWorldResidualKind
  ∷ oldInverseResidualKind
  ∷ carryResidualKind
  ∷ bodyMemoryResidualKind
  ∷ []

canonicalGateKinds : List GateKind
canonicalGateKinds =
  noRsaIdentityGate
  ∷ noFactorizationGate
  ∷ noDiagnosisGate
  ∷ plusOneNotCureGate
  ∷ noClinicalAuthorityGate
  ∷ []

record LiveSelfWorldRelation (n : Nat) : Setω where
  constructor liveSelfWorldRelation
  field
    self :
      Whole.theta_i n

    world :
      Whole.BrainWholeChainIntegrationProfile n

    chart :
      Map.BrainDnaRepresentationSemantics n

    relationRole :
      LiveRelationRole

    relationLabel :
      String

    selfWorldLive :
      Bool

    selfWorldLiveIsTrue :
      selfWorldLive ≡ true

    relationReading :
      String

open LiveSelfWorldRelation public

record ChartLocalInverse (n : Nat) : Setω where
  constructor chartLocalInverse
  field
    liveRelation :
      LiveSelfWorldRelation n

    chartIndex :
      Nat

    selfTerm :
      String

    worldInverseTerm :
      String

    compiledProductTerm :
      String

    compiledInverseTerm :
      String

    residualCheck :
      Bool

    residualCheckIsTrue :
      residualCheck ≡ true

    changedWorldTerm :
      String

    oldInverseInsideChangedWorldTerm :
      String

    carry :
      Nat

    carryIsSucc :
      carry ≡ suc chartIndex

    residualKind :
      ResidualKind

    residualKindIsCanonical :
      residualKind ≡ chartResidualKind

    residualReading :
      String

open ChartLocalInverse public

record BodyMemoryInverseReading (n : Nat) : Setω where
  constructor bodyMemoryInverseReading
  field
    inverseChartLocalInverse :
      ChartLocalInverse n

    bodyMemoryInverseTerm :
      String

    traumaBodyMemoryTerm :
      String

    changedWorldTerm :
      String

    oldInverseAppliedInsideChangedWorld :
      String

    bodyMemoryResidualTerm :
      String

    bodyMemoryReadingResidualKind :
      ResidualKind

    bodyMemoryReadingResidualKindIsCanonical :
      bodyMemoryReadingResidualKind ≡ bodyMemoryResidualKind

open BodyMemoryInverseReading public

record CompiledInverseGateLedger : Set where
  constructor compiledInverseGateLedger
  field
    rsaIdentityBlocked :
      Bool

    rsaIdentityBlockedIsFalse :
      rsaIdentityBlocked ≡ false

    factorizationBlocked :
      Bool

    factorizationBlockedIsFalse :
      factorizationBlocked ≡ false

    diagnosisBlocked :
      Bool

    diagnosisBlockedIsFalse :
      diagnosisBlocked ≡ false

    plusOneNotCure :
      Bool

    plusOneNotCureIsTrue :
      plusOneNotCure ≡ true

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    gates :
      List GateKind

    gatesAreCanonical :
      gates ≡ canonicalGateKinds

open CompiledInverseGateLedger public

canonicalCompiledInverseGateLedger : CompiledInverseGateLedger
canonicalCompiledInverseGateLedger =
  compiledInverseGateLedger
    false
    refl
    false
    refl
    false
    refl
    true
    refl
    false
    refl
    canonicalGateKinds
    refl

record BodyMemoryCompiledInverseBridge (n : Nat) : Setω where
  constructor bodyMemoryCompiledInverseBridge
  field
    theta :
      Whole.theta_i n

    wholeChainProfile :
      Whole.BrainWholeChainIntegrationProfile n

    representationSemantics :
      Map.BrainDnaRepresentationSemantics n

    liveRelation :
      LiveSelfWorldRelation n

    bridgeChartLocalInverse :
      ChartLocalInverse n

    bodyMemoryReading :
      BodyMemoryInverseReading n

    gateLedger :
      CompiledInverseGateLedger

    route :
      CompiledInverseRoute

    routeIsCandidateOnly :
      route ≡ candidateOnlyCompiledInverseRoute

    routeAdmissible :
      AdmissibleCompiledInverseRoute route

    notRsaIdentity :
      Bool

    notRsaIdentityIsFalse :
      notRsaIdentity ≡ false

    notFactorization :
      Bool

    notFactorizationIsFalse :
      notFactorization ≡ false

    notDiagnosis :
      Bool

    notDiagnosisIsFalse :
      notDiagnosis ≡ false

    plusOneNotCure :
      Bool

    plusOneNotCureIsTrue :
      plusOneNotCure ≡ true

    noClinicalAuthority :
      Bool

    noClinicalAuthorityIsFalse :
      noClinicalAuthority ≡ false

    bridgeReading :
      String

open BodyMemoryCompiledInverseBridge public

liveRelationOf :
  ∀ {n} → Whole.theta_i n → LiveSelfWorldRelation n
liveRelationOf θ =
  liveSelfWorldRelation
    θ
    (Whole.brainWholeChainIntegrationProfileOf θ)
    (Map.representationSemanticsOf
      (Whole.theta_i.state θ)
      (Whole.theta_i.region θ))
    selfRole
    "live self/world relation"
    true
    refl
    "self remains live against a changing world chart"

chartLocalInverseOf :
  ∀ {n} → Whole.theta_i n → ChartLocalInverse n
chartLocalInverseOf θ =
  chartLocalInverse
    (liveRelationOf θ)
    zero
    "self"
    "world^-1_j"
    "self * world^-1_j"
    "compiled chart-local inverse"
    true
    refl
    "changed world"
    "old inverse applied inside changed world"
    (suc zero)
    refl
    chartResidualKind
    refl
    "chart-local inverse and residual check remain candidate-only"

bodyMemoryInverseReadingOf :
  ∀ {n} → ChartLocalInverse n → BodyMemoryInverseReading n
bodyMemoryInverseReadingOf ci =
  bodyMemoryInverseReading
    ci
    "body-memory inverse reading"
    "trauma/body-memory is read as the old inverse applied inside a changed world"
    (ChartLocalInverse.changedWorldTerm ci)
    (ChartLocalInverse.oldInverseInsideChangedWorldTerm ci)
    "body-memory residual"
    bodyMemoryResidualKind
    refl

bodyMemoryCompiledInverseBridgeOf :
  ∀ {n} → Whole.theta_i n → BodyMemoryCompiledInverseBridge n
bodyMemoryCompiledInverseBridgeOf θ =
  let
    live = liveRelationOf θ
    chart = chartLocalInverseOf θ
    reading = bodyMemoryInverseReadingOf chart
  in
  bodyMemoryCompiledInverseBridge
    θ
    (Whole.brainWholeChainIntegrationProfileOf θ)
    (Map.representationSemanticsOf
      (Whole.theta_i.state θ)
      (Whole.theta_i.region θ))
    live
    chart
    reading
    canonicalCompiledInverseGateLedger
    candidateOnlyCompiledInverseRoute
    refl
    tt
    false
    refl
    false
    refl
    false
    refl
    true
    refl
    false
    refl
    "candidate-only compiled inverse bridge: self/world, chart-local inverse, residual check, carry j+1, and old inverse inside changed world"

bodyMemoryBridgeThetaExact :
  ∀ {n} (θ : Whole.theta_i n) →
  BodyMemoryCompiledInverseBridge.theta (bodyMemoryCompiledInverseBridgeOf θ) ≡ θ
bodyMemoryBridgeThetaExact θ = refl

bodyMemoryBridgeWorldThetaExact :
  ∀ {n} (θ : Whole.theta_i n) →
  Whole.BrainWholeChainIntegrationProfile.theta
    (BodyMemoryCompiledInverseBridge.wholeChainProfile
      (bodyMemoryCompiledInverseBridgeOf θ))
    ≡
  θ
bodyMemoryBridgeWorldThetaExact θ = refl

bodyMemoryBridgeWorldRecoveryBoundaryExact :
  ∀ {n} (θ : Whole.theta_i n) →
  Whole.BrainWholeChainIntegrationProfile.recoveryBoundary
    (BodyMemoryCompiledInverseBridge.wholeChainProfile
      (bodyMemoryCompiledInverseBridgeOf θ))
    ≡
  Whole.BrainWholeChainIntegrationProfile.recoveryBoundary
    (Whole.brainWholeChainIntegrationProfileOf θ)
bodyMemoryBridgeWorldRecoveryBoundaryExact θ = refl

bodyMemoryBridgeWorldRealismFloorExact :
  ∀ {n} (θ : Whole.theta_i n) →
  Whole.BrainWholeChainIntegrationProfile.realismFloor
    (BodyMemoryCompiledInverseBridge.wholeChainProfile
      (bodyMemoryCompiledInverseBridgeOf θ))
    ≡
  Whole.BrainWholeChainIntegrationProfile.realismFloor
    (Whole.brainWholeChainIntegrationProfileOf θ)
bodyMemoryBridgeWorldRealismFloorExact θ = refl

bodyMemoryBridgeWorldEmittedAdmissibilityExact :
  ∀ {n} (θ : Whole.theta_i n) →
  Whole.BrainWholeChainIntegrationProfile.emittedAdmissibility
    (BodyMemoryCompiledInverseBridge.wholeChainProfile
      (bodyMemoryCompiledInverseBridgeOf θ))
    ≡
  Whole.BrainWholeChainIntegrationProfile.emittedAdmissibility
    (Whole.brainWholeChainIntegrationProfileOf θ)
bodyMemoryBridgeWorldEmittedAdmissibilityExact θ = refl

bodyMemoryBridgeChartExact :
  ∀ {n} (θ : Whole.theta_i n) →
  BodyMemoryCompiledInverseBridge.representationSemantics
    (bodyMemoryCompiledInverseBridgeOf θ)
    ≡
  Map.representationSemanticsOf
    (Whole.theta_i.state θ)
    (Whole.theta_i.region θ)
bodyMemoryBridgeChartExact θ = refl

bodyMemoryBridgeCandidateRoute :
  ∀ {n} (θ : Whole.theta_i n) →
  BodyMemoryCompiledInverseBridge.route (bodyMemoryCompiledInverseBridgeOf θ)
    ≡
  candidateOnlyCompiledInverseRoute
bodyMemoryBridgeCandidateRoute θ = refl

bodyMemoryBridgeCarrySucc :
  ∀ {n} (θ : Whole.theta_i n) →
  ChartLocalInverse.carry
    (BodyMemoryCompiledInverseBridge.bridgeChartLocalInverse
      (bodyMemoryCompiledInverseBridgeOf θ))
    ≡
  suc
    (ChartLocalInverse.chartIndex
      (BodyMemoryCompiledInverseBridge.bridgeChartLocalInverse
        (bodyMemoryCompiledInverseBridgeOf θ)))
bodyMemoryBridgeCarrySucc θ = refl

bodyMemoryBridgeResidualCheck :
  ∀ {n} (θ : Whole.theta_i n) →
  ChartLocalInverse.residualCheck
    (BodyMemoryCompiledInverseBridge.bridgeChartLocalInverse
      (bodyMemoryCompiledInverseBridgeOf θ))
    ≡
  true
bodyMemoryBridgeResidualCheck θ = refl

bodyMemoryBridgePlusOneNotCure :
  ∀ {n} (θ : Whole.theta_i n) →
  BodyMemoryCompiledInverseBridge.plusOneNotCure
    (bodyMemoryCompiledInverseBridgeOf θ)
    ≡
  true
bodyMemoryBridgePlusOneNotCure θ = refl

bodyMemoryBridgeNoClinicalAuthority :
  ∀ {n} (θ : Whole.theta_i n) →
  BodyMemoryCompiledInverseBridge.noClinicalAuthority
    (bodyMemoryCompiledInverseBridgeOf θ)
    ≡
  false
bodyMemoryBridgeNoClinicalAuthority θ = refl

record BodyMemoryCompiledInverseBridgeSurface : Setω where
  field
    candidateRoute :
      CompiledInverseRoute

    candidateRouteIsAdmissible :
      AdmissibleCompiledInverseRoute candidateRoute

    bridge :
      ∀ {n} → Whole.theta_i n → BodyMemoryCompiledInverseBridge n

    surfaceReading :
      String

bodyMemoryCompiledInverseBridgeSurface :
  BodyMemoryCompiledInverseBridgeSurface
bodyMemoryCompiledInverseBridgeSurface = record
  { candidateRoute = candidateOnlyCompiledInverseRoute
  ; candidateRouteIsAdmissible = tt
  ; bridge = bodyMemoryCompiledInverseBridgeOf
  ; surfaceReading =
      "Compiled inverse body-memory bridge: self/world, world^-1_j, residual check, carry j+1, and old inverse in changed world remain candidate-only and non-clinical."
  }
