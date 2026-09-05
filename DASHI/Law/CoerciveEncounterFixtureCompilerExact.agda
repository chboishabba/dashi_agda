module DASHI.Law.CoerciveEncounterFixtureCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.CoerciveEncounterLawfulnessBidiExact as Law
import DASHI.Law.CoerciveEncounterLawfulnessProductExact as Product
import DASHI.Law.EvidenceProvenanceDependencyDagExact as Dag

------------------------------------------------------------------------
-- Empirical carrier.
--
-- A fixture stores record-level observations without promoting them to a legal
-- conclusion.  Compilation below projects those observations into existing
-- trajectory/lawfulness/provenance obligations.
------------------------------------------------------------------------

data FieldState : Set where
  observedTrue observedFalse fieldMissing fieldConflict : FieldState

record EncounterFixture : Set where
  constructor encounterFixture
  field
    encounterId : String
    eventTime : String
    place : String
    operationReference : String
    selectionBasisReference : String

    wandOccurred : FieldState
    wandAuthorityApplicable : FieldState
    triggerSatisfied : FieldState
    scopeSatisfied : FieldState
    procedureSatisfied : FieldState

    identityNotice : FieldState
    purposeNotice : FieldState
    nonComplianceNotice : FieldState
    leastInvasiveExercise : FieldState
    detentionDurationSatisfied : FieldState

    chronologyClosed : FieldState
    wandEvidenceReceipt : FieldState

    scannerAlarm : FieldState
    nonCompliance : FieldState
    searchOccurred : FieldState
    searchPredicateReceipt : FieldState
    weaponFound : FieldState
    otherContrabandFound : FieldState
    arrestOccurred : FieldState
    chargeOccurred : FieldState

    bodyCameraPresent : FieldState
    bodyCameraActivated : FieldState
    deviceTelemetryPresent : FieldState
    independentWitnessPresent : FieldState
    medicalEvidencePresent : FieldState
    independentProducerPresent : FieldState

    fixtureReference : String

open EncounterFixture public

------------------------------------------------------------------------
-- Field-to-obligation compilation.
------------------------------------------------------------------------

closedWhenTrue : FieldState → Product.CoordinateState
closedWhenTrue observedTrue = Product.coordinateClosed
closedWhenTrue observedFalse = Product.coordinateOpen
closedWhenTrue fieldMissing = Product.coordinateOpen
closedWhenTrue fieldConflict = Product.coordinateOpen

allSafeguardsClosed : EncounterFixture → Product.CoordinateState
allSafeguardsClosed f with identityNotice f
... | observedTrue with purposeNotice f
...   | observedTrue with nonComplianceNotice f
...     | observedTrue with leastInvasiveExercise f
...       | observedTrue with detentionDurationSatisfied f
...         | observedTrue = Product.coordinateClosed
...         | _ = Product.coordinateOpen
...       | _ = Product.coordinateOpen
...     | _ = Product.coordinateOpen
...   | _ = Product.coordinateOpen
... | _ = Product.coordinateOpen

compileLawfulnessVector : EncounterFixture → Product.LawfulnessObligationVector
compileLawfulnessVector f =
  Product.lawfulnessObligationVector
    (closedWhenTrue (wandOccurred f))
    (closedWhenTrue (wandAuthorityApplicable f))
    (closedWhenTrue (triggerSatisfied f))
    (closedWhenTrue (scopeSatisfied f))
    (closedWhenTrue (procedureSatisfied f))
    (allSafeguardsClosed f)
    (closedWhenTrue (chronologyClosed f))
    (closedWhenTrue (wandEvidenceReceipt f))

firstLawfulnessResidual : EncounterFixture → Product.LawfulnessReverseResult
firstLawfulnessResidual f = Product.firstOpenLawfulness (compileLawfulnessVector f)

------------------------------------------------------------------------
-- Provenance/audit projection.
------------------------------------------------------------------------

independenceState : EncounterFixture → Dag.IndependenceState
independenceState f with independentProducerPresent f
... | observedTrue = Dag.independent
... | observedFalse = Dag.dependent
... | fieldMissing = Dag.independenceUnresolved
... | fieldConflict = Dag.independenceUnresolved

record AuditProjection : Set where
  constructor auditProjection
  field
    camera : FieldState
    telemetry : FieldState
    witness : FieldState
    medical : FieldState
    producerIndependence : Dag.IndependenceState

open AuditProjection public

compileAuditProjection : EncounterFixture → AuditProjection
compileAuditProjection f =
  auditProjection
    (bodyCameraActivated f)
    (deviceTelemetryPresent f)
    (independentWitnessPresent f)
    (medicalEvidencePresent f)
    (independenceState f)

------------------------------------------------------------------------
-- Canonical fixture: the encounter occurred and upstream authority/scope are
-- recorded, but safeguard receipt is absent.  Downstream success is deliberately
-- present to prove it cannot skip the earlier legal gap.
------------------------------------------------------------------------

canonicalMissingSafeguardFixture : EncounterFixture
canonicalMissingSafeguardFixture = encounterFixture
  "fixture-qld-wand-001"
  "2026-09-05T12:00:00+10:00"
  "Queensland relevant-place fixture"
  "authorised wanding operation fixture"
  "selection basis recorded"
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  fieldMissing
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedFalse
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedTrue
  observedFalse
  fieldMissing
  fieldMissing
  observedFalse
  fieldMissing
  observedFalse
  "abstract Queensland wanding regression fixture; not a real-person event"

canonicalFixtureStopsAtSafeguard :
  firstLawfulnessResidual canonicalMissingSafeguardFixture
  ≡ Product.firstOpenLawfulnessCoordinate Product.safeguardCoordinate
canonicalFixtureStopsAtSafeguard = refl

canonicalFixtureSearchCannotLeapfrogSafeguard :
  searchOccurred canonicalMissingSafeguardFixture ≡ observedTrue
canonicalFixtureSearchCannotLeapfrogSafeguard = refl

canonicalFixtureContrabandCannotLeapfrogSafeguard :
  otherContrabandFound canonicalMissingSafeguardFixture ≡ observedTrue
canonicalFixtureContrabandCannotLeapfrogSafeguard = refl

------------------------------------------------------------------------
-- Boundary: fixture ingestion is non-promoting.
------------------------------------------------------------------------

record FixtureCompilerBoundary : Set where
  constructor fixtureCompilerBoundary
  field
    downstreamOutcomeClosesEarlierLegalGap : Bool
    downstreamOutcomeClosesEarlierLegalGapIsFalse :
      downstreamOutcomeClosesEarlierLegalGap ≡ false
    missingFieldIsNegativeReceipt : Bool
    missingFieldIsNegativeReceiptIsFalse :
      missingFieldIsNegativeReceipt ≡ false
    fixtureAutomaticallyProvesLawfulness : Bool
    fixtureAutomaticallyProvesLawfulnessIsFalse :
      fixtureAutomaticallyProvesLawfulness ≡ false

canonicalFixtureCompilerBoundary : FixtureCompilerBoundary
canonicalFixtureCompilerBoundary =
  fixtureCompilerBoundary false refl false refl false refl
