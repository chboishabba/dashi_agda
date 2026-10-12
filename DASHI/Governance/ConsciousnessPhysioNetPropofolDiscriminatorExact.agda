module DASHI.Governance.ConsciousnessPhysioNetPropofolDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Governance.ConsciousnessPhysicalDiscriminatorSynthesisExact as Consciousness

------------------------------------------------------------------------
-- MEASURED PHYSICAL DISCRIMINATOR: PROPOFOL LOC/ROC + EDA/ECG COVARIATES
--
-- Public dataset:
--   PhysioNet, "Behavioral and autonomic dynamics during propofol-induced
--   unconsciousness", version 1.0, DOI 10.13026/2rbc-1r03.
--
-- The study supplies nine healthy-volunteer propofol experiments, behavioural
-- loss/recovery-of-consciousness annotations, ECG, EDA and derived autonomic
-- coordinates.  Its published EDA visualisation maps each summary row to
-- `row * 20 / 60` minutes.  The repository metadata labels the compact
-- LOC_ROC table as seconds, but subject 1's raw files give LOC=3625.32 s and
-- ROC=10920.93 s, while the compact values 40.4093 and 162.0028 are exactly
-- those same events after a common 20.0127-minute origin shift.  This owner
-- therefore records both clocks and makes the offset reconciliation explicit.
--
-- This is an empirical discriminator instance, not evidence that EDA/HRV is
-- consciousness, not an exceptional-geometry neural realization, and not an
-- independent replication.  Phenylephrine/autonomic-vs-behavioural pathway
-- issues remain explicit nuisance/interpretation coordinates.
------------------------------------------------------------------------

record MeasuredCoordinate5 : Set where
  constructor measuredCoordinate5
  field
    c1 c2 c3 c4 c5 : String
open MeasuredCoordinate5 public

subject1PreLOC : MeasuredCoordinate5
subject1PreLOC =
  measuredCoordinate5
    "4.76208579591535"
    "4.18793376064776"
    "3.90142621690925"
    "0.0577025806511029"
    "0.0146947577955462"

subject1PostROC : MeasuredCoordinate5
subject1PostROC =
  measuredCoordinate5
    "1.69885090149667"
    "1.51237995747815"
    "1.55118912018814"
    "0.0333121704836705"
    "0.00364258367063108"

subject1RawLOCSeconds : String
subject1RawLOCSeconds = "3625.32"

subject1RawROCSeconds : String
subject1RawROCSeconds = "10920.93"

subject1AdjustedLOCMinutes : String
subject1AdjustedLOCMinutes = "40.4093"

subject1AdjustedROCMinutes : String
subject1AdjustedROCMinutes = "162.0028"

subject1CommonOriginOffsetMinutes : String
subject1CommonOriginOffsetMinutes = "20.0127"

preLOCRow : Nat
preLOCRow = 120

postROCRow : Nat
postROCRow = 487

preLOCTimeAdjustedMinutes : String
preLOCTimeAdjustedMinutes = "40.0"

postROCTimeAdjustedMinutes : String
postROCTimeAdjustedMinutes = "162.33333333333333"

logCoordinateDistance : String
logCoordinateDistance = "2.279858209762054"

------------------------------------------------------------------------
-- Existing discriminator contract instantiated with real measurement/provenance.
------------------------------------------------------------------------

physioNetPropofolDiscriminatorReceipt : Consciousness.PhysicalTheoryDiscriminatorReceipt
physioNetPropofolDiscriminatorReceipt =
  Consciousness.physical-theory-discriminator-receipt
    "five measured EDA/autonomic summary coordinates from PhysioNet EDA_temp_amp_1.csv"
    "same human subject 1 observed before behavioural LOC and after behavioural ROC"
    "computer-controlled propofol target-controlled infusion; behavioural button-response LOC/ROC task"
    "ECG + electrodermal activity with published derived EDA/autonomic summary coordinates"
    "EDA_deepdive_viz.m maps summary row k to k*20/60 minutes; raw subject-1 LOC/ROC are 3625.32/10920.93 seconds and reconcile with compact 40.4093/162.0028 values after common 20.0127-minute origin shift"
    "phenylephrine may be administered; autonomic and behavioural circuits are related but non-identical; public metadata/unit wording for compact LOC_ROC table is retained as a provenance caveat"
    "coarse behaviour-only observer labels both selected states responsive/conscious, while a substrate-sensitive physical-coordinate observer distinguishes their measured autonomic vectors"
    "PhysioNet v1.0, Behavioral and autonomic dynamics during propofol-induced unconsciousness, DOI 10.13026/2rbc-1r03"
    "within-dataset exact row/time-origin reconciliation and coordinate regression only; independent replication intentionally remains open for this first inhabitant"

record PhysioNetPropofolDiscriminatorLocalReceipt : Set where
  constructor physionet-propofol-discriminator-local-receipt
  field
    measuredHumanDataset : Bool
    controlledPropofolIntervention : Bool
    behaviouralLOCROCAnnotations : Bool
    measuredPhysicalCoordinates : Bool
    rowTimeCalibrationAvailable : Bool
    rawAndAdjustedClockOriginsReconciled : Bool
    preRowStrictlyBeforeLOCChecked : Bool
    postRowStrictlyAfterROCChecked : Bool
    sameCoarseResponsiveLabel : Bool
    physicalCoordinatesDistinct : Bool
    positiveLogCoordinateDistanceChecked : Bool
    logDistanceExceedsTwoChecked : Bool
    nuisanceCoordinatesRetained : Bool
    provenancePinned : Bool
    physicalDiscriminatorContractInhabited : Bool
    independentReplicationPaid : Bool
    consciousnessMechanismProved : Bool
    exceptionalGeometryNeuralSameObjectPaid : Bool
    boundary : String
open PhysioNetPropofolDiscriminatorLocalReceipt public

canonicalPhysioNetPropofolDiscriminatorLocalReceipt : PhysioNetPropofolDiscriminatorLocalReceipt
canonicalPhysioNetPropofolDiscriminatorLocalReceipt =
  physionet-propofol-discriminator-local-receipt
    true true true true true true true true true true true true true true true
    false false false
    "A real subject supplies the required observer collision after explicit time-origin reconciliation: responsive before LOC and responsive after ROC, yet the measured five-coordinate autonomic vectors differ (local Python log-coordinate distance 2.279858209762054). This pays an empirical discriminator shape only; it does not identify the measured coordinates with consciousness or with the exceptional hyperfabric."

------------------------------------------------------------------------
-- No-promotion firewall.
------------------------------------------------------------------------

data AutonomicDifferenceProvesConsciousnessMechanism : Set where

data PropofolDatasetCreatesExceptionalNeuralGeometry : Set where

autonomicDifferenceDoesNotProveConsciousness :
  AutonomicDifferenceProvesConsciousnessMechanism → {A : Set} → A
autonomicDifferenceDoesNotProveConsciousness ()

propofolDataDoesNotCreateExceptionalGeometry :
  PropofolDatasetCreatesExceptionalNeuralGeometry → {A : Set} → A
propofolDataDoesNotCreateExceptionalGeometry ()
