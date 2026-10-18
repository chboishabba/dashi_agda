module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDObservableSetAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- LT-MD MONITORING SURFACE VERSUS BE-META BIAS-CV SURFACE
--
-- Li, Liu & Ji 2015 explicitly state that AdK conformational transitions were
-- monitored by four variables:
--   1. C-alpha RMSD with reference to open and closed conformations,
--   2. LID--CORE angle theta1,
--   3. NMP--CORE angle theta2,
--   4. LID--NMP center-of-mass distance dLN.
--
-- In the BE-META method they then choose theta1, theta2 and dLN as the three
-- biased collective variables.  RMSD is therefore part of the paper's broader
-- monitoring surface but is not one of the three BE-META bias CVs.
--
-- This owner records that source distinction only.  It does not claim RMSD is
-- mathematically independent of the three CVs, necessary for every consumer, or
-- sufficient to recover an atomistic protein state.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Attr.liLiuJiSource

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

data AdKObservable : Set where
  rmsdOpenClosed : AdKObservable
  thetaOneLidCore : AdKObservable
  thetaTwoNmpCore : AdKObservable
  dLnLidNmp : AdKObservable

record ObservablePayment : Set where
  constructor observable-payment
  field
    observable : AdKObservable
    definition : String
    sourceLocator : String
    ltmdMonitored : Bool
    beMetaBiasCV : Bool
    sourceRole : String
open ObservablePayment public

rmsdOpenClosedObservation : ObservablePayment
rmsdOpenClosedObservation = observable-payment
  rmsdOpenClosed
  "RMSD of C-alpha atoms with reference to the open and closed conformations"
  "Li-Liu-Ji 2015 Materials and Methods, long-time explicit MD simulations: conformational transitions monitored by four variables"
  true false
  "source-paid LT-MD monitoring observable; not listed among the three BE-META biased CVs"

thetaOneObservation : ObservablePayment
thetaOneObservation = observable-payment
  thetaOneLidCore
  "LID--CORE angle theta1; detailed residue/center-of-mass construction retained by CollectiveVariableDefinitionAcquisitionExact"
  "Li-Liu-Ji 2015 Materials and Methods, LT-MD monitoring list and BE-META selected CVs"
  true true
  "source-paid LT-MD monitoring observable and BE-META bias collective variable"

thetaTwoObservation : ObservablePayment
thetaTwoObservation = observable-payment
  thetaTwoNmpCore
  "NMP--CORE angle theta2; detailed residue/center-of-mass construction retained by CollectiveVariableDefinitionAcquisitionExact"
  "Li-Liu-Ji 2015 Materials and Methods, LT-MD monitoring list and BE-META selected CVs"
  true true
  "source-paid LT-MD monitoring observable and BE-META bias collective variable"

dLnObservation : ObservablePayment
dLnObservation = observable-payment
  dLnLidNmp
  "distance between centers of mass of LID and NMP domains"
  "Li-Liu-Ji 2015 Materials and Methods, LT-MD monitoring list and BE-META selected CVs"
  true true
  "source-paid LT-MD monitoring observable and BE-META bias collective variable"

monitoringSurface : List ObservablePayment
monitoringSurface =
  rmsdOpenClosedObservation ∷ thetaOneObservation ∷ thetaTwoObservation ∷ dLnObservation ∷ []

beMetaBiasSurface : List ObservablePayment
beMetaBiasSurface = thetaOneObservation ∷ thetaTwoObservation ∷ dLnObservation ∷ []

------------------------------------------------------------------------
-- Attribution / WrongType firewalls.
------------------------------------------------------------------------

data ThreeCVsCreateWholePaperObservationState : Set where
data RMSDCreatesCompleteAtomisticState : Set where
data DOIorQIDCreatesRMSDDefinition : Set where
data MonitoringRoleCreatesConsumerNecessity : Set where

theThreeBiasCVsDoNotCreateWholePaperObservationState :
  ThreeCVsCreateWholePaperObservationState → ⊥
theThreeBiasCVsDoNotCreateWholePaperObservationState ()

rmsdDoesNotCreateCompleteAtomisticState :
  RMSDCreatesCompleteAtomisticState → ⊥
rmsdDoesNotCreateCompleteAtomisticState ()

identityMetadataDoesNotCreateRmsdDefinition :
  DOIorQIDCreatesRMSDDefinition → ⊥
identityMetadataDoesNotCreateRmsdDefinition ()

monitoringRoleDoesNotCreateUniversalConsumerNecessity :
  MonitoringRoleCreatesConsumerNecessity → ⊥
monitoringRoleDoesNotCreateUniversalConsumerNecessity ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKLTMDObservableSetBoundary : Set where
  constructor adk-ltmd-observable-set-boundary
  field
    fourLTMDMonitoringVariablesPaid : Bool
    rmsdMonitoringRolePaid : Bool
    thetaOneMonitoringRolePaid : Bool
    thetaTwoMonitoringRolePaid : Bool
    dLnMonitoringRolePaid : Bool
    threeBEMetaBiasCVsPaid : Bool
    rmsdIsBEMetaBiasCV : Bool
    threeBEMetaCVsEqualWholeLTMDMonitoringSurface : Bool
    threeBEMetaCVsRecoverCompleteAtomisticState : Bool
    sourceSaysRmsdIndependentOfThreeCVs : Bool
    sourceSaysRmsdRequiredForEveryConsumer : Bool
    identityMetadataCreatesRmsdMeasurement : Bool
    attributionEnvelopeReused : Bool
    nextResidual : String
open AdKLTMDObservableSetBoundary public

canonicalAdKLTMDObservableSetBoundary : AdKLTMDObservableSetBoundary
canonicalAdKLTMDObservableSetBoundary = adk-ltmd-observable-set-boundary
  true true true true true true
  false false false false false false true
  "retain the four-variable LT-MD monitoring surface separately from the three-variable BE-META bias surface. Future cross-paper values must preserve observable identity; RMSD is an additional source-paid observation role, not permission to infer missing named-state theta/dLN coordinates or complete atomistic state."
