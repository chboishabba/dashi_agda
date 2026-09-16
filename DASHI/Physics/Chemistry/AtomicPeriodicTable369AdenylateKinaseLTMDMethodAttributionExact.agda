module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDMethodAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTED LT-MD METHOD ENVELOPE
--
-- Li-Liu-Ji 2015 machine-readable Materials and Methods pays the simulation
-- setup below. These are method/provenance coordinates for interpreting the
-- LT-MD observations already acquired elsewhere. They do not create a physical
-- state, an experimental result, a Kramers rate, or force-field-independent
-- truth.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Attr.liLiuJiSource

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleDOI : Identity.ExternalIdentityDemand
articleDOI = Attr.articleDOI
articlePMID : Identity.ExternalIdentityDemand
articlePMID = Attr.articlePMID
articlePMCID : Identity.ExternalIdentityDemand
articlePMCID = Attr.articlePMCID
articleQID : Identity.ExternalIdentityDemand
articleQID = Attr.articleQID
adkQID : Identity.ExternalIdentityDemand
adkQID = Attr.adkQID
adkUniProt : Identity.ExternalIdentityDemand
adkUniProt = Attr.adkUniProt

record LTMDMethodProtocol : Set where
  constructor ltmd-method-protocol
  field
    engine : String
    forceField : String
    ligandParameterSource : String
    protonationEnvironment : String
    waterModel : String
    approximateBoxAngstrom : Nat
    approximateWaterCount : Nat
    approximateAtomCount : Nat
    neutralisingIonRole : String
    electrostaticsMethod : String
    minimisationAlgorithm : String
    minimisationSteps : Nat
    heatingTargetKelvin : Nat
    heatingPicoseconds : Nat
    restraintInitialHundredthsKcalMolA2 : Nat
    restraintFinalHundredthsKcalMolA2 : Nat
    sourceLocator : String
    methodRole : String
open LTMDMethodProtocol public

canonicalLTMDMethodProtocol : LTMDMethodProtocol
canonicalLTMDMethodProtocol = ltmd-method-protocol
  "GROMACS"
  "AMBER ffamber03"
  "explicit ATP/AMP force-field parameters attributed by Li-Liu-Ji to Carlson et al."
  "residue protonation assigned normally for pH 7; Asp deprotonated and His protonated only at N-3 as source examples"
  "TIP3P explicit water"
  80
  15000
  50000
  "appropriate magnesium ions added to neutralize the system"
  "particle mesh Ewald (PME) for long-range electrostatics"
  "steepest descent"
  10000
  300
  200
  239
  0
  "Li-Liu-Ji 2015, PMCID PMC4572606, Materials and Methods / Long-time explicit MD simulations"
  "source-paid LT-MD simulation-method envelope; method identity and setup provenance only"

------------------------------------------------------------------------
-- Force-field sensitivity is itself source-bounded.
------------------------------------------------------------------------

record ForceFieldCaveat : Set where
  constructor force-field-caveat
  field
    discrepancyAcknowledged : Bool
    amberHelixPreferenceReported : Bool
    comparisonBeyondStudyScope : Bool
    conclusionLimitedToUsedForceField : String
    sourceLocator : String
open ForceFieldCaveat public

canonicalForceFieldCaveat : ForceFieldCaveat
canonicalForceFieldCaveat = force-field-caveat
  true true true
  "authors state their results/conclusions are consistent and coherent under Amber ff03; cross-force-field comparison is beyond the study"
  "Li-Liu-Ji 2015 Results discussion of force-field discrepancies"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data MethodSetupCreatesExperimentalKinetics : Set where
data ForceFieldChoiceCreatesPhysicalTruth : Set where
data ApproximateBoxCreatesExactAtomCount : Set where
data DOIIdentityCreatesSimulationMethod : Set where

data SharedUniProtCreatesSameSimulationCondition : Set where

methodDoesNotCreateExperimentalKinetics : MethodSetupCreatesExperimentalKinetics → ⊥
methodDoesNotCreateExperimentalKinetics ()

forceFieldDoesNotCreatePhysicalTruth : ForceFieldChoiceCreatesPhysicalTruth → ⊥
forceFieldDoesNotCreatePhysicalTruth ()

approximateBoxDoesNotCreateExactAtomCount : ApproximateBoxCreatesExactAtomCount → ⊥
approximateBoxDoesNotCreateExactAtomCount ()

doiDoesNotCreateMethod : DOIIdentityCreatesSimulationMethod → ⊥
doiDoesNotCreateMethod ()

sharedUniProtDoesNotCreateSameCondition : SharedUniProtCreatesSameSimulationCondition → ⊥
sharedUniProtDoesNotCreateSameCondition ()

record LTMDMethodAttributionBoundary : Set where
  constructor ltmd-method-attribution-boundary
  field
    gromacsPaid : Bool
    amberFf03Paid : Bool
    ligandParameterSourceRolePaid : Bool
    phSevenProtonationSetupPaid : Bool
    tip3pWaterPaid : Bool
    boxWaterAtomScalePaid : Bool
    pmePaid : Bool
    minimisationAndHeatingPaid : Bool
    forceFieldCaveatRetained : Bool
    doiPmidPmcidRetained : Bool
    unresolvedArticleQidAllowed : Bool
    methodEqualsExperiment : Bool
    methodMakesForceFieldIndependentTruth : Bool
    identityMetadataPaysMethodFacts : Bool
open LTMDMethodAttributionBoundary public

canonicalLTMDMethodAttributionBoundary : LTMDMethodAttributionBoundary
canonicalLTMDMethodAttributionBoundary = ltmd-method-attribution-boundary
  true true true true true true true true true true true
  false false false
