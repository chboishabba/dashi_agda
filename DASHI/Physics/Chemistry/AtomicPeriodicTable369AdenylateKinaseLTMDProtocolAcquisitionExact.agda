module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDProtocolAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- MACHINE-READABLE LT-MD PROTOCOL ACQUISITION
--
-- Li, Liu & Ji 2015 explicitly report the physical/simulation setup used for
-- the long-time explicit MD simulations.  These setup coordinates materially
-- qualify the simulation observations but are not themselves conformational
-- state values, transition rates, experimental kinetics, or force-field truth.
--
-- Attribution remains layered:
--   * Li-Liu-Ji own the AdK simulation setup/result relation;
--   * Duan et al. 2003 are retained as the cited ffamber03 method source;
--   * Meagher et al. 2003 are retained as the cited ATP/AMP parameter source;
--   * DOI/QID metadata are navigation/provenance coordinates only.
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

------------------------------------------------------------------------
-- Method-source snowball.
------------------------------------------------------------------------

duan2003Source : Attribution.AttributedSource
duan2003Source =
  Attribution.mkDOISource
    "Duan, Wu, Chowdhury, Lee, Xiong, Zhang, Yang, Cieplak, Luo, Lee, Caldwell, Wang and Kollman"
    "A point-charge force field for molecular mechanics simulations of proteins based on condensed-phase quantum mechanical calculations"
    "Journal of Computational Chemistry"
    "2003"
    "10.1002/jcc.10349"
    "https://doi.org/10.1002/jcc.10349"
    Attribution.academicArticleSource
    "cited ffamber03 force-field method source; does not own Li-Liu-Ji AdK trajectory observations or biological conclusions"
    Attribution.publicAttribution

duan2003Receipt : Snowball.SourceRoleSnowballReceipt duan2003Source
duan2003Receipt = Snowball.canonicalSourceRoleSnowballReceipt duan2003Source

duan2003QID : Identity.ExternalIdentityDemand
duan2003QID =
  Identity.mkOptionalIdentityDemand
    "AdK LT-MD protocol attribution"
    "Duan et al. 2003 article Wikidata identity"
    "A point-charge force field for molecular mechanics simulations of proteins based on condensed-phase quantum mechanical calculations"
    Identity.wikidataQid
    (Identity.unresolved "article-level QID not verified in this acquisition tranche")

meagher2003Source : Attribution.AttributedSource
meagher2003Source =
  Attribution.mkDOISource
    "Meagher, Redman and Carlson"
    "Development of polyphosphate parameters for use with the AMBER force field"
    "Journal of Computational Chemistry"
    "2003"
    "10.1002/jcc.10262"
    "https://doi.org/10.1002/jcc.10262"
    Attribution.academicArticleSource
    "cited ATP/AMP force-field parameter source; does not own Li-Liu-Ji AdK trajectory observations or biological conclusions"
    Attribution.publicAttribution

meagher2003Receipt : Snowball.SourceRoleSnowballReceipt meagher2003Source
meagher2003Receipt = Snowball.canonicalSourceRoleSnowballReceipt meagher2003Source

meagher2003QID : Identity.ExternalIdentityDemand
meagher2003QID =
  Identity.mkOptionalIdentityDemand
    "AdK LT-MD protocol attribution"
    "Meagher et al. 2003 article Wikidata identity"
    "Development of polyphosphate parameters for use with the AMBER force field"
    Identity.wikidataQid
    (Identity.unresolved "article-level QID not verified in this acquisition tranche")

------------------------------------------------------------------------
-- Source-paid LT-MD protocol.
------------------------------------------------------------------------

record LTMDProtocol : Set where
  constructor ltmd-protocol
  field
    engine : String
    forceField : String
    ligandParameterLineage : String
    targetPH : Nat
    aspartateDeprotonatedExamplePaid : Bool
    histidineN3OnlyProtonationExamplePaid : Bool
    waterModel : String
    boxEdgeAngstromApprox : Nat
    waterMoleculesApprox : Nat
    atomCountApprox : Nat
    neutralizingMagnesiumAdded : Bool
    longRangeElectrostatics : String
    minimizationAlgorithm : String
    minimizationSteps : Nat
    heatingTargetKelvin : Nat
    heatingDurationPicoseconds : Nat
    restraintStartHundredthsKcalPerMolAngstromSquared : Nat
    restraintEndHundredthsKcalPerMolAngstromSquared : Nat
    productionTemperatureKelvin : Nat
    productionPressureBar : Nat
    thermostat : String
    thermostatRelaxationTenthsPicosecond : Nat
    barostat : String
    lincsConstrainsHBonds : Bool
    timeStepFemtoseconds : Nat
    nonbondedCutoffAngstrom : Nat
    neighbourUpdateSteps : Nat
    sourceLocator : String
    protocolRole : String
open LTMDProtocol public

canonicalLTMDProtocol : LTMDProtocol
canonicalLTMDProtocol = ltmd-protocol
  "GROMACS"
  "AMBER ffamber03"
  "ATP/AMP parameters cited to Meagher-Redman-Carlson 2003"
  7
  true
  true
  "TIP3P"
  80
  15000
  50000
  true
  "particle mesh Ewald (PME)"
  "steepest descent"
  10000
  300
  200
  239
  0
  300
  1
  "Nose-Hoover"
  5
  "Parrinello-Rahman"
  true
  2
  10
  10
  "Li-Liu-Ji 2015 Materials and Methods, Long-time explicit MD simulations, PMCID PMC4572606"
  "source-paid LT-MD simulation setup; approximate box/water/atom counts retain approximate source semantics and do not become exact physical system cardinalities"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data ProtocolCreatesStateCalibration : Set where
data ForceFieldCreatesUniversalMechanism : Set where
data MethodCitationImportsAdKResult : Set where
data ApproximateSetupCountBecomesExactCardinality : Set where
data MethodDOICreatesBiologicalAuthority : Set where

protocolDoesNotCreateStateCalibration : ProtocolCreatesStateCalibration → ⊥
protocolDoesNotCreateStateCalibration ()

forceFieldDoesNotCreateUniversalMechanism : ForceFieldCreatesUniversalMechanism → ⊥
forceFieldDoesNotCreateUniversalMechanism ()

methodCitationDoesNotImportAdKResult : MethodCitationImportsAdKResult → ⊥
methodCitationDoesNotImportAdKResult ()

approximateSetupCountDoesNotBecomeExactCardinality :
  ApproximateSetupCountBecomesExactCardinality → ⊥
approximateSetupCountDoesNotBecomeExactCardinality ()

methodDoiDoesNotCreateBiologicalAuthority : MethodDOICreatesBiologicalAuthority → ⊥
methodDoiDoesNotCreateBiologicalAuthority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKLTMDProtocolAcquisitionBoundary : Set where
  constructor adk-ltmd-protocol-acquisition-boundary
  field
    ffamber03Paid : Bool
    atpAmpParameterLineagePaid : Bool
    phAndProtonationSetupPaid : Bool
    tip3pSolvationSetupPaid : Bool
    pmeElectrostaticsPaid : Bool
    minimizationHeatingProtocolPaid : Bool
    productionDynamicsProtocolPaid : Bool
    methodSourceDoisRetained : Bool
    methodSourceQidsMayRemainUnresolved : Bool
    articleAttributionEnvelopeReused : Bool
    protocolCreatesStateCalibration : Bool
    forceFieldCreatesUniversalMechanism : Bool
    methodCitationImportsAdKResult : Bool
    approximateCountsAreExactCardinalities : Bool
    methodDoiCreatesBiologicalAuthority : Bool
open AdKLTMDProtocolAcquisitionBoundary public

canonicalAdKLTMDProtocolAcquisitionBoundary : AdKLTMDProtocolAcquisitionBoundary
canonicalAdKLTMDProtocolAcquisitionBoundary = adk-ltmd-protocol-acquisition-boundary
  true true true true true true true true true true
  false false false false false
