module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- MACHINE-READABLE COLLECTIVE-VARIABLE DEFINITION ACQUISITION
--
-- Li, Liu & Ji define the three AdK collective variables in the Figure-1
-- caption using explicit residue groups and centers of mass.  This owner pays
-- the *observable definitions* only.  It does not fill any named-state value,
-- identify a later paper's similarly named angle/distance as the same observable,
-- or let DOI/QID/PDB/UniProt metadata manufacture a measurement definition.
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
-- Exact source-side measurement identities.
------------------------------------------------------------------------

data ObservableKind : Set where
  threePointCenterOfMassAngle : ObservableKind
  interDomainCenterOfMassDistance : ObservableKind

record CollectiveVariableDefinition : Set where
  constructor collective-variable-definition
  field
    variableLabel : String
    observableKind : ObservableKind
    firstCarrier : String
    vertexOrSecondCarrier : String
    thirdCarrier : String
    atomSelectionRole : String
    unitRole : String
    sourceLocator : String
    sourceIdentity : Attribution.AttributedSource
    interpretation : String
open CollectiveVariableDefinition public

thetaOneDefinition : CollectiveVariableDefinition
thetaOneDefinition = collective-variable-definition
  "theta1 / LID--CORE angle"
  threePointCenterOfMassAngle
  "LID backbone center of mass: residues 123--155"
  "hinge backbone center of mass: residues 161--165"
  "CORE backbone center of mass: residues 1--8, 79--85, 104--110, 190--198"
  "centers of mass of the selected backbone residue groups"
  "degrees"
  "Li-Liu-Ji 2015 Figure 1 caption"
  source
  "source-paid definition of the LID--CORE collective variable; the ordering here records the three source-listed carriers without importing an unsourced geometric convention beyond the caption"

thetaTwoDefinition : CollectiveVariableDefinition
thetaTwoDefinition = collective-variable-definition
  "theta2 / NMP--CORE angle"
  threePointCenterOfMassAngle
  "NMP backbone center of mass: residues 50--59"
  "CORE backbone center of mass: residues 1--8, 79--85, 104--110, 190--198"
  "hinge backbone center of mass: residues 161--165"
  "centers of mass of the selected backbone residue groups"
  "degrees"
  "Li-Liu-Ji 2015 Figure 1 caption"
  source
  "source-paid definition of the NMP--CORE collective variable"

dLnDefinition : CollectiveVariableDefinition
dLnDefinition = collective-variable-definition
  "dLN / LID--NMP distance"
  interDomainCenterOfMassDistance
  "LID domain center of mass"
  "NMP domain center of mass"
  "not applicable to a two-point distance"
  "distance between centers of mass of the LID and NMP domains"
  "angstrom where numerical distances are reported in the article"
  "Li-Liu-Ji 2015 Figure 1 caption"
  source
  "source-paid definition of dLN; this does not by itself assign dLN to beta/gamma/delta/epsilon/eta/lambda"

------------------------------------------------------------------------
-- Observable-definition identity guard.
------------------------------------------------------------------------

record ObservableIdentityReceipt : Set where
  constructor observable-identity-receipt
  field
    definition : CollectiveVariableDefinition
    sourceDoiRetained : Bool
    sourceLocatorRetained : Bool
    residueOrDomainCarrierRetained : Bool
    centerOfMassConstructionRetained : Bool
    sameLabelAloneIsSufficientForSameObservable : Bool
open ObservableIdentityReceipt public

thetaOneIdentityReceipt : ObservableIdentityReceipt
thetaOneIdentityReceipt = observable-identity-receipt
  thetaOneDefinition true true true true false

thetaTwoIdentityReceipt : ObservableIdentityReceipt
thetaTwoIdentityReceipt = observable-identity-receipt
  thetaTwoDefinition true true true true false

dLnIdentityReceipt : ObservableIdentityReceipt
dLnIdentityReceipt = observable-identity-receipt
  dLnDefinition true true true true false

------------------------------------------------------------------------
-- WrongType / acquisition firewalls.
------------------------------------------------------------------------

data SameVariableNameCreatesSameObservableDefinition : Set where
data CollectiveVariableDefinitionCreatesNamedStateValue : Set where
data IdentityMetadataCreatesObservableDefinition : Set where
data ObservableDefinitionCreatesCompleteProteinState : Set where

data FigureOneDefinitionCreatesExperimentalMeasurement : Set where

sameVariableNameDoesNotCreateSameObservableDefinition :
  SameVariableNameCreatesSameObservableDefinition → ⊥
sameVariableNameDoesNotCreateSameObservableDefinition ()

collectiveVariableDefinitionDoesNotCreateNamedStateValue :
  CollectiveVariableDefinitionCreatesNamedStateValue → ⊥
collectiveVariableDefinitionDoesNotCreateNamedStateValue ()

identityMetadataDoesNotCreateObservableDefinition :
  IdentityMetadataCreatesObservableDefinition → ⊥
identityMetadataDoesNotCreateObservableDefinition ()

observableDefinitionDoesNotCreateCompleteProteinState :
  ObservableDefinitionCreatesCompleteProteinState → ⊥
observableDefinitionDoesNotCreateCompleteProteinState ()

figureDefinitionDoesNotCreateExperimentalMeasurement :
  FigureOneDefinitionCreatesExperimentalMeasurement → ⊥
figureDefinitionDoesNotCreateExperimentalMeasurement ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKCollectiveVariableDefinitionAcquisitionBoundary : Set where
  constructor adk-collective-variable-definition-acquisition-boundary
  field
    thetaOneDefinitionPaid : Bool
    thetaTwoDefinitionPaid : Bool
    dLnDefinitionPaid : Bool
    centerOfMassRolePaid : Bool
    residueGroupDefinitionPaid : Bool
    articleDoiPmidPmcidRetained : Bool
    articleQidResolved : Bool
    sameVariableNameImpliesSameObservableDefinition : Bool
    collectiveVariableDefinitionCreatesNamedStateValue : Bool
    identityMetadataCreatesObservableDefinition : Bool
    observableDefinitionCreatesCompleteProteinState : Bool
    figureDefinitionCreatesExperimentalMeasurement : Bool
    nextResidual : String
open AdKCollectiveVariableDefinitionAcquisitionBoundary public

canonicalAdKCollectiveVariableDefinitionAcquisitionBoundary :
  AdKCollectiveVariableDefinitionAcquisitionBoundary
canonicalAdKCollectiveVariableDefinitionAcquisitionBoundary =
  adk-collective-variable-definition-acquisition-boundary
    true true true true true true false
    false false false false false
    "future numeric promotion must preserve the exact observable definition and source locator as well as article identity; named-state dLN and Figure-5 energy/rate cells remain unpaid until a same-object locator supplies them"
