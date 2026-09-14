module DASHI.Core.RealObjectApplicationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ScientificCapabilityCarrierBidiExact as Capability
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as Transform

------------------------------------------------------------------------
-- REAL-OBJECT APPLICATION BIDI
--
-- An independently sourced engineering object is decomposed into requirements.
-- Existing science/capability carriers may fit those requirements at different
-- strengths. Fit is an engineering-design relation only: it neither rewrites
-- history nor establishes programme membership, possession, targeting or event
-- causation.
------------------------------------------------------------------------

data FitStrength : Set where
  directSourceFit engineeringTransfer methodTransfer analogyOnly noFit : FitStrength

record RealObjectRequirement : Set where
  constructor real-object-requirement
  field
    subsystemLabel : String
    requirementLabel : String
    requirementSource : String
    transformationTargets : List Transform.TransformationReverseTarget
    qualificationBoundary : String

open RealObjectRequirement public

record ScientistObjectFit : Set where
  constructor scientist-object-fit
  field
    person : String
    scienceOwner : String
    scienceCarrier : String
    requirement : RealObjectRequirement
    fitStrength : FitStrength
    evidenceReference : String
    fitRationale : String
    reverseQualificationLeaf : String
    historicalParticipationPaid : Bool
    historicalParticipationBoundary : String

open ScientistObjectFit public

record RealEngineeringObject : Set where
  constructor real-engineering-object
  field
    objectLabel : String
    objectClass : String
    sourceAtlas : Source.AttributedSourceAtlas
    requirements : List RealObjectRequirement
    intendedResearchUse : String
    applicationBoundary : String

open RealEngineeringObject public

record RealObjectReverseQuery : Set where
  constructor real-object-reverse-query
  field
    requestedObject : String
    requestedSubsystem : String
    missingCoordinates : List Transform.TransformationReverseTarget
    requestedQualificationEvidence : String
    historicalReceiptRequired : String
    whatItCannotPromote : String

open RealObjectReverseQuery public

------------------------------------------------------------------------
-- Generic non-promotion firewalls.
------------------------------------------------------------------------

subsystemFitPaysHistoricalParticipation : Bool
subsystemFitPaysHistoricalParticipation = false

multipleFitsPayCommonProgramme : Bool
multipleFitsPayCommonProgramme = false

engineeringTransferPaysQualification : Bool
engineeringTransferPaysQualification = false

methodTransferPaysDeployedImplementation : Bool
methodTransferPaysDeployedImplementation = false

realObjectFitPaysEventCause : Bool
realObjectFitPaysEventCause = false

realObjectFitPaysH2 : Bool
realObjectFitPaysH2 = false

noFitCanReduceInventedInterfaceDebt : Bool
noFitCanReduceInventedInterfaceDebt = true

sourceCitationPaysEngineeringQualification : Bool
sourceCitationPaysEngineeringQualification = false

sourceCitationImportsProof : Bool
sourceCitationImportsProof = false

------------------------------------------------------------------------
-- Bridge helpers.  These retain existing transformation/capability vocabulary
-- rather than introducing another application planner.
------------------------------------------------------------------------

mkRequirement :
  String → String → String → List Transform.TransformationReverseTarget → String →
  RealObjectRequirement
mkRequirement = real-object-requirement

mkFit :
  String → String → String → RealObjectRequirement → FitStrength → String → String →
  String → Bool → String → ScientistObjectFit
mkFit = scientist-object-fit

fitNeedsHistoricalReceipt : ScientistObjectFit → Bool
fitNeedsHistoricalReceipt f = historicalParticipationPaid f

record RealObjectBoundary : Set where
  constructor real-object-boundary
  field
    engineeringFitCreatesHistoricalFact : Bool
    multipleSubsystemFitsCreateProgrammeIdentity : Bool
    transferWithoutQualificationCreatesValidatedCapability : Bool
    noFitMayBeInformative : Bool

canonicalRealObjectBoundary : RealObjectBoundary
canonicalRealObjectBoundary = real-object-boundary false false false true
