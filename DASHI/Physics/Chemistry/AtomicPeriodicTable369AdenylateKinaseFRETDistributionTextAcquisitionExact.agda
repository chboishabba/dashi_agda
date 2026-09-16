module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETDistributionTextAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- MACHINE-READABLE FIGURE-7 / FRET-DISTRIBUTION TEXT ACQUISITION
--
-- Li, Liu & Ji explicitly discuss the distributions of dLN (LID--NMP) and dLC
-- (LID--CORE) in relation to the two historical single-molecule FRET labeling
-- schemes.  This owner records only the qualitative statements paid by the
-- machine-readable article text.  It does not visually transcribe Figure 7,
-- invent exact fractions, or identify a FRET "closed" population with the fully
-- closed three-domain AdK conformation.
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

data DistributionAxis : Set where
  lidNmpDLn : DistributionAxis
  lidCoreDLc : DistributionAxis

data LigandCondition : Set where
  ligandFree : LigandCondition
  ligandBound : LigandCondition

record QualitativeDistributionObservation : Set where
  constructor qualitative-distribution-observation
  field
    axis : DistributionAxis
    ligandCondition : LigandCondition
    observation : String
    sourceLocator : String
    sourceIdentity : Attribution.AttributedSource
    sourceRole : String
open QualitativeDistributionObservation public

ligandFreeDLnDistributionObservation : QualitativeDistributionObservation
ligandFreeDLnDistributionObservation = qualitative-distribution-observation
  lidNmpDLn ligandFree
  "dLN distribution shows two major states, with and without LID--NMP contact; both sample significant fractions and the closed-like fraction is smaller than the open-like fraction"
  "Li-Liu-Ji 2015 discussion of Fig. 7a"
  source
  "simulation-derived qualitative population/distribution statement compared with the Henzler-Wildman LID--NMP labeling experiment"

ligandBoundDLnDistributionObservation : QualitativeDistributionObservation
ligandBoundDLnDistributionObservation = qualitative-distribution-observation
  lidNmpDLn ligandBound
  "with ligands the enzyme is confined toward the closed state with a more compact structure in the dLN view"
  "Li-Liu-Ji 2015 discussion of Fig. 7a"
  source
  "simulation-derived ligand-conditioned distribution statement; not an exact population fraction"

ligandFreeDLcDistributionObservation : QualitativeDistributionObservation
ligandFreeDLcDistributionObservation = qualitative-distribution-observation
  lidCoreDLc ligandFree
  "the LID--CORE dLC view has a bias-weighted preference for LID closed toward CORE even though NMP opening can leave the full enzyme open"
  "Li-Liu-Ji 2015 discussion of Fig. 7b"
  source
  "simulation-derived labeling-axis interpretation compared with the Hanson LID--CORE experiment"

record IntermediateContactObservation : Set where
  constructor intermediate-contact-observation
  field
    namedExamples : String
    contactReading : String
    distanceReading : String
    sourceLocator : String
    sourceIdentity : Attribution.AttributedSource
open IntermediateContactObservation public

intermediateContactObservation : IntermediateContactObservation
intermediateContactObservation = intermediate-contact-observation
  "beta, gamma and delta examples in Figure 5"
  "in intermediate states LID closes to contact NMP/CORE while NMP can remain open or semi-open"
  "those contacts decrease dLN and dLC"
  "Li-Liu-Ji 2015 discussion following Fig. 7"
  source

------------------------------------------------------------------------
-- Source-bounded interpretive consequence.
------------------------------------------------------------------------

record LabelAxisInterpretation : Set where
  constructor label-axis-interpretation
  field
    lidNmpReadout : String
    lidCoreReadout : String
    transverseCoordinateMatters : Bool
    sourceLocator : String
open LabelAxisInterpretation public

labelAxisInterpretation : LabelAxisInterpretation
labelAxisInterpretation = label-axis-interpretation
  "LID--NMP labeling reports an open-like population as more favorable in ligand-free AdK"
  "LID--CORE labeling can report a closed-like LID state while NMP remains open or semi-open"
  true
  "Li-Liu-Ji 2015 Fig. 7 discussion and comparison of the two FRET labeling positions"

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data QualitativeFractionsCreateExactPopulationNumbers : Set where
data FRETClosedStateEqualsFullyClosedAdK : Set where
data FigureSevenDistributionCreatesNamedStateDLn : Set where
data LabelAxisExplanationProvesExperimentalAgreement : Set where
data QidCreatesDistributionObservation : Set where

qualitativeFractionsDoNotCreateExactNumbers :
  QualitativeFractionsCreateExactPopulationNumbers → ⊥
qualitativeFractionsDoNotCreateExactNumbers ()

fretClosedDoesNotEqualFullyClosedAdK : FRETClosedStateEqualsFullyClosedAdK → ⊥
fretClosedDoesNotEqualFullyClosedAdK ()

figureSevenDoesNotCreateNamedStateDLn : FigureSevenDistributionCreatesNamedStateDLn → ⊥
figureSevenDoesNotCreateNamedStateDLn ()

labelAxisExplanationDoesNotProveExperimentalAgreement :
  LabelAxisExplanationProvesExperimentalAgreement → ⊥
labelAxisExplanationDoesNotProveExperimentalAgreement ()

qidDoesNotCreateDistributionObservation : QidCreatesDistributionObservation → ⊥
qidDoesNotCreateDistributionObservation ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKFRETDistributionTextAcquisitionBoundary : Set where
  constructor adk-fret-distribution-text-acquisition-boundary
  field
    ligandFreeDLnTwoMajorStatesPaid : Bool
    closedLikeFractionSmallerThanOpenLikePaid : Bool
    ligandBoundDLnCompactionPaid : Bool
    ligandFreeDLcClosedLidPreferencePaid : Bool
    labelAxisDependentInterpretationPaid : Bool
    intermediateContactDecreasesDistancesPaid : Bool
    exactPopulationFractionsPaid : Bool
    exactNamedStateDLnValuesPaid : Bool
    fretClosedEqualsFullyClosedAdK : Bool
    simulationDistributionEqualsExperimentalPopulation : Bool
    articleDoiPmidPmcidRetained : Bool
    articleQidResolved : Bool
    qidCreatesScientificPayment : Bool
open AdKFRETDistributionTextAcquisitionBoundary public

canonicalAdKFRETDistributionTextAcquisitionBoundary :
  AdKFRETDistributionTextAcquisitionBoundary
canonicalAdKFRETDistributionTextAcquisitionBoundary =
  adk-fret-distribution-text-acquisition-boundary
    true true true true true true
    false false false false
    true false false
