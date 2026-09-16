module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNamedStateThreeCVManifestationFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attribution
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionExact as CV
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAcquisitionFrontierExact as Frontier
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseOneDimensionalDLnProjectionAcquisitionExact as Projection

------------------------------------------------------------------------
-- NAMED-STATE THREE-CV MANIFESTATION FRONTIER
--
-- Li-Liu-Ji explicitly state that BE-META states along the pathways are
-- characterised by theta1, theta2 and dLN.  The article discussion further
-- directs the reader to Figure S18 when contrasting the one-dimensional dLN
-- landscape with simultaneous theta1/theta2/dLN mapping and when discussing
-- gamma/delta and gamma_L/delta_L intermediate states.
--
-- That pays a same-article *manifestation role*: Figure S18 is a source-local
-- candidate surface for the three-CV state geometry.  It does NOT pay an exact
-- named-state table or a numeric dLN(beta/gamma/...) cell.  Figure 5a/6a remain
-- two-angle visual manifestations and cannot manufacture their absent third
-- coordinate.  DOI/PMID/PMCID/QID/PDB/UniProt stay provenance coordinates.
------------------------------------------------------------------------

data ManifestationDimension : Set where
  twoAngleManifestation : ManifestationDimension
  threeCVManifestation : ManifestationDimension

data NumericResolutionRole : Set where
  qualitativeRoleOnly : NumericResolutionRole
  visualIntervalRole : NumericResolutionRole
  exactNamedStateTableRole : NumericResolutionRole

data LigandContext : Set where
  ligandFreeContext ligandBoundContext crossContextDiscussion : LigandContext

record ThreeCVManifestation : Set where
  constructor three-cv-manifestation
  field
    label : String
    sourceLocator : String
    context : LigandContext
    dimensionRole : ManifestationDimension
    numericRole : NumericResolutionRole
    sameArticlePaid : Bool
    sameObservableDefinitionsRetained : Bool
    thetaOneNamedStateNumericsPaid : Bool
    thetaTwoNamedStateNumericsPaid : Bool
    dLnNamedStateNumericsPaid : Bool
    sourceReading : String
open ThreeCVManifestation public

figureFivePanelAManifestation : ThreeCVManifestation
figureFivePanelAManifestation = three-cv-manifestation
  "Figure 5a ligand-free two-angle landscape"
  "Li-Liu-Ji 2015 Figure 5a"
  ligandFreeContext
  twoAngleManifestation
  visualIntervalRole
  true true false false false
  "named ligand-free states are visually located on theta1/theta2; dLN is not plotted and exact state centroids are not printed as a table"

figureSixPanelAManifestation : ThreeCVManifestation
figureSixPanelAManifestation = three-cv-manifestation
  "Figure 6a ligand-bound two-angle landscape"
  "Li-Liu-Ji 2015 Figure 6a"
  ligandBoundContext
  twoAngleManifestation
  visualIntervalRole
  true true false false false
  "named ligand-bound states are visually located on theta1/theta2; dLN is not plotted and exact state centroids are not promoted"

figureS18Manifestation : ThreeCVManifestation
figureS18Manifestation = three-cv-manifestation
  "Figure S18 multidimensional three-CV supporting manifestation"
  "Li-Liu-Ji 2015 Supporting Material Figure S18; cited in article discussion of simultaneous theta1/theta2/dLN mapping and intermediate states"
  crossContextDiscussion
  threeCVManifestation
  qualitativeRoleOnly
  true true false false false
  "same-article source text points to Figure S18 for the multidimensional landscape involving theta1, theta2 and dLN, but no machine-readable exact named-state coordinate table is acquired here"

------------------------------------------------------------------------
-- Reused attribution, observable-definition and acquisition-frontier owners.
------------------------------------------------------------------------

articleAttributionBoundary : Attribution.AdKCalibrationAttributionBoundary
articleAttributionBoundary = Attribution.canonicalAdKCalibrationAttributionBoundary

collectiveVariableBoundary : CV.AdKCollectiveVariableDefinitionAcquisitionBoundary
collectiveVariableBoundary = CV.canonicalAdKCollectiveVariableDefinitionAcquisitionBoundary

priorAcquisitionFrontier : Frontier.AdKCalibrationAcquisitionFrontierBoundary
priorAcquisitionFrontier = Frontier.canonicalAdKCalibrationAcquisitionFrontierBoundary

projectionBoundary : Projection.OneDimensionalDLnProjectionAcquisitionBoundary
projectionBoundary = Projection.canonicalOneDimensionalDLnProjectionAcquisitionBoundary

sameArticleSourcePaid : Bool
sameArticleSourcePaid = true

threeCVRolePaid : Bool
threeCVRolePaid = true

exactNamedStateTablePaid : Bool
exactNamedStateTablePaid = false

namedStateDLnStillUnpaid : Bool
namedStateDLnStillUnpaid = true

attributionEnvelopeRetained : Bool
attributionEnvelopeRetained = true

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data FigureS18CitationCreatesExactNumericTable : Set where
data ThreeCVManifestationCreatesCompleteProteinState : Set where
data TwoAnglePanelCreatesDLn : Set where
data SameArticleCreatesSameNumericLocator : Set where
data IdentityMetadataCreatesThreeCVPayment : Set where

figureS18CitationDoesNotCreateExactNumericTable :
  FigureS18CitationCreatesExactNumericTable → ⊥
figureS18CitationDoesNotCreateExactNumericTable ()

threeCVManifestationDoesNotCreateCompleteProteinState :
  ThreeCVManifestationCreatesCompleteProteinState → ⊥
threeCVManifestationDoesNotCreateCompleteProteinState ()

twoAnglePanelDoesNotCreateDLn : TwoAnglePanelCreatesDLn → ⊥
twoAnglePanelDoesNotCreateDLn ()

sameArticleDoesNotCreateSameNumericLocator : SameArticleCreatesSameNumericLocator → ⊥
sameArticleDoesNotCreateSameNumericLocator ()

identityMetadataDoesNotCreateThreeCVPayment : IdentityMetadataCreatesThreeCVPayment → ⊥
identityMetadataDoesNotCreateThreeCVPayment ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKNamedStateThreeCVManifestationFrontierBoundary : Set where
  constructor adk-named-state-three-cv-manifestation-frontier-boundary
  field
    articleStatesCharacterisedByThreeCVs : Bool
    figureS18SameArticleThreeCVRolePaid : Bool
    figureFiveAndSixAreTwoAnglePanels : Bool
    sameObservableDefinitionsRetained : Bool
    exactNamedStateThetaTablePaid : Bool
    exactNamedStateDLnTablePaid : Bool
    figureS18MentionPaysNumerics : Bool
    twoAnglePanelPaysDLn : Bool
    threeCVViewEqualsCompleteAtomisticState : Bool
    qidDoiPdbUniProtCreateGeometryPayment : Bool
    currentShortestResidual : String
open AdKNamedStateThreeCVManifestationFrontierBoundary public

canonicalAdKNamedStateThreeCVManifestationFrontierBoundary :
  AdKNamedStateThreeCVManifestationFrontierBoundary
canonicalAdKNamedStateThreeCVManifestationFrontierBoundary =
  adk-named-state-three-cv-manifestation-frontier-boundary
    true true true true
    false false false false false false
    "acquire the actual same-article Figure-S18/supporting-material page or table at sufficient resolution to bind a named state to theta1/theta2/dLN under the retained Figure-1 observable definitions. Until then Figure S18 is a manifestation/indexing payment only, not a numeric payment."
