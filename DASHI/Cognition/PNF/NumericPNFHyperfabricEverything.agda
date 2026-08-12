module DASHI.Cognition.PNF.NumericPNFHyperfabricEverything where

-- Generic/cross-cutting theorem modules stay qualified so common record field
-- names do not pollute the public numeric-PNF namespace. Importing them here
-- still places them on the aggregate validation/dependency surface.
import DASHI.Core.ProvenanceBearingQuotient
import DASHI.Core.AdmissibleReachability
import DASHI.Core.DynamicalQuotientSafety
import DASHI.Core.ProvenanceQuotientDynamics
import DASHI.Core.PossibilityAccessibilitySupport
import DASHI.Core.FinePhaseObservation
import DASHI.Core.RelationalHorizon369
import DASHI.Core.StructuralSupportEdge
import DASHI.Core.ClassificationEdge
import DASHI.Foundations.DepthWheelGradedDynamics
import DASHI.Physics.Closure.SSP369PolarResidualQuotient
import DASHI.Cognition.PNF.BoundedExecutionAdapters
import DASHI.Cognition.PNF.SupportClassificationIdentitySpine
import DASHI.Cognition.PNF.TypePressure
import DASHI.Cognition.PNF.EvidencePhaseObservationAdapter
import DASHI.Cognition.PNF.EvidenceDepthWheelOrthogonality
import DASHI.Cognition.PNF.DepthWheelMemoryGradedAdapter
import DASHI.Cognition.PNF.WikidataRepairProposal
import DASHI.Cognition.PNF.TerminalisationDefectRegression
import DASHI.Cognition.PNF.PNFResidualTerminalisationRegression
import DASHI.Cognition.PNF.SemanticSamplingDynamicSafety

open import DASHI.Cognition.PNF.ComplexityArithmetic public
open import DASHI.Cognition.PNF.NumericAuthority public
open import DASHI.Cognition.PNF.SpacyNumericProjection public
open import DASHI.Cognition.PNF.NumericOccurrenceFibre public
open import DASHI.Cognition.PNF.NumericTokenStorageReference public
open import DASHI.Cognition.PNF.LexicalRetrievalProjection public
open import DASHI.Cognition.PNF.NumericHyperfabric public
open import DASHI.Cognition.PNF.DemandResolutionState public
open import DASHI.Cognition.PNF.InductiveDemandPreference public
open import DASHI.Cognition.PNF.AdjacentReconciliationWork public
open import DASHI.Cognition.PNF.OrderedWorldParserLookahead public
open import DASHI.Cognition.PNF.WorkConservingPersistence public
open import DASHI.Cognition.PNF.BoundedMDLPlanner public
open import DASHI.Cognition.PNF.BoundedInterfaceSketch public
open import DASHI.Cognition.PNF.ParentInterfaceReduction public
open import DASHI.Cognition.PNF.SparseFibredFrontier public
open import DASHI.Cognition.PNF.SparseFrontierConstraints public
open import DASHI.Cognition.PNF.EvidenceCoverageAudit public
open import DASHI.Cognition.PNF.ReferenceModeOutcomes public
open import DASHI.Cognition.PNF.ProofRelevantIdentityFibres public
open import DASHI.Cognition.PNF.IdentityEvidenceProduction public
open import DASHI.Cognition.PNF.DocumentScopedIdentityEvidenceExecution public
open import DASHI.Cognition.PNF.BoundedProperNameEvidenceExecution public
open import DASHI.Cognition.PNF.ProofRelevantFactorDerivations public
open import DASHI.Cognition.PNF.BoundedFactorCompositionExecution public
open import DASHI.Cognition.PNF.BoundedExecutionCarrier public
open import DASHI.Cognition.PNF.ParserArgumentSupportGluing public
open import DASHI.Cognition.PNF.ContextualRepresentationOrbit public
open import DASHI.Cognition.PNF.IdentityProofUtility public
open import DASHI.Cognition.PNF.EvidenceClassificationEdge public
open import DASHI.Cognition.PNF.EvidenceHorizon369 public
open import DASHI.Cognition.PNF.ReopenableEvidenceFibre public
open import DASHI.Cognition.PNF.PNFEvidenceHyperformalism public
open import DASHI.Cognition.PNF.TemporalRoleWorldAlignment public
open import DASHI.Cognition.PNF.DirectDemandLookup public
open import DASHI.Cognition.PNF.SemanticSamplingLookupGeometry public
open import DASHI.Cognition.PNF.SetBasedDemandPlanning public
open import DASHI.Cognition.PNF.NumericPNFCompilation public
open import DASHI.Cognition.PNF.NumericPNFRegression public
