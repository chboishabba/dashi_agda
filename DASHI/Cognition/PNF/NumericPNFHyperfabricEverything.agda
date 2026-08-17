module DASHI.Cognition.PNF.NumericPNFHyperfabricEverything where

-- Generic/cross-cutting theorem modules stay qualified so common record field
-- names do not pollute the public numeric-PNF namespace. Importing them here
-- still places them on the aggregate validation/dependency surface.
import DASHI.Core.ProvenanceBearingQuotient
import DASHI.Core.AdmissibleReachability
import DASHI.Core.DynamicalQuotientSafety
import DASHI.Core.ProvenanceQuotientDynamics
import DASHI.Core.PossibilityAccessibilitySupport
import DASHI.Core.ConsumerIndexedRelevanceMeasure
import DASHI.Core.ConsumerProjectionSufficiency
import DASHI.Core.FinePhaseObservation
import DASHI.Core.RelationalHorizon369
import DASHI.Core.StructuralSupportEdge
import DASHI.Core.ClassificationEdge
import DASHI.Foundations.DepthWheelGradedDynamics
import DASHI.Foundations.CantorConsumerRelevanceReference
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
import DASHI.Cognition.PNF.RelevanceMassDynamicSafetyRegression
import DASHI.Cognition.PNF.SemanticSamplingDynamicSafety

-- Runtime-economy constitution: these remain qualified because they deliberately
-- expose generic fields such as revision/depth/work rather than one public PNF
-- record namespace.
--
-- Companion theorem surfaces used by the next runtime pass live on sibling
-- formalisation PRs rather than being duplicated here: #530 supplies canonical
-- future-observation equivalence / exact-vs-relevant residual / dynamic
-- composition, and #531 supplies query-factorisation and policy-relative safety.
-- This branch supplies the numeric physical/execution constitution those
-- theorems are intended to govern.
import DASHI.Cognition.PNF.NumericHotPathConstitution
import DASHI.Cognition.PNF.CorpusLearningEconomy
import DASHI.Cognition.PNF.ContextualWorldCache
import DASHI.Cognition.PNF.RelativeOctantAddressReference
import DASHI.Cognition.PNF.LazyHorizonIncrementalExecution
import DASHI.Cognition.PNF.EditTransportLeafLocalityExact
import DASHI.Cognition.PNF.EditTransportCompositionExact
import DASHI.Cognition.PNF.DependencyDerivedOccurrenceIdentityExact
import DASHI.Cognition.PNF.EditTransportLeafLocalityRegression
import DASHI.Cognition.PNF.FrequencyAdaptiveSymbolCode
import DASHI.Cognition.PNF.HotColdExecutionProjection
import DASHI.Cognition.PNF.WorkloadGranularityReference
import DASHI.Cognition.PNF.StructuralSupportSelectivity

open import DASHI.Cognition.PNF.ComplexityArithmetic public
open import DASHI.Cognition.PNF.RuntimeThroughputConstitution public
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