module DASHI.Law.AustralianContractsLegalFollowExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Admissible
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as LegalFollow
import DASHI.Law.SensibLawProductionLegalRuntimeABIExact as Runtime
import DASHI.Interop.SLRPortableInteractionCommandWeldExact as Interaction

------------------------------------------------------------------------
-- AUSTRALIAN CONTRACTS LEGAL-FOLLOW OWNER
--
-- Contract doctrine is not represented as one flat national code.  A consumer
-- may need common-law/equitable authorities, Commonwealth overlays, and
-- State/Territory legislation indexed by jurisdiction and time.  LegalFollow
-- therefore discovers source material under typed constraints; acquisition is
-- not authority/payment, and a coarse doctrine label is not sufficient to
-- reconstruct an operative jurisdiction/as-at route.
------------------------------------------------------------------------

data ContractDoctrine : Set where
  formation : ContractDoctrine
  intention : ContractDoctrine
  termsAndIncorporation : ContractDoctrine
  construction : ContractDoctrine
  estoppel : ContractDoctrine
  unconscionability : ContractDoctrine
  penalties : ContractDoctrine
  repudiationAndTermination : ContractDoctrine
  damages : ContractDoctrine
  restitution : ContractDoctrine
  privity : ContractDoctrine
  consumerLaw : ContractDoctrine

data TraceNodeKind : Set where
  doctrineNode : TraceNodeKind
  caseAuthorityNode : TraceNodeKind
  legislationNode : TraceNodeKind
  researchRequirementNode : TraceNodeKind
  matterNode : TraceNodeKind

data ContractSourceRole : Set where
  primaryCaseLaw : ContractSourceRole
  primaryLegislation : ContractSourceRole
  officialRecord : ContractSourceRole
  researchIndex : ContractSourceRole
  secondaryAnalysis : ContractSourceRole

data ContractAuthorityLevel : Set where
  official : ContractAuthorityLevel
  supporting : ContractAuthorityLevel
  secondary : ContractAuthorityLevel

data ContractTreatment : Set where
  seeds : ContractTreatment
  supports : ContractTreatment
  applies : ContractTreatment
  follows : ContractTreatment
  distinguishes : ContractTreatment
  qualifies : ContractTreatment
  displaces : ContractTreatment
  temporalSuccessor : ContractTreatment
  requires : ContractTreatment
  intersects : ContractTreatment

record ContractTraceNode : Set where
  constructor contractTraceNode
  field
    semanticReference : String
    label : String
    nodeKind : TraceNodeKind
    doctrine : ContractDoctrine
    jurisdictionReference : String
    courtReference : String
    temporalReference : String
    sourceRole : ContractSourceRole
    authorityLevel : ContractAuthorityLevel
    sourceCitationReference : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false

open ContractTraceNode public

record ContractTraceEdge : Set where
  constructor contractTraceEdge
  field
    fromReference : String
    toReference : String
    treatment : ContractTreatment
    edgeCandidateOnly : Bool
    edgeCandidateOnlyIsTrue : edgeCandidateOnly ≡ true
    edgeCreatesLegalAuthority : Bool
    edgeCreatesLegalAuthorityIsFalse : edgeCreatesLegalAuthority ≡ false

open ContractTraceEdge public

record AustralianContractFollowTrace : Set where
  constructor australianContractFollowTrace
  field
    rootReference : String
    nodes : List ContractTraceNode
    edges : List ContractTraceEdge
    jurisdictionIndexed : Bool
    jurisdictionIndexedIsTrue : jurisdictionIndexed ≡ true
    temporalIndexed : Bool
    temporalIndexedIsTrue : temporalIndexed ≡ true
    sourceFollowOnly : Bool
    sourceFollowOnlyIsTrue : sourceFollowOnly ≡ true
    traceCreatesLegalAuthority : Bool
    traceCreatesLegalAuthorityIsFalse : traceCreatesLegalAuthority ≡ false

open AustralianContractFollowTrace public

------------------------------------------------------------------------
-- Existing generic owners remain the parents.
------------------------------------------------------------------------

LegalFollowBoundary : Set
LegalFollowBoundary = LegalFollow.LegalFollowProofSearchBoundary

legalFollowBoundaryPaid : LegalFollowBoundary
legalFollowBoundaryPaid = LegalFollow.canonicalLegalFollowProofSearchBoundary

RuntimeBoundary : Set
RuntimeBoundary = Runtime.RuntimeLegalProducerBoundary

runtimeBoundaryPaid : RuntimeBoundary
runtimeBoundaryPaid = Runtime.canonicalRuntimeLegalProducerBoundary

AdmissibilityBoundary : Set
AdmissibilityBoundary = Admissible.AdmissibleConsumerMDLBoundary

admissibilityBoundaryPaid : AdmissibilityBoundary
admissibilityBoundaryPaid = Admissible.canonicalAdmissibleConsumerMDLBoundary

InteractionCommandKind : Set
InteractionCommandKind = Interaction.MatterCommandKind

------------------------------------------------------------------------
-- Hyperfabric role: a contract landscape can be represented as a typed
-- incidence/provenance carrier, but topology does not create authority.
------------------------------------------------------------------------

data ContractVertex : Set where
  doctrineVertex : ContractVertex
  authorityVertex : ContractVertex
  legislationVertex : ContractVertex
  requirementVertex : ContractVertex
  matterVertex : ContractVertex

data ContractHyperedge : Set where
  treatmentEdge : ContractHyperedge
  jurisdictionEdge : ContractHyperedge
  temporalEdge : ContractHyperedge
  provenanceEdge : ContractHyperedge

ContractTraceHyperfabric : Set₁
ContractTraceHyperfabric =
  Hyperfabric.TypedHyperfabric ContractVertex ContractHyperedge

HyperfabricBoundary : Set
HyperfabricBoundary = Hyperfabric.TypedHyperfabricAuthorityBoundary

hyperfabricBoundaryPaid : HyperfabricBoundary
hyperfabricBoundaryPaid =
  Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary

------------------------------------------------------------------------
-- FactorsThrough regression:
-- "privity" alone cannot recover the operative Queensland route because the
-- as-at coordinate separates the old s 55 and successor s 68 regimes.
------------------------------------------------------------------------

data QueenslandPrivitySituation : Set where
  beforeAugust2025 : QueenslandPrivitySituation
  fromAugust2025 : QueenslandPrivitySituation

data CoarsePrivityLabel : Set where
  qldThirdPartyBenefit : CoarsePrivityLabel

coarsePrivityProjection : QueenslandPrivitySituation → CoarsePrivityLabel
coarsePrivityProjection beforeAugust2025 = qldThirdPartyBenefit
coarsePrivityProjection fromAugust2025 = qldThirdPartyBenefit

data OperativePrivityRoute : Set where
  propertyLaw1974Section55 : OperativePrivityRoute
  propertyLaw2023Section68 : OperativePrivityRoute

operativePrivityRoute : QueenslandPrivitySituation → OperativePrivityRoute
operativePrivityRoute beforeAugust2025 = propertyLaw1974Section55
operativePrivityRoute fromAugust2025 = propertyLaw2023Section68

operativeRoutesDiffer :
  operativePrivityRoute beforeAugust2025
    ≡
  operativePrivityRoute fromAugust2025 → ⊥
operativeRoutesDiffer ()

qldPrivityNonFactorability :
  NF.NonFactorabilityWitness coarsePrivityProjection operativePrivityRoute
qldPrivityNonFactorability =
  NF.nonFactorabilityWitness
    beforeAugust2025
    fromAugust2025
    refl
    operativeRoutesDiffer

coarseDoctrineLabelCannotRecoverAsAtRoute :
  NF.FactorsThrough coarsePrivityProjection operativePrivityRoute → ⊥
coarseDoctrineLabelCannotRecoverAsAtRoute =
  NF.witnessRulesOutEveryFlatFactorisation qldPrivityNonFactorability

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LegalFollowTraceAutomaticallyLegalAuthority : Set where
data ResearchIndexAutomaticallyPrimaryAuthority : Set where
data SharedDoctrineLabelEliminatesJurisdiction : Set where
data BindingHCAAuthorityMakesEveryStateStatuteSameObject : Set where
data CitationEdgeAutomaticallyAdoptsCitedProposition : Set where
data HyperfabricEdgeAutomaticallyConservedFlow : Set where
data ShorterTraceAutomaticallyLegallyAdequate : Set where

legalFollowTraceDoesNotCreateAuthority :
  LegalFollowTraceAutomaticallyLegalAuthority → ⊥
legalFollowTraceDoesNotCreateAuthority ()

researchIndexDoesNotBecomePrimaryAuthority :
  ResearchIndexAutomaticallyPrimaryAuthority → ⊥
researchIndexDoesNotBecomePrimaryAuthority ()

sharedDoctrineDoesNotEraseJurisdiction :
  SharedDoctrineLabelEliminatesJurisdiction → ⊥
sharedDoctrineDoesNotEraseJurisdiction ()

hcaAuthorityDoesNotCollapseStateStatutes :
  BindingHCAAuthorityMakesEveryStateStatuteSameObject → ⊥
hcaAuthorityDoesNotCollapseStateStatutes ()

citationDoesNotEqualAdoption :
  CitationEdgeAutomaticallyAdoptsCitedProposition → ⊥
citationDoesNotEqualAdoption ()

hyperfabricEdgeDoesNotCreateConservedFlow :
  HyperfabricEdgeAutomaticallyConservedFlow → ⊥
hyperfabricEdgeDoesNotCreateConservedFlow ()

shorterTraceDoesNotAutoEstablishAdequacy :
  ShorterTraceAutomaticallyLegallyAdequate → ⊥
shorterTraceDoesNotAutoEstablishAdequacy ()

record AustralianContractsFollowBoundary : Set where
  constructor australianContractsFollowBoundary
  field
    doctrineFollowUsesGenericLegalFollow : Bool
    doctrineFollowUsesGenericLegalFollowIsTrue :
      doctrineFollowUsesGenericLegalFollow ≡ true

    jurisdictionAndTimeAreRequiredAxes : Bool
    jurisdictionAndTimeAreRequiredAxesIsTrue :
      jurisdictionAndTimeAreRequiredAxes ≡ true

    acquisitionCreatesAuthority : Bool
    acquisitionCreatesAuthorityIsFalse :
      acquisitionCreatesAuthority ≡ false

    contextSourceEqualsLegalAuthority : Bool
    contextSourceEqualsLegalAuthorityIsFalse :
      contextSourceEqualsLegalAuthority ≡ false

    coarseDoctrineFactorsThroughOperativeLaw : Bool
    coarseDoctrineFactorsThroughOperativeLawIsFalse :
      coarseDoctrineFactorsThroughOperativeLaw ≡ false

    traceTopologyCreatesSemanticAuthority : Bool
    traceTopologyCreatesSemanticAuthorityIsFalse :
      traceTopologyCreatesSemanticAuthority ≡ false

canonicalAustralianContractsFollowBoundary :
  AustralianContractsFollowBoundary
canonicalAustralianContractsFollowBoundary =
  australianContractsFollowBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
