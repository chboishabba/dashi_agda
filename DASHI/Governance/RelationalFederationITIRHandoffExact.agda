module DASHI.Governance.RelationalFederationITIRHandoffExact where

-- Consume the suite's existing typed world, projection and structural
-- firewall owners. No new reducer, canonical store, or execution authority.
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Interop.ITIRFederatedTypedWorldProjectionExact as ITIR
import DASHI.Interop.SLRStructuralReceiptFirewallExact as Firewall
import DASHI.Interop.SLRPNFToAgdaPreflightProofJoinPipelineExact as PNF
import DASHI.Interop.DistributedProofProducerABIExact as ABI
import DASHI.Governance.RelationalFederationLESProofSearchExact as LES

suiteRoles : ITIR.SuiteRoleMap
suiteRoles = ITIR.canonicalSuiteRoleMap

-- Both derived projections must preserve the exact source-addressable
-- semantic node, not just a matching label or an equal content summary.
record SameNodeProjections (node : ITIR.SourceAddressableSemanticNode) : Set where
  field
    left right : ITIR.SemanticProjection
    leftExact : ITIR.projectedNode left ≡ node
    rightExact : ITIR.projectedNode right ≡ node

-- A different source revision does not silently satisfy an old obligation.
-- Actual source/authentication receipts must be supplied by their producers.
record SourceBoundDemand (node : ITIR.SourceAddressableSemanticNode)
  (target : ABI.ProofObligation)
  (SourceBindingsMatch : ITIR.SourceAddressableSemanticNode →
    ABI.ProofObligation → Set) : Set where
  field
    sourceBindingsExact : SourceBindingsMatch node target

-- SourceBindingsMatch must account for source revision separately from
-- world revision; equating those strings would be an invalid shortcut.
-- The PNF demand is owned by the existing compiler pipeline.
record StructuralHandoff (node : ITIR.SourceAddressableSemanticNode)
  (target : ABI.ProofObligation)
  (Binding : ITIR.SourceAddressableSemanticNode →
    PNF.PNFObligationDemand → ABI.ProofObligation → Set) : Set where
  field
    demand : PNF.PNFObligationDemand
    exactDemandBinding : Binding node demand target
    extractor : Firewall.ExtractionReceipt
    extractorAdmitted : Firewall.ExtractionAdmissible extractor
    matcher : Firewall.SymbolLinkReceipt
    matcherAdmitted : Firewall.SymbolLinkAdmissible matcher
    router : Firewall.RoutingReceipt
    routerAdmitted : Firewall.RoutingAdmissible router

-- Preserve canonical no-promotion results in the new consumer.
observerCannotPaySemanticAuthority :
  ITIR.TemporalObserverReceiptCreatesSemanticAuthority → ⊥
observerCannotPaySemanticAuthority = ITIR.temporalObserverReceiptIsNotSemanticAuthority

selectionCannotPayWorldTruth : ITIR.CaseySelectionCreatesWorldTruth → ⊥
selectionCannotPayWorldTruth = ITIR.caseySelectionIsNotWorldTruth

projectionCannotPayCanonicalState : ITIR.ProjectionCreatesCanonicalState → ⊥
projectionCannotPayCanonicalState = ITIR.projectionIsNotCanonicalState

formalProofCannotPayExternalTruth : ITIR.FormalProofCreatesExternalWorldTruth → ⊥
formalProofCannotPayExternalTruth = ITIR.formalProofIsNotExternalWorldTruth
