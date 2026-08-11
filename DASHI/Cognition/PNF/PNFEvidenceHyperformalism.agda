module DASHI.Cognition.PNF.PNFEvidenceHyperformalism where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Analysis.NormalizedFibreAveragingExact as Averaging
import DASHI.Analysis.GlassesProjectionInvolutionExact as Glasses
import DASHI.Reasoning.RelationalTernaryPhaseGeometry as Phase
import DASHI.Reasoning.RelationalBranchInterference as Interference
import DASHI.Biology.TraumaPsychogeographicMetricExact as TraumaMetric
import DASHI.Biology.ReachableSectorEntropyExact as ReachabilityReference

import DASHI.Cognition.PNF.ReopenableEvidenceFibre as Reopenable
import DASHI.Cognition.PNF.EvidenceHorizon369 as Horizon

------------------------------------------------------------------------
-- Evidence accessibility: three independent propositions.
--
-- A state may be semantically possible, currently outside the bounded
-- execution frontier, and still evidentially supported.  Conversely it may be
-- computationally accessible but unsupported.  No implication is built into
-- the carrier.
------------------------------------------------------------------------

record EvidenceAccessibility (Candidate : Set) : Set₁ where
  field
    SemanticallyPossible : Candidate → Set
    ComputationallyAccessible : Candidate → Set
    EvidentiallySupported : Candidate → Set

open EvidenceAccessibility public

record AccessibilityDeformation (Candidate : Set) : Set where
  constructor accessibilityDeformation
  field
    beforeCost : Candidate → Nat
    afterCost : Candidate → Nat
    historyReceipt : String

open AccessibilityDeformation public

------------------------------------------------------------------------
-- The PNF evidence hyperformalism is an assembly of existing DASHI cores, not
-- a new hypergraph/ternary/PQJ implementation.
--
-- * TypedHyperfabric supplies higher-arity incidence, stalks and provenance.
-- * FibreRestrictionCore supplies projection/restriction without recovery or
--   truth promotion.
-- * ReopenableFibreExtension adds an exact provenance receipt when available.
-- * H3/H6/H9 supplies cumulative evidence horizon independently of resolution.
-- * EvidenceAccessibility keeps possibility/access/support distinct.
------------------------------------------------------------------------

record PNFEvidenceHyperformalism
    (Vertex Edge Candidate : Set) : Set₁ where
  constructor pnfEvidenceHyperformalism
  field
    fabric : Hyperfabric.TypedHyperfabric Vertex Edge
    fibreCore : Fibre.FibreRestrictionCore
    reopening : Reopenable.ReopenableFibreExtension fibreCore
    accessibility : EvidenceAccessibility Candidate
    localStructuralH3 : Horizon.H3Evidence Candidate
    discourseTemporalH6 : Horizon.H6Evidence Candidate
    externalAuthorityH9 : Horizon.H9Evidence Candidate

open PNFEvidenceHyperformalism public

------------------------------------------------------------------------
-- Exact complementary-reading reference by direct reuse.
--
-- GlassesSystem is already generic in its coarse Base.  Instantiating Base with
-- Candidate gives an exact *two-point fibre observable* model over every
-- candidate base, retaining its existing P, Q and J with J^2=I, JPJ=Q and
-- JQJ=P.  This is the repository's adversarial/complementary-view reference;
-- it remains a two-point rational fibre and is not promoted to a theorem about
-- every semantic hyperfibre.
------------------------------------------------------------------------

module ComplementaryReadingReference {Candidate : Set} =
  Glasses.GlassesSystem {Base = Candidate}

------------------------------------------------------------------------
-- Exact repository reference spine.
--
-- The finite two-point averaging and Glasses P/Q/J theorems remain exact
-- reference models; the Eisenstein and n-slit modules remain exact finite phase
-- and interference models; the generic TypedHyperfabric remains the incidence
-- carrier.  Their authority boundaries are imported literally so this PNF
-- layer cannot silently strengthen them.
------------------------------------------------------------------------

record ExistingReferenceSpine : Set where
  constructor existingReferenceSpine
  field
    finiteNormalisedFibreBoundary : Averaging.NormalizedFibreClaimScope
    finitePQJBoundary : Glasses.GlassesInvolutionClaimScope
    ternaryPhaseBoundary : Phase.TernaryPhaseAuthorityBoundary
    branchInterferenceBoundary : Interference.BranchInterferenceAuthorityBoundary
    typedHyperfabricBoundary : Hyperfabric.TypedHyperfabricAuthorityBoundary
    pathAccessibilityBoundary : TraumaMetric.TraumaPsychogeographicBoundary
    reachableSectorBoundary : ReachabilityReference.ReachableSectorBoundary

open ExistingReferenceSpine public

canonicalExistingReferenceSpine : ExistingReferenceSpine
canonicalExistingReferenceSpine =
  existingReferenceSpine
    Averaging.canonicalNormalizedFibreClaimScope
    Glasses.canonicalGlassesInvolutionClaimScope
    Phase.canonicalTernaryPhaseAuthorityBoundary
    Interference.canonicalBranchInterferenceAuthorityBoundary
    Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary
    TraumaMetric.canonicalTraumaPsychogeographicBoundary
    ReachabilityReference.canonicalReachableSectorBoundary

-- The finite P/Q/J reference is not automatically a universal semantic
-- decomposition for arbitrary fibres; an application must construct the needed
-- projector/residual laws on its actual carrier.
data UniversalSemanticPQJPermission : Set where

finiteReferenceDoesNotPromoteUniversalPQJ :
  UniversalSemanticPQJPermission → ⊥
finiteReferenceDoesNotPromoteUniversalPQJ ()

record PNFEvidenceHyperformalismBoundary : Set where
  constructor pnfEvidenceHyperformalismBoundary
  field
    hypergraphCoreDuplicated : Bool
    hypergraphCoreDuplicatedIsFalse : hypergraphCoreDuplicated ≡ false
    ternaryPhaseCoreDuplicated : Bool
    ternaryPhaseCoreDuplicatedIsFalse : ternaryPhaseCoreDuplicated ≡ false
    finitePQJPromotedUniversally : Bool
    finitePQJPromotedUniversallyIsFalse : finitePQJPromotedUniversally ≡ false
    accessibilityEqualsSemanticPossibility : Bool
    accessibilityEqualsSemanticPossibilityIsFalse :
      accessibilityEqualsSemanticPossibility ≡ false

open PNFEvidenceHyperformalismBoundary public

canonicalPNFEvidenceHyperformalismBoundary : PNFEvidenceHyperformalismBoundary
canonicalPNFEvidenceHyperformalismBoundary =
  pnfEvidenceHyperformalismBoundary
    false refl
    false refl
    false refl
    false refl
