module DASHI.Reasoning.LogicalConsequenceDerivationPathExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.TrajectoryResidueExact as Trajectory
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF

------------------------------------------------------------------------
-- TYPED EPISTEMIC DERIVATION PATHS
--
-- A downstream formula is not fully characterised by its syntax.  Every edge
-- records the authority by which the transition was made.  This lets two paths
-- reconverge on the same formula while retaining different epistemic history.
------------------------------------------------------------------------

data DerivationEdgeKind : Set where
  parserObservationEdge
  semanticResolutionEdge
  logicalEntailmentEdge
  empiricalPromotionEdge
  residualRefinementEdge
  designDischargeEdge
  sourceWorldResolutionEdge
  : DerivationEdgeKind

logicalNotEmpirical : logicalEntailmentEdge ≡ empiricalPromotionEdge → ⊥
logicalNotEmpirical ()

semanticNotDesign : semanticResolutionEdge ≡ designDischargeEdge → ⊥
semanticNotDesign ()

data AuthorityGrade : Set where
  parserCandidateAuthority
  reviewedSemanticAuthority
  logicalTheoremAuthority
  empiricalQualifiedAuthority
  empiricalDischargedAuthority
  : AuthorityGrade

record DerivationNode : Set where
  constructor derivationNode
  field
    nodeKey : String
    formula : Candidate.Formula
    evidentialAssertion : EvidencePNF.PredicateNormalAssertion
    authority : AuthorityGrade
    provenanceReference : String

open DerivationNode public

record DerivationStep (from to : DerivationNode) : Set where
  constructor derivationStep
  field
    edgeKind : DerivationEdgeKind
    transitionReference : String
    authorityReference : String
    residualReference : String

open DerivationStep public

DerivationPath : DerivationNode → DerivationNode → Set
DerivationPath = Trajectory.Trace DerivationStep

pathRefl : ∀ {node} → DerivationPath node node
pathRefl = Trajectory.traceRefl

pathStep :
  ∀ {from middle to} →
  DerivationStep from middle →
  DerivationPath middle to →
  DerivationPath from to
pathStep = Trajectory.traceStep

composeDerivationPath :
  ∀ {a b c} →
  DerivationPath a b →
  DerivationPath b c →
  DerivationPath a c
composeDerivationPath = Trajectory.composeTrace

------------------------------------------------------------------------
-- Readback.  The final formula is one projection; the path is retained as a
-- separate proof-relevant coordinate rather than reconstructed from syntax.
------------------------------------------------------------------------

record DerivedConsequence : Set₁ where
  constructor derivedConsequence
  field
    source : DerivationNode
    target : DerivationNode
    path : DerivationPath source target
    finalFormula : Candidate.Formula
    finalFormulaMatchesTarget : finalFormula ≡ formula target
    pathReading : String

open DerivedConsequence public

record LogicalConsequenceDerivationBoundary : Set where
  constructor logicalConsequenceDerivationBoundary
  field
    finalFormulaDeterminesDerivationPath : Bool
    finalFormulaDeterminesDerivationPathIsFalse :
      finalFormulaDeterminesDerivationPath ≡ false
    logicalAndEmpiricalEdgesAreIdentified : Bool
    logicalAndEmpiricalEdgesAreIdentifiedIsFalse :
      logicalAndEmpiricalEdgesAreIdentified ≡ false
    derivationPathRetainsAuthorityTransitions : Bool
    derivationPathRetainsAuthorityTransitionsIsTrue :
      derivationPathRetainsAuthorityTransitions ≡ true
    pathCompositionIsExplicit : Bool
    pathCompositionIsExplicitIsTrue : pathCompositionIsExplicit ≡ true

canonicalLogicalConsequenceDerivationBoundary :
  LogicalConsequenceDerivationBoundary
canonicalLogicalConsequenceDerivationBoundary =
  logicalConsequenceDerivationBoundary false refl false refl true refl true refl
