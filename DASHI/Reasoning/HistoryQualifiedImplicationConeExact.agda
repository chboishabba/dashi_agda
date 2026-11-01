module DASHI.Reasoning.HistoryQualifiedImplicationConeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.LogicalConsequenceDerivationPathExact as Path

------------------------------------------------------------------------
-- HISTORY-QUALIFIED IMPLICATION CONE
--
-- Cone status is an evidential surface; derivation history is a separate
-- coordinate.  The same target assertion/status may therefore be reached by
-- different paths, and those paths remain inspectable rather than flattened.
------------------------------------------------------------------------

record HistoryQualifiedConeEdge
    (edge : Cone.ImplicationEdge) : Set₁ where
  constructor historyQualifiedConeEdge
  field
    sourceNode : Path.DerivationNode
    targetNode : Path.DerivationNode
    sourceKeyMatches : Path.nodeKey sourceNode ≡ Cone.fromNode edge
    targetKeyMatches : Path.nodeKey targetNode ≡ Cone.toNode edge
    derivation : Path.DerivationPath sourceNode targetNode
    edgeHistoryReference : String
    retainedResidualReference : String

open HistoryQualifiedConeEdge public

record HistoryQualifiedExperimentalCone
    {source : Cone.NaturalLanguageExperimentalAssertion}
    (cone : Cone.ExperimentalImplicationCone source) : Set₁ where
  constructor historyQualifiedExperimentalCone
  field
    edgeHistories : List (Σ Cone.ImplicationEdge HistoryQualifiedConeEdge)
    coverageReference : String
    missingHistoryReference : String

open HistoryQualifiedExperimentalCone public

------------------------------------------------------------------------
-- A path witness may be projected to the ordinary edge, but the reverse
-- reconstruction is intentionally unavailable without an explicit history.
------------------------------------------------------------------------

forgetHistory :
  Σ Cone.ImplicationEdge HistoryQualifiedConeEdge →
  Cone.ImplicationEdge
forgetHistory pair = proj₁ pair

record HistoryQualifiedImplicationBoundary : Set where
  constructor historyQualifiedImplicationBoundary
  field
    coneStatusDeterminesUniqueDerivationHistory : Bool
    coneStatusDeterminesUniqueDerivationHistoryIsFalse :
      coneStatusDeterminesUniqueDerivationHistory ≡ false
    finalNodeKeyDeterminesUniqueDerivationHistory : Bool
    finalNodeKeyDeterminesUniqueDerivationHistoryIsFalse :
      finalNodeKeyDeterminesUniqueDerivationHistory ≡ false
    coneEdgeMayRetainIndexedDerivationPath : Bool
    coneEdgeMayRetainIndexedDerivationPathIsTrue :
      coneEdgeMayRetainIndexedDerivationPath ≡ true
    forgettingHistoryIsAllowed : Bool
    forgettingHistoryIsAllowedIsTrue : forgettingHistoryIsAllowed ≡ true
    reconstructingHistoryFromFlatEdgeIsAutomatic : Bool
    reconstructingHistoryFromFlatEdgeIsAutomaticIsFalse :
      reconstructingHistoryFromFlatEdgeIsAutomatic ≡ false

canonicalHistoryQualifiedImplicationBoundary :
  HistoryQualifiedImplicationBoundary
canonicalHistoryQualifiedImplicationBoundary =
  historyQualifiedImplicationBoundary false refl false refl true refl true refl false refl
