module DASHI.Ontology.WikidataEpistemicBridgeTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.ContextualClaimComposition
open import DASHI.Ontology.WikidataEpistemicBridge

------------------------------------------------------------------------
-- Minimal executable proof witnesses.

data Axis : Set where
  temporal jurisdictional : Axis

leftState : Axis → EpistemicTrit
leftState temporal = supported
leftState jurisdictional = unresolved

rightState : Axis → EpistemicTrit
rightState temporal = contradicted
rightState jurisdictional = supported

leftStatement : StatementEnvelope Axis
leftStatement =
  statementEnvelope "Q-left" leftState [] preferred

rightStatement : StatementEnvelope Axis
rightStatement =
  statementEnvelope "Q-right" rightState [] normal

temporalConflictPreserved :
  stateAt (composeStatements leftStatement rightStatement) temporal
  ≡ unresolved
temporalConflictPreserved = refl

jurisdictionalUncertaintyPreserved :
  stateAt (composeStatements leftStatement rightStatement) jurisdictional
  ≡ unresolved
jurisdictionalUncertaintyPreserved = refl

binaryAcceptPolicyLosesDistinction :
  forceUnresolvedToAccept unresolved ≡ forceUnresolvedToAccept supported
binaryAcceptPolicyLosesDistinction = refl

binaryRejectPolicyLosesDistinction :
  forceUnresolvedToReject unresolved ≡ forceUnresolvedToReject contradicted
binaryRejectPolicyLosesDistinction = refl

data ExtraAxis : Set where
  sourceLanguage : ExtraAxis

extendedLeft : ScopedClaim (Axis ⊎ ExtraAxis)
extendedLeft = extendAxisUnresolved (asScopedClaim leftStatement)

oldTemporalCoordinateUnchanged :
  stateAt extendedLeft (inj₁ temporal) ≡ supported
oldTemporalCoordinateUnchanged = refl

newLanguageCoordinateUnresolved :
  stateAt extendedLeft (inj₂ sourceLanguage) ≡ unresolved
newLanguageCoordinateUnresolved = refl
