module DASHI.Visual.TemporalRootedFocusExact where

open import DASHI.Core.Prelude
open import DASHI.Core.SymbolIdentityEvolutionExact
open import DASHI.Core.VersionedStateGraphExact
open import DASHI.Visual.RootedSemanticFocusExact

------------------------------------------------------------------------
-- TEMPORAL ROOTED FOCUS
--
-- One semantic construction may be followed through a real parent lineage.
-- Exact identity is preferred; a supported morph requires explicit identity
-- evidence.  Uncertain similarity terminates continuity rather than inventing
-- a historical identity.
------------------------------------------------------------------------

data TemporalIdentityKind : Set where
  exactTemporalIdentity : TemporalIdentityKind
  supportedTemporalIdentity : TemporalIdentityKind

record TemporalFocusFrame : Set where
  constructor temporalFocusFrame
  field
    temporalFocusCommit : CommitNode
    temporalFocus : RootedSemanticFocus
    temporalIdentityKind : TemporalIdentityKind

open TemporalFocusFrame public

data TemporalFocusStep : Set where
  exactFocusContinuation :
    TemporalFocusFrame →
    TemporalFocusFrame →
    TemporalFocusStep

  supportedFocusMorph :
    SymbolIdentityEvidence →
    TemporalFocusFrame →
    TemporalFocusFrame →
    TemporalFocusStep

data TemporalFocusIntent : Set where
  focusContinuesExactly : TemporalFocusIntent
  focusMorphsWithEvidence : TemporalFocusIntent

temporalFocusIntent : TemporalFocusStep → TemporalFocusIntent
temporalFocusIntent (exactFocusContinuation _ _) =
  focusContinuesExactly
temporalFocusIntent (supportedFocusMorph _ _ _) =
  focusMorphsWithEvidence

record TemporalRootedFocusBoundary : Set where
  constructor temporalRootedFocusBoundary
  field
    uncertainIdentityMayContinueFocusedHistory : Bool
    uncertainIdentityMayContinueFocusedHistoryIsFalse :
      uncertainIdentityMayContinueFocusedHistory ≡ false

    temporalFocusMaySkipParentHistory : Bool
    temporalFocusMaySkipParentHistoryIsFalse :
      temporalFocusMaySkipParentHistory ≡ false

    layoutContinuityProvesSemanticIdentity : Bool
    layoutContinuityProvesSemanticIdentityIsFalse :
      layoutContinuityProvesSemanticIdentity ≡ false

    symbolIntroductionMayBeBackfilledBeforeExistence : Bool
    symbolIntroductionMayBeBackfilledBeforeExistenceIsFalse :
      symbolIntroductionMayBeBackfilledBeforeExistence ≡ false

canonicalTemporalRootedFocusBoundary :
  TemporalRootedFocusBoundary
canonicalTemporalRootedFocusBoundary =
  temporalRootedFocusBoundary
    false refl
    false refl
    false refl
    false refl
