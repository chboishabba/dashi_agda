module DASHI.Interop.SemanticReaderElucidatoryConeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawMaboProgressiveExplanationProjectionExact as Mabo

------------------------------------------------------------------------
-- PORTABLE SEMANTIC READER / ADAPTIVE ELUCIDATORY CONE
--
-- Runtime owner:
--   ITIR-suite/itir-svelte/src/lib/workbench/semanticTrail.js
--
-- This is a UI/projection parity owner.  It does not own PNF semantics,
-- source acquisition, legal authority, evidence payment, or world truth.
------------------------------------------------------------------------

data SemanticTargetKind : Set where
  roleTarget constituentTarget compositeTarget claimTarget entityTarget : SemanticTargetKind

data SemanticIntent : Set where
  explainSpanIntent : SemanticIntent
  explainRoleIntent : SemanticIntent
  whyClaimIntent : SemanticIntent
  openSourceIntent : SemanticIntent
  exploreEntityIntent : SemanticIntent
  followReferenceIntent : SemanticIntent
  expandProofConeIntent : SemanticIntent
  backIntent : SemanticIntent

data IntentOutcome : Set where
  executeOutcome deferOutcome rejectOutcome : IntentOutcome

data ConeNode : Set where
  focusNode nearNode farUsefulNode farNoiseNode : ConeNode

withinBaseDepthOne : ConeNode → Bool
withinBaseDepthOne focusNode = true
withinBaseDepthOne nearNode = true
withinBaseDepthOne farUsefulNode = false
withinBaseDepthOne farNoiseNode = false

highElucidatoryValue : ConeNode → Bool
highElucidatoryValue focusNode = false
highElucidatoryValue nearNode = false
highElucidatoryValue farUsefulNode = true
highElucidatoryValue farNoiseNode = false

_or_ : Bool → Bool → Bool
true or _ = true
false or value = value

keepInAdaptiveCone : ConeNode → Bool
keepInAdaptiveCone node = withinBaseDepthOne node or highElucidatoryValue node

focusKept : keepInAdaptiveCone focusNode ≡ true
focusKept = refl

nearKept : keepInAdaptiveCone nearNode ≡ true
nearKept = refl

farUsefulKept : keepInAdaptiveCone farUsefulNode ≡ true
farUsefulKept = refl

farNoiseExcluded : keepInAdaptiveCone farNoiseNode ≡ false
farNoiseExcluded = refl

record SemanticReaderParity : Set where
  constructor semanticReaderParity
  field
    constituentAndCompositeTargetsDistinct : Bool
    overlappingTargetsPermitted : Bool
    baseDepthNodesRetained : Bool
    highElucidatoryFarNodesMayBeRetained : Bool
    arbitraryFarNodesRetained : Bool
    localAdequacyExecutesWithoutAcquisition : Bool
    localInadequacyMayDeferWithResidual : Bool
    localUnavailabilityMeansGlobalFailure : Bool
    defaultShowsQids : Bool
    defaultShowsHashes : Bool
    defaultShowsProofGraph : Bool
    defaultShowsAllResiduals : Bool
    defaultShowsAllSourceRoles : Bool
    defaultShowsTechnicalPnfLabels : Bool
    wikiContextCreatesLegalAuthority : Bool
    qidIdentityCreatesApplicability : Bool
    contextLinkCreatesEvidencePayment : Bool
    roleOverlayCreatesComprehension : Bool
    uiIntentMutatesSemanticState : Bool
    acquiredSourceDisplayCreatesClaimTruth : Bool

open SemanticReaderParity public

canonicalSemanticReaderParity : SemanticReaderParity
canonicalSemanticReaderParity =
  semanticReaderParity
    true true true true false
    true true false
    false false false false false false
    false false false false false false

------------------------------------------------------------------------
-- Existing Mabo projection remains the legal/proof parent.  The portable
-- semantic reader adds interaction/cone behaviour; it does not fork legal
-- semantics.
------------------------------------------------------------------------

maboProjectionAnchor : Mabo.RuntimeReadingConeParity
maboProjectionAnchor = Mabo.canonicalRuntimeReadingConeParity

maboContextBoundaryAnchor : Mabo.ContextNavigationBoundary
maboContextBoundaryAnchor = Mabo.canonicalContextNavigationBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CompositeTargetEqualsConstituentTarget : Set where
data UIIntentCreatesSemanticMutation : Set where
data WikiContextCreatesLegalAuthority : Set where
data QIDIdentityCreatesApplicability : Set where
data ContextLinkPaysEvidence : Set where
data RoleOverlayCreatesComprehension : Set where
data HiddenFromViewMeansAbsentFromWorld : Set where
data LocalUnavailableMeansGloballyUnavailable : Set where
data AcquiredSourceDisplayCreatesClaimTruth : Set where

compositeAndConstituentRemainDistinct : CompositeTargetEqualsConstituentTarget → ⊥
compositeAndConstituentRemainDistinct ()

uiIntentDoesNotMutateSemanticState : UIIntentCreatesSemanticMutation → ⊥
uiIntentDoesNotMutateSemanticState ()

wikiContextIsNotLegalAuthority : WikiContextCreatesLegalAuthority → ⊥
wikiContextIsNotLegalAuthority ()

qidIdentityIsNotApplicability : QIDIdentityCreatesApplicability → ⊥
qidIdentityIsNotApplicability ()

contextLinkIsNotEvidencePayment : ContextLinkPaysEvidence → ⊥
contextLinkIsNotEvidencePayment ()

roleOverlayIsNotComprehension : RoleOverlayCreatesComprehension → ⊥
roleOverlayIsNotComprehension ()

hiddenFromViewIsNotAbsentFromWorld : HiddenFromViewMeansAbsentFromWorld → ⊥
hiddenFromViewIsNotAbsentFromWorld ()

localUnavailableIsNotGloballyUnavailable : LocalUnavailableMeansGloballyUnavailable → ⊥
localUnavailableIsNotGloballyUnavailable ()

acquiredSourceDisplayIsNotClaimTruth : AcquiredSourceDisplayCreatesClaimTruth → ⊥
acquiredSourceDisplayIsNotClaimTruth ()
