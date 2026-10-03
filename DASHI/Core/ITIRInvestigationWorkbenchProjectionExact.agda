module DASHI.Core.ITIRInvestigationWorkbenchProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ITIRInvestigationAcquisitionParetoExact as INV
import DASHI.Cognition.PNF.SensibLawMatterWorkspaceProjectionExact as Matter

-- A projection is indexed by Matter, consumer/question and authorised viewer.
record InvestigationProjectionIndex : Set where
  constructor investigation-projection-index
  field
    matterRef : String
    consumerRef : String
    viewerRef : String
open InvestigationProjectionIndex public

record AcquisitionWorld : Set₁ where
  constructor acquisition-world
  field
    Route : Set
    routeRef : Route → String
    WorldRoute : Route → Set
    FrontierRoute : Route → Set
    ExecutableRoute : Route → Set
    BlockedRoute : Route → Set
    PotentialReopening : Route → Set
    ActualReopening : Route → Set
open AcquisitionWorld public

record InvestigationView
    (world : AcquisitionWorld)
    (index : InvestigationProjectionIndex) : Set₁ where
  constructor investigation-view
  field
    VisibleRoute : Route world → Set
    SelectedRoute : Route world → Set
    PreferredRoute : Route world → Set
    visibleRouteIsReal :
      ∀ route → VisibleRoute route → WorldRoute world route
    frontierViewIsReal :
      ∀ route → VisibleRoute route → FrontierRoute world route → WorldRoute world route
    selectionDoesNotConstructPreference :
      ∀ route → SelectedRoute route → PreferredRoute route → ⊥
    projectionOnly : Bool
    projectionOnlyIsTrue : projectionOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsAccessAuthority : Bool
    createsAccessAuthorityIsFalse : createsAccessAuthority ≡ false
    createsEvidence : Bool
    createsEvidenceIsFalse : createsEvidence ≡ false
open InvestigationView public

-- Presentation/action confusion classes are uninhabited in the formal owner.
data HiddenRouteMeansAbsent : Set where
data SelectedRouteMeansPreferred : Set where
data FirstRenderedMeansBest : Set where
data FilteredRouteMeansDominated : Set where
data BlockedRouteMeansDominated : Set where
data ExecutableRouteMeansPreferred : Set where
data FrontierRouteMeansAuthorized : Set where
data SortChangesFrontier : Set where
data NavigationCreatesEvidence : Set where
data RequestAuthorizationGrantsAuthorization : Set where
data PotentialReopeningIsActual : Set where
data UIGeneratesPresentSource : Set where

hiddenDoesNotMeanAbsent : HiddenRouteMeansAbsent → ⊥
hiddenDoesNotMeanAbsent ()

selectedDoesNotMeanPreferred : SelectedRouteMeansPreferred → ⊥
selectedDoesNotMeanPreferred ()

firstDoesNotMeanBest : FirstRenderedMeansBest → ⊥
firstDoesNotMeanBest ()

filteredDoesNotMeanDominated : FilteredRouteMeansDominated → ⊥
filteredDoesNotMeanDominated ()

blockedDoesNotMeanDominated : BlockedRouteMeansDominated → ⊥
blockedDoesNotMeanDominated ()

executableDoesNotMeanPreferred : ExecutableRouteMeansPreferred → ⊥
executableDoesNotMeanPreferred ()

frontierDoesNotGrantAuthorization : FrontierRouteMeansAuthorized → ⊥
frontierDoesNotGrantAuthorization ()

sortDoesNotChangeFrontier : SortChangesFrontier → ⊥
sortDoesNotChangeFrontier ()

navigationDoesNotCreateEvidence : NavigationCreatesEvidence → ⊥
navigationDoesNotCreateEvidence ()

requestAuthorizationDoesNotGrantAuthorization :
  RequestAuthorizationGrantsAuthorization → ⊥
requestAuthorizationDoesNotGrantAuthorization ()

potentialReopeningDoesNotBecomeActual : PotentialReopeningIsActual → ⊥
potentialReopeningDoesNotBecomeActual ()

uiCannotGeneratePresentSource : UIGeneratesPresentSource → ⊥
uiCannotGeneratePresentSource ()

record InvestigationWorkbenchBoundary : Set where
  constructor investigation-workbench-boundary
  field
    matterWorkspaceReused : Bool
    matterWorkspaceReusedIsTrue : matterWorkspaceReused ≡ true
    directMixedParetoReused : Bool
    directMixedParetoReusedIsTrue : directMixedParetoReused ≡ true
    graphIsOptionalPowerView : Bool
    graphIsOptionalPowerViewIsTrue : graphIsOptionalPowerView ≡ true
    renderOrderCarriesPriority : Bool
    renderOrderCarriesPriorityIsFalse : renderOrderCarriesPriority ≡ false
    colorIsOnlyStateCarrier : Bool
    colorIsOnlyStateCarrierIsFalse : colorIsOnlyStateCarrier ≡ false
    uiMayConstructAcquisitionResult : Bool
    uiMayConstructAcquisitionResultIsFalse : uiMayConstructAcquisitionResult ≡ false

canonicalInvestigationWorkbenchBoundary : InvestigationWorkbenchBoundary
canonicalInvestigationWorkbenchBoundary =
  investigation-workbench-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

-- Explicit cross-owner references: Matter remains the visibility/projection
-- authority; INV remains the frontier authority.
matterProjectionAuthority : Matter.MatterSubsystemBoundary
matterProjectionAuthority = Matter.canonicalMatterSubsystemBoundary

paretoAuthority : INV.InvestigationAcquisitionBoundary
paretoAuthority = INV.canonicalInvestigationAcquisitionBoundary
