module DASHI.Visual.ResearchFilmDirectorExact where

open import DASHI.Core.Prelude
open import DASHI.Visual.ActiveWorkingSetExact
open import DASHI.Visual.CameraDirectorExact

record SemanticEpisode : Set where
  constructor semanticEpisode
  field
    episodeProgramme : String
    episodeTopicTokens : List String
    episodeCommitIds : List String
    episodeFocusNodeIds : List String
    episodeFocusEdgeIds : List String
    episodeSalience : Nat
    episodeReturnsToExistingRegion : Bool

open SemanticEpisode public

data FilmBeatKind : Set where
  episodeTitleBeat : FilmBeatKind
  semanticChangeBeat : FilmBeatKind
  branchForkBeat : FilmBeatKind
  branchMergeBeat : FilmBeatKind
  pullRequestMergeBeat : FilmBeatKind
  crossProgrammeOverviewBeat : FilmBeatKind

record FilmBeat : Set where
  constructor filmBeat
  field
    filmBeatKind : FilmBeatKind
    filmBeatCommit : String
    filmBeatProgramme : String
    filmBeatTopic : String
    filmBeatFocusNodeIds : List String
    filmBeatVisibleNodeIds : List String
    filmBeatCamera : CameraDirective

open FilmBeat public

record ResearchFilmDirectorBoundary : Set where
  constructor researchFilmDirectorBoundary
  field
    editorialPacingMayChangeSemanticHistory : Bool
    editorialPacingMayChangeSemanticHistoryIsFalse :
      editorialPacingMayChangeSemanticHistory ≡ false

    adjacentRelatedCommitsMayCoalesceForPresentation : Bool
    adjacentRelatedCommitsMayCoalesceForPresentationIsTrue :
      adjacentRelatedCommitsMayCoalesceForPresentation ≡ true

    programmeReturnMayReusePersistentRegion : Bool
    programmeReturnMayReusePersistentRegionIsTrue :
      programmeReturnMayReusePersistentRegion ≡ true

    branchAndPullRequestEventsMayAnnotateSemanticFilm : Bool
    branchAndPullRequestEventsMayAnnotateSemanticFilmIsTrue :
      branchAndPullRequestEventsMayAnnotateSemanticFilm ≡ true

    boundedProgrammeMemoryMayChangeSemanticHistory : Bool
    boundedProgrammeMemoryMayChangeSemanticHistoryIsFalse :
      boundedProgrammeMemoryMayChangeSemanticHistory ≡ false

    dormantContextMayBeHiddenWithoutBeingDeleted : Bool
    dormantContextMayBeHiddenWithoutBeingDeletedIsTrue :
      dormantContextMayBeHiddenWithoutBeingDeleted ≡ true

canonicalResearchFilmDirectorBoundary :
  ResearchFilmDirectorBoundary
canonicalResearchFilmDirectorBoundary =
  researchFilmDirectorBoundary
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
