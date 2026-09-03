module DASHI.Moonshine.Base369OODAProofExperimentObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Moonshine.Base369MonsterHistoryIndexedComputationObserverExact as Observer
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as B369

------------------------------------------------------------------------
-- BASE369 OBSERVER FOR THE PROOF / EXPERIMENT / ACTION LOOP
--
-- The 27-sector Base369 carrier is used as a finite observer/chart for control
-- roles.  It does not determine the semantic content, action authority, or a
-- Monster representation.  The map is intentionally one-way.
------------------------------------------------------------------------

data CyberneticRole : Set where
  observedRole
  orientedRole
  candidateDecisionRole
  executedRole
  feedbackRevisionRole
  : CyberneticRole

roleSector : CyberneticRole → B369.CubeFrequencySector
roleSector observedRole = Observer.roleSector Observer.observationRole
roleSector orientedRole = Observer.roleSector Observer.candidateRefinementRole
roleSector candidateDecisionRole = Observer.roleSector Observer.candidateRefinementRole
roleSector executedRole = Observer.roleSector Observer.successfulRecoveryRole
roleSector feedbackRevisionRole = Observer.roleSector Observer.modelRevisionRole

phaseRole : Loop.OODAPhase → CyberneticRole
phaseRole Loop.observePhase = observedRole
phaseRole Loop.orientPhase = orientedRole
phaseRole Loop.decidePhase = candidateDecisionRole
phaseRole Loop.actPhase = executedRole
phaseRole Loop.feedbackPhase = feedbackRevisionRole

phaseSector : Loop.OODAPhase → B369.CubeFrequencySector
phaseSector phase = roleSector (phaseRole phase)

record OODA369Chart : Set where
  constructor ooda369-chart
  field
    phase : Loop.OODAPhase
    role : CyberneticRole
    roleMatchesPhase : role ≡ phaseRole phase
    sector : B369.CubeFrequencySector
    sectorMatchesRole : sector ≡ roleSector role
    historyReference : String
    stateReference : String
    modelReference : String
    residualReference : String
    chartReference : String

open OODA369Chart public

chartPhase : OODA369Chart → B369.CubeFrequencySector
chartPhase chart = sector chart

------------------------------------------------------------------------
-- Move-kind observer.  Proof search, information acquisition, experiment, and
-- physical action may occupy related chart sectors without becoming the same
-- semantic operation.
------------------------------------------------------------------------

moveRole : Loop.EpistemicMoveKind → CyberneticRole
moveRole Loop.thinkMove = orientedRole
moveRole Loop.lookMove = observedRole
moveRole Loop.testMove = candidateDecisionRole
moveRole Loop.actMove = executedRole

moveSector : Loop.EpistemicMoveKind → B369.CubeFrequencySector
moveSector move = roleSector (moveRole move)

record SameSectorDifferentSemanticMove : Set₁ where
  constructor same-sector-different-semantic-move
  field
    leftMove rightMove : Loop.EpistemicMoveKind
    movesDiffer : leftMove ≡ rightMove → ⊥
    sameObservedSector : moveSector leftMove ≡ moveSector rightMove
    semanticDifferenceReference : String

open SameSectorDifferentSemanticMove public

------------------------------------------------------------------------
-- Multi-horizon labels remain observational labels; no phase-sector equality
-- can prove immediate, medium, or long-horizon benefit.
------------------------------------------------------------------------

data Horizon : Set where immediate3 medium6 long9 : Horizon

record HorizonObservation : Set where
  constructor horizon-observation
  field
    horizon : Horizon
    directionReference : String
    evidenceReference : String
    residualReference : String

open HorizonObservation public

record Base369OODAObserverBoundary : Set where
  constructor base369-ooda-observer-boundary
  field
    sectorDeterminesFullSemanticState : Bool
    sectorDeterminesFullSemanticStateIsFalse :
      sectorDeterminesFullSemanticState ≡ false

    sameSectorImpliesSameMoveKind : Bool
    sameSectorImpliesSameMoveKindIsFalse :
      sameSectorImpliesSameMoveKind ≡ false

    phaseSectorAuthorisesPhysicalAction : Bool
    phaseSectorAuthorisesPhysicalActionIsFalse :
      phaseSectorAuthorisesPhysicalAction ≡ false

    phaseSectorConstructsMonsterRepresentation : Bool
    phaseSectorConstructsMonsterRepresentationIsFalse :
      phaseSectorConstructsMonsterRepresentation ≡ false

    immediateSuccessPromotesToLongHorizonSuccess : Bool
    immediateSuccessPromotesToLongHorizonSuccessIsFalse :
      immediateSuccessPromotesToLongHorizonSuccess ≡ false

canonicalBase369OODAObserverBoundary : Base369OODAObserverBoundary
canonicalBase369OODAObserverBoundary =
  base369-ooda-observer-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
