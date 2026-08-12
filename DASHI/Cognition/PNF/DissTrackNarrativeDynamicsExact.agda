module DASHI.Cognition.PNF.DissTrackNarrativeDynamicsExact where

------------------------------------------------------------------------
-- DISS-TRACK NARRATIVE DYNAMICS / PHASE CAPTURE
--
-- Worked cultural stress-test for the provenance machinery. Song titles and
-- chronology are labels; disputed lyrical allegations are NOT promoted to
-- mathematical truth. Suspected/interpretive prehistory is typed separately
-- from the direct 2024 battle core.
--
-- Historical reference for the direct 2024 exchange:
--   Graham v. UMG Recordings, Inc., No. 1:25-cv-00399 (S.D.N.Y. 2025),
--   Document 96. The opinion describes a 16-day, eight-diss-track exchange
--   and treats the songs as an adversarial dialogue in context.
--
-- Adjacent-war titles are retained as adjacent rather than silently promoted
-- into the direct Kendrick/Drake chain. Contemporary timelines identify J.
-- Cole's 7 Minute Drill, Rick Ross's Champagne Moments, The Weeknd's All to
-- Myself, A$AP Rocky's Show of Hands, Metro Boomin's BBL Drizzy, and Drake's
-- use of the BBL Drizzy instrumental on U My Everything as part of the wider
-- 2024 conflict field.
--
-- No DOI is asserted for the journalistic or judicial provenance.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Concentric corpus rings. The adjacent ring remains explicitly open-ended;
-- the point is to preserve modality rather than turn fan interpretation into
-- a direct-diss fact.
------------------------------------------------------------------------

data CorpusRing : Set where
  causalPrehistory directBattle adjacentWar : CorpusRing

data Artifact : Set where
  buriedAliveInterlude
  poeticJustice
  fuckinProblems
  controlVerse
  betCypher2013
  theLanguage
  kingKunta
  hundred
  element
  theHillbillies
  firstPersonShooter
  likeThat
  pushUps
  taylorMadeFreestyle
  euphoria
  sixSixteenInLA
  familyMatters
  meetTheGrahams
  notLikeUs
  theHeartPart6
  sevenMinuteDrill
  champagneMoments
  allToMyself
  showOfHands
  bblDrizzy
  uMyEverything
  adjacentUnresolved : Artifact

ringOf : Artifact → CorpusRing
ringOf buriedAliveInterlude = causalPrehistory
ringOf poeticJustice = causalPrehistory
ringOf fuckinProblems = causalPrehistory
ringOf controlVerse = causalPrehistory
ringOf betCypher2013 = causalPrehistory
ringOf theLanguage = causalPrehistory
ringOf kingKunta = causalPrehistory
ringOf hundred = causalPrehistory
ringOf element = causalPrehistory
ringOf theHillbillies = causalPrehistory
ringOf firstPersonShooter = causalPrehistory
ringOf likeThat = directBattle
ringOf pushUps = directBattle
ringOf taylorMadeFreestyle = directBattle
ringOf euphoria = directBattle
ringOf sixSixteenInLA = directBattle
ringOf familyMatters = directBattle
ringOf meetTheGrahams = directBattle
ringOf notLikeUs = directBattle
ringOf theHeartPart6 = directBattle
ringOf sevenMinuteDrill = adjacentWar
ringOf champagneMoments = adjacentWar
ringOf allToMyself = adjacentWar
ringOf showOfHands = adjacentWar
ringOf bblDrizzy = adjacentWar
ringOf uMyEverything = adjacentWar
ringOf adjacentUnresolved = adjacentWar

------------------------------------------------------------------------
-- Operator roles: songs need not perform the same state transition.
------------------------------------------------------------------------

data OperatorRole : Set where
  rankingProposal
  rankingRejection
  commercialCounter
  responsePhasePressure
  authenticityReframe
  provenanceAttack
  hiddenFibreAttack
  relationalFibreAttack
  categoricalCompression
  evidentiaryReopening
  adjacentResponse : OperatorRole

roleOf : Artifact → OperatorRole
roleOf firstPersonShooter = rankingProposal
roleOf likeThat = rankingRejection
roleOf pushUps = commercialCounter
roleOf taylorMadeFreestyle = responsePhasePressure
roleOf euphoria = authenticityReframe
roleOf sixSixteenInLA = provenanceAttack
roleOf familyMatters = hiddenFibreAttack
roleOf meetTheGrahams = relationalFibreAttack
roleOf notLikeUs = categoricalCompression
roleOf theHeartPart6 = evidentiaryReopening
roleOf sevenMinuteDrill = adjacentResponse
roleOf champagneMoments = adjacentResponse
roleOf allToMyself = adjacentResponse
roleOf showOfHands = adjacentResponse
roleOf bblDrizzy = adjacentResponse
roleOf uMyEverything = adjacentResponse
roleOf buriedAliveInterlude = adjacentResponse
roleOf poeticJustice = adjacentResponse
roleOf fuckinProblems = adjacentResponse
roleOf controlVerse = adjacentResponse
roleOf betCypher2013 = adjacentResponse
roleOf theLanguage = adjacentResponse
roleOf kingKunta = adjacentResponse
roleOf hundred = adjacentResponse
roleOf element = adjacentResponse
roleOf theHillbillies = adjacentResponse
roleOf adjacentUnresolved = adjacentResponse

------------------------------------------------------------------------
-- Explicit direct-core successor relation. This is a provenance path, not a
-- claim that every public timeline contains only these artifacts.
------------------------------------------------------------------------

data DirectSuccessor : Artifact → Artifact → Set where
  likeToPush : DirectSuccessor likeThat pushUps
  pushToTaylor : DirectSuccessor pushUps taylorMadeFreestyle
  taylorToEuphoria : DirectSuccessor taylorMadeFreestyle euphoria
  euphoriaTo616 : DirectSuccessor euphoria sixSixteenInLA
  six16ToFamily : DirectSuccessor sixSixteenInLA familyMatters
  familyToMeet : DirectSuccessor familyMatters meetTheGrahams
  meetToNotLike : DirectSuccessor meetTheGrahams notLikeUs
  notLikeToHeart6 : DirectSuccessor notLikeUs theHeartPart6

------------------------------------------------------------------------
-- Phase capture mini-world.
--
-- Family Matters is modelled as opening a Drake-controlled response window.
-- Meet the Grahams immediately following it moves the public phase to a
-- distinct captured state before the first frame stabilises. The theorem is
-- intentionally only about update order in this finite model.
------------------------------------------------------------------------

data PublicPhase : Set where
  openField drakeWindow kendrickCaptured anthemCompressed reopeningWindow : PublicPhase

familyMattersUpdate : PublicPhase → PublicPhase
familyMattersUpdate state = drakeWindow

meetTheGrahamsUpdate : PublicPhase → PublicPhase
meetTheGrahamsUpdate drakeWindow = kendrickCaptured
meetTheGrahamsUpdate state = state

notLikeUsUpdate : PublicPhase → PublicPhase
notLikeUsUpdate state = anthemCompressed

heartPart6Update : PublicPhase → PublicPhase
heartPart6Update state = reopeningWindow

familyAlone : PublicPhase
familyAlone = familyMattersUpdate openField

familyThenMeet : PublicPhase
familyThenMeet = meetTheGrahamsUpdate (familyMattersUpdate openField)

phaseCaptureChangesPublicState : familyThenMeet ≡ familyAlone → ⊥
phaseCaptureChangesPublicState ()

notLikeUsAfterCaptureIsCompressed :
  notLikeUsUpdate familyThenMeet ≡ anthemCompressed
notLikeUsAfterCaptureIsCompressed = refl

heartPart6AttemptsReopeningAfterCompression :
  heartPart6Update (notLikeUsUpdate familyThenMeet) ≡ reopeningWindow
heartPart6AttemptsReopeningAfterCompression = refl

------------------------------------------------------------------------
-- Timing/provenance cannot be erased merely because two transitions mention
-- the same underlying proposition family.
------------------------------------------------------------------------

data UpdateOrder : Set where
  drakeThenKendrick kendrickThenDrake : UpdateOrder

orderSensitive : UpdateOrder → PublicPhase
orderSensitive drakeThenKendrick = kendrickCaptured
orderSensitive kendrickThenDrake = drakeWindow

orderChangesOutcome :
  orderSensitive drakeThenKendrick ≡ orderSensitive kendrickThenDrake → ⊥
orderChangesOutcome ()
