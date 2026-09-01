module DASHI.Core.ProofSearchFrontierObserverTrustExact where

------------------------------------------------------------------------
-- PROOF-SEARCH FRONTIER OBSERVER TRUST
--
-- Cross-pollinates the observation-intervention lesson into theorem search:
--   actual repo frontier != reported/search frontier != route belief.
-- A route may reason coherently from a stale or falsified frontier and still be
-- structurally wrong about novelty, prerequisite closure or urgency.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ObservationInterventionTrustFibreExact
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission

------------------------------------------------------------------------
-- Three frontier layers.
------------------------------------------------------------------------

data ActualFrontier : Set where
  actualLeafOpen actualLeafClosed : ActualFrontier

data ReportedFrontier : Set where
  reportsOpen reportsClosed : ReportedFrontier

data BelievedFrontier : Set where
  believesOpen believesClosed : BelievedFrontier

data SearchMove : Set where
  elaborateCandidate reuseExisting reopenPrerequisite : SearchMove

data FrontierProvenance : Set where
  repoVerified staleSnapshot routeSelfReport unresolvedFrontier : FrontierProvenance

record FrontierObservation : Set where
  constructor frontier-observation
  field
    actual : ActualFrontier
    reported : ReportedFrontier
    believed : BelievedFrontier
    provenance : FrontierProvenance

open FrontierObservation public

accurateOpen : FrontierObservation
accurateOpen = frontier-observation actualLeafOpen reportsOpen believesOpen repoVerified

falseClosed : FrontierObservation
falseClosed = frontier-observation actualLeafOpen reportsClosed believesClosed routeSelfReport

staleOpenAfterClosure : FrontierObservation
staleOpenAfterClosure = frontier-observation actualLeafClosed reportsOpen believesOpen staleSnapshot

routeMove : FrontierObservation → SearchMove
routeMove state with actual state | believed state
... | actualLeafOpen | believesOpen = elaborateCandidate
... | actualLeafOpen | believesClosed = reopenPrerequisite
... | actualLeafClosed | believesOpen = reuseExisting
... | actualLeafClosed | believesClosed = reuseExisting

sameActualDifferentReported :
  actual accurateOpen ≡ actual falseClosed
sameActualDifferentReported = refl

reportedDiffersDespiteSameActual :
  reported accurateOpen ≡ reported falseClosed → ⊥
reportedDiffersDespiteSameActual ()

beliefDiffersDespiteSameActual :
  believed accurateOpen ≡ believed falseClosed → ⊥
beliefDiffersDespiteSameActual ()

moveDiffersDespiteSameActual :
  routeMove accurateOpen ≡ routeMove falseClosed → ⊥
moveDiffersDespiteSameActual ()

------------------------------------------------------------------------
-- Promotion/novelty require repo-grounded frontier receipts.
------------------------------------------------------------------------

data RepoGroundedFrontier : FrontierObservation → Set where
  groundedOpen : RepoGroundedFrontier accurateOpen

data FrontierPromotion : FrontierObservation → Set where
  promoteGrounded : RepoGroundedFrontier accurateOpen → FrontierPromotion accurateOpen

falseClosedCannotPromote : FrontierPromotion falseClosed → ⊥
falseClosedCannotPromote ()

staleOpenCannotProveNovelty : RepoGroundedFrontier staleOpenAfterClosure → ⊥
staleOpenCannotProveNovelty ()

------------------------------------------------------------------------
-- Route belief is not an exact-consumer capability.
------------------------------------------------------------------------

data BeliefGeneratedConsumerReceipt : BelievedFrontier → Set where
-- intentionally no constructor

beliefCannotManufactureExactConsumerAuthority :
  BeliefGeneratedConsumerReceipt believesClosed → ⊥
beliefCannotManufactureExactConsumerAuthority ()

exactConsumerStillOwnsProgrammePromotion :
  Admission.ExactConsumerReceipt → Admission.ProgrammeProgress
exactConsumerStillOwnsProgrammePromotion = Admission.promote

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ProofSearchFrontierTrustBoundary : Set where
  constructor proof-search-frontier-trust-boundary
  field
    reportedFrontierIsActualFrontier : Bool
    reportedFrontierIsActualFrontierIsFalse : reportedFrontierIsActualFrontier ≡ false
    believedFrontierIsActualFrontier : Bool
    believedFrontierIsActualFrontierIsFalse : believedFrontierIsActualFrontier ≡ false
    routeBeliefCanEstablishNovelty : Bool
    routeBeliefCanEstablishNoveltyIsFalse : routeBeliefCanEstablishNovelty ≡ false
    staleOpenLeafShouldBeReproved : Bool
    staleOpenLeafShouldBeReprovedIsFalse : staleOpenLeafShouldBeReproved ≡ false
    falseClosureMayMoveProgrammeFrontier : Bool
    falseClosureMayMoveProgrammeFrontierIsFalse : falseClosureMayMoveProgrammeFrontier ≡ false
    reading : String

canonicalProofSearchFrontierTrustBoundary : ProofSearchFrontierTrustBoundary
canonicalProofSearchFrontierTrustBoundary =
  proof-search-frontier-trust-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    "Proof search separates the actual repository frontier, the frontier reported to the route, and the route's belief. A stale or injected frontier can rationally alter route choice without changing repository truth; novelty and programme promotion require repo-grounded/exact-consumer receipts rather than route belief."
