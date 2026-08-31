module DASHI.Physics.Closure.NSCriticalConeAristotleRouteHypergraph2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNHighestAlphaFrontierRound285Exact as R285

------------------------------------------------------------------------
-- NS CRITICAL-CONE ARISTOTLE ROUTE HYPERGRAPH
--
-- Repository-native search representation of the current Round285 frontier.
-- No theorem below is attributed to Aristotle/Harmonic Team or to an NS source;
-- Aristotle supplies only the generic AND/OR hypergraph semantics.
--
-- Important semantic guard: in Aristotle an empty target list is a successful
-- terminal action.  Therefore unresolved analytic leaves and rejected routes
-- below are NEVER encoded with targets = [].
------------------------------------------------------------------------

data NSState : Set where
  packageA
  criticalConeSignedCovariance
  integratedSignedBudgetLeaf
  relativeAbsorptionLeaf
  thresholdEscapeProfileLeaf
  rejectedBoundedCompactRoute
  : NSState

data NSAction : Set where
  directCriticalCone
  integratedBudgetRoute
  relativeAbsorptionRoute
  profileRoute
  boundedCompactAttempt
  : NSAction

source : NSAction → NSState
source directCriticalCone = packageA
source integratedBudgetRoute = criticalConeSignedCovariance
source relativeAbsorptionRoute = criticalConeSignedCovariance
source profileRoute = packageA
source boundedCompactAttempt = packageA

targets : NSAction → List NSState
targets directCriticalCone = criticalConeSignedCovariance ∷ []
targets integratedBudgetRoute = integratedSignedBudgetLeaf ∷ []
targets relativeAbsorptionRoute = relativeAbsorptionLeaf ∷ []
targets profileRoute = thresholdEscapeProfileLeaf ∷ []
-- Self-blocking: Round285 has already rejected this route for the declared
-- persistent-badness predicate.  It must not become a false terminal success.
targets boundedCompactAttempt = rejectedBoundedCompactRoute ∷ []

nsCriticalConeHypergraph : Aristotle.SearchHypergraph
nsCriticalConeHypergraph = record
  { State = NSState
  ; Action = NSAction
  ; source = source
  ; targets = targets
  }

------------------------------------------------------------------------
-- Route admission is explicit and inherits the authoritative R285 cut.
------------------------------------------------------------------------

routeDisposition : NSAction → Admission.RouteDisposition
routeDisposition directCriticalCone = Admission.admitted
routeDisposition integratedBudgetRoute = Admission.admitted
routeDisposition relativeAbsorptionRoute = Admission.admitted
routeDisposition profileRoute = Admission.admitted
routeDisposition boundedCompactAttempt = Admission.rejected Admission.noGoCollision

boundedCompactRejectedByCurrentFrontier :
  R285.round285BoundedAlmostPeriodicPersistentBadRouteRejected ≡ true
boundedCompactRejectedByCurrentFrontier =
  R285.round285BoundedAlmostPeriodicPersistentBadRouteRejectedIsTrue

directRouteIsHighestAlpha :
  R285.round285DirectPhysicalCoherentDebtRouteHighestAlpha ≡ true
directRouteIsHighestAlpha =
  R285.round285DirectPhysicalCoherentDebtRouteHighestAlphaIsTrue

criticalConeLeafStillOpen :
  R285.round285PhysicalCriticalConeSignedCovarianceClosed ≡ false
criticalConeLeafStillOpen =
  R285.round285PhysicalCriticalConeSignedCovarianceClosedIsFalse

------------------------------------------------------------------------
-- The two direct sufficient consumers are intentionally separate OR branches.
-- Round285 explicitly says they are both admissible but not totally ordered by
-- strength.  The hypergraph therefore does not collapse one into the other.
------------------------------------------------------------------------

integratedAndRelativeAreSeparateActions :
  integratedBudgetRoute ≡ relativeAbsorptionRoute → ⊥
integratedAndRelativeAreSeparateActions ()

record NSRouteHypergraphBoundary : Set where
  constructor nsRouteHypergraphBoundary
  field
    unresolvedLeafUsesEmptyTargets : Bool
    unresolvedLeafUsesEmptyTargetsIsFalse : unresolvedLeafUsesEmptyTargets ≡ false
    rejectedRouteUsesEmptyTargets : Bool
    rejectedRouteUsesEmptyTargetsIsFalse : rejectedRouteUsesEmptyTargets ≡ false
    integratedAndRelativeCollapsedToOneRoute : Bool
    integratedAndRelativeCollapsedToOneRouteIsFalse :
      integratedAndRelativeCollapsedToOneRoute ≡ false
    knownNoGoMayBeRetriedAsIfAdmitted : Bool
    knownNoGoMayBeRetriedAsIfAdmittedIsFalse : knownNoGoMayBeRetriedAsIfAdmitted ≡ false
    directPhysicalCriticalConeRemainsHighestAlpha : Bool
    directPhysicalCriticalConeRemainsHighestAlphaIsTrue :
      directPhysicalCriticalConeRemainsHighestAlpha ≡ true

canonicalNSRouteHypergraphBoundary : NSRouteHypergraphBoundary
canonicalNSRouteHypergraphBoundary =
  nsRouteHypergraphBoundary
    false refl
    false refl
    false refl
    false refl
    true refl

highestAlphaReading : String
highestAlphaReading =
  "Attack the physical signed covariance on the parabolic critical cone. Keep integrated signed-budget and strict relative-absorption consumers as incomparable OR branches; retain the bounded compact persistent-bad route as a proved no-go, not an assumption to be weakened."
