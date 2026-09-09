module DASHI.ComputerScience.Ternary27ResidualProgramDecisionBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.TopDownObservationCalculusExact as TopDown
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Branch
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryDependentRecoverableBridgeExact as Recoverable27
import DASHI.ComputerScience.TernaryResidualBinaryDecisionRefinementExact as Decision
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid

------------------------------------------------------------------------
-- EXACT 27-STATE RESIDUAL CODE FOR BOUNDED PROGRAM DIAGNOSTICS
--
-- Three bounded semantic decisions are packed into one ternary cube.  The
-- existing 27 -> 14 antipodal quotient plus dependent orientation residual is
-- then reused.  The canonical TopDown theorem says this exact dependent code is
-- sufficient for every declared consumer of the fine ternary diagnostic state.
------------------------------------------------------------------------

statusToSSP : DASHI.Algebra.Trit.Trit → SSP.SSPTrit
statusToSSP = SSP.fromTrit

programDiagnosticTriple :
  Nat →
  Decision.BoundedBoolProperty →
  Decision.BoundedBoolProperty →
  Decision.BoundedBoolProperty →
  Machine.MachineState →
  Orbit.TritTriple
programDiagnosticTriple fuel p q r start =
  Branch.triple
    (statusToSSP (Decision.boundedDecisionTrit fuel p start))
    (statusToSSP (Decision.boundedDecisionTrit fuel q start))
    (statusToSSP (Decision.boundedDecisionTrit fuel r start))

ternary27ExactCodeObserver :
  Orbit.TritTriple →
  DASHI.Core.DependentRecoverableProjectionExact.DependentCode
    Recoverable27.canonicalAntipodalDependentProjection
ternary27ExactCodeObserver =
  TopDown.dependentCodeObserver Recoverable27.canonicalAntipodalDependentProjection

ternary27ExactCodeAdequateForEveryConsumer :
  ∀ {Outcome : Set} →
  (consumer : Orbit.TritTriple → Outcome) →
  Descent.ConsumerSufficient ternary27ExactCodeObserver consumer
ternary27ExactCodeAdequateForEveryConsumer consumer =
  TopDown.dependentCodeIsAdequateForEveryConsumer
    Recoverable27.canonicalAntipodalDependentProjection
    consumer

------------------------------------------------------------------------
-- Concrete same-program diagnostic packet for Euclid (48,18).
------------------------------------------------------------------------

haltedAgain : Decision.BoundedBoolProperty
haltedAgain state = Machine.halted state

euclidDiagnosticAt0 : Orbit.TritTriple
euclidDiagnosticAt0 =
  programDiagnosticTriple
    0
    Decision.r0IsSix
    Decision.r0IsOne
    haltedAgain
    (Euclid.euclidInitialState 48 18)

euclidDiagnosticAt19 : Orbit.TritTriple
euclidDiagnosticAt19 =
  programDiagnosticTriple
    19
    Decision.r0IsSix
    Decision.r0IsOne
    haltedAgain
    (Euclid.euclidInitialState 48 18)

-- At zero fuel all three coordinates are unresolved.
euclidDiagnosticAt0Exact :
  euclidDiagnosticAt0 ≡
  Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero
euclidDiagnosticAt0Exact = refl

-- At fuel 19:
--   r0 = 6      -> +1
--   r0 = 1      -> -1
--   halted      -> +1
-- giving a genuinely directional three-coordinate semantic packet.
euclidDiagnosticAt19Exact :
  euclidDiagnosticAt19 ≡
  Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne
euclidDiagnosticAt19Exact = refl

------------------------------------------------------------------------
-- Boundary: the gain is refinement/information retention, not a stronger
-- computability class than sufficiently expressive binary coding.
------------------------------------------------------------------------

data ExactTernaryResidualCodeSolvesUniversalHalting : Set where
data Ternary27ConsumerSufficiencyImpliesFasterExecution : Set where
data CoarseAntipodalClassAloneIsAdequateForEveryConsumer : Set where

exactResidualCodeDoesNotSolveUniversalHalting :
  ExactTernaryResidualCodeSolvesUniversalHalting → ⊥
exactResidualCodeDoesNotSolveUniversalHalting ()

consumerSufficiencyDoesNotImplyFasterExecution :
  Ternary27ConsumerSufficiencyImpliesFasterExecution → ⊥
consumerSufficiencyDoesNotImplyFasterExecution ()

coarseClassIsNotPromotedToUniversalAdequacy :
  CoarseAntipodalClassAloneIsAdequateForEveryConsumer → ⊥
coarseClassIsNotPromotedToUniversalAdequacy ()

record Ternary27ResidualProgramDecisionBoundary : Set where
  constructor ternary27ResidualProgramDecisionBoundary
  field
    threeBoundedDecisionsPackInto27State : Bool
    exactAntipodalDependentCodeReused : Bool
    exactCodeAdequateForEveryConsumer : Bool
    unresolvedNegativePositiveRemainDistinct : Bool
    coarseQuotientPromotedToUniversalConsumerAdequacy : Bool
    universalHaltingClaimed : Bool
    runtimeSpeedupClaimedFromRepresentationAlone : Bool

canonicalTernary27ResidualProgramDecisionBoundary :
  Ternary27ResidualProgramDecisionBoundary
canonicalTernary27ResidualProgramDecisionBoundary =
  ternary27ResidualProgramDecisionBoundary
    true true true true false false false
