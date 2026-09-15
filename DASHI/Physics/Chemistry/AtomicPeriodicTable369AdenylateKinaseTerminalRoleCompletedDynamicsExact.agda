module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseTerminalRoleCompletedDynamicsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reach
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialStateCoordinateAlignmentExact as Align
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialAlignedDynamicsExact as Partial
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseTerminalNotationRoleBridgeExact as Terminal

------------------------------------------------------------------------
-- TERMINAL-ROLE-COMPLETED PARTIAL ALIGNMENT DYNAMICS
--
-- The previous dependent aligned carrier stops before equation-level xi because
-- there is no source-paid xi=zeta equality.  The source itself does, however,
-- pay a weaker seam: prose routes terminate at Figure/prose zeta while Eq. (1)
-- writes the corresponding route-flux expressions with terminal xi.
--
-- We therefore complete the *route role*, not object identity.  The terminal
-- state below is tagged by the heterogeneous TerminalRoleBridge.  Its coordinate
-- view is Figure-zeta's already-paid closed two-angle region; this does not turn
-- equation xi into zeta or assign xi a per-state dLN coordinate.
------------------------------------------------------------------------

data RoleCompletedState : Set where
  alignedState : Partial.AlignedAdKState → RoleCompletedState
  terminalRoleState : Terminal.TerminalRoleBridge → RoleCompletedState

alphaRoleState betaRoleState gammaRoleState deltaRoleState epsilonRoleState : RoleCompletedState
alphaRoleState = alignedState Partial.alphaAlignedState
betaRoleState = alignedState Partial.betaAlignedState
gammaRoleState = alignedState Partial.gammaAlignedState
deltaRoleState = alignedState Partial.deltaAlignedState
epsilonRoleState = alignedState Partial.epsilonAlignedState

canonicalTerminalRoleState : RoleCompletedState
canonicalTerminalRoleState = terminalRoleState Terminal.canonicalTerminalRoleBridge

data RolePosition : Set where
  graphPosition : Graph.AdKLandscapeState → RolePosition
  terminalClosedPosition : RolePosition

rolePosition : RoleCompletedState → RolePosition
rolePosition (alignedState state) = graphPosition (proj₁ state)
rolePosition (terminalRoleState bridge) = terminalClosedPosition

------------------------------------------------------------------------
-- Coordinate observation remains source-role qualified.
------------------------------------------------------------------------

roleCoordinateRegion : RoleCompletedState → Align.PartialThreeCvRegion
roleCoordinateRegion (alignedState state) = Partial.alignedRegion state
roleCoordinateRegion (terminalRoleState bridge) = Align.figureStateRegion Align.zetaFigure

terminalRoleClosedRegion : Align.PartialThreeCvRegion
terminalRoleClosedRegion = roleCoordinateRegion canonicalTerminalRoleState

terminalRoleExactTwoAnglePoint : Align.ExactTwoAnglePoint
terminalRoleExactTwoAnglePoint = Align.exactTwoAnglePoint terminalRoleClosedRegion

terminalRoleDLnStatus : Align.DLnAlignmentStatus
terminalRoleDLnStatus = Align.dLnStatus terminalRoleClosedRegion

------------------------------------------------------------------------
-- Route actions.  The final two actions target the tagged terminal role rather
-- than a fabricated aligned xi/zeta state.
------------------------------------------------------------------------

data RoleCompletedAction : Set where
  roleAlphaBeta : RoleCompletedAction
  roleBetaGamma : RoleCompletedAction
  roleGammaDelta : RoleCompletedAction
  roleBetaEpsilon : RoleCompletedAction
  roleDeltaTerminal : RoleCompletedAction
  roleEpsilonTerminal : RoleCompletedAction

roleActionSource : RoleCompletedAction → RolePosition
roleActionSource roleAlphaBeta = graphPosition Graph.alpha
roleActionSource roleBetaGamma = graphPosition Graph.beta
roleActionSource roleGammaDelta = graphPosition Graph.gamma
roleActionSource roleBetaEpsilon = graphPosition Graph.beta
roleActionSource roleDeltaTerminal = graphPosition Graph.delta
roleActionSource roleEpsilonTerminal = graphPosition Graph.epsilon

roleActionTarget : RoleCompletedAction → RolePosition
roleActionTarget roleAlphaBeta = graphPosition Graph.beta
roleActionTarget roleBetaGamma = graphPosition Graph.gamma
roleActionTarget roleGammaDelta = graphPosition Graph.delta
roleActionTarget roleBetaEpsilon = graphPosition Graph.epsilon
roleActionTarget roleDeltaTerminal = terminalClosedPosition
roleActionTarget roleEpsilonTerminal = terminalClosedPosition

roleActionEdge : RoleCompletedAction → Graph.DirectedLandscapeEdge
roleActionEdge roleAlphaBeta = Graph.alphaBeta
roleActionEdge roleBetaGamma = Graph.betaGamma
roleActionEdge roleGammaDelta = Graph.gammaDelta
roleActionEdge roleBetaEpsilon = Graph.betaEpsilon
roleActionEdge roleDeltaTerminal = Graph.deltaXi
roleActionEdge roleEpsilonTerminal = Graph.epsilonXi

rolePrecondition : RoleCompletedState → RoleCompletedAction → Set
rolePrecondition before action = rolePosition before ≡ roleActionSource action

rolePostcondition :
  RoleCompletedState → RoleCompletedAction → RoleCompletedState → Set
rolePostcondition before action after =
  rolePosition after ≡ roleActionTarget action

roleActionLabel : RoleCompletedAction → String
roleActionLabel roleAlphaBeta = "alpha->beta"
roleActionLabel roleBetaGamma = "beta->gamma"
roleActionLabel roleGammaDelta = "gamma->delta"
roleActionLabel roleBetaEpsilon = "beta->epsilon"
roleActionLabel roleDeltaTerminal = "delta->terminal-role[xi|zeta]"
roleActionLabel roleEpsilonTerminal = "epsilon->terminal-role[xi|zeta]"

roleCompletedActionSystem :
  Dependency.DependentActionSystem RoleCompletedState RoleCompletedAction
roleCompletedActionSystem = record
  { Precondition = rolePrecondition
  ; Postcondition = rolePostcondition
  ; actionLabel = roleActionLabel
  }

------------------------------------------------------------------------
-- Concrete admissible steps and complete role-level routes.
------------------------------------------------------------------------

alphaBetaRoleAdmissible :
  Dependency.AdmissibleAction roleCompletedActionSystem alphaRoleState roleAlphaBeta
alphaBetaRoleAdmissible = record
  { precondition = refl
  ; after = betaRoleState
  ; postcondition = refl
  ; dependencyReceipt = "paid aligned edge alpha->beta"
  }

betaGammaRoleAdmissible :
  Dependency.AdmissibleAction roleCompletedActionSystem betaRoleState roleBetaGamma
betaGammaRoleAdmissible = record
  { precondition = refl
  ; after = gammaRoleState
  ; postcondition = refl
  ; dependencyReceipt = "paid aligned edge beta->gamma"
  }

gammaDeltaRoleAdmissible :
  Dependency.AdmissibleAction roleCompletedActionSystem gammaRoleState roleGammaDelta
gammaDeltaRoleAdmissible = record
  { precondition = refl
  ; after = deltaRoleState
  ; postcondition = refl
  ; dependencyReceipt = "paid aligned edge gamma->delta"
  }

betaEpsilonRoleAdmissible :
  Dependency.AdmissibleAction roleCompletedActionSystem betaRoleState roleBetaEpsilon
betaEpsilonRoleAdmissible = record
  { precondition = refl
  ; after = epsilonRoleState
  ; postcondition = refl
  ; dependencyReceipt = "paid aligned edge beta->epsilon"
  }

deltaTerminalRoleAdmissible :
  Dependency.AdmissibleAction roleCompletedActionSystem deltaRoleState roleDeltaTerminal
deltaTerminalRoleAdmissible = record
  { precondition = refl
  ; after = canonicalTerminalRoleState
  ; postcondition = refl
  ; dependencyReceipt = "equation edge delta->xi plus source-internal terminal-role bridge to prose/Figure zeta; no xi=zeta equality asserted"
  }

epsilonTerminalRoleAdmissible :
  Dependency.AdmissibleAction roleCompletedActionSystem epsilonRoleState roleEpsilonTerminal
epsilonTerminalRoleAdmissible = record
  { precondition = refl
  ; after = canonicalTerminalRoleState
  ; postcondition = refl
  ; dependencyReceipt = "equation edge epsilon->xi plus source-internal terminal-role bridge to prose/Figure zeta; no xi=zeta equality asserted"
  }

primaryRoleCompletedRouteExecutes :
  Reach.Executes roleCompletedActionSystem
    (roleAlphaBeta ∷ roleBetaGamma ∷ roleGammaDelta ∷ roleDeltaTerminal ∷ [])
    alphaRoleState
    canonicalTerminalRoleState
primaryRoleCompletedRouteExecutes =
  Reach.executesCons alphaBetaRoleAdmissible
    (Reach.executesCons betaGammaRoleAdmissible
      (Reach.executesCons gammaDeltaRoleAdmissible
        (Reach.executesCons deltaTerminalRoleAdmissible Reach.executesNil)))

alternativeRoleCompletedRouteExecutes :
  Reach.Executes roleCompletedActionSystem
    (roleAlphaBeta ∷ roleBetaEpsilon ∷ roleEpsilonTerminal ∷ [])
    alphaRoleState
    canonicalTerminalRoleState
alternativeRoleCompletedRouteExecutes =
  Reach.executesCons alphaBetaRoleAdmissible
    (Reach.executesCons betaEpsilonRoleAdmissible
      (Reach.executesCons epsilonTerminalRoleAdmissible Reach.executesNil))

------------------------------------------------------------------------
-- Attribution donors.
------------------------------------------------------------------------

terminalNotationSourceDonor : Terminal.TerminalNotationSourceCoordinate
terminalNotationSourceDonor = Terminal.liLiuJi2015TerminalNotationSource

partialAlignmentSourceDonor : Align.PartialAlignmentSourceCoordinate
partialAlignmentSourceDonor = Align.liLiuJi2015PartialAlignmentSource

weightedGraphSourceDonor : Graph.WeightedGraphSourceCoordinate
weightedGraphSourceDonor = Graph.liLiuJi2015WeightedGraphSource

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKTerminalRoleCompletedDynamicsBoundary : Set where
  constructor adk-terminal-role-completed-dynamics-boundary
  field
    primaryRouteReachesTaggedTerminalRole : Bool
    alternativeRouteReachesTaggedTerminalRole : Bool
    terminalRoleRetainsFigureClosedRegion : Bool
    terminalRolePreservesEquationAndFigureNotationDistinction : Bool
    equationXiDefinitionallyEqualsFigureZeta : Bool
    equationXiAssignedPerStateDLn : Bool
    roleCompletionCreatesNumericPerEdgeRates : Bool
    roleCompletionEqualsExperimentalKineticMechanism : Bool
    terminalRoleMeansCompleteThreeCvState : Bool
    sourceOwnsDashiRoleCompletionConstruction : Bool

canonicalAdKTerminalRoleCompletedDynamicsBoundary :
  AdKTerminalRoleCompletedDynamicsBoundary
canonicalAdKTerminalRoleCompletedDynamicsBoundary =
  adk-terminal-role-completed-dynamics-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
