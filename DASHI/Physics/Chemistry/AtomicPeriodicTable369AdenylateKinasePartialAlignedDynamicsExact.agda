module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialAlignedDynamicsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reach
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialStateCoordinateAlignmentExact as Align

------------------------------------------------------------------------
-- PARTIALLY ALIGNED ADK DYNAMICS
--
-- State membership itself requires a paid graph-state <-> Figure-state
-- alignment.  This replaces the previous product separation for the part of the
-- Li-Liu-Ji route for which the source/owner actually pays named-state identity.
--
-- Because xi remains an equation-level target while Figure 5 uses zeta for the
-- closed crystal label, there is intentionally no aligned xi state.  The aligned
-- action system therefore admits only edges whose source and target both live in
-- the paid alignment fibre.  Partiality is the theorem, not an implementation
-- defect.
------------------------------------------------------------------------

AlignedStateAt : Graph.AdKLandscapeState → Set
AlignedStateAt graphState =
  Σ Align.FigureLandscapeStateLabel
    (λ label → Align.GraphStateAlignedToFigureLabel graphState label)

AlignedAdKState : Set
AlignedAdKState = Σ Graph.AdKLandscapeState AlignedStateAt

alphaAlignedState : AlignedAdKState
alphaAlignedState = Graph.alpha , (Align.alphaFigure , Align.alphaAligned)

betaAlignedState : AlignedAdKState
betaAlignedState = Graph.beta , (Align.betaFigure , Align.betaAligned)

gammaAlignedState : AlignedAdKState
gammaAlignedState = Graph.gamma , (Align.gammaFigure , Align.gammaAligned)

deltaAlignedState : AlignedAdKState
deltaAlignedState = Graph.delta , (Align.deltaFigure , Align.deltaAligned)

epsilonAlignedState : AlignedAdKState
epsilonAlignedState = Graph.epsilon , (Align.epsilonFigure , Align.epsilonAligned)

xiAlignedStateImpossible : AlignedStateAt Graph.xiEquationTarget → ⊥
xiAlignedStateImpossible = Align.xiHasNoPaidFigureAlignment

alignedFigureLabel : AlignedAdKState → Align.FigureLandscapeStateLabel
alignedFigureLabel state = proj₁ (proj₂ state)

alignedRegion : AlignedAdKState → Align.PartialThreeCvRegion
alignedRegion state = Align.alignedGraphRegion (proj₂ (proj₂ state))

------------------------------------------------------------------------
-- Only route edges with paid aligned endpoints are action constructors.
------------------------------------------------------------------------

data AlignedGraphAction : Set where
  alignedAlphaBeta : AlignedGraphAction
  alignedBetaGamma : AlignedGraphAction
  alignedGammaDelta : AlignedGraphAction
  alignedBetaEpsilon : AlignedGraphAction

alignedActionSource : AlignedGraphAction → Graph.AdKLandscapeState
alignedActionSource alignedAlphaBeta = Graph.alpha
alignedActionSource alignedBetaGamma = Graph.beta
alignedActionSource alignedGammaDelta = Graph.gamma
alignedActionSource alignedBetaEpsilon = Graph.beta

alignedActionTarget : AlignedGraphAction → Graph.AdKLandscapeState
alignedActionTarget alignedAlphaBeta = Graph.beta
alignedActionTarget alignedBetaGamma = Graph.gamma
alignedActionTarget alignedGammaDelta = Graph.delta
alignedActionTarget alignedBetaEpsilon = Graph.epsilon

alignedActionEdge : AlignedGraphAction → Graph.DirectedLandscapeEdge
alignedActionEdge alignedAlphaBeta = Graph.alphaBeta
alignedActionEdge alignedBetaGamma = Graph.betaGamma
alignedActionEdge alignedGammaDelta = Graph.gammaDelta
alignedActionEdge alignedBetaEpsilon = Graph.betaEpsilon

alignedPrecondition : AlignedAdKState → AlignedGraphAction → Set
alignedPrecondition before action = proj₁ before ≡ alignedActionSource action

alignedPostcondition :
  AlignedAdKState → AlignedGraphAction → AlignedAdKState → Set
alignedPostcondition before action after =
  proj₁ after ≡ alignedActionTarget action

alignedActionLabel : AlignedGraphAction → String
alignedActionLabel alignedAlphaBeta = "aligned alpha->beta"
alignedActionLabel alignedBetaGamma = "aligned beta->gamma"
alignedActionLabel alignedGammaDelta = "aligned gamma->delta"
alignedActionLabel alignedBetaEpsilon = "aligned beta->epsilon"

partialAlignedActionSystem :
  Dependency.DependentActionSystem AlignedAdKState AlignedGraphAction
partialAlignedActionSystem = record
  { Precondition = alignedPrecondition
  ; Postcondition = alignedPostcondition
  ; actionLabel = alignedActionLabel
  }

------------------------------------------------------------------------
-- Concrete source-paid aligned transitions.
------------------------------------------------------------------------

alphaBetaAlignedAdmissible :
  Dependency.AdmissibleAction
    partialAlignedActionSystem alphaAlignedState alignedAlphaBeta
alphaBetaAlignedAdmissible = record
  { precondition = refl
  ; after = betaAlignedState
  ; postcondition = refl
  ; dependencyReceipt = "alpha->beta retained only because both graph endpoints have paid Figure-state alignment"
  }

betaGammaAlignedAdmissible :
  Dependency.AdmissibleAction
    partialAlignedActionSystem betaAlignedState alignedBetaGamma
betaGammaAlignedAdmissible = record
  { precondition = refl
  ; after = gammaAlignedState
  ; postcondition = refl
  ; dependencyReceipt = "beta->gamma retained only because both graph endpoints have paid Figure-state alignment"
  }

gammaDeltaAlignedAdmissible :
  Dependency.AdmissibleAction
    partialAlignedActionSystem gammaAlignedState alignedGammaDelta
gammaDeltaAlignedAdmissible = record
  { precondition = refl
  ; after = deltaAlignedState
  ; postcondition = refl
  ; dependencyReceipt = "gamma->delta retained only because both graph endpoints have paid Figure-state alignment"
  }

betaEpsilonAlignedAdmissible :
  Dependency.AdmissibleAction
    partialAlignedActionSystem betaAlignedState alignedBetaEpsilon
betaEpsilonAlignedAdmissible = record
  { precondition = refl
  ; after = epsilonAlignedState
  ; postcondition = refl
  ; dependencyReceipt = "beta->epsilon retained only because both graph endpoints have paid Figure-state alignment"
  }

primaryAlignedPrefixExecutes :
  Reach.Executes partialAlignedActionSystem
    (alignedAlphaBeta ∷ alignedBetaGamma ∷ alignedGammaDelta ∷ [])
    alphaAlignedState
    deltaAlignedState
primaryAlignedPrefixExecutes =
  Reach.executesCons alphaBetaAlignedAdmissible
    (Reach.executesCons betaGammaAlignedAdmissible
      (Reach.executesCons gammaDeltaAlignedAdmissible Reach.executesNil))

alternativeAlignedPrefixExecutes :
  Reach.Executes partialAlignedActionSystem
    (alignedAlphaBeta ∷ alignedBetaEpsilon ∷ [])
    alphaAlignedState
    epsilonAlignedState
alternativeAlignedPrefixExecutes =
  Reach.executesCons alphaBetaAlignedAdmissible
    (Reach.executesCons betaEpsilonAlignedAdmissible Reach.executesNil)

------------------------------------------------------------------------
-- Coordinate-bearing observations now move with the source graph.
------------------------------------------------------------------------

alphaRegion : Align.PartialThreeCvRegion
alphaRegion = alignedRegion alphaAlignedState

betaRegion : Align.PartialThreeCvRegion
betaRegion = alignedRegion betaAlignedState

gammaRegion : Align.PartialThreeCvRegion
gammaRegion = alignedRegion gammaAlignedState

deltaRegion : Align.PartialThreeCvRegion
deltaRegion = alignedRegion deltaAlignedState

epsilonRegion : Align.PartialThreeCvRegion
epsilonRegion = alignedRegion epsilonAlignedState

------------------------------------------------------------------------
-- Attribution: this action layer is DASHI synthesis over source-paid topology
-- and source-paid partial coordinate/state labels.  It does not reassign source
-- authorship or turn computational route topology into experimental kinetics.
------------------------------------------------------------------------

alignmentSourceDonor : Align.PartialAlignmentSourceCoordinate
alignmentSourceDonor = Align.liLiuJi2015PartialAlignmentSource

weightedGraphSourceDonor : Graph.WeightedGraphSourceCoordinate
weightedGraphSourceDonor = Graph.liLiuJi2015WeightedGraphSource

record AdKPartialAlignedDynamicsBoundary : Set where
  constructor adk-partial-aligned-dynamics-boundary
  field
    dependentStateRequiresPaidGraphFigureAlignment : Bool
    primaryAlignedPrefixExecutable : Bool
    alternativeAlignedPrefixExecutable : Bool
    coordinateRegionMovesWithAlignedGraphState : Bool
    deltaXiAlignedTransitionAdmitted : Bool
    epsilonXiAlignedTransitionAdmitted : Bool
    xiZetaIdentityManufactured : Bool
    namedStateDLnValuesManufactured : Bool
    routeTopologyPromotedToExperimentalTransitionEvents : Bool
    partialDynamicsEqualsCompleteKineticModel : Bool
    sourceOwnsDashiDependentActionConstruction : Bool

canonicalAdKPartialAlignedDynamicsBoundary :
  AdKPartialAlignedDynamicsBoundary
canonicalAdKPartialAlignedDynamicsBoundary =
  adk-partial-aligned-dynamics-boundary
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
    false
