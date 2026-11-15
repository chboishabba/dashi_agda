{-# OPTIONS --safe #-}
module DASHI.Interop.CombinatorialMaxCutPhysicsAlignmentExact where

------------------------------------------------------------------------
-- COMBINATORIAL MAX CUT / PHYSICS ALIGNMENT
--
-- Source attribution:
-- Michel X. Goemans and David P. Williamson,
-- "Improved Approximation Algorithms for Maximum Cut and Satisfiability
-- Problems Using Semidefinite Programming", JACM 42(6), 1995.
--
-- Fan R. K. Chung,
-- "Spectral Graph Theory", CBMS 92, AMS, 1997.
--
-- This owner separates a literal finite graph cut from DASHI proof-search
-- "max-cut" terminology.  It also blocks promotion from graph structure to
-- Yang--Mills or Navier--Stokes same-object claims.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Product using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.BalabanP33GaugeModeRGResidualCrossPollinationExact as YM
import DASHI.Physics.Closure.ProjectionNonlocalityLeakagePrincipleBoundary as Projection
import DASHI.Physics.Closure.NSTriadKNNestedInnerSwapCommutatorRound310Exact as NS310
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as NS567

data CutSide : Set where
  leftSide : CutSide
  rightSide : CutSide

data OppositeSides : CutSide → CutSide → Set where
  leftRight : OppositeSides leftSide rightSide
  rightLeft : OppositeSides rightSide leftSide

record FiniteCutGraph (Vertex Edge : Set) : Set where
  constructor finite-cut-graph
  field
    source : Edge → Vertex
    target : Edge → Vertex
    side : Vertex → CutSide

open FiniteCutGraph public

CrossingEdge :
  ∀ {Vertex Edge : Set} →
  FiniteCutGraph Vertex Edge →
  Edge →
  Set
CrossingEdge graph edge =
  OppositeSides
    (side graph (source graph edge))
    (side graph (target graph edge))

record BoundaryVertex
    {Vertex Edge : Set}
    (graph : FiniteCutGraph Vertex Edge)
    (vertex : Vertex) : Set where
  constructor boundary-vertex
  field
    edge : Edge
    incident :
      source graph edge ≡ vertex
      ⊎
      target graph edge ≡ vertex
    crossing : CrossingEdge graph edge

open BoundaryVertex public

record DiscreteLaplacianCutWitness
    (Vertex Scalar : Set) : Set₁ where
  constructor discrete-laplacian-cut-witness
  field
    cutSignal : Vertex → Scalar
    laplacian : (Vertex → Scalar) → Vertex → Scalar
    quadraticForm : (Vertex → Scalar) → Scalar
    boundaryWeight : Scalar
    cutQuadraticEqualsBoundaryWeight :
      quadraticForm cutSignal ≡ boundaryWeight

open DiscreteLaplacianCutWitness public

record GoemansWilliamsonSDPReceipt
    (Vertex Vector Score : Set) : Set₁ where
  constructor goemans-williamson-sdp-receipt
  field
    relaxationVector : Vertex → Vector
    UnitVector : Vector → Set
    relaxationVectorsAreUnit :
      (vertex : Vertex) →
      UnitVector (relaxationVector vertex)
    _≤score_ : Score → Score → Set
    sdpObjective : Score
    roundedCutWeight : Score
    roundedCutBelowRelaxation :
      _≤score_ roundedCutWeight sdpObjective
    randomHyperplaneRoundingRepresented : Bool
    randomHyperplaneRoundingRepresentedIsTrue :
      randomHyperplaneRoundingRepresented ≡ true

open GoemansWilliamsonSDPReceipt public

record PhysicsCutAdapter
    {Vertex Edge : Set}
    (graph : FiniteCutGraph Vertex Edge)
    (PhysicsObject : Set) : Set₁ where
  constructor physics-cut-adapter
  field
    vertexObject : Vertex → PhysicsObject
    boundaryObject : Edge → PhysicsObject
    SameObjectBoundary : Edge → PhysicsObject → Set
    crossingEdgeRequiresSameObjectWitness :
      (edge : Edge) →
      CrossingEdge graph edge →
      SameObjectBoundary edge (boundaryObject edge)

open PhysicsCutAdapter public

------------------------------------------------------------------------
-- Existing physics anchors.
------------------------------------------------------------------------

ymEffectiveResidualAnchor : ℚ → ℚ → ℚ
ymEffectiveResidualAnchor =
  YM.effectiveResidual

ymGaugeHodgeCommutatorTargetIsRecorded :
  Projection.YMBTHodgeGaugeCommutatorLeakageTargetRecorded ≡ true
ymGaugeHodgeCommutatorTargetIsRecorded =
  Projection.projectionNonlocalityRecordsYMBTHodgeGaugeTarget

ymGaugeHodgeCompatibilityIsStillOpen :
  Projection.BTGaugeHodgeCompatibilityDefect ≡ false
ymGaugeHodgeCompatibilityIsStillOpen =
  Projection.projectionNonlocalityKeepsBTGaugeHodgeCompatibilityDefectFalse

nsInnerSwapCommutatorPairingIsClosed :
  NS310.round310InnerFixedOutputSwapPairingClosed ≡ true
nsInnerSwapCommutatorPairingIsClosed = refl

nsFactoredFullIsFourForcingCommutatorSquare :
  NS567.round567FactoredFullIsFourForcingSquare ≡ true
nsFactoredFullIsFourForcingCommutatorSquare =
  NS567.round567FactoredFullIsFourForcingSquareIsTrue

nsClayPromotionRemainsFalse :
  NS567.round567ClayPromotion ≡ false
nsClayPromotionRemainsFalse =
  NS567.round567ClayPromotionIsFalse

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

record CombinatorialMaxCutPhysicsBoundary : Set where
  constructor combinatorial-max-cut-physics-boundary
  field
    literalGraphCutIsDistinctFromProofSearchMaxCut : Bool
    literalGraphCutIsDistinctFromProofSearchMaxCutIsTrue :
      literalGraphCutIsDistinctFromProofSearchMaxCut ≡ true
    laplacianWitnessRequiresExplicitCarrier : Bool
    laplacianWitnessRequiresExplicitCarrierIsTrue :
      laplacianWitnessRequiresExplicitCarrier ≡ true
    sdpReceiptCreatesPhysicsTheorem : Bool
    sdpReceiptCreatesPhysicsTheoremIsFalse :
      sdpReceiptCreatesPhysicsTheorem ≡ false
    graphCutCreatesYangMillsEquation : Bool
    graphCutCreatesYangMillsEquationIsFalse :
      graphCutCreatesYangMillsEquation ≡ false
    graphCutCreatesNavierStokesEstimate : Bool
    graphCutCreatesNavierStokesEstimateIsFalse :
      graphCutCreatesNavierStokesEstimate ≡ false
    physicsAdapterRequiresSameObjectWitness : Bool
    physicsAdapterRequiresSameObjectWitnessIsTrue :
      physicsAdapterRequiresSameObjectWitness ≡ true
    goemansWilliamsonApproximationRatioProvedHere : Bool
    goemansWilliamsonApproximationRatioProvedHereIsFalse :
      goemansWilliamsonApproximationRatioProvedHere ≡ false

open CombinatorialMaxCutPhysicsBoundary public

canonicalCombinatorialMaxCutPhysicsBoundary :
  CombinatorialMaxCutPhysicsBoundary
canonicalCombinatorialMaxCutPhysicsBoundary =
  combinatorial-max-cut-physics-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl

maxCutDoesNotPromoteYangMills :
  graphCutCreatesYangMillsEquation
    canonicalCombinatorialMaxCutPhysicsBoundary
  ≡ false
maxCutDoesNotPromoteYangMills = refl

maxCutDoesNotPromoteNavierStokes :
  graphCutCreatesNavierStokesEstimate
    canonicalCombinatorialMaxCutPhysicsBoundary
  ≡ false
maxCutDoesNotPromoteNavierStokes = refl

sdpReceiptDoesNotCreatePhysicsTheorem :
  sdpReceiptCreatesPhysicsTheorem
    canonicalCombinatorialMaxCutPhysicsBoundary
  ≡ false
sdpReceiptDoesNotCreatePhysicsTheorem = refl
