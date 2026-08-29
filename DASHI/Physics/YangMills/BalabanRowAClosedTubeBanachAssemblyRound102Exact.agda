{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRowAClosedTubeBanachAssemblyRound102Exact where

------------------------------------------------------------------------
-- ROUND102 A: INVARIANT BETA TUBE + q<1 -> SHOOTING FIXED POINT
--
-- Two-sided beta bounds already make the shooting interval invariant.  The
-- response-kernel lane supplies the remaining q<1 contraction estimate.  The
-- only theorem between those facts and a fixed point is the standard Banach
-- contraction theorem on a closed real interval.
--
-- This module keeps that theorem as a standard-analysis interface and proves the
-- source-specific assembly: once a fixed point is returned, it is converted to
-- `LiteralFiniteCutoffShootingFixedPoint`, whose terminal inverse-square
-- coordinate is exactly the selected renormalised target.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _-ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRowAShootingTubeFromBetaBoundsRound102Exact as Tube
import DASHI.Physics.YangMills.BalabanRowAShootingFixedPointTerminalExactRound102 as Terminal
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget as Budget

record ClosedTubeContractionData (Point : Set) : Set₁ where
  field
    tube : Tube.ShootingTubeBounds Point

    -- Exact contraction predicate in the caller's real metric.  The existing
    -- q<1 sensitivity lane instantiates this; no metric structure is duplicated
    -- here merely to restate Banach's theorem.
    Contraction : Set
    contraction : Contraction

open ClosedTubeContractionData public

record ClosedTubeBanachPrinciple : Set₁ where
  field
    fixedPoint :
      ∀ {Point}
        (dataSet : ClosedTubeContractionData Point) →
      Σ Point (λ point →
        Tube.renormalisationMap (tube dataSet) point ≡ point)

open ClosedTubeBanachPrinciple public

record LiteralCMP109ClosedTubeShooting (K : Nat) : Set₁ where
  field
    Point : Set
    contractionData : ClosedTubeContractionData Point

    dynamicsAt : Point → BetaLaw.BalabanCutoffCouplingDynamics K

    initialCoordinateExact : ∀ point →
      Trajectory.inverseSquaredCoupling
          (BetaLaw.step (dynamicsAt point)) 0
      ≡ Tube.coordinate (tube contractionData) point

    cumulativeIsLiteralBetaPrefix : ∀ point →
      Tube.cumulativeBeta (tube contractionData) point
      ≡ Budget.betaPrefixSum (BetaLaw.step (dynamicsAt point)) K

    arithmetic : Budget.InverseSquareBudgetArithmetic
    addThenSubtractRight : ∀ a b →
      (a DASHI.Foundations.RealAnalysisAxioms.+ℝ b) -ℝ b ≡ a

open LiteralCMP109ClosedTubeShooting public

shootingFixedPoint :
  (banach : ClosedTubeBanachPrinciple) →
  ∀ {K} (dataSet : LiteralCMP109ClosedTubeShooting K) →
  Σ (Point dataSet) (λ point →
    Tube.renormalisationMap
      (tube (contractionData dataSet)) point ≡ point)
shootingFixedPoint banach dataSet =
  fixedPoint banach (contractionData dataSet)

asLiteralFiniteCutoffFixedPoint :
  (banach : ClosedTubeBanachPrinciple) →
  ∀ {K} (dataSet : LiteralCMP109ClosedTubeShooting K) →
  Terminal.LiteralFiniteCutoffShootingFixedPoint K
asLiteralFiniteCutoffFixedPoint banach {K} dataSet =
  let
    selected = shootingFixedPoint banach dataSet
    point = proj₁ selected
    fixed = proj₂ selected
    sourceTube = tube (contractionData dataSet)
    prefix = Budget.betaPrefixSum (BetaLaw.step (dynamicsAt dataSet point)) K

    fixedCoordinate :
      Tube.coordinate sourceTube point
      ≡ Tube.coordinate sourceTube (Tube.renormalisationMap sourceTube point)
    fixedCoordinate = sym (cong (Tube.coordinate sourceTube) fixed)

    mapEquation = Tube.mapFormula sourceTube point
    cumulativeExact = cumulativeIsLiteralBetaPrefix dataSet point

    shootingEquation :
      Tube.coordinate sourceTube point
      ≡ Tube.renormalisedInverseSquare sourceTube
          DASHI.Foundations.RealAnalysisAxioms.+ℝ prefix
    shootingEquation =
      trans fixedCoordinate
        (trans mapEquation
          (cong
            (Tube.renormalisedInverseSquare sourceTube
              DASHI.Foundations.RealAnalysisAxioms.+ℝ_)
            cumulativeExact))
  in
  record
    { Terminal.LiteralFiniteCutoffShootingFixedPoint.dynamics = dynamicsAt dataSet point
    ; Terminal.LiteralFiniteCutoffShootingFixedPoint.renormalisedInverseSquare =
        Tube.renormalisedInverseSquare sourceTube
    ; Terminal.LiteralFiniteCutoffShootingFixedPoint.bareInverseSquare =
        Tube.coordinate sourceTube point
    ; Terminal.LiteralFiniteCutoffShootingFixedPoint.initialCoordinateExact =
        initialCoordinateExact dataSet point
    ; Terminal.LiteralFiniteCutoffShootingFixedPoint.shootingFixedPointEquation =
        shootingEquation
    ; Terminal.LiteralFiniteCutoffShootingFixedPoint.arithmetic = arithmetic dataSet
    ; Terminal.LiteralFiniteCutoffShootingFixedPoint.addThenSubtractRight =
        addThenSubtractRight dataSet
    }

closedTubeBanachAssemblyLevel : ProofLevel
closedTubeBanachAssemblyLevel = machineChecked

closedRealIntervalBanachPrincipleLevel : ProofLevel
closedRealIntervalBanachPrincipleLevel = standardImported

-- Physical A tuning input remaining after this assembly: instantiate the
-- contraction predicate with the SAME CMP109 history map.  Two-sided beta bounds
-- already supply tube invariance and the terminal target is exact after Banach.
literalCMP109ClosedTubeContractionInstantiationLevel : ProofLevel
literalCMP109ClosedTubeContractionInstantiationLevel = conditional
