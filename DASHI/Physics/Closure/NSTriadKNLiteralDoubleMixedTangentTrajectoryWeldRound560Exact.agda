module DASHI.Physics.Closure.NSTriadKNLiteralDoubleMixedTangentTrajectoryWeldRound560Exact where

------------------------------------------------------------------------
-- ROUND560 / R408/R427 LIVE DOUBLE-MIXED DERIVATIVE -> LITERAL R388 TANGENT
--
-- R427 differentiates the literal plus-minus cell using the literal R30
-- coefficient.  R382/R388 store the same cell tangent through the damped
-- coefficient.  R380 already proves those two modal coefficients equal
-- pointwise.  Since R292.cellTangent reads only p and q, two pointwise rewrites
-- close the same-object tangent seam without function extensionality.
--
-- R425 then lifts tau and swap(tau) to the actual derivative of the literal
-- double-mixed cell.  Thus the remaining R551 trajectory problem is not a
-- double-mixed product rule: it is the fixed R290 resolvent-weight / finite
-- self-pair family weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralMixedCellGramPairClosedRound382Exact as R382
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388
import DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact as R387
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNLiteralTrajectoryMixedCellDerivativeRound427Exact as R427

F : C3.RealField _
F = Rational.rationalRealField

module LiteralDoubleMixedTrajectory
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (projectedCross : R426.ProjectedCrossDerivativeCalculus Time DerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time DerivativeOf) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Cell = R427.LiteralCellDynamics
    Time initialTime integrateTo DerivativeOf projectedCross

  storedMixedTangentAt :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    Physical.PhysicalTriadIncidence →
    Time → C3.Complex3 F
  storedMixedTangentAt D S cutoff tau time =
    let
      module Stored = R382.ClosedLiteralPair
        (Live.physicalSystemAt (Live.support D) cutoff time) S
    in Stored.mixedCellTangent tau

  liveMixedTangentIsStored560 :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (tau : Physical.PhysicalTriadIncidence) →
    (time : Time) →
    Cell.literalMixedCellTangentCurve D S cutoff tau time
    ≡ storedMixedTangentAt D S cutoff tau time
  liveMixedTangentIsStored560 D S cutoff tau time =
    let
      module Stored = R382.ClosedLiteralPair
        (Live.physicalSystemAt (Live.support D) cutoff time) S
    in
    cong₂ C3.complex3Add
      (cong
        (λ selected →
          Cross.complex3Cross
            (Helical.helicalProjectorPlus
              (Live.Base.E (Live.stateTrajectory (Live.support D)))
              (Live.Base.I (Live.stateTrajectory (Live.support D))) S
              (Physical.p tau) selected)
            (Helical.helicalProjectorMinus
              (Live.Base.E (Live.stateTrajectory (Live.support D)))
              (Live.Base.I (Live.stateTrajectory (Live.support D))) S
              (Physical.q tau)
              (Stored.velocity (Physical.q tau))))
        (Stored.literalCoefficientIsDamped (Physical.p tau)))
      (cong
        (λ selected →
          Cross.complex3Cross
            (Helical.helicalProjectorPlus
              (Live.Base.E (Live.stateTrajectory (Live.support D)))
              (Live.Base.I (Live.stateTrajectory (Live.support D))) S
              (Physical.p tau)
              (Stored.velocity (Physical.p tau)))
            (Helical.helicalProjectorMinus
              (Live.Base.E (Live.stateTrajectory (Live.support D)))
              (Live.Base.I (Live.stateTrajectory (Live.support D))) S
              (Physical.q tau) selected))
        (Stored.literalCoefficientIsDamped (Physical.q tau)))

  storedDoubleTangentAt :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    Physical.PhysicalTriadIncidence →
    Time → C3.Complex3 F
  storedDoubleTangentAt D S cutoff tau time =
    let
      module Stored = R388.PhysicalDoubleMixed
        (Live.physicalSystemAt (Live.support D) cutoff time) S
    in Stored.doubleTangent tau

  doubledLiveTangentsAreStoredDouble560 :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (tau : Physical.PhysicalTriadIncidence) →
    (time : Time) →
    C3.complex3Add
      (R387.doublePlus
        (Cell.literalMixedCellTangentCurve D S cutoff tau time))
      (R387.doublePlus
        (Cell.literalMixedCellTangentCurve D S cutoff
          (Symmetry.swapTriad tau) time))
    ≡ storedDoubleTangentAt D S cutoff tau time
  doubledLiveTangentsAreStoredDouble560 D S cutoff tau time =
    cong₂ C3.complex3Add
      (cong R387.doublePlus
        (liveMixedTangentIsStored560 D S cutoff tau time))
      (cong R387.doublePlus
        (liveMixedTangentIsStored560
          D S cutoff (Symmetry.swapTriad tau) time))

  actualDoubleMixedDerivativeIsStoredR388Tangent560 :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (tau : Physical.PhysicalTriadIncidence) →
    let
      module Double = R425.DoubleMixedDerivative
        Time DerivativeOf vectorAlgebra S (Cell.liveVelocity D cutoff)
    in
    DerivativeOf
      (Double.doubleMixedCurve tau)
      (storedDoubleTangentAt D S cutoff tau)
  actualDoubleMixedDerivativeIsStoredR388Tangent560 D S cutoff tau =
    let
      module Double = R425.DoubleMixedDerivative
        Time DerivativeOf vectorAlgebra S (Cell.liveVelocity D cutoff)
      tangent = Cell.literalMixedCellTangentCurve D S cutoff tau
      tangentSwap = Cell.literalMixedCellTangentCurve
        D S cutoff (Symmetry.swapTriad tau)
    in
    Double.plusMinusDerivativesBuildDoubleMixedDerivative
      tau tangent tangentSwap (storedDoubleTangentAt D S cutoff tau)
      (Cell.round408BuildsActualMixedCellDerivative D S cutoff tau)
      (Cell.round408BuildsActualMixedCellDerivative
        D S cutoff (Symmetry.swapTriad tau))
      (doubledLiveTangentsAreStoredDouble560 D S cutoff tau)

round560LiteralR30ToStoredR382MixedTangentWeldClosed : Bool
round560LiteralR30ToStoredR382MixedTangentWeldClosed = true

round560ActualDoubleMixedDerivativeUsesR425R427 : Bool
round560ActualDoubleMixedDerivativeUsesR425R427 = true

round560ActualDoubleMixedDerivativeIsStoredR388Tangent : Bool
round560ActualDoubleMixedDerivativeIsStoredR388Tangent = true

round560FunctionExtensionalityUsed : Bool
round560FunctionExtensionalityUsed = false

round560FixedResolventWeightStillOpen : Bool
round560FixedResolventWeightStillOpen = true

round560FiniteSelfPairFamilyStillOpen : Bool
round560FiniteSelfPairFamilyStillOpen = true

round560ClayPromotion : Bool
round560ClayPromotion = false

round560ActualDoubleMixedDerivativeIsStoredR388TangentIsTrue :
  round560ActualDoubleMixedDerivativeIsStoredR388Tangent ≡ true
round560ActualDoubleMixedDerivativeIsStoredR388TangentIsTrue = refl

round560FunctionExtensionalityUsedIsFalse :
  round560FunctionExtensionalityUsed ≡ false
round560FunctionExtensionalityUsedIsFalse = refl

round560ClayPromotionIsFalse : round560ClayPromotion ≡ false
round560ClayPromotionIsFalse = refl
