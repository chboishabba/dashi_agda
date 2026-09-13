module DASHI.Physics.Closure.NSTriadKNLiteralLiveSelfPairDerivativeRound561Exact where

------------------------------------------------------------------------
-- ROUND561 / R408 LIVE TRAJECTORY -> ONE LITERAL R559 SELF-PAIR DERIVATIVE
--
-- R559 reduced the self-flux temporal seam to a finite family of R418
-- same-pair derivative data. R560 proved that the self-pair R290 resolvent
-- weight is time-fixed on the actual R240 trajectory. This owner closes the
-- remaining ONE-PAIR construction on the stronger literal R408 trajectory.
--
-- The chain is entirely existing machinery:
--
--   R408 modal velocity derivative = literal Round30 RHS
--     -> R427 actual plus-minus mixed-cell derivative
--     -> R425 actual double-mixed derivative
--     -> R417 R291 self-pair curve
--     -> R560 fixed-resolvent R290 curve
--     -> R418 SAME-pair derivative datum.
--
-- No new derivative semantics, FTC, integration theorem, or NS estimate is
-- introduced. The only calculus inputs are the already-separated ordinary
-- projected-cross derivative rule and vector derivative algebra used by
-- R425-R427.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR291R290SamePairDerivativeRound418Exact as R418
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNLiteralTrajectoryMixedCellDerivativeRound427Exact as R427
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNLiveSelfPairFixedResolventRound560Exact as R560

F : C3.RealField _
F = Rational.rationalRealField

module LiteralSelfPairDerivative
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (crossCalculus : R426.ProjectedCrossDerivativeCalculus Time DerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time DerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo DerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo DerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo DerivativeOf D))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (alpha : Physical.PhysicalTriadIncidence)
    (outputExact : Physical.k alpha ≡ output) where

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Cell = R427.LiteralCellDynamics
    Time initialTime integrateTo DerivativeOf crossCalculus

  T : R240.PhysicalNSDynamics.PhysicalNSGalerkinTrajectory
    Time initialTime integrateTo DerivativeOf
  T = Literal.literalPhysicalTrajectory D

  S = Literal.Base.S (Literal.stateTrajectory (Literal.support D))

  module Double = R425.DoubleMixedDerivative
    Time DerivativeOf vectorAlgebra S (Cell.liveVelocity D cutoff)

  module Fixed = R560.LiveSelfPair
    Time initialTime integrateTo DerivativeOf
    T R cutoff output outputNonzero alpha outputExact

  alphaTangent : Time → C3.Complex3 F
  alphaTangent = Cell.literalMixedCellTangentCurve D S cutoff alpha

  swapTangent : Time → C3.Complex3 F
  swapTangent =
    Cell.literalMixedCellTangentCurve D S cutoff (Symmetry.swapTriad alpha)

  alphaMixedDerivative :
    DerivativeOf (Double.plusMinusCurve alpha) alphaTangent
  alphaMixedDerivative =
    Cell.round408BuildsActualMixedCellDerivative D S cutoff alpha

  swapMixedDerivative :
    DerivativeOf
      (Double.plusMinusCurve (Symmetry.swapTriad alpha)) swapTangent
  swapMixedDerivative =
    Cell.round408BuildsActualMixedCellDerivative
      D S cutoff (Symmetry.swapTriad alpha)

  rawDoubleDerivative :
    DerivativeOf
      (Double.doubleMixedCurve alpha)
      (λ time → R417.tangentACurve
        (record { R417.pairAt = Fixed.physicalPairAt }) time)
  rawDoubleDerivative =
    Double.plusMinusDerivativesBuildDoubleMixedDerivative
      alpha alphaTangent swapTangent
      (λ time → R417.tangentACurve
        (record { R417.pairAt = Fixed.physicalPairAt }) time)
      alphaMixedDerivative swapMixedDerivative
      (λ time → refl)

  r291Curve : R417.DampedCellPairCurve Time
  r291Curve = record
    { R417.pairAt = Fixed.physicalPairAt
    }

  doubleMixedDerivative :
    DerivativeOf
      (R417.cellACurve r291Curve)
      (R417.tangentACurve r291Curve)
  doubleMixedDerivative =
    R425.transportDerivative vectorAlgebra
      (λ time → refl)
      (λ time → refl)
      rawDoubleDerivative

  samePairCurve : R418.SameR291R290PairCurve Time
  samePairCurve = record
    { R418.r291Curve = r291Curve
    ; R418.r290Curve = Fixed.fixedResolventCurve
    ; R418.sameGram = λ time → refl
    ; R418.sameGramTangent = λ time → refl
    }

  literalSelfPairDerivativeData :
    R422.PairCurveDerivativeData Time DerivativeOf
  literalSelfPairDerivativeData = record
    { R422.pairCurve = samePairCurve
    ; R422.cellADerivative = doubleMixedDerivative
    ; R422.cellBDerivative = doubleMixedDerivative
    }

round561LiteralR408SelfPairDerivativeConstructed : Bool
round561LiteralR408SelfPairDerivativeConstructed = true

round561UsesR560FixedResolventCurve : Bool
round561UsesR560FixedResolventCurve = true

round561CallerSelectedDoubleMixedTangent : Bool
round561CallerSelectedDoubleMixedTangent = false

round561IntroducesNewDerivativeInterface : Bool
round561IntroducesNewDerivativeInterface = false

round561IntroducesNewNavierStokesEstimate : Bool
round561IntroducesNewNavierStokesEstimate = false

round561FiniteSelfPairEnumerationClosed : Bool
round561FiniteSelfPairEnumerationClosed = false

round561ClayPromotion : Bool
round561ClayPromotion = false

round561LiteralR408SelfPairDerivativeConstructedIsTrue :
  round561LiteralR408SelfPairDerivativeConstructed ≡ true
round561LiteralR408SelfPairDerivativeConstructedIsTrue = refl

round561CallerSelectedDoubleMixedTangentIsFalse :
  round561CallerSelectedDoubleMixedTangent ≡ false
round561CallerSelectedDoubleMixedTangentIsFalse = refl

round561ClayPromotionIsFalse : round561ClayPromotion ≡ false
round561ClayPromotionIsFalse = refl
