module DASHI.Physics.Closure.NSTriadKNLiteralLiveOffDiagonalPairDerivativeMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 Q4+E / ONE LITERAL LIVE OFF-DIAGONAL R290 PAIR DERIVATIVE
--
-- Generalizes the R561 self-pair construction to alpha,beta on the same
-- nonzero output fibre.  The alpha and beta double-mixed cells are differentiated
-- independently through the existing R427 -> R425 path, then welded to the
-- fixed-resolvent R290 curve from the off-diagonal fixed-rate owner.
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
import DASHI.Physics.Closure.NSTriadKNLiveOffDiagonalPairFixedResolventMaxCutExact as FixedOwner

F : C3.RealField _
F = Rational.rationalRealField

module LiteralOffDiagonalPairDerivative
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
    (alpha beta : Physical.PhysicalTriadIncidence)
    (alphaOutput : Physical.k alpha ≡ output)
    (betaOutput : Physical.k beta ≡ output) where

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

  module Fixed = FixedOwner.LivePair
    Time initialTime integrateTo DerivativeOf
    T R cutoff output outputNonzero
    alpha beta alphaOutput betaOutput

  alphaTangent : Time → C3.Complex3 F
  alphaTangent = Cell.literalMixedCellTangentCurve D S cutoff alpha

  alphaSwapTangent : Time → C3.Complex3 F
  alphaSwapTangent =
    Cell.literalMixedCellTangentCurve D S cutoff (Symmetry.swapTriad alpha)

  betaTangent : Time → C3.Complex3 F
  betaTangent = Cell.literalMixedCellTangentCurve D S cutoff beta

  betaSwapTangent : Time → C3.Complex3 F
  betaSwapTangent =
    Cell.literalMixedCellTangentCurve D S cutoff (Symmetry.swapTriad beta)

  alphaMixedDerivative :
    DerivativeOf (Double.plusMinusCurve alpha) alphaTangent
  alphaMixedDerivative =
    Cell.round408BuildsActualMixedCellDerivative D S cutoff alpha

  alphaSwapMixedDerivative :
    DerivativeOf
      (Double.plusMinusCurve (Symmetry.swapTriad alpha)) alphaSwapTangent
  alphaSwapMixedDerivative =
    Cell.round408BuildsActualMixedCellDerivative
      D S cutoff (Symmetry.swapTriad alpha)

  betaMixedDerivative :
    DerivativeOf (Double.plusMinusCurve beta) betaTangent
  betaMixedDerivative =
    Cell.round408BuildsActualMixedCellDerivative D S cutoff beta

  betaSwapMixedDerivative :
    DerivativeOf
      (Double.plusMinusCurve (Symmetry.swapTriad beta)) betaSwapTangent
  betaSwapMixedDerivative =
    Cell.round408BuildsActualMixedCellDerivative
      D S cutoff (Symmetry.swapTriad beta)

  r291Curve : R417.DampedCellPairCurve Time
  r291Curve = record
    { R417.pairAt = Fixed.physicalPairAt
    }

  rawAlphaDoubleDerivative :
    DerivativeOf
      (Double.doubleMixedCurve alpha)
      (R417.tangentACurve r291Curve)
  rawAlphaDoubleDerivative =
    Double.plusMinusDerivativesBuildDoubleMixedDerivative
      alpha alphaTangent alphaSwapTangent
      (R417.tangentACurve r291Curve)
      alphaMixedDerivative alphaSwapMixedDerivative
      (λ time → refl)

  rawBetaDoubleDerivative :
    DerivativeOf
      (Double.doubleMixedCurve beta)
      (R417.tangentBCurve r291Curve)
  rawBetaDoubleDerivative =
    Double.plusMinusDerivativesBuildDoubleMixedDerivative
      beta betaTangent betaSwapTangent
      (R417.tangentBCurve r291Curve)
      betaMixedDerivative betaSwapMixedDerivative
      (λ time → refl)

  alphaDoubleDerivative :
    DerivativeOf
      (R417.cellACurve r291Curve)
      (R417.tangentACurve r291Curve)
  alphaDoubleDerivative =
    R425.transportDerivative vectorAlgebra
      (λ time → refl) (λ time → refl) rawAlphaDoubleDerivative

  betaDoubleDerivative :
    DerivativeOf
      (R417.cellBCurve r291Curve)
      (R417.tangentBCurve r291Curve)
  betaDoubleDerivative =
    R425.transportDerivative vectorAlgebra
      (λ time → refl) (λ time → refl) rawBetaDoubleDerivative

  samePairCurve : R418.SameR291R290PairCurve Time
  samePairCurve = record
    { R418.r291Curve = r291Curve
    ; R418.r290Curve = Fixed.fixedResolventCurve
    ; R418.sameGram = λ time → refl
    ; R418.sameGramTangent = λ time → refl
    }

  literalOffDiagonalPairDerivativeData :
    R422.PairCurveDerivativeData Time DerivativeOf
  literalOffDiagonalPairDerivativeData = record
    { R422.pairCurve = samePairCurve
    ; R422.cellADerivative = alphaDoubleDerivative
    ; R422.cellBDerivative = betaDoubleDerivative
    }

roundB7LiteralOffDiagonalPairDerivativeConstructed : Bool
roundB7LiteralOffDiagonalPairDerivativeConstructed = true

roundB7LiteralOffDiagonalPairDerivativeIntroducesEstimate : Bool
roundB7LiteralOffDiagonalPairDerivativeIntroducesEstimate = false

roundB7LiteralOffDiagonalPairDerivativeConstructedIsTrue :
  roundB7LiteralOffDiagonalPairDerivativeConstructed ≡ true
roundB7LiteralOffDiagonalPairDerivativeConstructedIsTrue = refl
