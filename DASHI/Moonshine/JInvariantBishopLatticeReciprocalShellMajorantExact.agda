module DASHI.Moonshine.JInvariantBishopLatticeReciprocalShellMajorantExact where

------------------------------------------------------------------------
-- COERCIVITY -> RECIPROCAL NORM-SQUARE SHELL MAJORANT
--
-- On the successor square shell of radius r=R+1, the previous owners give
--
--   r^2 <= m^2+n^2
--
-- and, for tau=x+iy in the Bishop upper half plane,
--
--   y^2(m^2+n^2) <= C_tau * normSq(m*tau+n),
--
-- where C_tau = 1+x^2+y^2.
--
-- Positive cross multiplication therefore yields the literal reciprocal bound
--
--   normSq((m*tau+n)^-1)
--     <= C_tau * (y^2 r^2)^-1.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Bool.Base using (T)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopPositiveCrossReciprocalUpperExact as Cross
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Moonshine.JInvariantBishopLatticeDenominatorCoercivityExact as Coercive
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as Kernel
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as Upper
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as Shell
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellRadiusExact as Radius
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Lattice

squarePositive :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.0ℝ (Norm.square x)
squarePositive positive =
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx*y
      (BishopP.0<x⇒posx positive)
      (BishopP.0<x⇒posx positive))

radiusPositive :
  (inner : Nat) →
  BishopReal._<_ BishopReal.0ℝ (Radius.radiusReal inner)
radiusPositive =
  NatPositive.natRealSuccessorStrictlyPositive

radiusSquarePositive :
  (inner : Nat) →
  BishopReal._<_ BishopReal.0ℝ (Radius.radiusSquare inner)
radiusSquarePositive inner =
  squarePositive (radiusPositive inner)

imagSquarePositive :
  (parameter : Upper.BishopUpperHalfPlanePoint) →
  BishopReal._<_ BishopReal.0ℝ
    (Norm.square
      (DASHI.Analysis.BishopComplexSeriesConvergenceExact.im
        (Upper.tau parameter)))
imagSquarePositive parameter =
  squarePositive (Upper.imaginaryPositive parameter)

weightedRadius :
  Upper.BishopUpperHalfPlanePoint →
  Nat →
  BishopReal.ℝ
weightedRadius parameter inner =
  BishopReal._*_
    (Norm.square
      (DASHI.Analysis.BishopComplexSeriesConvergenceExact.im
        (Upper.tau parameter)))
    (Radius.radiusSquare inner)

weightedRadiusPositive :
  (parameter : Upper.BishopUpperHalfPlanePoint) →
  (inner : Nat) →
  BishopReal._<_ BishopReal.0ℝ (weightedRadius parameter inner)
weightedRadiusPositive parameter inner =
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx*y
      (BishopP.0<x⇒posx (imagSquarePositive parameter))
      (BishopP.0<x⇒posx (radiusSquarePositive inner)))

shellCoerciveBound :
  (parameter : Upper.BishopUpperHalfPlanePoint) →
  (inner : Nat) →
  (point : Lattice.LatticePoint) →
  T (Shell.onSuccessorSquareShell? inner point) →
  BishopReal._≤_
    (weightedRadius parameter inner)
    (BishopReal._*_
      (Coercive.coercivityFactor (Upper.tau parameter))
      (Norm.normSqC
        (Kernel.latticeDenominator point (Upper.tau parameter))))
shellCoerciveBound parameter inner point shellProof =
  let
    tau = Upper.tau parameter
    y = DASHI.Analysis.BishopComplexSeriesConvergenceExact.im tau

    radiusBelow =
      Radius.successorSquareShellRadiusSquareLower
        inner point shellProof

    ySquareNN =
      BishopP.nonNegx⇒0≤x
        (SquareNN.bishopSquareNonnegative y)

    scaledRadiusBelow =
      BishopP.*-monoˡ-≤-nonNeg
        radiusBelow ySquareNN
  in
  BishopP.≤-trans
    scaledRadiusBelow
    (Coercive.latticeDenominatorCoercivity point tau)

reciprocalNormSquareShellUpper :
  (parameter : Upper.BishopUpperHalfPlanePoint) →
  (inner : Nat) →
  (index : Kernel.NonzeroLatticePoint) →
  T (Shell.onSuccessorSquareShell? inner (Kernel.point index)) →
  BishopReal._≤_
    (Norm.normSqC
      (Kernel.latticeReciprocal
        Upper.upperHalfPlaneDenominatorGeometry
        parameter index))
    (BishopReal._*_
      (Coercive.coercivityFactor (Upper.tau parameter))
      (Cross.positiveInverse
        (weightedRadiusPositive parameter inner)))
reciprocalNormSquareShellUpper parameter inner index shellProof =
  let
    point = Kernel.point index
    z = Kernel.latticeDenominator point (Upper.tau parameter)
    nz =
      Upper.upperHalfPlaneDenominatorNonzero parameter index
    dPositive = Reciprocal.normSquarePositive nz
    aPositive = weightedRadiusPositive parameter inner

    raw =
      Cross.positiveCrossReciprocalUpper
        aPositive
        dPositive
        (shellCoerciveBound
          parameter inner point shellProof)

    reciprocalNormLaw =
      Reciprocal.normSquareReciprocal z nz
  in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm reciprocalNormLaw)
    raw

record ReciprocalShellMajorantBoundary : Set where
  field
    shellCoercivityComposedExact : Agda.Builtin.Bool.Bool
    reciprocalNormSquareShellUpperExact : Agda.Builtin.Bool.Bool
    reciprocalPowerComponentMajorantsPaidHere : Agda.Builtin.Bool.Bool
    finiteShellFoldDominationPaidHere : Agda.Builtin.Bool.Bool

canonicalReciprocalShellMajorantBoundary :
  ReciprocalShellMajorantBoundary
canonicalReciprocalShellMajorantBoundary = record
  { shellCoercivityComposedExact = Agda.Builtin.Bool.true
  ; reciprocalNormSquareShellUpperExact = Agda.Builtin.Bool.true
  ; reciprocalPowerComponentMajorantsPaidHere = Agda.Builtin.Bool.false
  ; finiteShellFoldDominationPaidHere = Agda.Builtin.Bool.false
  }
