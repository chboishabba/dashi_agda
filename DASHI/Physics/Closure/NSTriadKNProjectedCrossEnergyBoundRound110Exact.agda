module DASHI.Physics.Closure.NSTriadKNProjectedCrossEnergyBoundRound110Exact where

------------------------------------------------------------------------
-- ROUND110 / PROJECTED CROSS ENERGY WELD
--
-- Compose the literal rational Leray contraction with the already-proved
-- complex Lagrange inequality:
--
--   ||P_k (u x v)||^2 <= ||u x v||^2 <= ||u||^2 ||v||^2.
--
-- This is the exact finite carrier needed by the self-phase energy payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeEnergyProductRound105Exact as Energy

F : C3.RealField _
F = Rational.rationalRealField

projectedCrossNormSquaredBelowProduct :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (k : Z3.FourierMode) →
  (u v : C3.Complex3 F) →
  Z3.NonZeroMode k →
  L2.complex3NormSquared
    (C3.lerayProject3 E I k (Cross.complex3Cross u v))
  ≤ L2.complex3NormSquared u * L2.complex3NormSquared v
projectedCrossNormSquaredBelowProduct E I O k u v nonzero =
  ℚP.≤-trans
    (Leray.rationalLerayNormSquaredContraction
      E I O k (Cross.complex3Cross u v) nonzero)
    (Energy.crossNormSquaredBelowProduct u v)

round110ProjectedCrossEnergyBoundClosed : Bool
round110ProjectedCrossEnergyBoundClosed = true

round110ProjectedCrossEnergyBoundClosedIsTrue :
  round110ProjectedCrossEnergyBoundClosed ≡ true
round110ProjectedCrossEnergyBoundClosedIsTrue = refl
