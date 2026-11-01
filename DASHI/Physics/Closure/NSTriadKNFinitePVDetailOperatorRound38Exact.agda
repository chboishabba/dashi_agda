module DASHI.Physics.Closure.NSTriadKNFinitePVDetailOperatorRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- DASHI CONTRIBUTION
--
-- Rephrase the finite principal-value identity as a genuine coarse/detail
-- factorization.  For a base line projector P_x, let the coarse field be the
-- constant field y |-> P_x and let Q_x remove it.  If the discrete kernel has
-- zero mass, then
--
--   K P_x = 0,
--   K P = K (P - P_x) = K Q_x P.
--
-- This is the exact finite algebra intended for the periodic PV realization;
-- no singular-kernel bound or continuum zero-mass theorem is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNDirectionalProjectorStabilizerRound37Exact as Projector
import DASHI.Physics.Closure.NSTriadKNFinitePVProjectorIncrementRound37Exact as PV

weightedConstantCoordinate :
  (Matrix.Matrix3 → ℚ) →
  Projector.UnitDirection →
  List PV.KernelDirectionSample → ℚ
weightedConstantCoordinate coordinate base samples =
  coordinate (Projector.rankOneProjector (Projector.vector base))
    * PV.sumWeights samples

weightedConstantProjectorSum :
  Projector.UnitDirection →
  List PV.KernelDirectionSample → Matrix.Matrix3
weightedConstantProjectorSum base samples =
  Matrix.matrix3
    (weightedConstantCoordinate Matrix.m11 base samples)
    (weightedConstantCoordinate Matrix.m12 base samples)
    (weightedConstantCoordinate Matrix.m13 base samples)
    (weightedConstantCoordinate Matrix.m21 base samples)
    (weightedConstantCoordinate Matrix.m22 base samples)
    (weightedConstantCoordinate Matrix.m23 base samples)
    (weightedConstantCoordinate Matrix.m31 base samples)
    (weightedConstantCoordinate Matrix.m32 base samples)
    (weightedConstantCoordinate Matrix.m33 base samples)

zeroMassKernelAnnihilatesConstantProjector :
  ∀ base samples →
  PV.ZeroMassKernel samples →
  weightedConstantProjectorSum base samples ≡ Matrix.zeroMatrix
zeroMassKernelAnnihilatesConstantProjector base samples zeroMass =
  Matrix.matrixExt
    (coordinateZero Matrix.m11)
    (coordinateZero Matrix.m12)
    (coordinateZero Matrix.m13)
    (coordinateZero Matrix.m21)
    (coordinateZero Matrix.m22)
    (coordinateZero Matrix.m23)
    (coordinateZero Matrix.m31)
    (coordinateZero Matrix.m32)
    (coordinateZero Matrix.m33)
  where
  coordinateZero :
    (coordinate : Matrix.Matrix3 → ℚ) →
    weightedConstantCoordinate coordinate base samples ≡ 0ℚ
  coordinateZero coordinate =
    trans
      (cong
        (λ mass →
          coordinate (Projector.rankOneProjector (Projector.vector base))
            * mass)
        (PV.totalWeightZero zeroMass))
      (solve
        (coordinate
          (Projector.rankOneProjector (Projector.vector base)) ∷ []))

coarseProjectorOperator :
  Projector.UnitDirection →
  List PV.KernelDirectionSample → Matrix.Matrix3
coarseProjectorOperator = weightedConstantProjectorSum

detailProjectorOperator :
  Projector.UnitDirection →
  List PV.KernelDirectionSample → Matrix.Matrix3
detailProjectorOperator = PV.weightedProjectorIncrementSum

kernelProjectorOperator :
  List PV.KernelDirectionSample → Matrix.Matrix3
kernelProjectorOperator = PV.weightedProjectorSum

kernelFactorsThroughProjectorDetail :
  ∀ base samples →
  PV.ZeroMassKernel samples →
  kernelProjectorOperator samples
  ≡ detailProjectorOperator base samples
kernelFactorsThroughProjectorDetail = PV.finitePVProjectorIncrementIdentity

record FinitePVDetailFactorization
    (base : Projector.UnitDirection)
    (samples : List PV.KernelDirectionSample) : Set where
  constructor finite-pv-detail-factorization
  field
    zeroMass : PV.ZeroMassKernel samples
    coarseKilled :
      coarseProjectorOperator base samples ≡ Matrix.zeroMatrix
    factorsThroughDetail :
      kernelProjectorOperator samples
      ≡ detailProjectorOperator base samples

open FinitePVDetailFactorization public

finitePVDetailFactorization :
  ∀ base samples →
  PV.ZeroMassKernel samples →
  FinitePVDetailFactorization base samples
finitePVDetailFactorization base samples zeroMass =
  finite-pv-detail-factorization
    zeroMass
    (zeroMassKernelAnnihilatesConstantProjector base samples zeroMass)
    (kernelFactorsThroughProjectorDetail base samples zeroMass)

finitePVDetailOperatorClosed : Bool
finitePVDetailOperatorClosed = true

literalPeriodicPVDetailFactorizationConstructed : Bool
literalPeriodicPVDetailFactorizationConstructed = false

finitePVDetailOperatorClosedIsTrue :
  finitePVDetailOperatorClosed ≡ true
finitePVDetailOperatorClosedIsTrue = refl
