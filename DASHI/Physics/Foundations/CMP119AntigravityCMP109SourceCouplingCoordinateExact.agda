{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceCouplingCoordinateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; Positive; _*_; _≤_)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PRIMARY CMP109 SOURCE COUPLING COORDINATE
--
-- The source trajectory already owns
--
--   u_k = inverseCoupling trajectory k.
--
-- The physical coupling g_k must therefore be attached to THAT node and prove
--
--   u_k g_k^2 = 1
--
-- there.  The plaquette producer remainder coupling at an edge is a
-- coefficient-side coordinate and is not silently promoted to g_k.
------------------------------------------------------------------------

record CMP109SourceCouplingCoordinate
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    sourceCoupling : Nat → ℚ
    sourceCouplingPositive : ∀ scale → Positive (sourceCoupling scale)

    sourceInverseSquareMeaning : ∀ scale →
      Flow.inverseCoupling trajectory scale
      * Order.square (sourceCoupling scale)
      ≡ 1ℚ

open CMP109SourceCouplingCoordinate public

------------------------------------------------------------------------
-- OPTIONAL COEFFICIENT-SIDE WELD
--
-- This is deliberately separate.  It records exactly which source node a
-- literal plaquette coefficient packet uses when its quartic remainder is
-- parameterised by a coupling.
------------------------------------------------------------------------

record PlaquetteCoefficientCouplingWeld
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    (plaquette : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory)
    (source : CMP109SourceCouplingCoordinate trajectory) : Set₁ where
  field
    coefficientCouplingNode : Nat → Nat

    remainderCouplingIsSourceCoupling :
      ∀ edge →
      Plaquette.coupling
        (Plaquette.remainder
          (Constructor.asPhysicalRunningCouplingData plaquette))
        edge
      ≡ sourceCoupling source (coefficientCouplingNode edge)

open PlaquetteCoefficientCouplingWeld public

sourceCouplingIsDefinitionallyRemainderCoupling : Bool
sourceCouplingIsDefinitionallyRemainderCoupling = false

sourceInverseSquareMeaningStillRequired : Bool
sourceInverseSquareMeaningStillRequired = true

coefficientCouplingIdentificationIsSeparate : Bool
coefficientCouplingIdentificationIsSeparate = true

sourceCouplingIsDefinitionallyRemainderCouplingIsFalse :
  sourceCouplingIsDefinitionallyRemainderCoupling ≡ false
sourceCouplingIsDefinitionallyRemainderCouplingIsFalse = refl

sourceInverseSquareMeaningStillRequiredIsTrue :
  sourceInverseSquareMeaningStillRequired ≡ true
sourceInverseSquareMeaningStillRequiredIsTrue = refl

coefficientCouplingIdentificationIsSeparateIsTrue :
  coefficientCouplingIdentificationIsSeparate ≡ true
coefficientCouplingIdentificationIsSeparateIsTrue = refl

cmp109SourceCouplingCoordinateCompilerLevel : ProofLevel
cmp109SourceCouplingCoordinateCompilerLevel = machineChecked

-- This is a genuine source-meaning leaf, not scalar analysis:
-- identify the CMP109 physical coupling with the primary inverse-square
-- trajectory coordinate.
cmp109SourceInverseSquareCouplingMeaningLevel : ProofLevel
cmp109SourceInverseSquareCouplingMeaningLevel = conditional
