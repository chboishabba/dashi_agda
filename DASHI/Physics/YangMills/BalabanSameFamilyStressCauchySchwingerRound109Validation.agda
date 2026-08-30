{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Validation where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _*_)

import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

stressTelescopeValidation :
  (dataSet : R109.SourceNativeStressScaleCauchy) → ∀ start count →
  R109.stressDifference dataSet start count
  ≤ Scale.coefficient
      (Sum.commonMajorant
        (Source.sourceCompatibleSameFamilyIncrement
          (R109.source dataSet)
          (R109.smallHistory dataSet)
          (R109.stressInsertion dataSet)))
      * (Geo.half * Geo.halfPower start)
stressTelescopeValidation = R109.stressResponseCauchyModulus
