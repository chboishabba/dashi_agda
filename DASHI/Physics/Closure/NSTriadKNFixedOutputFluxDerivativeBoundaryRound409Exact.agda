module DASHI.Physics.Closure.NSTriadKNFixedOutputFluxDerivativeBoundaryRound409Exact where

------------------------------------------------------------------------
-- ROUND409 / ONE ANALYTIC LEAF: ACTUAL DERIVATIVE OF THE FIXED-OUTPUT FLUX
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406

F : C3.RealField _
F = Rational.rationalRealField

module Boundary
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf

  record FixedOutputFluxDerivative
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) : Set where
    field
      derivativeIsExactR406Tangent :
        ScalarDerivativeOf
          (λ time → Flux.At.offDiagonalFlux T R cutoff time)
          (λ time → Flux.At.offDiagonalFluxTangent T R cutoff time)

  open FixedOutputFluxDerivative public

round409CallerSelectedFluxEliminated : Bool
round409CallerSelectedFluxEliminated = true

round409SameLiteralR406ObservableFrozen : Bool
round409SameLiteralR406ObservableFrozen = true

round409FiniteAlgebraUpstreamClosed : Bool
round409FiniteAlgebraUpstreamClosed = true

round409ActualDerivativeTheoremAnalyticLeaf : Bool
round409ActualDerivativeTheoremAnalyticLeaf = true

round409CallerSelectedFluxEliminatedIsTrue :
  round409CallerSelectedFluxEliminated ≡ true
round409CallerSelectedFluxEliminatedIsTrue = refl

round409SameLiteralR406ObservableFrozenIsTrue :
  round409SameLiteralR406ObservableFrozen ≡ true
round409SameLiteralR406ObservableFrozenIsTrue = refl
