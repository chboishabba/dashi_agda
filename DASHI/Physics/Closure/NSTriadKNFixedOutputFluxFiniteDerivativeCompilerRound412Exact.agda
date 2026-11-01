module DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact where

------------------------------------------------------------------------
-- ROUND412 / FINITE DIFFERENTIATION COMPILER FOR THE SAME R406 OBSERVABLE
--
-- R409 correctly froze the analytic target as the derivative of the literal
-- R406 fixed-output flux.  This round removes the purely finite part of that
-- payment.  A scalar derivative semantics needs only:
--
--   * derivative of the zero curve;
--   * closure under addition;
--   * transport along pointwise equal curves/tangents.
--
-- Given a finite decomposition whose sums are pointwise IDENTICAL to R406's
-- offDiagonalFlux and offDiagonalFluxTangent, per-term derivative witnesses
-- compile to the exact R409 theorem.  No caller-selected replacement flux can
-- be used: both endpoints of transport are pinned to R406.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxDerivativeBoundaryRound409Exact as R409

F : C3.RealField _
F = Rational.rationalRealField

sumCurves : ∀ {Time : Set} → List (Time → ℚ) → Time → ℚ
sumCurves [] time = 0ℚ
sumCurves (f ∷ rest) time = f time + sumCurves rest time

record ScalarDerivativeAlgebra
    (Time : Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set) : Set₁ where
  field
    zeroDerivative :
      ScalarDerivativeOf (λ _ → 0ℚ) (λ _ → 0ℚ)

    addDerivative :
      ∀ {f g df dg} →
      ScalarDerivativeOf f df →
      ScalarDerivativeOf g dg →
      ScalarDerivativeOf
        (λ time → f time + g time)
        (λ time → df time + dg time)

    transportDerivative :
      ∀ {f g df dg} →
      ((time : Time) → f time ≡ g time) →
      ((time : Time) → df time ≡ dg time) →
      ScalarDerivativeOf f df →
      ScalarDerivativeOf g dg

open ScalarDerivativeAlgebra public

data AllDerivatives
    {Time : Set}
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set) :
    List (Time → ℚ) → List (Time → ℚ) → Set where
  derivativesNil : AllDerivatives ScalarDerivativeOf [] []
  derivativesCons :
    ∀ {f df fs dfs} →
    ScalarDerivativeOf f df →
    AllDerivatives ScalarDerivativeOf fs dfs →
    AllDerivatives ScalarDerivativeOf (f ∷ fs) (df ∷ dfs)

finiteSumDerivative :
  ∀ {Time : Set}
    {ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set} →
  (A : ScalarDerivativeAlgebra Time ScalarDerivativeOf) →
  ∀ {fs dfs} →
  AllDerivatives ScalarDerivativeOf fs dfs →
  ScalarDerivativeOf (sumCurves fs) (sumCurves dfs)
finiteSumDerivative A derivativesNil = zeroDerivative A
finiteSumDerivative A (derivativesCons head tail) =
  addDerivative A head (finiteSumDerivative A tail)

module R406FiniteDerivative
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (A : ScalarDerivativeAlgebra Time ScalarDerivativeOf) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf
  module Boundary = R409.Boundary
    Time initialTime integrateTo DerivativeOf ScalarDerivativeOf

  record LiteralFiniteFluxDecomposition
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) : Set₁ where
    field
      fluxTerms tangentTerms : List (Time → ℚ)

      termDerivatives :
        AllDerivatives ScalarDerivativeOf fluxTerms tangentTerms

      fluxSumIsLiteralR406 :
        (time : Time) →
        sumCurves fluxTerms time
        ≡ Flux.At.offDiagonalFlux T R cutoff time

      tangentSumIsLiteralR406 :
        (time : Time) →
        sumCurves tangentTerms time
        ≡ Flux.At.offDiagonalFluxTangent T R cutoff time

  open LiteralFiniteFluxDecomposition public

  finiteDecompositionBuildsR409 :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) →
    LiteralFiniteFluxDecomposition T R cutoff →
    Boundary.FixedOutputFluxDerivative T R cutoff
  finiteDecompositionBuildsR409 T R cutoff D = record
    { Boundary.derivativeIsExactR406Tangent =
        transportDerivative A
          (fluxSumIsLiteralR406 D)
          (tangentSumIsLiteralR406 D)
          (finiteSumDerivative A (termDerivatives D))
    }

round412FiniteSumDifferentiationClosed : Bool
round412FiniteSumDifferentiationClosed = true

round412TransportTargetIsLiteralR406Flux : Bool
round412TransportTargetIsLiteralR406Flux = true

round412NoFunctionExtensionalityRequired : Bool
round412NoFunctionExtensionalityRequired = true

round412RemainingDerivativeWorkIsPerTermCalculus : Bool
round412RemainingDerivativeWorkIsPerTermCalculus = true

round412FiniteSumDifferentiationClosedIsTrue :
  round412FiniteSumDifferentiationClosed ≡ true
round412FiniteSumDifferentiationClosedIsTrue = refl

round412TransportTargetIsLiteralR406FluxIsTrue :
  round412TransportTargetIsLiteralR406Flux ≡ true
round412TransportTargetIsLiteralR406FluxIsTrue = refl
