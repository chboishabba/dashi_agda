module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4PointwiseSpacetimeMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 / Q4 POINTWISE -> SPACETIME COMPILER
--
-- The preferred Q4 leaf is currently stated as a cutoff-uniform integrated
-- off-diagonal Gram bound.  The repository already has ordinary monotone,
-- constant-scale integration authority.  Therefore time integration is not a
-- separate Navier--Stokes estimate.
--
-- If on the SAME literal R406 off-diagonal Gram curve
--
--   G_N(t) <= A * D_N(t),          A >= 0,
--
-- and
--
--   integral D_N <= D_*(T)
--
-- uniformly in N, then
--
--   integral G_N <= A * D_*(T).
--
-- The coefficient A may already contain a cutoff-independent energy ceiling,
-- so the genuine PDE leaf can be attacked pointwise in ED currency.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCommutatorSpacetimeEDPaymentExact as Ordered
import DASHI.Physics.Closure.NSTriadKNDirectResolventGramFluxNormalFormExact as Q4E
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405

F : C3.RealField _
F = Rational.rationalRealField

module PointwiseToSpacetime
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (transport : R495.IntegrationTransportAuthority Time integrateTo)
    (orderIntegration : Ordered.OrderedScaledIntegration Time integrateTo) where

  module LiveQ4E = Q4E.LiveNormalForm
    Time initialTime integrateTo DerivativeOf transport
  module Dyn = R240.PhysicalNSDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf

  record PointwiseGramDissipationData
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      coefficient : ℚ
      coefficientNN : 0ℚ ≤ coefficient

      dissipationAt : Nat → Time → ℚ

      pointwiseGramBelowScaledDissipation :
        (cutoff : Nat) (time : Time) →
        LiveQ4E.offDiagonalGramAt T R cutoff time
        ≤ coefficient * dissipationAt cutoff time

      cutoffIndependentIntegratedDissipationBound : Time → ℚ
      integratedDissipationBudget :
        (cutoff : Nat) (terminal : Time) →
        integrateTo (dissipationAt cutoff) terminal
        ≤ cutoffIndependentIntegratedDissipationBound terminal

  open PointwiseGramDissipationData public

  cutoffIndependentGramBound :
    ∀ {T R} → PointwiseGramDissipationData T R → Time → ℚ
  cutoffIndependentGramBound D terminal =
    coefficient D * cutoffIndependentIntegratedDissipationBound D terminal

  integratedGramBudget :
    ∀ {T R} →
    (D : PointwiseGramDissipationData T R) →
    (cutoff : Nat) (terminal : Time) →
    LiveQ4E.integratedOffDiagonalGram T R cutoff terminal
    ≤ cutoffIndependentGramBound D terminal
  integratedGramBudget {T} {R} D cutoff terminal =
    let
      pointwise = pointwiseGramBelowScaledDissipation D cutoff

      monotone :
        integrateTo (LiveQ4E.offDiagonalGramAt T R cutoff) terminal
        ≤ integrateTo (λ time → coefficient D * dissipationAt D cutoff time) terminal
      monotone =
        Ordered.integrateMonotone orderIntegration
          (LiveQ4E.offDiagonalGramAt T R cutoff)
          (λ time → coefficient D * dissipationAt D cutoff time)
          pointwise terminal

      scale :
        integrateTo (λ time → coefficient D * dissipationAt D cutoff time) terminal
        ≡ coefficient D * integrateTo (dissipationAt D cutoff) terminal
      scale =
        Ordered.integrateNonnegativeConstantScale orderIntegration
          (coefficient D) (coefficientNN D)
          (dissipationAt D cutoff) terminal

      scaledBudget :
        coefficient D * integrateTo (dissipationAt D cutoff) terminal
        ≤ coefficient D * cutoffIndependentIntegratedDissipationBound D terminal
      scaledBudget =
        let instance coefficientNNI : NonNegative (coefficient D)
            coefficientNNI = nonNegative (coefficientNN D)
        in
        ℚP.*-monoˡ-≤-nonNeg
          (coefficient D)
          (integratedDissipationBudget D cutoff terminal)

      afterScale :
        integrateTo (λ time → coefficient D * dissipationAt D cutoff time) terminal
        ≤ coefficient D * cutoffIndependentIntegratedDissipationBound D terminal
      afterScale =
        subst
          (_≤ coefficient D * cutoffIndependentIntegratedDissipationBound D terminal)
          (sym scale)
          scaledBudget
    in
    ℚP.≤-trans monotone afterScale

------------------------------------------------------------------------
-- Status / exact research seam.
------------------------------------------------------------------------

q4PointwiseToSpacetimeCompilerClosed : Bool
q4PointwiseToSpacetimeCompilerClosed = true

q4IntegratedBoundIndependentResearchLeaf : Bool
q4IntegratedBoundIndependentResearchLeaf = false

q4PointwisePhysicalGramEstimateClosedHere : Bool
q4PointwisePhysicalGramEstimateClosedHere = false

q4PointwiseCompilerIntroducesEstimate : Bool
q4PointwiseCompilerIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

q4PointwiseToSpacetimeCompilerClosedIsTrue :
  q4PointwiseToSpacetimeCompilerClosed ≡ true
q4PointwiseToSpacetimeCompilerClosedIsTrue = refl

q4IntegratedBoundIndependentResearchLeafIsFalse :
  q4IntegratedBoundIndependentResearchLeaf ≡ false
q4IntegratedBoundIndependentResearchLeafIsFalse = refl

q4PointwisePhysicalGramEstimateClosedHereIsFalse :
  q4PointwisePhysicalGramEstimateClosedHere ≡ false
q4PointwisePhysicalGramEstimateClosedHereIsFalse = refl
