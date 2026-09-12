module DASHI.Physics.Closure.NSTriadKNLiveSpectatorResolventNestedLeafABidiExact where

------------------------------------------------------------------------
-- LIVE SPECTATOR-RESOLVENT NESTED LEAF-A BIDI
--
-- Compose the fixed-slice same-object weld with the existing R240/R405/R406
-- live trajectory infrastructure and R495 integration authority.
--
-- At every (N,t,k), R568's sole forcing/commutator square is exactly a finite
-- sum over spectators beta of Hermitian pairings against the R541-resolved,
-- R573-nested four-sign commutator carrier.  The identity is then lifted over
-- the canonical output list and through time integration.
--
-- Hence a cutoff-uniform spacetime bound on THIS signed nested object directly
-- constructs the pre-existing R568 commutator budget.  No norm, absolute value,
-- Schur/Cotlar, Laplace transform, Bony majorant, or new analytic estimate is
-- introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedForcingSquareBidiExact as NestedFixed

F : C3.RealField _
F = Rational.rationalRealField

module LiveNested
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf
  module Comm = R568.LiveCommutatorOnly
    Time initialTime integrateTo DerivativeOf integration

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time) where

    module Slice = Flux.At T R cutoff time

    S = Dyn.Base.S (Dyn.forgetDynamics T)
    L = Dyn.Base.L (Dyn.forgetDynamics T)
    H = Dyn.Base.H (Dyn.forgetDynamics T)

    velocityTransverse =
      Dyn.Base.velocityTransverse (Dyn.forgetDynamics T) cutoff time

    module Weld = NestedFixed.Weld
      Slice.PS S L H velocityTransverse

    storedCutoff : Nat
    storedCutoff = Audit.cutoff (Field30.finiteSystem Slice.PS)

    cutoffExact : storedCutoff ≡ cutoff
    cutoffExact =
      Dyn.Base.systemCutoffAgreement (Dyn.forgetDynamics T) cutoff time

    nestedOutputForcingFull : Z3.FourierMode → ℚ
    nestedOutputForcingFull output =
      Weld.allNestedForcingRows output
        (Output.physicalOutputFiber cutoff output)

    outputForcingFullIsNested :
      (output : Z3.FourierMode) →
      Comm.outputForcingFull T R cutoff time output
      ≡ nestedOutputForcingFull output
    outputForcingFullIsNested output =
      subst
        (λ selectedCutoff →
          R543.fullSquareSum Weld.T.forcingPair
            (Output.physicalOutputFiber selectedCutoff output)
          ≡ Weld.allNestedForcingRows output
            (Output.physicalOutputFiber selectedCutoff output))
        cutoffExact
        (Weld.forcingFullIsNestedSpectatorRows output)

  nestedSumOutputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) → Time → List Z3.FourierMode → ℚ
  nestedSumOutputs T R cutoff time [] = 0ℚ
  nestedSumOutputs T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    A.nestedOutputForcingFull output
      + nestedSumOutputs T R cutoff time rest

  nestedGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  nestedGlobalForcingFull T R cutoff time =
    nestedSumOutputs T R cutoff time (Canonical.nonzeroCutoffModes cutoff)

  sumOutputsForcingIsNested :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    (outputs : List Z3.FourierMode) →
    Comm.sumOutputForcingFull T R cutoff time outputs
    ≡ nestedSumOutputs T R cutoff time outputs
  sumOutputsForcingIsNested T R cutoff time [] = refl
  sumOutputsForcingIsNested T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    cong₂ _+_
      (A.outputForcingFullIsNested output)
      (sumOutputsForcingIsNested T R cutoff time rest)

  globalForcingIsNested :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    Comm.globalForcingFull T R cutoff time
    ≡ nestedGlobalForcingFull T R cutoff time
  globalForcingIsNested T R cutoff time =
    sumOutputsForcingIsNested T R cutoff time
      (Canonical.nonzeroCutoffModes cutoff)

  integratedNestedGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedNestedGlobalForcingFull T R cutoff terminal =
    integrateTo (nestedGlobalForcingFull T R cutoff) terminal

  integratedForcingIsNested :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    Comm.integratedGlobalForcingFull T R cutoff terminal
    ≡ integratedNestedGlobalForcingFull T R cutoff terminal
  integratedForcingIsNested T R cutoff terminal =
    R495.integrateCongruent integration
      (Comm.globalForcingFull T R cutoff)
      (nestedGlobalForcingFull T R cutoff)
      (globalForcingIsNested T R cutoff)
      terminal

  record NestedSpectatorSpacetimeBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      cutoffIndependentNestedBound : Time → ℚ
      nestedSpectatorBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 *
          integratedNestedGlobalForcingFull T R cutoff terminal
        ≤ cutoffIndependentNestedBound terminal

  open NestedSpectatorSpacetimeBudget public

  nestedBudgetBuildsR568 :
    ∀ {T R} →
    NestedSpectatorSpacetimeBudget T R →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  nestedBudgetBuildsR568 {T} {R} P = record
    { Comm.cutoffIndependentCommutatorBound568 =
        cutoffIndependentNestedBound P
    ; Comm.liveCommutatorOnlyBudget568 = λ cutoff terminal →
        subst
          (λ lhs → lhs ≤ cutoffIndependentNestedBound P terminal)
          (sym
            (cong (R567.four567 *_)
              (integratedForcingIsNested T R cutoff terminal)))
          (nestedSpectatorBudget P cutoff terminal)
    }

------------------------------------------------------------------------
-- STATUS / INTROSPECTIVE RESULT
------------------------------------------------------------------------

liveNestedR568OutputSameObjectWeldClosed : Bool
liveNestedR568OutputSameObjectWeldClosed = true

liveNestedCanonicalOutputSumWeldClosed : Bool
liveNestedCanonicalOutputSumWeldClosed = true

liveNestedIntegrationTransportClosed : Bool
liveNestedIntegrationTransportClosed = true

liveNestedBudgetCompilesToR568 : Bool
liveNestedBudgetCompilesToR568 = true

liveNestedIntroducesNewAnalyticEstimate : Bool
liveNestedIntroducesNewAnalyticEstimate = false

liveNestedCutoffUniformSpacetimeEstimateClosed : Bool
liveNestedCutoffUniformSpacetimeEstimateClosed = false

liveNestedClayPromotion : Bool
liveNestedClayPromotion = false

liveNestedBudgetCompilesToR568IsTrue :
  liveNestedBudgetCompilesToR568 ≡ true
liveNestedBudgetCompilesToR568IsTrue = refl

liveNestedIntroducesNewAnalyticEstimateIsFalse :
  liveNestedIntroducesNewAnalyticEstimate ≡ false
liveNestedIntroducesNewAnalyticEstimateIsFalse = refl

liveNestedClayPromotionIsFalse :
  liveNestedClayPromotion ≡ false
liveNestedClayPromotionIsFalse = refl
