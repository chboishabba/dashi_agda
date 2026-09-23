{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNOrderedOrientedSelfExternalSpacetimeRound615Exact where

------------------------------------------------------------------------
-- ROUND615 / TERMINAL ORDERED SELF+EXTERNAL SPLIT THROUGH SPACE AND TIME
--
-- R614 proves on one physical output fibre
--
--   Ordered(H) = Ordered(H_self) + Ordered(H_external).
--
-- This module lifts that exact identity over:
--
--   * the canonical selected-output aggregation used by the direct R503 lane;
--   * the literal live Galerkin trajectory;
--   * the existing integration transport authority.
--
-- It then gives a least-privilege producer:
--
--   cutoff-uniform signed self budget
--   + cutoff-uniform signed external-network budget
--
--      => existing OrderedOrientedSpacetimeBudget
--      => existing R503 DirectOffDiagonalBudget.
--
-- Both channels remain signed.  No norm, absolute value, Schur majorant, shell
-- count, or new PDE estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact as R398
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNDirectIntegratedOrderedOrientedForceBidiExact as Ordered
import DASHI.Physics.Closure.NSTriadKNOrderedOrientedForceToR503BidiExact as ToR503
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNOrderedOrientedSelfExternalSplitRound614Exact as R614

F : C3.RealField _
F = Rational.rationalRealField

module GlobalSplit
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem))) where

  module Global = R398.GlobalFluxLocal physicalSystem S L H P
  module Original = Ordered.GlobalOrdered physicalSystem S L H P

  globalSelfOrdered :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    Global.OutputFibresPositiveOn cutoff outputs → ℚ
  globalSelfOrdered cutoff [] Global.positiveOutputsNil = 0ℚ
  globalSelfOrdered cutoff (output ∷ outputs)
      (Global.positiveOutputsCons headPositive tailPositive) =
    let
      module Split = R614.FixedOutput physicalSystem S output
      fibre = Output.physicalOutputFiber cutoff output
    in
    R539.orderedOffDiagonalSum Split.selfOrientedForceCross fibre
      + globalSelfOrdered cutoff outputs tailPositive

  globalExternalOrdered :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    Global.OutputFibresPositiveOn cutoff outputs → ℚ
  globalExternalOrdered cutoff [] Global.positiveOutputsNil = 0ℚ
  globalExternalOrdered cutoff (output ∷ outputs)
      (Global.positiveOutputsCons headPositive tailPositive) =
    let
      module Split = R614.FixedOutput physicalSystem S output
      fibre = Output.physicalOutputFiber cutoff output
    in
    R539.orderedOffDiagonalSum Split.externalOrientedForceCross fibre
      + globalExternalOrdered cutoff outputs tailPositive

  globalOrderedSplitsSelfExternal :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    (positive : Global.OutputFibresPositiveOn cutoff outputs) →
    Original.globalOrderedOrientedForce cutoff outputs positive
    ≡
    globalSelfOrdered cutoff outputs positive
      + globalExternalOrdered cutoff outputs positive
  globalOrderedSplitsSelfExternal cutoff [] Global.positiveOutputsNil = refl
  globalOrderedSplitsSelfExternal cutoff (output ∷ outputs)
      (Global.positiveOutputsCons headPositive tailPositive) =
    let
      module Split = R614.FixedOutput physicalSystem S output
      fibre = Output.physicalOutputFiber cutoff output
      headSelf =
        R539.orderedOffDiagonalSum Split.selfOrientedForceCross fibre
      headExternal =
        R539.orderedOffDiagonalSum Split.externalOrientedForceCross fibre
      tailSelf = globalSelfOrdered cutoff outputs tailPositive
      tailExternal = globalExternalOrdered cutoff outputs tailPositive
    in
    trans
      (cong₂ _+_
        (Split.orderedOrientedForceSplitsSelfExternal fibre)
        (globalOrderedSplitsSelfExternal cutoff outputs tailPositive))
      (solve (headSelf ∷ headExternal ∷ tailSelf ∷ tailExternal ∷ []))

module LiveSplit
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
  module Original = Ordered.IntegratedOrdered
    Time initialTime integrateTo DerivativeOf integration
  module Kernel = ToR503.OrderedToR503
    Time initialTime integrateTo DerivativeOf integration
  module Direct = R503.DirectSignedCross
    Time initialTime integrateTo DerivativeOf integration

  instantaneousSelfOrdered :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  instantaneousSelfOrdered T R cutoff time =
    let
      module At = Flux.At T R cutoff time
      module Split = GlobalSplit
        At.PS
        (Dyn.Base.S (Dyn.forgetDynamics T))
        (Dyn.Base.L (Dyn.forgetDynamics T))
        (Dyn.Base.H (Dyn.forgetDynamics T))
        At.P
    in
    Split.globalSelfOrdered cutoff At.outputs At.canonicalOutputPositivity

  instantaneousExternalOrdered :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  instantaneousExternalOrdered T R cutoff time =
    let
      module At = Flux.At T R cutoff time
      module Split = GlobalSplit
        At.PS
        (Dyn.Base.S (Dyn.forgetDynamics T))
        (Dyn.Base.L (Dyn.forgetDynamics T))
        (Dyn.Base.H (Dyn.forgetDynamics T))
        At.P
    in
    Split.globalExternalOrdered cutoff At.outputs At.canonicalOutputPositivity

  instantaneousOrderedSplitsSelfExternal :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    Ordered.LiveOrdered.instantaneousOrderedOrientedForce
      Time initialTime integrateTo DerivativeOf T R cutoff time
    ≡
    instantaneousSelfOrdered T R cutoff time
      + instantaneousExternalOrdered T R cutoff time
  instantaneousOrderedSplitsSelfExternal T R cutoff time =
    let
      module At = Flux.At T R cutoff time
      module Split = GlobalSplit
        At.PS
        (Dyn.Base.S (Dyn.forgetDynamics T))
        (Dyn.Base.L (Dyn.forgetDynamics T))
        (Dyn.Base.H (Dyn.forgetDynamics T))
        At.P
    in
    Split.globalOrderedSplitsSelfExternal
      cutoff At.outputs At.canonicalOutputPositivity

  integratedSelfOrdered :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedSelfOrdered T R cutoff terminal =
    integrateTo (instantaneousSelfOrdered T R cutoff) terminal

  integratedExternalOrdered :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedExternalOrdered T R cutoff terminal =
    integrateTo (instantaneousExternalOrdered T R cutoff) terminal

  integratedOrderedSplitsSelfExternal :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    Original.integratedOrderedOrientedForce T R cutoff terminal
    ≡
    integratedSelfOrdered T R cutoff terminal
      + integratedExternalOrdered T R cutoff terminal
  integratedOrderedSplitsSelfExternal T R cutoff terminal =
    let
      original =
        Ordered.LiveOrdered.instantaneousOrderedOrientedForce
          Time initialTime integrateTo DerivativeOf T R cutoff
      self = instantaneousSelfOrdered T R cutoff
      external = instantaneousExternalOrdered T R cutoff
      pointwise =
        instantaneousOrderedSplitsSelfExternal T R cutoff
    in
    trans
      (R495.integrateCongruent integration
        original
        (λ time → self time + external time)
        pointwise
        terminal)
      (R495.integrateAdd integration self external terminal)

  record SelfExternalOrderedSpacetimeBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      selfBound externalBound : Time → ℚ

      selfSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        Ordered.two * integratedSelfOrdered T R cutoff terminal
        ≤ selfBound terminal

      externalSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        Ordered.two * integratedExternalOrdered T R cutoff terminal
        ≤ externalBound terminal

  open SelfExternalOrderedSpacetimeBudget public

  combinedBound :
    ∀ {T R} → SelfExternalOrderedSpacetimeBudget T R → Time → ℚ
  combinedBound B terminal = selfBound B terminal + externalBound B terminal

  selfExternalBudgetBuildsOrderedBudget :
    ∀ {T R} →
    SelfExternalOrderedSpacetimeBudget T R →
    Kernel.OrderedOrientedSpacetimeBudget T R
  selfExternalBudgetBuildsOrderedBudget {T} {R} B = record
    { Kernel.cutoffIndependentBound = combinedBound B
    ; Kernel.orderedOrientedBudget = λ cutoff terminal →
        let
          selfI = integratedSelfOrdered T R cutoff terminal
          extI = integratedExternalOrdered T R cutoff terminal

          split :
            Original.integratedOrderedOrientedForce T R cutoff terminal
            ≡ selfI + extI
          split = integratedOrderedSplitsSelfExternal T R cutoff terminal

          summed :
            Ordered.two * selfI + Ordered.two * extI
            ≤ selfBound B terminal + externalBound B terminal
          summed = ℚP.+-mono-≤
            (selfSignedBudget B cutoff terminal)
            (externalSignedBudget B cutoff terminal)

          scaleSplit :
            Ordered.two
              * Original.integratedOrderedOrientedForce T R cutoff terminal
            ≡ Ordered.two * selfI + Ordered.two * extI
          scaleSplit rewrite split = solve (selfI ∷ extI ∷ [])
        in
        subst
          (_≤ combinedBound B terminal)
          (sym scaleSplit)
          summed
    }

  selfExternalBudgetBuildsR503 :
    ∀ {T R} →
    SelfExternalOrderedSpacetimeBudget T R →
    Direct.DirectOffDiagonalBudget T R
  selfExternalBudgetBuildsR503 =
    Kernel.orderedBudgetBuildsR503 ∘ selfExternalBudgetBuildsOrderedBudget
    where
    _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
    (f ∘ g) x = f (g x)

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round615GlobalSelfExternalAggregationClosed : Bool
round615GlobalSelfExternalAggregationClosed = true

round615IntegratedSelfExternalSplitClosed : Bool
round615IntegratedSelfExternalSplitClosed = true

round615SelfExternalBudgetsCompileToR503 : Bool
round615SelfExternalBudgetsCompileToR503 = true

round615SelfSignedSpacetimeBudgetClosed : Bool
round615SelfSignedSpacetimeBudgetClosed = false

round615ExternalSignedSpacetimeBudgetClosed : Bool
round615ExternalSignedSpacetimeBudgetClosed = false

round615IntroducesNormOrAbsoluteValue : Bool
round615IntroducesNormOrAbsoluteValue = false

round615IntroducesEstimate : Bool
round615IntroducesEstimate = false

round615SelfExternalBudgetsCompileToR503IsTrue :
  round615SelfExternalBudgetsCompileToR503 ≡ true
round615SelfExternalBudgetsCompileToR503IsTrue = refl

round615IntroducesEstimateIsFalse :
  round615IntroducesEstimate ≡ false
round615IntroducesEstimateIsFalse = refl
