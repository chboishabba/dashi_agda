module DASHI.Physics.Closure.NSTriadKNDirectResolventGramFluxNormalFormExact where

------------------------------------------------------------------------
-- DIRECT R503 NORMAL FORM: QUINTIC REMAINDER -> QUARTIC GRAM + ENDPOINT FLUX
--
-- For every literal positive off-diagonal R290 pair, R290 already proves
--
--   weightedNonlinearRemainder = gram + weightedGramFluxTangent.
--
-- R497/R498 identify the sum of those SAME weighted remainders with
--
--   4 * directResolventCompanion.
--
-- Therefore, before any absolute value or positive Gram observer,
--
--   4 C_direct
--     = offDiagonalGram + offDiagonalWeightedFluxTangent.
--
-- On the live trajectory and after ordinary integration transport,
--
--   4 integral C_direct
--     = integral offDiagonalGram
--       + integral offDiagonalWeightedFluxTangent.
--
-- A standard FTC receipt for the exact weighted-flux curve then turns the
-- second term into an endpoint increment.  Consequently R503 can be paid by
-- TWO QUARTIC bounds, with no quintic forcing estimate:
--
--   integral Gram <= G(T)
--   Flux(T) - Flux(0) <= F(T)
--
-- giving the cutoff-independent R503 bound G(T)+F(T).
--
-- This file does not prove either quartic analytic bound and does not install
-- scalar FTC.  It removes the higher-degree producer obligation exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNDirectResolventFibreCompanionRound497Exact as R497
import DASHI.Physics.Closure.NSTriadKNDirectResolventGlobalCompanionRound498Exact as R498
import DASHI.Physics.Closure.NSTriadKNDirectResolventTrajectoryCompanionRound499Exact as R499
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Generic finite R290 normal form.
------------------------------------------------------------------------

finiteRemainderIsGramPlusFluxTangent :
  (pairs : List R290.DampedGramPair) →
  R385.sumWeightedRemainder pairs
  ≡ R385.sumGram pairs + R385.sumWeightedFluxTangent pairs
finiteRemainderIsGramPlusFluxTangent pairs
  rewrite R385.finiteGramAsNegativeFluxDerivativePlusRemainder pairs =
  solve
    ( R385.sumWeightedFluxTangent pairs
    ∷ R385.sumWeightedRemainder pairs
    ∷ [] )

------------------------------------------------------------------------
-- 2. Exact R497/R498 direct-companion normal form.
------------------------------------------------------------------------

module FibreNormalForm
    (physicalSystem :
      Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Fibre = R497.DirectFibre physicalSystem S

  directFibreCompanionIsGramPlusFluxTangent :
    (items :
      List Physical.PhysicalTriadIncidence) →
    (positive : Fibre.Local.PairRatePositiveOn items) →
    R299.four * Fibre.directFibreCompanion items positive
    ≡
    R385.sumGram (Fibre.Local.allR290Pairs items positive)
      + R385.sumWeightedFluxTangent
          (Fibre.Local.allR290Pairs items positive)
  directFibreCompanionIsGramPlusFluxTangent items positive =
    trans
      (sym (Fibre.allRemainderIsFourCompanion items positive))
      (finiteRemainderIsGramPlusFluxTangent
        (Fibre.Local.allR290Pairs items positive))

module GlobalNormalForm
    (physicalSystem :
      Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt
        (Field30.finiteSystem physicalSystem))) where

  module Global = R498.DirectGlobal physicalSystem S L H P

  directGlobalCompanionIsGramPlusFluxTangent :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    (positive : Global.Global.OutputFibresPositiveOn cutoff outputs) →
    R299.four * Global.globalDirectCompanion cutoff outputs positive
    ≡
    R385.sumGram (Global.Global.globalPairs cutoff outputs positive)
      + R385.sumWeightedFluxTangent
          (Global.Global.globalPairs cutoff outputs positive)
  directGlobalCompanionIsGramPlusFluxTangent cutoff outputs positive =
    trans
      (sym
        (Global.globalRemainderIsFourDirectCompanion
          cutoff outputs positive))
      (finiteRemainderIsGramPlusFluxTangent
        (Global.Global.globalPairs cutoff outputs positive))

------------------------------------------------------------------------
-- 3. Live trajectory specialization and integration.
------------------------------------------------------------------------

module LiveNormalForm
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
  module Direct = R499.DirectTrajectory
    Time initialTime integrateTo DerivativeOf
  module Integrated = R500.IntegratedDirect
    Time initialTime integrateTo DerivativeOf integration
  module R503Direct = R503.DirectSignedCross
    Time initialTime integrateTo DerivativeOf integration

  livePairs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → List R290.DampedGramPair
  livePairs T R cutoff time =
    let
      module At = Flux.At T R cutoff time
      module G = R498.DirectGlobal
        At.PS
        (Dyn.Base.S (Dyn.forgetDynamics T))
        (Dyn.Base.L (Dyn.forgetDynamics T))
        (Dyn.Base.H (Dyn.forgetDynamics T))
        At.P
    in
    G.Global.globalPairs
      cutoff At.outputs At.canonicalOutputPositivity

  offDiagonalGramAt :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  offDiagonalGramAt T R cutoff time =
    R385.sumGram (livePairs T R cutoff time)

  offDiagonalFluxTangentAt :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  offDiagonalFluxTangentAt T R cutoff time =
    R385.sumWeightedFluxTangent (livePairs T R cutoff time)

  offDiagonalFluxAt :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  offDiagonalFluxAt T R cutoff time =
    R385.sumWeightedFlux (livePairs T R cutoff time)

  pointwiseDirectIsGramPlusFluxTangent :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    R299.four * Direct.instantaneousDirectCompanion T R cutoff time
    ≡ offDiagonalGramAt T R cutoff time
      + offDiagonalFluxTangentAt T R cutoff time
  pointwiseDirectIsGramPlusFluxTangent T R cutoff time =
    let
      module At = Flux.At T R cutoff time
      module G = GlobalNormalForm
        At.PS
        (Dyn.Base.S (Dyn.forgetDynamics T))
        (Dyn.Base.L (Dyn.forgetDynamics T))
        (Dyn.Base.H (Dyn.forgetDynamics T))
        At.P
    in
    G.directGlobalCompanionIsGramPlusFluxTangent
      cutoff At.outputs At.canonicalOutputPositivity

  integratedOffDiagonalGram :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedOffDiagonalGram T R cutoff terminal =
    integrateTo (offDiagonalGramAt T R cutoff) terminal

  integratedOffDiagonalFluxTangent :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedOffDiagonalFluxTangent T R cutoff terminal =
    integrateTo (offDiagonalFluxTangentAt T R cutoff) terminal

  fourIntegratedDirectIsGramPlusFluxTangent :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    R299.four * Integrated.integratedDirectCompanion T R cutoff terminal
    ≡ integratedOffDiagonalGram T R cutoff terminal
      + integratedOffDiagonalFluxTangent T R cutoff terminal
  fourIntegratedDirectIsGramPlusFluxTangent T R cutoff terminal =
    let
      direct = Direct.instantaneousDirectCompanion T R cutoff
      pointwise =
        pointwiseDirectIsGramPlusFluxTangent T R cutoff

      scaleBack :
        R299.four * Integrated.integratedDirectCompanion T R cutoff terminal
        ≡ integrateTo (λ time → R299.four * direct time) terminal
      scaleBack =
        sym (Integrated.integrateFour direct terminal)

      transport =
        R495.integrateCongruent integration
          (λ time → R299.four * direct time)
          (λ time →
            offDiagonalGramAt T R cutoff time
              + offDiagonalFluxTangentAt T R cutoff time)
          pointwise
          terminal

      split =
        R495.integrateAdd integration
          (offDiagonalGramAt T R cutoff)
          (offDiagonalFluxTangentAt T R cutoff)
          terminal
    in
    trans scaleBack (trans transport split)

  ----------------------------------------------------------------------
  -- Quartic producer for R503.
  ----------------------------------------------------------------------

  record DirectGramFluxBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      cutoffIndependentGramBound : Time → ℚ
      integratedGramBudget :
        (cutoff : Nat) (terminal : Time) →
        integratedOffDiagonalGram T R cutoff terminal
        ≤ cutoffIndependentGramBound terminal

      cutoffIndependentFluxEndpointBound : Time → ℚ

      -- Standard-analysis receipt on the EXACT weighted flux curve.
      offDiagonalFluxFTC :
        (cutoff : Nat) (terminal : Time) →
        integratedOffDiagonalFluxTangent T R cutoff terminal
        ≡ offDiagonalFluxAt T R cutoff terminal
            - offDiagonalFluxAt T R cutoff initialTime

      fluxEndpointBudget :
        (cutoff : Nat) (terminal : Time) →
        offDiagonalFluxAt T R cutoff terminal
          - offDiagonalFluxAt T R cutoff initialTime
        ≤ cutoffIndependentFluxEndpointBound terminal

  open DirectGramFluxBudget public

  gramFluxBudgetBuildsR503 :
    ∀ {T R} →
    DirectGramFluxBudget T R →
    R503Direct.DirectOffDiagonalBudget T R
  gramFluxBudgetBuildsR503 {T} {R} P = record
    { R503Direct.cutoffIndependentBound =
        λ terminal →
          cutoffIndependentGramBound P terminal
            + cutoffIndependentFluxEndpointBound P terminal
    ; R503Direct.directOffDiagonalBudget = λ cutoff terminal →
        let
          exact =
            fourIntegratedDirectIsGramPlusFluxTangent
              T R cutoff terminal

          fluxPaid :
            integratedOffDiagonalFluxTangent T R cutoff terminal
            ≤ cutoffIndependentFluxEndpointBound P terminal
          fluxPaid =
            subst
              (_≤ cutoffIndependentFluxEndpointBound P terminal)
              (sym (offDiagonalFluxFTC P cutoff terminal))
              (fluxEndpointBudget P cutoff terminal)

          paid =
            ℚP.+-mono-≤
              (integratedGramBudget P cutoff terminal)
              fluxPaid
        in
        subst
          (λ lower →
            lower
            ≤ cutoffIndependentGramBound P terminal
              + cutoffIndependentFluxEndpointBound P terminal)
          (sym exact)
          paid
    }

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

directR503QuinticProducerMandatory : Bool
directR503QuinticProducerMandatory = false

directR503QuarticGramPlusEndpointProducerAvailable : Bool
directR503QuarticGramPlusEndpointProducerAvailable = true

directGramFluxNormalFormIntroducesAbsoluteValue : Bool
directGramFluxNormalFormIntroducesAbsoluteValue = false

directGramFluxNormalFormIntroducesCutoffFactor : Bool
directGramFluxNormalFormIntroducesCutoffFactor = false

directGramFluxAnalyticBoundsClosed : Bool
directGramFluxAnalyticBoundsClosed = false

clayPromotion : Bool
clayPromotion = false

directR503QuinticProducerMandatoryIsFalse :
  directR503QuinticProducerMandatory ≡ false
directR503QuinticProducerMandatoryIsFalse = refl

directR503QuarticGramPlusEndpointProducerAvailableIsTrue :
  directR503QuarticGramPlusEndpointProducerAvailable ≡ true
directR503QuarticGramPlusEndpointProducerAvailableIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
