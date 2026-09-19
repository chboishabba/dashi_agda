module DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCommutatorSpacetimeEDPaymentExact where

------------------------------------------------------------------------
-- GLOBAL COMMUTATOR MASS: POINTWISE 36 E D -> CUTOFF-UNIFORM SPACETIME
--
-- The pointwise theorem
--
--   M_N(t) <= 36 E_N(t) D_N(t)
--
-- is already proved on the literal retained physical carrier by
-- PhysicalGlobalCommutatorFourHelicityEDPaymentExact.
--
-- This owner performs the load-bearing time integration without changing the
-- observable.  If the SAME literal trajectory has
--
--   E_N(t) <= E_*,
--   integral D_N <= D_*(T),
--
-- uniformly in N, then
--
--   integral M_N <= 36 E_* D_*(T).
--
-- No fibre cardinality, shell count, absolute Schur envelope, or critical
-- barrier is used.  The only non-PDE authority is ordinary monotonicity and
-- constant scaling of the supplied time integral.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCommutatorFourHelicityEDPaymentExact as Pointwise
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109

F : C3.RealField _
F = Rational.rationalRealField

record OrderedScaledIntegration
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ) : Set₁ where
  field
    integrateMonotone :
      (left right : Time → ℚ) →
      ((time : Time) → left time ≤ right time) →
      (terminal : Time) →
      integrateTo left terminal ≤ integrateTo right terminal

    integrateNonnegativeConstantScale :
      (constant : ℚ) →
      0ℚ ≤ constant →
      (f : Time → ℚ) →
      (terminal : Time) →
      integrateTo (λ time → constant * f time) terminal
      ≡ constant * integrateTo f terminal

open OrderedScaledIntegration public

module PhysicalCommutatorSpacetime
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : OrderedScaledIntegration Time integrateTo) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf

  record PhysicalCommutatorSpacetimeEDData
      (D : Live.LiteralRHSTrajectoryData)
      (S : Helical.HelicalModeScalars F)
      (L : Helical.PeriodicHelicalProjectorLaws
        F
        (Live.Base.E (Live.stateTrajectory (Live.support D)))
        (Live.Base.I (Live.stateTrajectory (Live.support D)))
        S)
      (O : Leray.RationalInverseNormOrder
        (Live.Base.E (Live.stateTrajectory (Live.support D)))
        (Live.Base.I (Live.stateTrajectory (Live.support D)))) : Set₁ where
    field
      cutoffIndependentEnergyCeiling : ℚ
      energyCeilingNN : 0ℚ ≤ cutoffIndependentEnergyCeiling

      pointwiseEnergyBound :
        (cutoff : Nat) (time : Time) →
        let module G = Pointwise.GlobalCommutatorPayment
              (Live.physicalSystemAt (Live.support D) cutoff time)
              S L O
        in
        R109.sumEnergy G.modalED G.modes
        ≤ cutoffIndependentEnergyCeiling

      cutoffIndependentDissipationBound : Time → ℚ
      integratedDissipationBound :
        (cutoff : Nat) (terminal : Time) →
        let
          dissipation : Time → ℚ
          dissipation time =
            let module G = Pointwise.GlobalCommutatorPayment
                  (Live.physicalSystemAt (Live.support D) cutoff time)
                  S L O
            in R109.sumDissipation G.modalED G.modes
        in
        integrateTo dissipation terminal
        ≤ cutoffIndependentDissipationBound terminal

  open PhysicalCommutatorSpacetimeEDData public

  globalCommutatorMassAt :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (L : Helical.PeriodicHelicalProjectorLaws
      F
      (Live.Base.E (Live.stateTrajectory (Live.support D)))
      (Live.Base.I (Live.stateTrajectory (Live.support D)))
      S) →
    (O : Leray.RationalInverseNormOrder
      (Live.Base.E (Live.stateTrajectory (Live.support D)))
      (Live.Base.I (Live.stateTrajectory (Live.support D)))) →
    Nat → Time → ℚ
  globalCommutatorMassAt D S L O cutoff time =
    let module G = Pointwise.GlobalCommutatorPayment
          (Live.physicalSystemAt (Live.support D) cutoff time)
          S L O
    in G.globalCommutatorComponentMass

  energyAt :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (L : Helical.PeriodicHelicalProjectorLaws
      F
      (Live.Base.E (Live.stateTrajectory (Live.support D)))
      (Live.Base.I (Live.stateTrajectory (Live.support D)))
      S) →
    (O : Leray.RationalInverseNormOrder
      (Live.Base.E (Live.stateTrajectory (Live.support D)))
      (Live.Base.I (Live.stateTrajectory (Live.support D)))) →
    Nat → Time → ℚ
  energyAt D S L O cutoff time =
    let module G = Pointwise.GlobalCommutatorPayment
          (Live.physicalSystemAt (Live.support D) cutoff time)
          S L O
    in R109.sumEnergy G.modalED G.modes

  dissipationAt :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (L : Helical.PeriodicHelicalProjectorLaws
      F
      (Live.Base.E (Live.stateTrajectory (Live.support D)))
      (Live.Base.I (Live.stateTrajectory (Live.support D)))
      S) →
    (O : Leray.RationalInverseNormOrder
      (Live.Base.E (Live.stateTrajectory (Live.support D)))
      (Live.Base.I (Live.stateTrajectory (Live.support D)))) →
    Nat → Time → ℚ
  dissipationAt D S L O cutoff time =
    let module G = Pointwise.GlobalCommutatorPayment
          (Live.physicalSystemAt (Live.support D) cutoff time)
          S L O
    in R109.sumDissipation G.modalED G.modes

  pointwiseMassBelowCeilingTimesDissipation :
    ∀ {D S L O} →
    (I : PhysicalCommutatorSpacetimeEDData D S L O) →
    (cutoff : Nat) (time : Time) →
    globalCommutatorMassAt D S L O cutoff time
    ≤ Pointwise.thirtySix
        * cutoffIndependentEnergyCeiling I
        * dissipationAt D S L O cutoff time
  pointwiseMassBelowCeilingTimesDissipation {D} {S} {L} {O}
      I cutoff time =
    let
      module G = Pointwise.GlobalCommutatorPayment
        (Live.physicalSystemAt (Live.support D) cutoff time)
        S L O

      base = G.globalCommutatorComponentMassBelowThirtySixED

      dissNN : 0ℚ ≤ R109.sumDissipation G.modalED G.modes
      dissNN = R109.sumDissipationNonnegative G.modalED G.modes

      scaledEnergy :
        R109.sumEnergy G.modalED G.modes
          * R109.sumDissipation G.modalED G.modes
        ≤ cutoffIndependentEnergyCeiling I
          * R109.sumDissipation G.modalED G.modes
      scaledEnergy =
        let instance dissNNI : NonNegative (R109.sumDissipation G.modalED G.modes)
            dissNNI = nonNegative dissNN
        in ℚP.*-monoʳ-≤-nonNeg
          (R109.sumDissipation G.modalED G.modes)
          (pointwiseEnergyBound I cutoff time)

      thirtySixNN : 0ℚ ≤ Pointwise.thirtySix
      thirtySixNN =
        Rational.productNonnegative
          (Rational.productNonnegative
            (Rational.productNonnegative
              Pointwise.R178.threeNN Pointwise.R178.threeNN)
            (Rational.addNonnegative Pointwise.R178.oneNN Pointwise.R178.oneNN))
          (Rational.addNonnegative Pointwise.R178.oneNN Pointwise.R178.oneNN)

      scaled =
        let instance thirtySixNNI : NonNegative Pointwise.thirtySix
            thirtySixNNI = nonNegative thirtySixNN
        in ℚP.*-monoˡ-≤-nonNeg Pointwise.thirtySix scaledEnergy
    in
    ℚP.≤-trans base scaled

  integratedGlobalCommutatorMassBound :
    ∀ {D S L O} →
    (I : PhysicalCommutatorSpacetimeEDData D S L O) →
    (cutoff : Nat) (terminal : Time) →
    integrateTo (globalCommutatorMassAt D S L O cutoff) terminal
    ≤ Pointwise.thirtySix
        * cutoffIndependentEnergyCeiling I
        * cutoffIndependentDissipationBound I terminal
  integratedGlobalCommutatorMassBound {D} {S} {L} {O}
      I cutoff terminal =
    let
      constant = Pointwise.thirtySix * cutoffIndependentEnergyCeiling I

      thirtySixNN : 0ℚ ≤ Pointwise.thirtySix
      thirtySixNN =
        Rational.productNonnegative
          (Rational.productNonnegative
            (Rational.productNonnegative
              Pointwise.R178.threeNN Pointwise.R178.threeNN)
            (Rational.addNonnegative Pointwise.R178.oneNN Pointwise.R178.oneNN))
          (Rational.addNonnegative Pointwise.R178.oneNN Pointwise.R178.oneNN)

      constantNN : 0ℚ ≤ constant
      constantNN =
        Rational.productNonnegative thirtySixNN (energyCeilingNN I)

      monotone =
        integrateMonotone integration
          (globalCommutatorMassAt D S L O cutoff)
          (λ time → constant * dissipationAt D S L O cutoff time)
          (pointwiseMassBelowCeilingTimesDissipation I cutoff)
          terminal

      scaledMeaning =
        integrateNonnegativeConstantScale integration
          constant constantNN
          (dissipationAt D S L O cutoff)
          terminal

      dissPaid =
        integratedDissipationBound I cutoff terminal

      finalScale =
        let instance constantNNI : NonNegative constant
            constantNNI = nonNegative constantNN
        in ℚP.*-monoˡ-≤-nonNeg constant dissPaid
    in
    ℚP.≤-trans
      monotone
      (subst
        (λ left →
          left
          ≤ Pointwise.thirtySix
              * cutoffIndependentEnergyCeiling I
              * cutoffIndependentDissipationBound I terminal)
        scaledMeaning
        finalScale)

roundCommutatorPointwiseThirtySixEDReused : Bool
roundCommutatorPointwiseThirtySixEDReused = true

roundCommutatorSpacetimeCompilerAddsCutoffFactor : Bool
roundCommutatorSpacetimeCompilerAddsCutoffFactor = false

roundCommutatorSpacetimeCompilerUsesCriticalBarrier : Bool
roundCommutatorSpacetimeCompilerUsesCriticalBarrier = false
