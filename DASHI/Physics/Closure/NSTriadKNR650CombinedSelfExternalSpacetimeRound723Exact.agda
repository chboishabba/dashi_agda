{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact where

------------------------------------------------------------------------
-- ROUND723 / THE RECOMBINED SELF+EXTERNAL RESIDUE IS THE ONE R691
--            SPACETIME COMMUTATOR PAYMENT
--
-- R722 is instantaneous and exact:
--
--   CombinedSelfExternal_N(t)
--     = CompleteNestedOrbit_N(t)
--     = 12 * GlobalCommutator_N(t).
--
-- R701 already transports the literal complete nested orbit through the live
-- R408 trajectory and the repository's integration authority.  This owner
-- makes the R722 recombination itself a first-class spacetime payment surface:
--
--   integral CombinedSelfExternal_N(t) dt
--     = 12 * R691.globalIntegratedCommutator_N(T).
--
-- Consequently a cutoff-uniform bound on the COMBINED signed self+external
-- residue builds the exact R691 global commutator payment.  No separate self
-- cancellation theorem and no separate external estimate are prerequisites.
--
-- This does NOT identify the R691 currency with the unlifted R568 forcing
-- square. R687 proves only the pair-rate-lifted bridge, and the unlifted ->
-- lifted quantitative implication remains explicitly open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNR650RateLiftedR568ToC2CommutatorRound687Exact as R687
import DASHI.Physics.Closure.NSTriadKNR650IntegratedNestedFourHelicityOrbitRound701Exact as R701
import DASHI.Physics.Closure.NSTriadKNR650SelfExternalRecombinationRound722Exact as R722
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700

F : C3.RealField _
F = Rational.rationalRealField

module CombinedSpacetime
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (scalarScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module Nested = R701.IntegratedNestedOrbit
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Balance = Nested.Balance

  module At
      (cutoff : Nat)
      (time : Time) where

    module N = Nested.At cutoff time

    module R = R722.Recombine
      N.physicalSystem
      Nested.S
      Nested.L
      Nested.H
      N.allModeTransverse

    combinedSelfExternalResidue : ℚ
    combinedSelfExternalResidue =
      R.combinedSelfExternalResidue

    literalNestedOrbitResidue : ℚ
    literalNestedOrbitResidue =
      N.nestedOrbitResidue

    combinedIsLiteralNestedOrbit :
      combinedSelfExternalResidue
      ≡ literalNestedOrbitResidue
    combinedIsLiteralNestedOrbit =
      R.combinedSelfExternalIsCompleteNestedOrbit

    combinedIsTwelveLiveGlobalCommutator :
      combinedSelfExternalResidue
      ≡
      R700.twelve *
        Nested.Orbit.sumCommutatorAt cutoff
          (Canonical.nonzeroCutoffModes cutoff)
          time
    combinedIsTwelveLiveGlobalCommutator =
      trans
        combinedIsLiteralNestedOrbit
        N.nestedOrbitResidueIsTwelveLiveCommutator

  combinedResidueAt :
    Nat → Time → ℚ
  combinedResidueAt cutoff time =
    At.combinedSelfExternalResidue cutoff time

  integratedCombinedSelfExternal :
    Nat → Time → ℚ
  integratedCombinedSelfExternal cutoff terminal =
    integrateTo (combinedResidueAt cutoff) terminal

  integratedCombinedIsIntegratedNested :
    (cutoff : Nat) (terminal : Time) →
    integratedCombinedSelfExternal cutoff terminal
    ≡ Nested.integratedNestedOrbitResidue cutoff terminal
  integratedCombinedIsIntegratedNested cutoff terminal =
    Energy.integrationCongruent integrationLinearity
      (At.combinedIsLiteralNestedOrbit cutoff)
      terminal

  integratedCombinedIsTwelveR691Commutator :
    (cutoff : Nat) (terminal : Time) →
    integratedCombinedSelfExternal cutoff terminal
    ≡
    R700.twelve *
      Balance.globalIntegratedCommutator cutoff terminal
  integratedCombinedIsTwelveR691Commutator cutoff terminal =
    trans
      (integratedCombinedIsIntegratedNested cutoff terminal)
      (Nested.integratedNestedOrbitResidueIsTwelveR691Commutator
        cutoff terminal)

  record CutoffUniformCombinedSelfExternalPayment : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      combinedSelfExternalPayment :
        (cutoff : Nat) (terminal : Time) →
        integratedCombinedSelfExternal cutoff terminal
        ≤ R700.twelve * cutoffIndependentBound terminal

  open CutoffUniformCombinedSelfExternalPayment public

  combinedPaymentBuildsNestedOrbitPayment :
    CutoffUniformCombinedSelfExternalPayment →
    Nested.CutoffUniformNestedFourHelicityOrbitPayment
  combinedPaymentBuildsNestedOrbitPayment P = record
    { cutoffIndependentBound =
        CutoffUniformCombinedSelfExternalPayment.cutoffIndependentBound P
    ; nestedOrbitSpacetimePayment =
        λ cutoff terminal →
          subst
            (λ left →
              left
              ≤ R700.twelve *
                  CutoffUniformCombinedSelfExternalPayment.cutoffIndependentBound
                    P terminal)
            (integratedCombinedIsIntegratedNested cutoff terminal)
            (combinedSelfExternalPayment P cutoff terminal)
    }

  combinedPaymentBuildsR691GlobalCommutatorPayment :
    CutoffUniformCombinedSelfExternalPayment →
    Nested.CutoffUniformGlobalCommutatorPayment
  combinedPaymentBuildsR691GlobalCommutatorPayment P =
    Nested.nestedOrbitPaymentBuildsR691GlobalCommutatorPayment
      (combinedPaymentBuildsNestedOrbitPayment P)

------------------------------------------------------------------------
-- Trust / routing boundary.
------------------------------------------------------------------------

round723CombinedSelfExternalIntegratedBeforeEstimate : Bool
round723CombinedSelfExternalIntegratedBeforeEstimate = true

round723IntegratedCombinedIsTwelveR691Commutator : Bool
round723IntegratedCombinedIsTwelveR691Commutator = true

round723CombinedPaymentBuildsR691GlobalCommutatorPayment : Bool
round723CombinedPaymentBuildsR691GlobalCommutatorPayment = true

round723SeparateSelfCancellationAnalyticLeaf : Bool
round723SeparateSelfCancellationAnalyticLeaf = false

round723SeparateExternalAnalyticLeaf : Bool
round723SeparateExternalAnalyticLeaf = false

round723UnliftedR568BudgetAutomaticallyPaysR691Commutator : Bool
round723UnliftedR568BudgetAutomaticallyPaysR691Commutator =
  R687.round687UnliftedR568BudgetControlsRateLiftedFull

round723CombinedCutoffUniformPaymentClosed : Bool
round723CombinedCutoffUniformPaymentClosed = false

round723IntroducesEstimate : Bool
round723IntroducesEstimate = false

round723ClayPromotion : Bool
round723ClayPromotion = false

round723CombinedSelfExternalIntegratedBeforeEstimateIsTrue :
  round723CombinedSelfExternalIntegratedBeforeEstimate ≡ true
round723CombinedSelfExternalIntegratedBeforeEstimateIsTrue = refl

round723IntegratedCombinedIsTwelveR691CommutatorIsTrue :
  round723IntegratedCombinedIsTwelveR691Commutator ≡ true
round723IntegratedCombinedIsTwelveR691CommutatorIsTrue = refl

round723CombinedPaymentBuildsR691GlobalCommutatorPaymentIsTrue :
  round723CombinedPaymentBuildsR691GlobalCommutatorPayment ≡ true
round723CombinedPaymentBuildsR691GlobalCommutatorPaymentIsTrue = refl

round723SeparateSelfCancellationAnalyticLeafIsFalse :
  round723SeparateSelfCancellationAnalyticLeaf ≡ false
round723SeparateSelfCancellationAnalyticLeafIsFalse = refl

round723SeparateExternalAnalyticLeafIsFalse :
  round723SeparateExternalAnalyticLeaf ≡ false
round723SeparateExternalAnalyticLeafIsFalse = refl

round723UnliftedR568BudgetAutomaticallyPaysR691CommutatorIsFalse :
  round723UnliftedR568BudgetAutomaticallyPaysR691Commutator ≡ false
round723UnliftedR568BudgetAutomaticallyPaysR691CommutatorIsFalse =
  R687.round687UnliftedR568BudgetControlsRateLiftedFullIsFalse

round723CombinedCutoffUniformPaymentClosedIsFalse :
  round723CombinedCutoffUniformPaymentClosed ≡ false
round723CombinedCutoffUniformPaymentClosedIsFalse = refl

round723IntroducesEstimateIsFalse :
  round723IntroducesEstimate ≡ false
round723IntroducesEstimateIsFalse = refl

round723ClayPromotionIsFalse :
  round723ClayPromotion ≡ false
round723ClayPromotionIsFalse = refl
