{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650WeightedEndpointToCombinedPaymentRound731Exact where

------------------------------------------------------------------------
-- ROUND731 / PRODUCER FOR R723 FROM R691 WEIGHTED WORK + TERMINAL MIXED MASS
--
-- R691 is exactly
--
--   Weighted_N = Commutator_N - (E_M,N(T) - E_M,N(0)).
--
-- Hence
--
--   Commutator_N = Weighted_N + E_M,N(T) - E_M,N(0)
--                <= Weighted_N + E_M,N(T),
--
-- because the initial mixed mass is nonnegative.
--
-- Therefore A/R723 can be produced from:
--
--   (i)  a cutoff-uniform payment of the global weighted/input-Laplacian work;
--   (ii) a cutoff-uniform ceiling for the TERMINAL coherent mixed mass.
--
-- This is the exact dual of R699, which used terminal nonnegativity in the
-- opposite direction to derive Weighted <= Commutator + initial mass.
--
-- The result is useful because it exposes the only endpoint obstruction on this
-- producer route: the coherent terminal mixed mass.  The existing positive
-- sum-of-cell-masses theorem does not automatically control this coherent mass.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
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
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyEndpointUpperRound699Exact as R699
import DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact as R723
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700

F : C3.RealField _
F = Rational.rationalRealField

twelveNN : 0ℚ ≤ R700.twelve
twelveNN =
  let
    oneNN = Rational.squareNonnegative 1ℚ
    twoNN = Rational.addNonnegative oneNN oneNN
    fourNN = Rational.addNonnegative twoNN twoNN
    sixNN = Rational.addNonnegative fourNN twoNN
  in
  Rational.addNonnegative sixNN sixNN

module WeightedEndpointProducer
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

  module Upper = R699.EndpointUpper
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Combined = R723.CombinedSpacetime
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Balance = Upper.Balance

  record CutoffUniformTerminalMixedMassCeiling : Set₁ where
    field
      terminalMixedMassBound : Time → ℚ
      terminalMixedMassCeiling :
        (cutoff : Nat) (terminal : Time) →
        Upper.globalSelfEnergy cutoff terminal
        ≤ terminalMixedMassBound terminal

  open CutoffUniformTerminalMixedMassCeiling public

  globalCommutatorBelowWeightedPlusTerminal :
    (cutoff : Nat) (terminal : Time) →
    Balance.globalIntegratedCommutator cutoff terminal
    ≤
    Balance.globalIntegratedWeighted cutoff terminal
      + Upper.globalSelfEnergy cutoff terminal
  globalCommutatorBelowWeightedPlusTerminal cutoff terminal =
    let
      weighted = Balance.globalIntegratedWeighted cutoff terminal
      comm = Balance.globalIntegratedCommutator cutoff terminal
      terminalMass = Upper.globalSelfEnergy cutoff terminal
      initialMass = Upper.globalSelfEnergy cutoff initialTime

      exact :
        weighted ≡ comm - (terminalMass - initialMass)
      exact =
        trans
          (Balance.globalMixedEnergyBalance cutoff terminal)
          (subst
            (λ endpoint →
              weighted ≡ comm - endpoint)
            (Upper.globalEndpointDeltaIsTerminalMinusInitial cutoff terminal)
            refl)

      initialNN : 0ℚ ≤ initialMass
      initialNN =
        Upper.sumSelfEnergyNonnegative
          cutoff initialTime
          (Canonical.nonzeroCutoffModes cutoff)

      shiftedExact :
        weighted + terminalMass - initialMass
        ≡
        (comm - (terminalMass - initialMass))
          + terminalMass - initialMass
      shiftedExact =
        cong
          (λ w → w + terminalMass - initialMass)
          exact

      rhsNormal :
        (comm - (terminalMass - initialMass))
          + terminalMass - initialMass
        ≡ comm
      rhsNormal =
        solve (comm ∷ terminalMass ∷ initialMass ∷ [])

      rearranged :
        comm ≡ weighted + terminalMass - initialMass
      rearranged =
        sym (trans shiftedExact rhsNormal)

      upper :
        weighted + terminalMass - initialMass
        ≤ weighted + terminalMass
      upper =
        Rational.subtractNonnegativeBelow
          (weighted + terminalMass) initialMass initialNN
    in
    subst
      (_≤ weighted + terminalMass)
      (sym rearranged)
      upper

  weightedAndTerminalBuildCombinedPayment :
    Upper.CutoffUniformGlobalWeightedPayment →
    CutoffUniformTerminalMixedMassCeiling →
    Combined.CutoffUniformCombinedSelfExternalPayment
  weightedAndTerminalBuildCombinedPayment W E = record
    { Combined.cutoffIndependentBound =
        λ terminal →
          Upper.cutoffIndependentBound W terminal
            + terminalMixedMassBound E terminal
    ; Combined.combinedSelfExternalPayment =
        λ cutoff terminal →
          let
            commUpper :
              Balance.globalIntegratedCommutator cutoff terminal
              ≤
              Upper.cutoffIndependentBound W terminal
                + terminalMixedMassBound E terminal
            commUpper =
              ℚP.≤-trans
                (globalCommutatorBelowWeightedPlusTerminal cutoff terminal)
                (ℚP.+-mono-≤
                  (Upper.globalWeightedPayment W cutoff terminal)
                  (terminalMixedMassCeiling E cutoff terminal))

            scaled :
              R700.twelve
                * Balance.globalIntegratedCommutator cutoff terminal
              ≤
              R700.twelve
                * (Upper.cutoffIndependentBound W terminal
                    + terminalMixedMassBound E terminal)
            scaled =
              let instance twelveNNI = nonNegative twelveNN
              in ℚP.*-monoˡ-≤-nonNeg R700.twelve commUpper
          in
          subst
            (λ left →
              left
              ≤
              R700.twelve
                * (Upper.cutoffIndependentBound W terminal
                    + terminalMixedMassBound E terminal))
            (sym
              (Combined.integratedCombinedIsTwelveR691Commutator
                cutoff terminal))
            scaled
    }

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round731R691DualEndpointUpperClosed : Bool
round731R691DualEndpointUpperClosed = true

round731WeightedPlusTerminalMassBuildsR723CombinedPayment : Bool
round731WeightedPlusTerminalMassBuildsR723CombinedPayment = true

round731TerminalMixedMassCeilingClosed : Bool
round731TerminalMixedMassCeilingClosed = false

round731GlobalWeightedPaymentClosed : Bool
round731GlobalWeightedPaymentClosed = false

round731PositiveCellMassAutomaticallyPaysCoherentTerminalMass : Bool
round731PositiveCellMassAutomaticallyPaysCoherentTerminalMass = false

round731IntroducesEstimate : Bool
round731IntroducesEstimate = false

round731ClayPromotion : Bool
round731ClayPromotion = false

round731R691DualEndpointUpperClosedIsTrue :
  round731R691DualEndpointUpperClosed ≡ true
round731R691DualEndpointUpperClosedIsTrue = refl

round731WeightedPlusTerminalMassBuildsR723CombinedPaymentIsTrue :
  round731WeightedPlusTerminalMassBuildsR723CombinedPayment ≡ true
round731WeightedPlusTerminalMassBuildsR723CombinedPaymentIsTrue = refl

round731TerminalMixedMassCeilingClosedIsFalse :
  round731TerminalMixedMassCeilingClosed ≡ false
round731TerminalMixedMassCeilingClosedIsFalse = refl

round731GlobalWeightedPaymentClosedIsFalse :
  round731GlobalWeightedPaymentClosed ≡ false
round731GlobalWeightedPaymentClosedIsFalse = refl

round731PositiveCellMassAutomaticallyPaysCoherentTerminalMassIsFalse :
  round731PositiveCellMassAutomaticallyPaysCoherentTerminalMass ≡ false
round731PositiveCellMassAutomaticallyPaysCoherentTerminalMassIsFalse = refl

round731IntroducesEstimateIsFalse :
  round731IntroducesEstimate ≡ false
round731IntroducesEstimateIsFalse = refl

round731ClayPromotionIsFalse :
  round731ClayPromotion ≡ false
round731ClayPromotionIsFalse = refl
