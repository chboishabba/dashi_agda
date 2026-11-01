{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650TriadOrbitSpacetimePaymentRound698Exact where

------------------------------------------------------------------------
-- ROUND698 / CLAY-FACING PAYMENT SHAPE FOR THE COMPLETE TRIAD-ORBIT RESIDUE
--
-- R697 proves exactly
--
--   IntegratedOrbitResidue_N(T) = 3 * C_N(T),
--
-- where C_N is the literal R691 globally summed coherent commutator.
--
-- Therefore the highest-value analytic theorem should be stated directly as
--
--   IntegratedOrbitResidue_N(T) <= 3 * B(T)
--
-- with B independent of N.  Positivity of 3 then cancels the fixed factor and
-- yields
--
--   C_N(T) <= B(T).
--
-- This owner performs only that compiler step.  It deliberately does NOT
-- identify C_N with the R568 forcing full-square or with literal R406; those
-- are different currencies and require the existing exact bridges.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

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
import DASHI.Physics.Closure.NSTriadKNR650IntegratedTriadOrbitResidueRound697Exact as R697
import DASHI.Physics.Closure.NSTriadKNR650MaskedCompleteTriadOrbitResidueRound696Exact as R696

F : C3.RealField _
F = Rational.rationalRealField

threePositive : 0ℚ < R696.three
threePositive =
  ℚP.positive⁻¹ R696.three

module OrbitPayment
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

  module Orbit = R697.IntegratedOrbit
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Balance = Orbit.Balance

  record CutoffUniformTriadOrbitSpacetimePayment : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      triadOrbitSpacetimePayment :
        (cutoff : Nat) (terminal : Time) →
        Orbit.integratedOrbitResidue cutoff terminal
        ≤ R696.three * cutoffIndependentBound terminal

  open CutoffUniformTriadOrbitSpacetimePayment public

  record CutoffUniformGlobalCommutatorPayment : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      globalCommutatorPayment :
        (cutoff : Nat) (terminal : Time) →
        Balance.globalIntegratedCommutator cutoff terminal
        ≤ cutoffIndependentBound terminal

  open CutoffUniformGlobalCommutatorPayment public

  orbitPaymentBuildsGlobalCommutatorPayment :
    CutoffUniformTriadOrbitSpacetimePayment →
    CutoffUniformGlobalCommutatorPayment
  orbitPaymentBuildsGlobalCommutatorPayment P = record
    { CutoffUniformGlobalCommutatorPayment.cutoffIndependentBound =
        CutoffUniformTriadOrbitSpacetimePayment.cutoffIndependentBound P
    ; CutoffUniformGlobalCommutatorPayment.globalCommutatorPayment =
        λ cutoff terminal →
          let
            comm = Balance.globalIntegratedCommutator cutoff terminal
            bound =
              CutoffUniformTriadOrbitSpacetimePayment.cutoffIndependentBound
                P terminal

            orbitUpper :
              Orbit.integratedOrbitResidue cutoff terminal
              ≤ R696.three * bound
            orbitUpper =
              triadOrbitSpacetimePayment P cutoff terminal

            threeCommUpper :
              R696.three * comm ≤ R696.three * bound
            threeCommUpper =
              subst
                (λ left → left ≤ R696.three * bound)
                (Orbit.integratedOrbitResidueIsThreeR691Commutator
                  cutoff terminal)
                orbitUpper
          in
          ℚP.*-cancelˡ-≤-pos
            R696.three threeCommUpper
    }

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round698ClayFacingAnalyticObjectIsIntegratedTriadOrbitResidue : Bool
round698ClayFacingAnalyticObjectIsIntegratedTriadOrbitResidue = true

round698OrbitPaymentUsesFixedFactorThreeWithoutDivision : Bool
round698OrbitPaymentUsesFixedFactorThreeWithoutDivision = true

round698OrbitPaymentCompilesToExactR691GlobalCommutatorCurrency : Bool
round698OrbitPaymentCompilesToExactR691GlobalCommutatorCurrency = true

round698OrbitPaymentDirectlyEqualsR568ForcingFullSquare : Bool
round698OrbitPaymentDirectlyEqualsR568ForcingFullSquare = false

round698OrbitPaymentDirectlyEqualsLiteralR406 : Bool
round698OrbitPaymentDirectlyEqualsLiteralR406 = false

round698IntroducesNSEstimate : Bool
round698IntroducesNSEstimate = false

round698CutoffUniformTriadOrbitSpacetimePaymentClosed : Bool
round698CutoffUniformTriadOrbitSpacetimePaymentClosed = false

round698ClayPromotion : Bool
round698ClayPromotion = false

round698ClayFacingAnalyticObjectIsIntegratedTriadOrbitResidueIsTrue :
  round698ClayFacingAnalyticObjectIsIntegratedTriadOrbitResidue ≡ true
round698ClayFacingAnalyticObjectIsIntegratedTriadOrbitResidueIsTrue = refl

round698OrbitPaymentUsesFixedFactorThreeWithoutDivisionIsTrue :
  round698OrbitPaymentUsesFixedFactorThreeWithoutDivision ≡ true
round698OrbitPaymentUsesFixedFactorThreeWithoutDivisionIsTrue = refl

round698OrbitPaymentCompilesToExactR691GlobalCommutatorCurrencyIsTrue :
  round698OrbitPaymentCompilesToExactR691GlobalCommutatorCurrency ≡ true
round698OrbitPaymentCompilesToExactR691GlobalCommutatorCurrencyIsTrue = refl

round698OrbitPaymentDirectlyEqualsR568ForcingFullSquareIsFalse :
  round698OrbitPaymentDirectlyEqualsR568ForcingFullSquare ≡ false
round698OrbitPaymentDirectlyEqualsR568ForcingFullSquareIsFalse = refl

round698OrbitPaymentDirectlyEqualsLiteralR406IsFalse :
  round698OrbitPaymentDirectlyEqualsLiteralR406 ≡ false
round698OrbitPaymentDirectlyEqualsLiteralR406IsFalse = refl

round698IntroducesNSEstimateIsFalse :
  round698IntroducesNSEstimate ≡ false
round698IntroducesNSEstimateIsFalse = refl

round698CutoffUniformTriadOrbitSpacetimePaymentClosedIsFalse :
  round698CutoffUniformTriadOrbitSpacetimePaymentClosed ≡ false
round698CutoffUniformTriadOrbitSpacetimePaymentClosedIsFalse = refl

round698ClayPromotionIsFalse :
  round698ClayPromotion ≡ false
round698ClayPromotionIsFalse = refl
