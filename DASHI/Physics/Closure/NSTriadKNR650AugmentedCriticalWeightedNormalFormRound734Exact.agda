{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact where

------------------------------------------------------------------------
-- ROUND734 / DIRECT LEAF D AS AUGMENTED CRITICAL ENERGY <= WEIGHTED WORK
--
-- R730's Pareto leaf is
--
--   X_N(T) - X_N(0) + delta D_N(T)
--     <= IntegratedCombined_N(T).
--
-- R723 and R691 give exactly
--
--   IntegratedCombined_N(T)
--     = 12 * C_N(T)
--     = 12 * [ W_N(T) + E_M,N(T) - E_M,N(0) ].
--
-- Hence R730 is equivalent to
--
--   [X_N(T) - 12 E_M,N(T)]
--     - [X_N(0) - 12 E_M,N(0)]
--     + delta D_N(T)
--   <= 12 W_N(T).
--
-- This is the preferred analytic normal form for D: the quintic commutator has
-- disappeared from the target.  R684 identifies the instantaneous weighted
-- scalar W with viscosity times one input-Laplacian coherent work, so theorem
-- search may stay on that signed quartic carrier.
--
-- 2026-10-27 SOURCE-SPECIFIC PHYSICAL NEGATIVE CONTROL (NO CLAY CLAIM):
-- On a real smooth six-mode, pure-positive-helicity velocity (all H- modes
-- zero initially), M(0)=0 and integrated weighted W'(0)=0, yet the
-- same literal dyadic critical production is
-- Pcrit=(5+sqrt(5)-sqrt(30))/10>0; Xcrit=8, Dcrit=36.
-- Scaling the *actual* physical Fourier velocity by 512 with nu=1 gives
-- Xcrit'(0)=512^2(512 Pcrit -72)>0. Consequently the sought R734
-- inequality with ANY retained margin delta>0 is false on a sufficiently
-- short initial interval of the actual projected finite Galerkin ODE.
-- The record below is a CONDITIONAL compiler, not an unproved universal
-- theorem awaiting only routine constants. Preserve original conditional
-- algebra and the historical positive-proof status flags as false.
-- Exact symbolic/real-helical acceptance: tests/test_ns_r734_pure_plus_physical_w2_no_go.py
-- Details/credit: Docs/research/ns_r734_pure_plus_physical_w2_no_go_20261027.md
-- Crucial PRIOR-ART REUSE: Waleffe's true signed-helicity invariant
-- (R92/R102) uses the exact curl eigenvalue +/-|k|, NOT R734's
-- rounded-up dyadic weight 2^ceil(log2 ||k||infty). On the SAME
-- pure-plus counterexample, exact-helicity nonlinear production is
-- zero, while dyadic-weighted production is >0: the difference
-- is the exact signed weight-defect sum
--    2 Re Σ_k [dyadicWeight(k)-|k|] <u_k, PNSnonlin(u)_k>.
-- Norm equivalence does not imply derivative/sign equivalence.
-- A viable replacement analytical target must control this defect
-- together with physical same-helicity and mixed-helicity channels.
-- The full real-analytic Galerkin witness is NOT kernel formalised here.
--
-- 2026-10-27 PHYSICAL CRITICAL SMALL-DATA COMPANION (NOT THE W2 LEAF):
-- For the SAME sharp cube weight w(k)=2^ceil(log2 ||k||infty), the full
-- unforced mean-zero Fourier Galerkin trajectory satisfies
--   X'_N + 2 nu D_N = P_N,
--   |P_N| <= Ccrit sqrt(X_N) D_N,
--   Ccrit=4*3^(3/4)*C6*C3.
-- Here C6,C3 are the FIXED periodic H1->L6 and H3/2->W1,3
-- Sobolev constants; r/sqrt(3)<=w(k)<2r for r=|k|2.
-- This classical Fujita--Kato critical-small-data consequence yields
--   X_N(T) + (2nu-Ccrit sqrt(X_N(0))) int_0^T D_N <= X_N(0)
-- ONLY WHEN  Ccrit sqrt(X_N(0))<2nu.
-- Furthermore arbitrary E0>0 eventually enters X<=nu²/Ccrit²
-- at common t_enter=1/nu+max(0,log(sqrt(2)*Ccrit²*E0/nu²)/(2nu)).
-- Then X_N(T)+nu int_t_enter^T D_N <= nu²/Ccrit².
-- These are analytical physical-source derivations recorded at:
--   Docs/research/ns_r734_critical_small_data_dyadic_20261027.md
-- with seven local arithmetic tests in test_ns_r734_critical_small_data.py.
-- They do NOT establish the ORIGINAL signed W2 bound involving 12 C_N,
-- do NOT pay the arbitrary-large-data [0,t_enter] middle interval,
-- and are NOT Agda kernel-proved by this rational polynomial module.
-- Original Fujita--Kato ownership, classical embeddings and exact
-- original source-vs-code distinctions must be preserved.
--
-- No estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact as R723
import DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyEndpointUpperRound699Exact as R699
import DASHI.Physics.Closure.NSTriadKNR650DirectCombinedCriticalGrowthRound730Exact as R730
import DASHI.Physics.Closure.NSTriadKNR650RateKernelInputLaplacianCollapseRound684Exact as R684

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- SOURCE-WRITTEN R734 POLARIZATION / WEIGHT-DEFECT IDENTITY
--
-- Original roots: Waleffe helical signed conservation, already compiled
-- by DASHI R92/R102. The original R734 weight is DYADIC, not |k|.
-- For ANY real weight w, exact curl radius r, plus energy ep and
-- minus energy em:
--   w(ep+em) = r(ep-em) + 2*r*em + (w-r)(ep+em).
-- As a polynomial identity this is generic ℚ ring algebra.
-- Applied physically it says dyadic critical energy = exact signed
-- helicity + twice the negative-helicity mass + weight defect.
-- The physical square root, helical projectors, PDE derivative and
-- nonlinear bound are NOT supplied by this rational polynomial lemma.
------------------------------------------------------------------------

dyadicCriticalEnergyAsSignedHelicityPlusNegativeAndDefect :
  (w radius plusMass minusMass : ℚ) →
  w * (plusMass + minusMass)
  ≡ radius * (plusMass - minusMass)
    + ((1ℚ + 1ℚ) * radius) * minusMass
    + (w - radius) * (plusMass + minusMass)
dyadicCriticalEnergyAsSignedHelicityPlusNegativeAndDefect
    w radius plusMass minusMass =
  solve (w ∷ radius ∷ plusMass ∷ minusMass ∷ [])

------------------------------------------------------------------------
-- R734 / R92 EXACT WALEFFE-TRIAD WEIGHT CURVATURE (2026-10-27)
--
-- Original triad conservation roots: Waleffe (1992); inherited R92/R102.
-- Source-specific witness: tests/test_ns_r734_phase_curvature.py.
-- For an ordered positive-helicity triad with radial frequencies a<b<c,
-- modal paired transfers are A*(b-c,c-a,a-b). The following RATIONAL
-- polynomial identities do not claim that the original physical |k|
-- square roots, Galerkin nonlinear force, or A are inhabited by this
-- rational carrier. They DO preserve exact algebra and avoid importing
-- false universal R734 W2 positivity.
--
-- Weighted production is A times a spectral secant-slope difference:
-- ((b-c)wp+(c-a)wq+(a-b)wk)
--    = (c-b)(wq-wp) - (b-a)(wk-wq).
-- There is no division by an unproved spectral gap in this certificate.
------------------------------------------------------------------------

waleffeTriadEnergyTransferCyclicZero :
  (small middle large : ℚ) →
  ((middle - large) + (large - small)) + (small - middle) ≡ 0ℚ
waleffeTriadEnergyTransferCyclicZero small middle large =
  solve (small ∷ middle ∷ large ∷ [])

waleffeTriadExactRadiusTransferCyclicZero :
  (small middle large : ℚ) →
  ((small * (middle - large)) + (middle * (large - small)))
     + (large * (small - middle)) ≡ 0ℚ
waleffeTriadExactRadiusTransferCyclicZero small middle large =
  solve (small ∷ middle ∷ large ∷ [])

weightedTriadProductionAsSecantNumerator :
  (amplitude small middle large lowWeight middleWeight highWeight : ℚ) →
  amplitude *
    (((middle - large) * lowWeight +
       (large - small) * middleWeight) +
       (small - middle) * highWeight)
  ≡ amplitude *
    ((large - middle) * (middleWeight - lowWeight) -
     (middle - small) * (highWeight - middleWeight))
weightedTriadProductionAsSecantNumerator
    amplitude small middle large lowWeight middleWeight highWeight =
  solve (amplitude ∷ small ∷ middle ∷ large ∷ lowWeight ∷ middleWeight ∷ highWeight ∷ [])

module AugmentedWeighted
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
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where

  module Direct = R730.DirectCombinedGrowth
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Upper = R699.EndpointUpper
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Balance = Upper.Balance
  module Combined = Direct.Combined
  module Obs = Direct.Obs
  module Growth = Direct.Growth

  T = Direct.T

  augmentedCriticalEnergy :
    Nat → Time → ℚ
  augmentedCriticalEnergy cutoff time =
    Obs.criticalEnergyAt T cutoff time
      - R700.twelve * Upper.globalSelfEnergy cutoff time

  augmentedCriticalGrowthWithMargin :
    Nat → ℚ → Time → ℚ
  augmentedCriticalGrowthWithMargin cutoff margin terminal =
    augmentedCriticalEnergy cutoff terminal
      - augmentedCriticalEnergy cutoff initialTime
      + margin * Obs.integratedCriticalDissipation T cutoff terminal

  combinedAsTwelveWeightedPlusEndpoint :
    (cutoff : Nat) (terminal : Time) →
    Combined.integratedCombinedSelfExternal cutoff terminal
    ≡
    R700.twelve *
      ( Balance.globalIntegratedWeighted cutoff terminal
      + Upper.globalSelfEnergy cutoff terminal
      - Upper.globalSelfEnergy cutoff initialTime )
  combinedAsTwelveWeightedPlusEndpoint cutoff terminal =
    let
      weighted = Balance.globalIntegratedWeighted cutoff terminal
      comm = Balance.globalIntegratedCommutator cutoff terminal
      eT = Upper.globalSelfEnergy cutoff terminal
      e0 = Upper.globalSelfEnergy cutoff initialTime

      combinedToComm =
        Combined.integratedCombinedIsTwelveR691Commutator cutoff terminal

      balance =
        Balance.globalMixedEnergyBalance cutoff terminal

      endpoint =
        Upper.globalEndpointDeltaIsTerminalMinusInitial cutoff terminal

      commMeaning :
        comm ≡ weighted + (eT - e0)
      commMeaning =
        let
          first :
            weighted ≡ comm - (eT - e0)
          first =
            subst
              (λ delta → weighted ≡ comm - delta)
              endpoint
              balance

          shifted :
            weighted + (eT - e0)
            ≡ (comm - (eT - e0)) + (eT - e0)
          shifted =
            cong (_+ (eT - e0)) first

          rhsNormal :
            (comm - (eT - e0)) + (eT - e0) ≡ comm
          rhsNormal =
            solve (comm ∷ eT ∷ e0 ∷ [])
        in
        sym (trans shifted rhsNormal)
    in
    trans
      combinedToComm
      (trans
        (cong (R700.twelve *_) commMeaning)
        (solve
          ( R700.twelve
          ∷ weighted
          ∷ eT
          ∷ e0
          ∷ [])))

  directGrowthMinusEndpointIsAugmentedGrowth :
    (cutoff : Nat) (margin : ℚ) (terminal : Time) →
    Growth.criticalEnergyGrowthWithMargin D cutoff margin terminal
      - R700.twelve *
          ( Upper.globalSelfEnergy cutoff terminal
          - Upper.globalSelfEnergy cutoff initialTime )
    ≡ augmentedCriticalGrowthWithMargin cutoff margin terminal
  directGrowthMinusEndpointIsAugmentedGrowth cutoff margin terminal =
    solve
      ( Obs.criticalEnergyAt T cutoff terminal
      ∷ Obs.criticalEnergyAt T cutoff initialTime
      ∷ Upper.globalSelfEnergy cutoff terminal
      ∷ Upper.globalSelfEnergy cutoff initialTime
      ∷ margin
      ∷ Obs.integratedCriticalDissipation T cutoff terminal
      ∷ R700.twelve
      ∷ [])

  record AugmentedCriticalWeightedPayment
      (cutoff : Nat)
      (terminal : Time) : Set where
    field
      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin
      augmentedGrowthPaidByWeighted :
        augmentedCriticalGrowthWithMargin cutoff retainedMargin terminal
        ≤ R700.twelve * Balance.globalIntegratedWeighted cutoff terminal

  open AugmentedCriticalWeightedPayment public

  directBuildsAugmented :
    (cutoff : Nat) (terminal : Time) →
    Direct.DirectCombinedCriticalGrowthPayment cutoff terminal →
    AugmentedCriticalWeightedPayment cutoff terminal
  directBuildsAugmented cutoff terminal P = record
    { retainedMargin = Direct.retainedMargin P
    ; retainedMarginPositive = Direct.retainedMarginPositive P
    ; augmentedGrowthPaidByWeighted =
        let
          margin = Direct.retainedMargin P
          growth =
            Growth.criticalEnergyGrowthWithMargin
              D cutoff margin terminal
          weighted = Balance.globalIntegratedWeighted cutoff terminal
          eT = Upper.globalSelfEnergy cutoff terminal
          e0 = Upper.globalSelfEnergy cutoff initialTime

          direct :
            growth ≤ Combined.integratedCombinedSelfExternal cutoff terminal
          direct = Direct.criticalGrowthPaidByCombined P

          combinedMeaning =
            combinedAsTwelveWeightedPlusEndpoint cutoff terminal

          exposed :
            growth
            ≤ R700.twelve * (weighted + eT - e0)
          exposed =
            subst
              (growth ≤_)
              combinedMeaning
              direct

          shifted :
            growth - R700.twelve * (eT - e0)
            ≤
            R700.twelve * (weighted + eT - e0)
              - R700.twelve * (eT - e0)
          shifted =
            ℚP.+-mono-≤ exposed ℚP.≤-refl

          normalized :
            growth - R700.twelve * (eT - e0)
            ≤ R700.twelve * weighted
          normalized =
            subst
              (λ rhs →
                growth - R700.twelve * (eT - e0) ≤ rhs)
              (solve (R700.twelve ∷ weighted ∷ eT ∷ e0 ∷ []))
              shifted
        in
        subst
          (λ lhs → lhs ≤ R700.twelve * weighted)
          (sym
            (directGrowthMinusEndpointIsAugmentedGrowth
              cutoff margin terminal))
          normalized
    }

  augmentedBuildsDirect :
    (cutoff : Nat) (terminal : Time) →
    AugmentedCriticalWeightedPayment cutoff terminal →
    Direct.DirectCombinedCriticalGrowthPayment cutoff terminal
  augmentedBuildsDirect cutoff terminal P = record
    { Direct.retainedMargin = retainedMargin P
    ; Direct.retainedMarginPositive = retainedMarginPositive P
    ; Direct.criticalGrowthPaidByCombined =
        let
          margin = retainedMargin P
          growth =
            Growth.criticalEnergyGrowthWithMargin
              D cutoff margin terminal
          weighted = Balance.globalIntegratedWeighted cutoff terminal
          eT = Upper.globalSelfEnergy cutoff terminal
          e0 = Upper.globalSelfEnergy cutoff initialTime

          aug :
            augmentedCriticalGrowthWithMargin cutoff margin terminal
            ≤ R700.twelve * weighted
          aug = augmentedGrowthPaidByWeighted P

          unshifted :
            growth
            ≤ R700.twelve * (weighted + eT - e0)
          unshifted =
            let
              exposed :
                growth - R700.twelve * (eT - e0)
                ≤ R700.twelve * weighted
              exposed =
                subst
                  (λ lhs → lhs ≤ R700.twelve * weighted)
                  (directGrowthMinusEndpointIsAugmentedGrowth
                    cutoff margin terminal)
                  aug

              shifted =
                ℚP.+-mono-≤ exposed ℚP.≤-refl
            in
            subst
              (λ lhs →
                lhs ≤
                  R700.twelve * weighted
                    + R700.twelve * (eT - e0))
              (solve (growth ∷ R700.twelve ∷ eT ∷ e0 ∷ []))
              (subst
                (λ rhs →
                  (growth - R700.twelve * (eT - e0))
                    + R700.twelve * (eT - e0)
                  ≤ rhs)
                (solve (R700.twelve ∷ weighted ∷ eT ∷ e0 ∷ []))
                shifted)
        in
        subst
          (growth ≤_)
          (sym (combinedAsTwelveWeightedPlusEndpoint cutoff terminal))
          unshifted
    }

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round734DirectLeafEquivalentToAugmentedWeightedPayment : Bool
round734DirectLeafEquivalentToAugmentedWeightedPayment = true

round734QuinticCommutatorAbsentFromPreferredDTarget : Bool
round734QuinticCommutatorAbsentFromPreferredDTarget = true

round734WeightedCarrierHasInputLaplacianNormalForm : Bool
round734WeightedCarrierHasInputLaplacianNormalForm =
  R684.round684PhysicalRateKernelIsInputLaplacianWork

round734AugmentedWeightedPaymentClosed : Bool
round734AugmentedWeightedPaymentClosed = false

round734IntroducesEstimate : Bool
round734IntroducesEstimate = false

round734ClayPromotion : Bool
round734ClayPromotion = false

round734DirectLeafEquivalentToAugmentedWeightedPaymentIsTrue :
  round734DirectLeafEquivalentToAugmentedWeightedPayment ≡ true
round734DirectLeafEquivalentToAugmentedWeightedPaymentIsTrue = refl

round734QuinticCommutatorAbsentFromPreferredDTargetIsTrue :
  round734QuinticCommutatorAbsentFromPreferredDTarget ≡ true
round734QuinticCommutatorAbsentFromPreferredDTargetIsTrue = refl

round734WeightedCarrierHasInputLaplacianNormalFormIsTrue :
  round734WeightedCarrierHasInputLaplacianNormalForm ≡ true
round734WeightedCarrierHasInputLaplacianNormalFormIsTrue =
  R684.round684PhysicalRateKernelIsInputLaplacianWorkIsTrue

round734AugmentedWeightedPaymentClosedIsFalse :
  round734AugmentedWeightedPaymentClosed ≡ false
round734AugmentedWeightedPaymentClosedIsFalse = refl

round734IntroducesEstimateIsFalse :
  round734IntroducesEstimate ≡ false
round734IntroducesEstimateIsFalse = refl

round734ClayPromotionIsFalse :
  round734ClayPromotion ≡ false
round734ClayPromotionIsFalse = refl
