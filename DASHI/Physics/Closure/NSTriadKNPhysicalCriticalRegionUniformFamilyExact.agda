module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionUniformFamilyExact where

------------------------------------------------------------------------
-- PERIODIC B / NATIVE UNIFORM FAMILY FOR THE LITERAL R236 d1b2 PAYMENT
--
-- This bypasses the historical R284/R435 scalar decomposition.
--
-- For each retained output k, a producer supplies the literal physical R236
-- payment P_k together with ONE common theta and ONE common ED coefficient C:
--
--   theta(P_k) = theta < 1,
--   deepBudget(P_k) + coreEDBudget(P_k) <= C * ED_k.
--
-- The local ED charge is tied to the actual physical output fibre and one
-- Boolean selected-pair kernel.  Finite output summation then gives
--
--   sum_k Cov_k
--     <= theta * sum_k [nu Q_k]
--       + (nu C) * sum_k ED_k,
--
-- and R469/R219 pay the final ED sum by the global selected-pair E*D currency
-- with no output-cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109
import DASHI.Physics.Closure.NSTriadKNSelectedPairPhysicalTriadRoutingRound469Exact as R469
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as RegionPay

F : C3.RealField _
F = Rational.rationalRealField

module UniformFamily
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (theta coefficient : ℚ)
    (select : Z3.FourierMode → Z3.FourierMode → Bool) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocity system
  cutoff = Audit.cutoff system
  nu = Field30.viscosity physicalSystem

  module Live = LiveOwner.Live physicalSystem S

  record UniformPhysicalCriticalRegionFamily : Set₁ where
    constructor uniform-physical-critical-region-family
    field
      paymentAt :
        (output : Z3.FourierMode) →
        let module P = RegionPay.LiveRegionPayment physicalSystem S output
        in P.PhysicalCriticalRegionPayment

      thetaStrictlyBelowOne : theta < 1

      coefficientNN : 0ℚ ≤ coefficient

      viscosityNN : 0ℚ ≤ nu

      thetaMeaning :
        (output : Z3.FourierMode) →
        let
          module P = RegionPay.LiveRegionPayment physicalSystem S output
          payment = paymentAt output
        in
        P.theta payment ≡ theta

      localED : Z3.FourierMode → ℚ

      localEDMeaning :
        (output : Z3.FourierMode) →
        localED output
        ≡ R38.foldPower
            (R469.selectedTriadValue
              (R219.physicalModalED E I velocity) select)
            (Output.physicalOutputFiber cutoff output)

      localEDBudgetPaid :
        (output : Z3.FourierMode) →
        let
          module P = RegionPay.LiveRegionPayment physicalSystem S output
          payment = paymentAt output
        in
        P.deepBudget payment + P.coreEDBudget payment
        ≤ coefficient * localED output

  open UniformPhysicalCriticalRegionFamily public

  companionAt :
    UniformPhysicalCriticalRegionFamily →
    Z3.FourierMode → ℚ
  companionAt family output =
    let
      module P = RegionPay.LiveRegionPayment physicalSystem S output
      payment = paymentAt family output
    in
    nu * P.coreCompanionMass payment

  covarianceAt :
    UniformPhysicalCriticalRegionFamily →
    Z3.FourierMode → ℚ
  covarianceAt family output =
    Live.coherentCovarianceNumerator output

  fixedOutputUniformBound :
    (family : UniformPhysicalCriticalRegionFamily) →
    (output : Z3.FourierMode) →
    covarianceAt family output
    ≤ theta * companionAt family output
      + (nu * coefficient) * localED family output
  fixedOutputUniformBound family output =
    let
      module P = RegionPay.LiveRegionPayment physicalSystem S output
      payment = paymentAt family output

      base :
        covarianceAt family output ≤ P.fixedOutputBudget payment
      base = P.physicalCriticalRegionPaymentClosesFixedOutput payment

      nuNN : 0ℚ ≤ nu
      nuNN = P.viscosityNN payment

      localBudget :
        P.deepBudget payment + P.coreEDBudget payment
        ≤ coefficient * localED family output
      localBudget = localEDBudgetPaid family output

      scaledLocal :
        nu * (P.deepBudget payment + P.coreEDBudget payment)
        ≤ nu * (coefficient * localED family output)
      scaledLocal =
        let instance nuNNI = nonNegative nuNN
        in ℚP.*-monoˡ-≤-nonNeg nu localBudget

      thetaEq = thetaMeaning family output

      expose :
        P.fixedOutputBudget payment
        ≡
        P.theta payment * companionAt family output
          + nu * (P.deepBudget payment + P.coreEDBudget payment)
      expose =
        solve
          ( nu
          ∷ P.deepBudget payment
          ∷ P.theta payment
          ∷ P.coreCompanionMass payment
          ∷ P.coreEDBudget payment
          ∷ [])

      localEndpoint :
        nu * (coefficient * localED family output)
        ≡ (nu * coefficient) * localED family output
      localEndpoint =
        solve (nu ∷ coefficient ∷ localED family output ∷ [])

      afterLocal :
        P.fixedOutputBudget payment
        ≤
        P.theta payment * companionAt family output
          + (nu * coefficient) * localED family output
      afterLocal =
        subst
          (_≤
            P.theta payment * companionAt family output
              + (nu * coefficient) * localED family output)
          (sym expose)
          (ℚP.+-mono-≤
            ℚP.≤-refl
            (subst
              (nu * (P.deepBudget payment + P.coreEDBudget payment) ≤_)
              localEndpoint
              scaledLocal))

      uniformTheta :
        P.theta payment * companionAt family output
          + (nu * coefficient) * localED family output
        ≡
        theta * companionAt family output
          + (nu * coefficient) * localED family output
      uniformTheta =
        cong
          (λ selected →
            selected * companionAt family output
              + (nu * coefficient) * localED family output)
          thetaEq
    in
    ℚP.≤-trans base
      (subst
        (P.fixedOutputBudget payment ≤_)
        uniformTheta
        afterLocal)

  sumCovariance :
    UniformPhysicalCriticalRegionFamily →
    List Z3.FourierMode → ℚ
  sumCovariance family [] = 0ℚ
  sumCovariance family (output ∷ rest) =
    covarianceAt family output + sumCovariance family rest

  sumCompanion :
    UniformPhysicalCriticalRegionFamily →
    List Z3.FourierMode → ℚ
  sumCompanion family [] = 0ℚ
  sumCompanion family (output ∷ rest) =
    companionAt family output + sumCompanion family rest

  sumLocalED :
    UniformPhysicalCriticalRegionFamily →
    List Z3.FourierMode → ℚ
  sumLocalED family [] = 0ℚ
  sumLocalED family (output ∷ rest) =
    localED family output + sumLocalED family rest

  finiteOutputUniformBound :
    (family : UniformPhysicalCriticalRegionFamily) →
    (outputs : List Z3.FourierMode) →
    sumCovariance family outputs
    ≤ theta * sumCompanion family outputs
      + (nu * coefficient) * sumLocalED family outputs
  finiteOutputUniformBound family [] =
    subst
      (0ℚ ≤_)
      (sym (solve (theta ∷ nu ∷ coefficient ∷ [])))
      ℚP.≤-refl
  finiteOutputUniformBound family (output ∷ rest) =
    let
      added =
        ℚP.+-mono-≤
          (fixedOutputUniformBound family output)
          (finiteOutputUniformBound family rest)

      endpoint :
        ( theta * companionAt family output
            + (nu * coefficient) * localED family output )
        + ( theta * sumCompanion family rest
            + (nu * coefficient) * sumLocalED family rest )
        ≡
        theta * sumCompanion family (output ∷ rest)
          + (nu * coefficient) * sumLocalED family (output ∷ rest)
      endpoint =
        solve
          ( theta ∷ nu ∷ coefficient
          ∷ companionAt family output
          ∷ localED family output
          ∷ sumCompanion family rest
          ∷ sumLocalED family rest
          ∷ [])
    in
    subst
      (sumCovariance family (output ∷ rest) ≤_)
      endpoint added

  sumLocalEDMeaning :
    (family : UniformPhysicalCriticalRegionFamily) →
    (outputs : List Z3.FourierMode) →
    sumLocalED family outputs
    ≡
    R38.foldPower
      (R469.selectedTriadValue
        (R219.physicalModalED E I velocity) select)
      (R39.concatOutputFibers cutoff outputs)
  sumLocalEDMeaning family [] = refl
  sumLocalEDMeaning family (output ∷ rest) =
    trans
      (cong₂ _+_
        (localEDMeaning family output)
        (sumLocalEDMeaning family rest))
      (sym
        (R39.foldAppend
          (R469.selectedTriadValue
            (R219.physicalModalED E I velocity) select)
          (Output.physicalOutputFiber cutoff output)
          (R39.concatOutputFibers cutoff rest)))

  cutoffLocalEDIsSelectedPairSum :
    (family : UniformPhysicalCriticalRegionFamily) →
    sumLocalED family (Cube.cutoffModes cutoff)
    ≡
    R109.selectedOrderedPairSum
      (R219.physicalModalED E I velocity)
      (R469.outputFilteredSelect cutoff select)
      (Cube.cutoffModes cutoff)
      (Cube.cutoffModes cutoff)
  cutoffLocalEDIsSelectedPairSum family =
    trans
      (sumLocalEDMeaning family (Cube.cutoffModes cutoff))
      (sym
        (R469.selectedPairsEqualOutputFibrePartitionFold
          (R219.physicalModalED E I velocity)
          cutoff select))

  globalEnergyDissipationProduct : ℚ
  globalEnergyDissipationProduct =
    R109.sumEnergy
      (R219.physicalModalED E I velocity)
      (Cube.cutoffModes cutoff)
    *
    R109.sumDissipation
      (R219.physicalModalED E I velocity)
      (Cube.cutoffModes cutoff)

  cutoffLocalEDPaid :
    (family : UniformPhysicalCriticalRegionFamily) →
    sumLocalED family (Cube.cutoffModes cutoff)
    ≤ globalEnergyDissipationProduct + globalEnergyDissipationProduct
  cutoffLocalEDPaid family =
    subst
      (_≤ globalEnergyDissipationProduct + globalEnergyDissipationProduct)
      (sym (cutoffLocalEDIsSelectedPairSum family))
      (R219.physicalSelectedPairEDBound
        E I velocity
        (R469.outputFilteredSelect cutoff select)
        (Cube.cutoffModes cutoff))

  cutoffUniformGlobalBound :
    (family : UniformPhysicalCriticalRegionFamily) →
    sumCovariance family (Cube.cutoffModes cutoff)
    ≤
    theta * sumCompanion family (Cube.cutoffModes cutoff)
      + (nu * coefficient)
        * (globalEnergyDissipationProduct + globalEnergyDissipationProduct)
  cutoffUniformGlobalBound family =
    let
      finite =
        finiteOutputUniformBound family (Cube.cutoffModes cutoff)

      nuC-NN : 0ℚ ≤ nu * coefficient
      nuC-NN =
        Rational.productNonnegative
          (viscosityNN family)
          (coefficientNN family)

      scaledED :
        (nu * coefficient) * sumLocalED family (Cube.cutoffModes cutoff)
        ≤
        (nu * coefficient)
          * (globalEnergyDissipationProduct + globalEnergyDissipationProduct)
      scaledED =
        let instance nuC-NNI = nonNegative nuC-NN
        in
        ℚP.*-monoˡ-≤-nonNeg
          (nu * coefficient)
          (cutoffLocalEDPaid family)

      added =
        ℚP.+-monoʳ-≤
          (theta * sumCompanion family (Cube.cutoffModes cutoff))
          scaledED
    in
    ℚP.≤-trans finite added

nativeR236UniformFamilySummationClosed : Bool
nativeR236UniformFamilySummationClosed = true

nativeR236OutputSummationAddsCardinalityFactor : Bool
nativeR236OutputSummationAddsCardinalityFactor = false

nativeR236GlobalEDRoutingUsesExistingR469R219 : Bool
nativeR236GlobalEDRoutingUsesExistingR469R219 = true

nativeR236UniformFamilyProducerInhabitedHere : Bool
nativeR236UniformFamilyProducerInhabitedHere = false

clayPromotion : Bool
clayPromotion = false

nativeR236UniformFamilySummationClosedIsTrue :
  nativeR236UniformFamilySummationClosed ≡ true
nativeR236UniformFamilySummationClosedIsTrue = refl
