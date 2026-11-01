module DASHI.Physics.Closure.NSTriadKNPhysicalSignedGramToPackageARound377Exact where

------------------------------------------------------------------------
-- ROUND377 / BIDI: THE PHYSICAL SIGNED-GRAM FAMILY IS THE PACKAGE-A INPUT
--
-- R375 made the R353 companion observable and integration operator literally
-- physical. R376 proved the remaining pointwise mixed<=companion fact by finite
-- rational norm algebra. Therefore callers should not provide any of R354's
-- transport receipts at all.
--
-- The live input now contains only substantive signed-payment data:
--   * physical integration laws;
--   * the companion <= 36 E D + signed Gram ledger;
--   * cutoff-uniform integrated energy payment;
--   * one R303 signed flux payment at every cutoff/terminal time;
--   * same-debt identity and cutoff-uniform signed Gram upper envelope.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxPaymentRound303Exact as R303
import DASHI.Physics.Closure.NSTriadKNSignedIntegratedGramConsumerRound293Exact as R293
import DASHI.Physics.Closure.NSTriadKNPhysicalSignedGramFamilyRound375Exact as R375
import DASHI.Physics.Closure.NSTriadKNMixedHelicityPointwiseDominanceRound376Exact as R376

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalSignedGramToPackageA
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Physical = R375.PhysicalSignedGramFamily
    Time initialTime integrateTo DerivativeOf
  module Dominance = R376.PhysicalDominance Time integrateTo

  record PhysicalSignedGramCoreInputs
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      energyDissipation : Nat → Time → ℚ
      gramDebt : Nat → Time → ℚ

      integrationMonotone :
        (left right : Time → ℚ) →
        ((t : Time) → left t ≤ right t) →
        (terminal : Time) →
        integrateTo left terminal ≤ integrateTo right terminal

      integrationAdditive :
        (left right : Time → ℚ) →
        (terminal : Time) →
        integrateTo (λ time → left time + right time) terminal
        ≡ integrateTo left terminal + integrateTo right terminal

      pointwiseCompanionLedger :
        (N : Nat) (t : Time) →
        Physical.physicalCompanion T N t
        ≤ R293.thirtySix * energyDissipation N t + gramDebt N t

      scaledEnergyIntegralUpperBound : Time → ℚ
      integratedScaledEnergyBound :
        (N : Nat) (terminal : Time) →
        integrateTo
          (λ time → R293.thirtySix * energyDissipation N time)
          terminal
        ≤ scaledEnergyIntegralUpperBound terminal

      gramFluxPayment : Nat → Time → R303.SignedGramFluxPayment

      gramFluxIsSameIntegratedDebt :
        (N : Nat) (terminal : Time) →
        R303.signedGramIntegral (gramFluxPayment N terminal)
        ≡ integrateTo (gramDebt N) terminal

      signedGramIntegralUpperBound : Time → ℚ

      gramFluxPaidUniformlyInCutoff :
        (N : Nat) (terminal : Time) →
        R303.signedGramUpperBound (gramFluxPayment N terminal)
        ≤ signedGramIntegralUpperBound terminal

  open PhysicalSignedGramCoreInputs public

  asR375Inputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    PhysicalSignedGramCoreInputs T →
    Physical.PhysicalSignedGramInputs T
  asR375Inputs T I = record
    { Physical.energyDissipation = energyDissipation I
    ; Physical.gramDebt = gramDebt I
    ; Physical.integrationMonotone = integrationMonotone I
    ; Physical.integrationAdditive = integrationAdditive I
    ; Physical.pointwiseCompanionLedger = pointwiseCompanionLedger I
    ; Physical.scaledEnergyIntegralUpperBound = scaledEnergyIntegralUpperBound I
    ; Physical.integratedScaledEnergyBound = integratedScaledEnergyBound I
    ; Physical.gramFluxPayment = gramFluxPayment I
    ; Physical.gramFluxIsSameIntegratedDebt = gramFluxIsSameIntegratedDebt I
    ; Physical.signedGramIntegralUpperBound = signedGramIntegralUpperBound I
    ; Physical.gramFluxPaidUniformlyInCutoff = gramFluxPaidUniformlyInCutoff I
    ; Physical.pointwiseMixedBelowCompanion = λ N t →
        Dominance.physicalMixedBelowCompanion (Dyn.forgetDynamics T) N t
    }

  physicalSignedGramCoreBuildsPackageA :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    PhysicalSignedGramCoreInputs T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  physicalSignedGramCoreBuildsPackageA T I =
    Physical.physicalSignedGramInputsBuildPackageA T (asR375Inputs T I)

round377CallerSuppliesMixedCompanionDominance : Bool
round377CallerSuppliesMixedCompanionDominance = false

round377CallerSuppliesR354SameObjectIntegralEquality : Bool
round377CallerSuppliesR354SameObjectIntegralEquality = false

round377OnlySignedPaymentAndPhysicalIntegrationDataRemain : Bool
round377OnlySignedPaymentAndPhysicalIntegrationDataRemain = true

round377CoreInputsBuildLiteralR240PackageA : Bool
round377CoreInputsBuildLiteralR240PackageA = true

round377CallerSuppliesMixedCompanionDominanceIsFalse :
  round377CallerSuppliesMixedCompanionDominance ≡ false
round377CallerSuppliesMixedCompanionDominanceIsFalse = refl

round377CallerSuppliesR354SameObjectIntegralEqualityIsFalse :
  round377CallerSuppliesR354SameObjectIntegralEquality ≡ false
round377CallerSuppliesR354SameObjectIntegralEqualityIsFalse = refl
