module DASHI.Physics.Closure.NSTriadKNPhysicalGlobalGramToPackageARound379Exact where

------------------------------------------------------------------------
-- ROUND379 / BIDI: FIX R293'S GRAM DEBT TO THE LITERAL R378 GLOBAL DEBT
--
-- R378 proves on the exact R227 output list
--
--   companion = globalCellMass + globalGramDebt.
--
-- Therefore the R293 pointwise ledger is automatic once the incoherent cell
-- mass is paid by 36 E D.  The caller no longer chooses `gramDebt` and no
-- longer supplies the full companion ledger.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxPaymentRound303Exact as R303
import DASHI.Physics.Closure.NSTriadKNSignedIntegratedGramConsumerRound293Exact as R293
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCompanionGramLedgerRound378Exact as R378
import DASHI.Physics.Closure.NSTriadKNPhysicalSignedGramToPackageARound377Exact as R377

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalGlobalGramToPackageA
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Core = R377.PhysicalSignedGramToPackageA
    Time initialTime integrateTo DerivativeOf

  physicalGlobalCellMass :
    Dyn.PhysicalNSGalerkinTrajectory → Nat → Time → ℚ
  physicalGlobalCellMass T N t =
    R378.globalCellMass
      (Dyn.Base.E (Dyn.forgetDynamics T))
      (Dyn.Base.S (Dyn.forgetDynamics T))
      (Audit.velocity (Dyn.Base.systemAt (Dyn.forgetDynamics T) N t))
      N
      (Audit.modes (Dyn.Base.systemAt (Dyn.forgetDynamics T) N t))

  physicalGlobalGramDebt :
    Dyn.PhysicalNSGalerkinTrajectory → Nat → Time → ℚ
  physicalGlobalGramDebt T N t =
    R378.globalGramDebt
      (Dyn.Base.E (Dyn.forgetDynamics T))
      (Dyn.Base.S (Dyn.forgetDynamics T))
      (Audit.velocity (Dyn.Base.systemAt (Dyn.forgetDynamics T) N t))
      N
      (Audit.modes (Dyn.Base.systemAt (Dyn.forgetDynamics T) N t))

  record PhysicalGlobalSignedGramInputs
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      energyDissipation : Nat → Time → ℚ

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

      globalCellMassBound :
        (N : Nat) (t : Time) →
        physicalGlobalCellMass T N t
        ≤ R293.thirtySix * energyDissipation N t

      scaledEnergyIntegralUpperBound : Time → ℚ
      integratedScaledEnergyBound :
        (N : Nat) (terminal : Time) →
        integrateTo
          (λ time → R293.thirtySix * energyDissipation N time)
          terminal
        ≤ scaledEnergyIntegralUpperBound terminal

      gramFluxPayment : Nat → Time → R303.SignedGramFluxPayment

      gramFluxIsSameIntegratedGlobalDebt :
        (N : Nat) (terminal : Time) →
        R303.signedGramIntegral (gramFluxPayment N terminal)
        ≡ integrateTo (physicalGlobalGramDebt T N) terminal

      signedGramIntegralUpperBound : Time → ℚ

      gramFluxPaidUniformlyInCutoff :
        (N : Nat) (terminal : Time) →
        R303.signedGramUpperBound (gramFluxPayment N terminal)
        ≤ signedGramIntegralUpperBound terminal

  open PhysicalGlobalSignedGramInputs public

  physicalCompanionLedger :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (I : PhysicalGlobalSignedGramInputs T) →
    (N : Nat) (t : Time) →
    Core.Physical.physicalCompanion T N t
    ≤ R293.thirtySix * energyDissipation I N t
        + physicalGlobalGramDebt T N t
  physicalCompanionLedger T I N t =
    let
      state = Dyn.Base.systemAt (Dyn.forgetDynamics T) N t
      exactLedger :
        Core.Physical.physicalCompanion T N t
        ≡ physicalGlobalCellMass T N t + physicalGlobalGramDebt T N t
      exactLedger =
        R378.globalCompanionGramLedger
          (Dyn.Base.E (Dyn.forgetDynamics T))
          (Dyn.Base.S (Dyn.forgetDynamics T))
          (Audit.velocity state)
          N (Audit.modes state)

      paid :
        physicalGlobalCellMass T N t + physicalGlobalGramDebt T N t
        ≤ R293.thirtySix * energyDissipation I N t
            + physicalGlobalGramDebt T N t
      paid = ℚP.+-mono-≤ (globalCellMassBound I N t) ℚP.≤-refl
    in
    subst
      (λ left →
        left ≤ R293.thirtySix * energyDissipation I N t
          + physicalGlobalGramDebt T N t)
      exactLedger paid

  asR377Inputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (I : PhysicalGlobalSignedGramInputs T) →
    Core.PhysicalSignedGramCoreInputs T
  asR377Inputs T I = record
    { Core.energyDissipation = energyDissipation I
    ; Core.gramDebt = physicalGlobalGramDebt T
    ; Core.integrationMonotone = integrationMonotone I
    ; Core.integrationAdditive = integrationAdditive I
    ; Core.pointwiseCompanionLedger = physicalCompanionLedger T I
    ; Core.scaledEnergyIntegralUpperBound = scaledEnergyIntegralUpperBound I
    ; Core.integratedScaledEnergyBound = integratedScaledEnergyBound I
    ; Core.gramFluxPayment = gramFluxPayment I
    ; Core.gramFluxIsSameIntegratedDebt = gramFluxIsSameIntegratedGlobalDebt I
    ; Core.signedGramIntegralUpperBound = signedGramIntegralUpperBound I
    ; Core.gramFluxPaidUniformlyInCutoff = gramFluxPaidUniformlyInCutoff I
    }

  physicalGlobalSignedGramBuildsPackageA :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    PhysicalGlobalSignedGramInputs T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  physicalGlobalSignedGramBuildsPackageA T I =
    Core.physicalSignedGramCoreBuildsPackageA T (asR377Inputs T I)

round379GramDebtCallerSelectable : Bool
round379GramDebtCallerSelectable = false

round379CompanionLedgerCallerSupplied : Bool
round379CompanionLedgerCallerSupplied = false

round379ExactR378GlobalGramDebtUsed : Bool
round379ExactR378GlobalGramDebtUsed = true

round379OnlyCellMassAndIntegratedSignedFluxPaymentsRemain : Bool
round379OnlyCellMassAndIntegratedSignedFluxPaymentsRemain = true

round379LiteralR240PackageABuilt : Bool
round379LiteralR240PackageABuilt = true

round379GramDebtCallerSelectableIsFalse :
  round379GramDebtCallerSelectable ≡ false
round379GramDebtCallerSelectableIsFalse = refl
