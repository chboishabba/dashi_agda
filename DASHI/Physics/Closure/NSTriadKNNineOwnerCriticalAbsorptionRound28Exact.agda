module DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- DASHI CONTRIBUTION
--
-- Combine the exact nine-owner admissible language with one signed critical
-- balance.  Once physical owner estimates and a strict eta certificate are
-- supplied, the theorem moves the full viscosity tax to the left and returns
-- only data and integral-critical remainders.  This closes V2--V3 algebra but
-- does not manufacture any physical owner estimate or strict coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as TaxLanguage

record NineOwnerCriticalBalance : Set where
  constructor nine-owner-critical-balance
  field
    environment : TaxLanguage.TaxEnvironment
    family : TaxLanguage.NineOwnerEstimateFamily environment
    energyIn energyOut : ℚ
    signedBalance :
      energyOut + TaxLanguage.dissipation environment
      ≤
      energyIn
      + TaxLanguage.sumProduction
          (TaxLanguage.nineOwnerList family)
    strictBudget :
      TaxLanguage.StrictAdmissibleOwnerBudget
        (TaxLanguage.nineOwnerList family)

open NineOwnerCriticalBalance public

remainingViscosity : NineOwnerCriticalBalance → ℚ
remainingViscosity balance =
  1ℚ
  - TaxLanguage.sumEta
      (TaxLanguage.nineOwnerList (family balance))

admissibleRemainder : NineOwnerCriticalBalance → ℚ
admissibleRemainder balance =
  TaxLanguage.sumDataRemainder estimates
  + TaxLanguage.sumCriticalCoefficient estimates
    * TaxLanguage.integralCritical (environment balance)
  where
  estimates = TaxLanguage.nineOwnerList (family balance)

nineOwnerStrictCriticalEstimate :
  (balance : NineOwnerCriticalBalance) →
  energyOut balance
    + remainingViscosity balance
      * TaxLanguage.dissipation (environment balance)
  ≤
  energyIn balance + admissibleRemainder balance
nineOwnerStrictCriticalEstimate balance =
  let
    env = environment balance
    estimates = TaxLanguage.nineOwnerList (family balance)
    etaTotal = TaxLanguage.sumEta estimates
    dataTotal = TaxLanguage.sumDataRemainder estimates
    criticalTotal = TaxLanguage.sumCriticalCoefficient estimates
    diss = TaxLanguage.dissipation env
    critical = TaxLanguage.integralCritical env

    transferBound :
      TaxLanguage.sumProduction estimates
      ≤
      etaTotal * diss + dataTotal + criticalTotal * critical
    transferBound = TaxLanguage.aggregateOwnerEstimates estimates

    withEnergy :
      energyIn balance + TaxLanguage.sumProduction estimates
      ≤
      energyIn balance
      + (etaTotal * diss + dataTotal + criticalTotal * critical)
    withEnergy = ℚₚ.+-monoʳ-≤ (energyIn balance) transferBound

    assembled :
      energyOut balance + diss
      ≤
      energyIn balance
      + (etaTotal * diss + dataTotal + criticalTotal * critical)
    assembled = ℚₚ.≤-trans (signedBalance balance) withEnergy

    shift = - (etaTotal * diss)

    shiftedLeft :
      shift + (energyOut balance + diss)
      ≤
      shift
      + (energyIn balance
        + (etaTotal * diss + dataTotal + criticalTotal * critical))
    shiftedLeft = ℚₚ.+-monoʳ-≤ shift assembled

    shifted :
      (energyOut balance + diss) + shift
      ≤
      (energyIn balance
        + (etaTotal * diss + dataTotal + criticalTotal * critical))
      + shift
    shifted =
      subst
        (λ left →
          left
          ≤
          (energyIn balance
            + (etaTotal * diss + dataTotal + criticalTotal * critical))
          + shift)
        (solve (shift ∷ energyOut balance ∷ diss ∷ []))
        (subst
          (λ right → shift + (energyOut balance + diss) ≤ right)
          (solve
            ( shift ∷ energyIn balance ∷ etaTotal ∷ diss
            ∷ dataTotal ∷ criticalTotal ∷ critical ∷ []))
          shiftedLeft)

    leftMeaning :
      (energyOut balance + diss) + shift
      ≡
      energyOut balance + (1ℚ - etaTotal) * diss
    leftMeaning =
      solve (energyOut balance ∷ diss ∷ etaTotal ∷ [])

    rightMeaning :
      (energyIn balance
        + (etaTotal * diss + dataTotal + criticalTotal * critical))
      + shift
      ≡
      energyIn balance + (dataTotal + criticalTotal * critical)
    rightMeaning =
      solve
        ( energyIn balance ∷ etaTotal ∷ diss
        ∷ dataTotal ∷ criticalTotal ∷ critical ∷ [])
  in
  subst
    (λ left → left ≤ energyIn balance + admissibleRemainder balance)
    leftMeaning
    (subst
      (λ right →
        (energyOut balance + TaxLanguage.dissipation (environment balance))
        + (- (TaxLanguage.sumEta
              (TaxLanguage.nineOwnerList (family balance))
            * TaxLanguage.dissipation (environment balance)))
        ≤ right)
      rightMeaning
      shifted)

nineOwnerCriticalAbsorptionAlgebraClosed : Bool
nineOwnerCriticalAbsorptionAlgebraClosed = true

physicalNineOwnerCriticalBalanceInstantiated : Bool
physicalNineOwnerCriticalBalanceInstantiated = false

strictPhysicalEtaCertificateInstantiated : Bool
strictPhysicalEtaCertificateInstantiated = false

nineOwnerCriticalAbsorptionAlgebraClosedIsTrue :
  nineOwnerCriticalAbsorptionAlgebraClosed ≡ true
nineOwnerCriticalAbsorptionAlgebraClosedIsTrue = refl

physicalNineOwnerCriticalBalanceInstantiatedIsFalse :
  physicalNineOwnerCriticalBalanceInstantiated ≡ false
physicalNineOwnerCriticalBalanceInstantiatedIsFalse = refl
