module DASHI.Physics.Closure.NSTriadKNFiveOwnerToIntegratedCutoffRound44Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Compose Round 44's five-free-eta reserve reduction with the existing
-- NineOwnerCriticalBalance.  Once the physical five-owner estimates, the
-- same-object Bony tail identity, the exact five-owner strict reserve, and the
-- signed cutoff balance are supplied, the repository immediately obtains the
-- integrated cutoff energy inequality consumed by the block-decay lane.
--
-- This removes one more parallel bookkeeping seam: no independent
-- `physicalNineOwnerCriticalBalance` object needs to be manufactured after the
-- five-owner gate passes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _≤_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNNineOwnerToBlockDecayBridgeRound43Exact as BlockBridge
import DASHI.Physics.Closure.NSTriadKNBonyTailOwnerRound44Exact as Tail
import DASHI.Physics.Closure.NSTriadKNFiveOwnerReserveReductionRound44Exact as Five

record FiveOwnerSignedCutoffInput
    (environment : Owner.TaxEnvironment)
    (remaining : Five.FiveRemainingPhysicalOwners environment)
    (tailInput : Tail.PhysicalTailCriticalOwnerInput environment) : Set where
  field
    reserve : Five.FiveOwnerStrictReserveInput remaining
    energyIn energyOut : ℚ
    signedBalance :
      energyOut + Owner.dissipation environment
      ≤
      energyIn
      + Owner.sumProduction
          (Owner.nineOwnerList
            (Five.physicalNineOwnerEstimateFamily remaining tailInput))

open FiveOwnerSignedCutoffInput public

physicalNineOwnerCriticalBalance :
  ∀ {environment remaining tailInput} →
  FiveOwnerSignedCutoffInput environment remaining tailInput →
  Nine.NineOwnerCriticalBalance
physicalNineOwnerCriticalBalance
    {environment} {remaining} {tailInput} input =
  Nine.nine-owner-critical-balance
    environment
    (Five.physicalNineOwnerEstimateFamily remaining tailInput)
    (energyIn input)
    (energyOut input)
    (signedBalance input)
    (Five.strictPhysicalNineOwnerBudget
      remaining tailInput (reserve input))

physicalFiveOwnerIntegratedCutoffEnergyInequality :
  ∀ {environment remaining tailInput}
    (input : FiveOwnerSignedCutoffInput environment remaining tailInput) →
  BlockBridge.NineOwnerIntegratedCutoffEnergyInequality
    (physicalNineOwnerCriticalBalance input)
physicalFiveOwnerIntegratedCutoffEnergyInequality input =
  BlockBridge.physicalNineOwnerBalanceToIntegratedCutoffEnergyInequality
    (physicalNineOwnerCriticalBalance input)

fiveOwnerReserveFeedsIntegratedCutoffDirectly : Bool
fiveOwnerReserveFeedsIntegratedCutoffDirectly = true

fiveOwnerReserveFeedsIntegratedCutoffDirectlyIsTrue :
  fiveOwnerReserveFeedsIntegratedCutoffDirectly ≡ true
fiveOwnerReserveFeedsIntegratedCutoffDirectlyIsTrue = refl
