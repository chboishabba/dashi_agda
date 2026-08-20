module DASHI.Physics.Closure.NSTriadKNHHBadPhysicalIdentificationRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Give the two remaining HH-bad same-object seams the paper-facing names used
-- by the highest-alpha plan.  No new physical hypothesis is introduced here:
-- both theorems are exact projections of already-existing, stronger records.
--
--   physicalHHBadGainBelowDefectProfile
--   physicalHHBadUnmaskedChargeBelowDissipation
--
-- The second endpoint is especially important: masked bad-cell charge is
-- already proved to be a literal subcharge of the unmasked shell charge, so a
-- physical proof must dominate only the unmasked charge by dissipation.  There
-- is no extra bad-set dissipation allocation to prove.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadGainBelowDefectProfileRound51Exact as GainDefect
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingRound50Exact as Sum
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Charge
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain

physicalHHBadGainBelowDefectProfile :
  ∀ {effectiveViscosity summableInput}
    (bridge : GainDefect.GainBelowDefectProfileBridge
      effectiveViscosity summableInput)
    shell →
  Factor.scaleFreeDensityCoefficient
    (GainDefect.density bridge shell) shell
  ≤ Sum.profile summableInput shell
physicalHHBadGainBelowDefectProfile bridge shell =
  GainDefect.normalizedDensityBelowDefectProfile bridge shell

physicalHHBadUnmaskedChargeBelowDissipation :
  ∀ {environment effectiveViscosity eta shell}
    (input : Charge.HHBadFullChargeDominationInput
      environment effectiveViscosity eta shell) →
  Charge.sumCellUnmaskedViscousCharge
    effectiveViscosity shell
    (Gain.cells (Charge.densityCertificate input))
  ≤ Owner.dissipation environment
physicalHHBadUnmaskedChargeBelowDissipation input =
  Charge.unmaskedChargeBelowPhysicalDissipation input

physicalHHBadRestrictedChargeBelowDissipation :
  ∀ {environment effectiveViscosity eta shell}
    (input : Charge.HHBadFullChargeDominationInput
      environment effectiveViscosity eta shell) →
  Gain.sumCellViscousCharge
    (Gain.cells (Charge.densityCertificate input))
  ≤ Owner.dissipation environment
physicalHHBadRestrictedChargeBelowDissipation =
  Charge.restrictedChargeBelowPhysicalDissipation

gainBelowDefectProfileEndpointExists : Bool
gainBelowDefectProfileEndpointExists = true

unmaskedChargeDominationIsOnlyRemainingDissipationSeam : Bool
unmaskedChargeDominationIsOnlyRemainingDissipationSeam = true

gainBelowDefectProfileEndpointExistsIsTrue :
  gainBelowDefectProfileEndpointExists ≡ true
gainBelowDefectProfileEndpointExistsIsTrue = refl

unmaskedChargeDominationIsOnlyRemainingDissipationSeamIsTrue :
  unmaskedChargeDominationIsOnlyRemainingDissipationSeam ≡ true
unmaskedChargeDominationIsOnlyRemainingDissipationSeamIsTrue = refl
