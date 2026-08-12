module DASHI.Physics.Closure.NSTriadKNHHBadDirectOwnerRound43Exact where

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
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- If the new direct same-object HH-bad density lane succeeds, the old
-- threshold/one-derivative Schur tax is not needed *after* that estimate.
-- This file proves the exact owner reduction.
--
-- Round 39 gives
--
--   G_bad <= g_q(eta) D_bad,
--   g_q(eta) = (eta/2) 2^-q.
--
-- Since q>=0, (1/2)2^-q <= 1.  Hence g_q(eta)<=eta for eta>=0.  If the
-- evidence-restricted viscous charge is literally a subcharge of the physical
-- dissipation, then
--
--   G_bad <= eta D_bad <= eta D.
--
-- Thus the terminal HH-bad owner has zero data and critical remainders.  The
-- hard physical work is now sharply isolated to (i) the literal gain-density
-- estimate and (ii) same-object restricted-charge inclusion in D.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _+_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadInverseSquareBeatsRequiredGainRound42Exact as InverseSquare

halfTimesInverseDyadicAtMostOne :
  ∀ shell →
  Sharp.half * Sharp.inverseDyadicScale shell ≤ 1ℚ
halfTimesInverseDyadicAtMostOne shell =
  let
    mu = Sharp.inverseDyadicScale shell
    muNN = Floor.inverseDyadicScaleNonnegative shell

    halfMuBelowMu : Sharp.half * mu ≤ 1ℚ * mu
    halfMuBelowMu =
      let instance muNNI = nonNegative muNN
      in ℚP.*-monoʳ-≤-nonNeg mu InverseSquare.halfBelowOne

    halfMuBelowMuNormalized : Sharp.half * mu ≤ mu
    halfMuBelowMuNormalized =
      subst
        (λ upper → Sharp.half * mu ≤ upper)
        (ℚP.*-identityˡ mu)
        halfMuBelowMu
  in
  ℚP.≤-trans
    halfMuBelowMuNormalized
    (InverseSquare.inverseDyadicScaleAtMostOne shell)

requiredHHBadGainNonnegative :
  ∀ eta shell →
  0ℚ ≤ eta →
  0ℚ ≤ Sharp.requiredHHBadGain eta shell
requiredHHBadGainNonnegative eta shell etaNN =
  let
    muNN = Floor.inverseDyadicScaleNonnegative shell
    halfNN : 0ℚ ≤ Sharp.half
    halfNN = toWitness {a? = 0ℚ ≤? Sharp.half} _
    instance
      etaNNI = nonNegative etaNN
      halfNNI = nonNegative halfNN
      firstNNI = ℚP.nonNeg*nonNeg⇒nonNeg eta Sharp.half
      muNNI = nonNegative muNN
      secondNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (eta * Sharp.half) (Sharp.inverseDyadicScale shell)
  in
  ℚP.nonNegative⁻¹ (Sharp.requiredHHBadGain eta shell)

requiredHHBadGainAtMostEta :
  ∀ eta shell →
  0ℚ ≤ eta →
  Sharp.requiredHHBadGain eta shell ≤ eta
requiredHHBadGainAtMostEta eta shell etaNN =
  let
    factor = Sharp.half * Sharp.inverseDyadicScale shell
    factor≤one = halfTimesInverseDyadicAtMostOne shell

    scaled : eta * factor ≤ eta * 1ℚ
    scaled =
      let instance etaNNI = nonNegative etaNN
      in ℚP.*-monoˡ-≤-nonNeg eta factor≤one

    leftMeaning :
      Sharp.requiredHHBadGain eta shell ≡ eta * factor
    leftMeaning = solve
      (eta ∷ Sharp.half ∷ Sharp.inverseDyadicScale shell ∷ [])
  in
  subst
    (λ lower → lower ≤ eta)
    (sym leftMeaning)
    (subst
      (λ upper → eta * factor ≤ upper)
      (ℚP.*-identityʳ eta)
      scaled)

record DirectHHBadOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity eta : ℚ)
    (shell : Nat) : Set where
  field
    etaNonnegative : 0ℚ ≤ eta

    densityCertificate :
      Gain.InverseShellRestrictedGainDensity effectiveViscosity shell

    inverseShellTargetMeaning :
      Gain.inverseShellTarget densityCertificate
      ≡ Sharp.requiredHHBadGain eta shell

    restrictedChargeBelowPhysicalDissipation :
      Gain.sumCellViscousCharge (Gain.cells densityCertificate)
      ≤ Owner.dissipation environment

open DirectHHBadOwnerInput public

physicalHHBadDirectAbsorption :
  ∀ {environment effectiveViscosity eta shell}
    (input : DirectHHBadOwnerInput environment effectiveViscosity eta shell) →
  Gain.sumCellGain (Gain.cells (densityCertificate input))
  ≤ eta * Owner.dissipation environment
physicalHHBadDirectAbsorption
    {environment} {effectiveViscosity} {eta} {shell} input =
  let
    certificate = densityCertificate input
    gain = Gain.sumCellGain (Gain.cells certificate)
    charge = Gain.sumCellViscousCharge (Gain.cells certificate)
    target = Gain.inverseShellTarget certificate

    gainToTargetCharge : gain ≤ target * charge
    gainToTargetCharge =
      Gain.restrictedGainBelowInverseShellCharge
        effectiveViscosity shell certificate

    targetNN : 0ℚ ≤ target
    targetNN = Gain.inverseShellTargetNonnegative certificate

    chargeNN : 0ℚ ≤ charge
    chargeNN = Gain.sumCellViscousChargeNonnegative (Gain.cells certificate)

    target≤eta : target ≤ eta
    target≤eta =
      subst
        (λ selected → selected ≤ eta)
        (sym (inverseShellTargetMeaning input))
        (requiredHHBadGainAtMostEta eta shell (etaNonnegative input))

    targetChargeToEtaCharge : target * charge ≤ eta * charge
    targetChargeToEtaCharge =
      L2.nonnegativeProductMonotone
        targetNN chargeNN
        (etaNonnegative input) chargeNN
        target≤eta ℚP.≤-refl

    etaChargeToEtaDiss :
      eta * charge ≤ eta * Owner.dissipation environment
    etaChargeToEtaDiss =
      let instance etaNNI = nonNegative (etaNonnegative input)
      in ℚP.*-monoˡ-≤-nonNeg eta
        (restrictedChargeBelowPhysicalDissipation input)
  in
  ℚP.≤-trans gainToTargetCharge
    (ℚP.≤-trans targetChargeToEtaCharge etaChargeToEtaDiss)

physicalHHBadOwnerEstimate :
  ∀ {environment effectiveViscosity eta shell} →
  DirectHHBadOwnerInput environment effectiveViscosity eta shell →
  Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerEstimate {environment} {eta = eta} input =
  Owner.admissible-owner-estimate
    Tax.HH-bad
    (Gain.sumCellGain (Gain.cells (densityCertificate input)))
    eta
    0ℚ
    0ℚ
    ownerBound
  where
  ownerBound :
    Gain.sumCellGain (Gain.cells (densityCertificate input))
    ≤ eta * Owner.dissipation environment
      + 0ℚ
      + 0ℚ * Owner.integralCritical environment
  ownerBound =
    subst
      (λ upper →
        Gain.sumCellGain (Gain.cells (densityCertificate input)) ≤ upper)
      (sym (solve (eta ∷ Owner.dissipation environment ∷ [])))
      (physicalHHBadDirectAbsorption input)

physicalHHBadOwnerIdentity :
  ∀ {environment effectiveViscosity eta shell}
    (input : DirectHHBadOwnerInput environment effectiveViscosity eta shell) →
  Owner.owner (physicalHHBadOwnerEstimate input) ≡ Tax.HH-bad
physicalHHBadOwnerIdentity input = refl

directHHBadOwnerReductionClosed : Bool
directHHBadOwnerReductionClosed = true

oldThresholdedSchurTaxAvoidedAfterDirectDensityProof : Bool
oldThresholdedSchurTaxAvoidedAfterDirectDensityProof = true

directHHBadOwnerReductionClosedIsTrue :
  directHHBadOwnerReductionClosed ≡ true
directHHBadOwnerReductionClosedIsTrue = refl

oldThresholdedSchurTaxAvoidedAfterDirectDensityProofIsTrue :
  oldThresholdedSchurTaxAvoidedAfterDirectDensityProof ≡ true
oldThresholdedSchurTaxAvoidedAfterDirectDensityProofIsTrue = refl
