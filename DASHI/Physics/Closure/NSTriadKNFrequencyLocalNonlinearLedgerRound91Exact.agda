module DASHI.Physics.Closure.NSTriadKNFrequencyLocalNonlinearLedgerRound91Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND91 / FINITE I+II+III ASSEMBLY
--
-- The preceding Round91 files prove:
--
--   * exact cubic Young on every weighted interaction;
--   * exact uniform geometric masses for the three Cheskidov--Shvydkoy
--     normalized gap kernels.
--
-- This module closes the finite assembly.  A concrete shell enumeration only
-- has to show that each Young left/right charge has the appropriate geometric
-- multiplicity against ONE cubic shell mass M.  Then
--
--   I   <= (25/9) M,
--   II  <= (64/39) M,
--   III <= (25/4) M,
--
-- and hence
--
--   I+II+III <= (4993/468) M.
--
-- This is exactly the unconditional dyadic-convolution stage before the
-- critical B^{-1}_{infinity,infinity} amplitude is used to absorb M into the
-- viscous sum.  The remaining physical seam is now sharply source-facing:
-- construct the three interaction lists from the literal periodic Bony fibre,
-- prove their charge-multiplicity bounds, and identify M with
-- sum lambda_q^(2+epsilon) ||u_q||_3^3 (or its radical-free equivalent).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNFrequencyLocalCubicYoungRound91Exact as Young
import DASHI.Physics.Closure.NSTriadKNFrequencyLocalDyadicKernelMassRound91Exact as Kernel

record CubicInteractionChargeBudget
    (kernelMass cubicMass : ℚ) : Set where
  constructor cubic-interaction-charge-budget
  field
    interactions : List Young.WeightedCubicInteraction
    cubicMassNonnegative : 0ℚ ≤ cubicMass
    kernelMassNonnegative : 0ℚ ≤ kernelMass

    leftChargeMultiplicity :
      Young.sumLeftCharge interactions ≤ kernelMass * cubicMass

    rightChargeMultiplicity :
      Young.sumRightCharge interactions ≤ kernelMass * cubicMass

open CubicInteractionChargeBudget public

threePositive : 0ℚ ℚP.< Young.three
threePositive = toWitness {a? = 0ℚ <? Young.three} _

twoNonnegative : 0ℚ ≤ Young.two
twoNonnegative = ℚP.<⇒≤
  (toWitness {a? = 0ℚ <? Young.two} _)

interactionSumBelowKernelMass :
  ∀ {kernelMass cubicMass}
    (budget : CubicInteractionChargeBudget kernelMass cubicMass) →
  Young.sumInteraction (interactions budget) ≤ kernelMass * cubicMass
interactionSumBelowKernelMass {kernelMass} {cubicMass} budget =
  let
    cells = interactions budget
    M = kernelMass * cubicMass

    young :
      Young.three * Young.sumInteraction cells
      ≤ Young.sumLeftCharge cells + Young.two * Young.sumRightCharge cells
    young = Young.finiteWeightedCubicYoung cells

    rightScale :
      Young.two * Young.sumRightCharge cells ≤ Young.two * M
    rightScale =
      let instance twoNNI = nonNegative twoNonnegative
      in ℚP.*-monoˡ-≤-nonNeg Young.two (rightChargeMultiplicity budget)

    chargeStage :
      Young.sumLeftCharge cells + Young.two * Young.sumRightCharge cells
      ≤ M + Young.two * M
    chargeStage =
      ℚP.+-mono-≤ (leftChargeMultiplicity budget) rightScale

    tripleMeaning : M + Young.two * M ≡ Young.three * M
    tripleMeaning = solve (M ∷ [])

    tripleBound :
      Young.three * Young.sumInteraction cells ≤ Young.three * M
    tripleBound =
      ℚP.≤-trans young
        (subst
          (λ upper →
            Young.sumLeftCharge cells + Young.two * Young.sumRightCharge cells
            ≤ upper)
          tripleMeaning chargeStage)

    instance threeIsPositive = Data.Rational.Base.positive threePositive
  in
  ℚP.*-cancelˡ-≤-pos Young.three tripleBound

record FrequencyLocalThreeChannelLedger : Set₁ where
  constructor frequency-local-three-channel-ledger
  field
    cubicMass : ℚ
    cubicMassNonnegative : 0ℚ ≤ cubicMass

    iBudget : CubicInteractionChargeBudget Kernel.iMass cubicMass
    iiBudget : CubicInteractionChargeBudget Kernel.iiMass cubicMass
    iiiBudget : CubicInteractionChargeBudget Kernel.iiiFullMass cubicMass

open FrequencyLocalThreeChannelLedger public

frequencyLocalThreeChannelBound :
  (ledger : FrequencyLocalThreeChannelLedger) →
  Young.sumInteraction (interactions (iBudget ledger))
    + Young.sumInteraction (interactions (iiBudget ledger))
    + Young.sumInteraction (interactions (iiiBudget ledger))
  ≤ Kernel.combinedMass * cubicMass ledger
frequencyLocalThreeChannelBound ledger =
  let
    M = cubicMass ledger
    i = interactionSumBelowKernelMass (iBudget ledger)
    ii = interactionSumBelowKernelMass (iiBudget ledger)
    iii = interactionSumBelowKernelMass (iiiBudget ledger)
    summed = ℚP.+-mono-≤ (ℚP.+-mono-≤ i ii) iii
    endpoint :
      Kernel.iMass * M + Kernel.iiMass * M + Kernel.iiiFullMass * M
      ≡ Kernel.combinedMass * M
    endpoint rewrite Kernel.combinedMassMeaning = solve
      (Kernel.iMass ∷ Kernel.iiMass ∷ Kernel.iiiFullMass ∷ M ∷ [])
  in
  subst
    (λ upper →
      Young.sumInteraction (interactions (iBudget ledger))
        + Young.sumInteraction (interactions (iiBudget ledger))
        + Young.sumInteraction (interactions (iiiBudget ledger))
      ≤ upper)
    endpoint summed

round91FiniteFrequencyLocalThreeChannelAssemblyClosed : Bool
round91FiniteFrequencyLocalThreeChannelAssemblyClosed = true

round91LiteralPeriodicIIIInteractionEnumerationClosed : Bool
round91LiteralPeriodicIIIInteractionEnumerationClosed = false

round91PhysicalCubicShellMassIdentificationClosed : Bool
round91PhysicalCubicShellMassIdentificationClosed = false

round91FiniteFrequencyLocalThreeChannelAssemblyClosedIsTrue :
  round91FiniteFrequencyLocalThreeChannelAssemblyClosed ≡ true
round91FiniteFrequencyLocalThreeChannelAssemblyClosedIsTrue = refl
