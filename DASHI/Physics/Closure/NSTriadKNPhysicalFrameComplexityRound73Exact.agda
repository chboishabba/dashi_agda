module DASHI.Physics.Closure.NSTriadKNPhysicalFrameComplexityRound73Exact where

------------------------------------------------------------------------
-- ROUND73 / PHYSICAL FRAME COMPLEXITY
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Ole Christensen.
-- Title: "An Introduction to Frames and Riesz Bases".
-- DOI: 10.1007/978-3-319-25613-9.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- Round72 proved that raw cardinality is only the unit-weight special case of
-- a factorized Cauchy estimate.  This file isolates the next invariant: the
-- right-factor squared mass is controlled by a PHYSICAL energy through a frame
-- constant, rather than by the number of triads.
--
--     a_tau = x_tau y_tau
--     Q     = sum x_tau^2
--     W     = sum y_tau^2
--
-- A physical frame certificate supplies
--
--     W <= B * E_phys.
--
-- Therefore every same-object remainder lower bound mu obeys
--
--     mu^2 <= Q * (B * E_phys).
--
-- No division and no square roots are used.  The genuinely analytic theorem
-- still required downstream is to construct B and E_phys from the literal
-- localized velocity/Gram geometry.  This file deliberately does not infer a
-- frame bound from atom count.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as R72
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record PhysicalFrameComplexityCertificate
    (factors : List R72.FactorizedContribution)
    (physicalEnergy frameBound : ℚ) : Set where
  field
    physicalEnergyNonnegative : 0ℚ ≤ physicalEnergy
    frameBoundNonnegative : 0ℚ ≤ frameBound
    frameControlsEffectiveComplexity :
      R72.effectiveComplexity factors ≤ frameBound * physicalEnergy

open PhysicalFrameComplexityCertificate public

frameControlledRemainder :
  ∀ {factors remainder mu physicalEnergy frameBound} →
  R72.SameObjectFactorizedRemainder factors remainder mu →
  PhysicalFrameComplexityCertificate factors physicalEnergy frameBound →
  L2.square mu
  ≤ R72.concentrationCharge factors * (frameBound * physicalEnergy)
frameControlledRemainder {factors} remainderWitness frameWitness =
  ℚP.≤-trans
    (R72.factorizedRemainderForcesChargeTimesComplexity remainderWitness)
    (L2.nonnegativeProductMonotone
      (R72.concentrationChargeNonnegative factors)
      (R72.effectiveComplexityNonnegative factors)
      (R72.concentrationChargeNonnegative factors)
      (ℚP.*-nonNegative
        (frameBoundNonnegative frameWitness)
        (physicalEnergyNonnegative frameWitness))
      ℚP.≤-refl
      (frameControlsEffectiveComplexity frameWitness))

record BudgetedPhysicalFrame
    (factors : List R72.FactorizedContribution)
    (chargeBudget physicalEnergy frameBound : ℚ) : Set where
  field
    chargeBudgetNonnegative : 0ℚ ≤ chargeBudget
    chargeWithinBudget : R72.concentrationCharge factors ≤ chargeBudget
    frameCertificate :
      PhysicalFrameComplexityCertificate factors physicalEnergy frameBound

open BudgetedPhysicalFrame public

budgetedFrameRemainder :
  ∀ {factors remainder mu chargeBudget physicalEnergy frameBound} →
  R72.SameObjectFactorizedRemainder factors remainder mu →
  BudgetedPhysicalFrame factors chargeBudget physicalEnergy frameBound →
  L2.square mu ≤ chargeBudget * (frameBound * physicalEnergy)
budgetedFrameRemainder {factors} remainderWitness budgetWitness =
  ℚP.≤-trans
    (frameControlledRemainder remainderWitness
      (frameCertificate budgetWitness))
    (L2.nonnegativeProductMonotone
      (R72.concentrationChargeNonnegative factors)
      (ℚP.*-nonNegative
        (frameBoundNonnegative (frameCertificate budgetWitness))
        (physicalEnergyNonnegative (frameCertificate budgetWitness)))
      (chargeBudgetNonnegative budgetWitness)
      (ℚP.*-nonNegative
        (frameBoundNonnegative (frameCertificate budgetWitness))
        (physicalEnergyNonnegative (frameCertificate budgetWitness)))
      (chargeWithinBudget budgetWitness)
      ℚP.≤-refl)

round73FrameComplexityTheoremConstructed : Bool
round73FrameComplexityTheoremConstructed = true

round73PhysicalTriadicFrameCertificateConstructed : Bool
round73PhysicalTriadicFrameCertificateConstructed = false

round73FrameComplexityTheoremConstructedIsTrue :
  round73FrameComplexityTheoremConstructed ≡ true
round73FrameComplexityTheoremConstructedIsTrue = refl

round73PhysicalTriadicFrameCertificateConstructedIsFalse :
  round73PhysicalTriadicFrameCertificateConstructed ≡ false
round73PhysicalTriadicFrameCertificateConstructedIsFalse = refl
