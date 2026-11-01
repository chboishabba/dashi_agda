module DASHI.Physics.Closure.NSTriadKNC5CompactTransferPivotRound82Exact where

------------------------------------------------------------------------
-- ROUND82 / C5 PRIMARY-CURRENCY CORRECTION
--
-- Round81 established two useful but different facts:
--
--   * smooth spectral alignment P_beta(S) is gap-free and bounded;
--   * hard-projector turnover is a legitimate local perturbation mechanism.
--
-- Neither fact proves that dangerous transfer forces one-sided decrease of the
-- smooth strain-alignment potential.  The repository's executable
-- `scripts/ns_compact_gamma_potential_audit.py` explicitly records that the
-- earlier top-strain alignment potential was falsified on the matched dangerous
-- triad: large geometric turnover did not produce signed escape.
--
-- That finite audit is not promoted here into a continuum theorem.  It is used
-- only to reject a *proof strategy* that required an already-falsified
-- implication as its primary C5 premise.
--
-- The selected global C5 candidate is instead the source-coupled bounded
-- transfer potential
--
--     B = Q_+ / (Q_+ + 2 nu D) = Gamma / (1 + Gamma),
--
-- whose exact division-free derivative surface already exists in
-- `NSCompactGammaPotentialDerivative`.
--
-- The remaining physical theorem is deliberately integrated:
--
--   dangerCost * dangerousResidence <= unabsorbed compact-transfer escape,
--
-- together with cutoff-uniform replenishment absorption.  Pointwise negative
-- drift is not required.  Spectral/projector geometry remains available as a
-- local mechanism for estimating the pressure/nonlinear terms, but it is not
-- itself promoted to the finite global budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSCompactGammaPotentialDerivative as Compact
import DASHI.Physics.Closure.NSTriadKNSmoothSpectralAlignmentPotentialRound81Exact as Smooth
import DASHI.Physics.Closure.NSTriadKNUnsignedProjectorTurnoverNoBudgetRound81Exact as Turnover
import DASHI.Physics.Closure.NSTriadKNCompactGammaDangerThresholdRound82Exact as Threshold
import DASHI.Physics.Closure.NSTriadKNDeterministicDangerOccupationRound82Exact as Occupation
import DASHI.Physics.Closure.NSTriadKNPointwiseDangerDriftNoGoRound82Exact as Pointwise

-- These flags are architecture statements only.  The positive flags mean the
-- corresponding exact reducer/candidate has been selected; they do not assert
-- the missing Navier--Stokes coercivity estimate.
round82SmoothStrainAlignmentSelectedAsPrimaryC5Currency : Bool
round82SmoothStrainAlignmentSelectedAsPrimaryC5Currency = false

round82UnsignedProjectorPathLengthSelectedAsGlobalBudget : Bool
round82UnsignedProjectorPathLengthSelectedAsGlobalBudget = false

round82CompactTransferPotentialSelectedAsPrimaryC5Currency : Bool
round82CompactTransferPotentialSelectedAsPrimaryC5Currency = true

round82PointwiseDangerImpliesNegativeCompactDriftRequired : Bool
round82PointwiseDangerImpliesNegativeCompactDriftRequired = false

round82IntegratedCompactDangerOccupationTargetSelected : Bool
round82IntegratedCompactDangerOccupationTargetSelected = true

round82PhysicalIntegratedCompactDangerCoercivityConstructed : Bool
round82PhysicalIntegratedCompactDangerCoercivityConstructed = false

round82CutoffUniformCompactReplenishmentAbsorptionConstructed : Bool
round82CutoffUniformCompactReplenishmentAbsorptionConstructed = false

round82CompactTransferPotentialSelectedAsPrimaryC5CurrencyIsTrue :
  round82CompactTransferPotentialSelectedAsPrimaryC5Currency ≡ true
round82CompactTransferPotentialSelectedAsPrimaryC5CurrencyIsTrue = refl

round82IntegratedCompactDangerOccupationTargetSelectedIsTrue :
  round82IntegratedCompactDangerOccupationTargetSelected ≡ true
round82IntegratedCompactDangerOccupationTargetSelectedIsTrue = refl

round82PhysicalIntegratedCompactDangerCoercivityConstructedIsFalse :
  round82PhysicalIntegratedCompactDangerCoercivityConstructed ≡ false
round82PhysicalIntegratedCompactDangerCoercivityConstructedIsFalse = refl
