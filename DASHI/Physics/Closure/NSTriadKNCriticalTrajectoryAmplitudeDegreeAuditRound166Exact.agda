module DASHI.Physics.Closure.NSTriadKNCriticalTrajectoryAmplitudeDegreeAuditRound166Exact where

------------------------------------------------------------------------
-- ROUND166 / AMPLITUDE-HOMOGENEITY AUDIT OF THE SLOT-DEFECT TRAJECTORY ROUTE
--
-- This is a fail-closed correction to the post-R157 plan.
-- Under amplitude scaling u -> alpha u:
--
--   normalized curl S u             has degree 1,
--   B_j=<S u,u x u>                 has degree 3,
--   critical production             has degree 3,
--   NS forcing N(u)                 has degree 2,
--   slot network forcing F_B        has degree 4,
--   |B_i-B_q|^2                     has degree 6,
--   W(B_i-B_q,F_B)                  has degree 7.
--
-- If Cauchy--Schwarz is used in the A-facing form
--
--   Pcrit^2 <= Dcrit * Qcomp,
--
-- then Pcrit^2 has amplitude degree 6 and Dcrit is quadratic, so the companion
-- must have degree 4.  The raw cubic slot-defect energy has degree 6 and its
-- nonlinear forcing-work has degree 7.  Therefore those objects CANNOT be the
-- missing quartic companion without an additional normalization/cancellation.
--
-- This redirects the dynamic search toward a quartic pair/covariance object on
-- the residual cell network, exactly matching the YM covariance/reopening
-- lesson, rather than trying to integrate |B_i-B_q|^2 directly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)

velocityDegree normalizedCurlDegree nsForcingDegree : Nat
velocityDegree = 1
normalizedCurlDegree = 1
nsForcingDegree = 2

slotAmplitudeDegree : Nat
slotAmplitudeDegree = normalizedCurlDegree + velocityDegree + velocityDegree

criticalProductionDegree : Nat
criticalProductionDegree = slotAmplitudeDegree

slotNetworkForcingDegree : Nat
slotNetworkForcingDegree = nsForcingDegree + velocityDegree + velocityDegree

slotDefectEnergyDegree : Nat
slotDefectEnergyDegree = 2 * slotAmplitudeDegree

slotDefectForcingWorkDegree : Nat
slotDefectForcingWorkDegree = slotAmplitudeDegree + slotNetworkForcingDegree

criticalProductionSquareDegree : Nat
criticalProductionSquareDegree = 2 * criticalProductionDegree

criticalDissipationDegree : Nat
criticalDissipationDegree = 2

requiredCompanionDegree : Nat
requiredCompanionDegree = criticalProductionSquareDegree - criticalDissipationDegree

slotAmplitudeDegreeIsThree : slotAmplitudeDegree ≡ 3
slotAmplitudeDegreeIsThree = refl

slotNetworkForcingDegreeIsFour : slotNetworkForcingDegree ≡ 4
slotNetworkForcingDegreeIsFour = refl

slotDefectEnergyDegreeIsSix : slotDefectEnergyDegree ≡ 6
slotDefectEnergyDegreeIsSix = refl

slotDefectForcingWorkDegreeIsSeven : slotDefectForcingWorkDegree ≡ 7
slotDefectForcingWorkDegreeIsSeven = refl

requiredCompanionDegreeIsFour : requiredCompanionDegree ≡ 4
requiredCompanionDegreeIsFour = refl

round166RawSlotDefectEnergyHasRequiredCompanionDegree : Bool
round166RawSlotDefectEnergyHasRequiredCompanionDegree = false

round166RawSlotForcingWorkHasRequiredCompanionDegree : Bool
round166RawSlotForcingWorkHasRequiredCompanionDegree = false

round166QuarticResidualPairCompanionIsHomogeneityCompatible : Bool
round166QuarticResidualPairCompanionIsHomogeneityCompatible = true

round166PackageAClosed : Bool
round166PackageAClosed = false

round166RawSlotDefectEnergyHasRequiredCompanionDegreeIsFalse :
  round166RawSlotDefectEnergyHasRequiredCompanionDegree ≡ false
round166RawSlotDefectEnergyHasRequiredCompanionDegreeIsFalse = refl

round166QuarticResidualPairCompanionIsHomogeneityCompatibleIsTrue :
  round166QuarticResidualPairCompanionIsHomogeneityCompatible ≡ true
round166QuarticResidualPairCompanionIsHomogeneityCompatibleIsTrue = refl

round166PackageAClosedIsFalse : round166PackageAClosed ≡ false
round166PackageAClosedIsFalse = refl
