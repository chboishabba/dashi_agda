module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound80Exact where

------------------------------------------------------------------------
-- ROUND80 HIGHEST-ALPHA CUTSET
--
-- Round79 made the C4 denominator honest. Round80 asks whether classical
-- spectral-subspace perturbation theory removes that obstruction.
--
-- Answer: partly, and in exactly the useful way.
--
-- * Davis--Kahan/Kato replace a noncanonical individual eigenvector by a
--   spectral CLUSTER projector.  Internal degeneracy no longer forces a basis.
-- * They do NOT remove the cluster-vs-complement separation requirement.
--   At S=0 every rank-one projector is invariant, so no directional line is
--   canonically selected; only the full-space projector is canonical.
-- * A cluster projector also cannot recover arbitrary internal directional
--   observables.  A consumer must be cluster-invariant or retain a residual.
-- * In 3D trace-free strain, however, the two adjacent gaps reconstruct the
--   entire spectrum.  Hence C4 has an exhaustive replacement architecture:
--
--       g12 separated -> top-line/lower-plane projector route
--       OR
--       g23 separated -> upper-plane/bottom-line projector route
--       OR
--       both gaps small -> whole strain spectrum small.
--
-- This removes the need for a uniformly simple eigenframe at every event while
-- retaining a genuine physical separation/small-strain theorem obligation.
--
-- C5 is also compressed.  Repository archaeology found the already-existing
-- `spectralProjectorTurnoverCurrency` in NSDepletionCurrencyFork, and the
-- deterministic NSCoherenceBudgetResidenceReduction already proves
--
--   (margin * dangerCost) * dangerousResidence <= budgetUpper
--
-- once projector turnover consumes depletion and its remainder is absorbed.
-- Foias--Rosa--Temam's recurrence/positive-sojourn theorem is rigorous and
-- useful statistical infrastructure, but its almost-everywhere/existential
-- positive-sojourn conclusion is not the deterministic upper-residence theorem
-- required for the selected critical trajectory.
--
-- PRIMARY SOURCES
--
-- Chandler Davis; W. M. Kahan,
-- "The Rotation of Eigenvectors by a Perturbation. III",
-- DOI 10.1137/0707001.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", 2nd ed.,
-- DOI 10.1007/978-3-642-66282-9.
--
-- Yi Yu; Tengyao Wang; Richard J. Samworth,
-- "A useful variant of the Davis--Kahan theorem for statisticians",
-- DOI 10.1093/biomet/asv008.
--
-- Moritz Jirak; Martin Wahl,
-- "Perturbation bounds for eigenspaces under a relative gap condition",
-- DOI 10.1090/proc/14714.
--
-- Ciprian Foias; Ricardo M. S. Rosa; Roger M. Temam,
-- "Convergence of time averages of weak solutions of the three-dimensional
-- Navier--Stokes equations",
-- DOI 10.1007/s10955-015-1248-3.
--
-- SHORTEST CUTSET
--
-- The seven package count remains unchanged.  Producer 3 is sharpened to:
--
-- 3a. same-event scalar pressure/stretching surplus or depletion;
-- 3b. selected-event strain spectral data and projector/small-strain fork;
-- 3c. on a separated branch, physical cluster-projector turnover estimate;
--     on the both-small branch, physical weak-stretching/depletion estimate;
-- 3d. feed projector turnover (or another proved currency) into the existing
--     deterministic residence theorem and frame-weighted antichain budget.
--
-- No statistical-sojourn or gap-free Davis--Kahan promotion is accepted.
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound79Exact as R79
import DASHI.Physics.Closure.NSTriadKNSpectralProjectorDegeneracyBoundaryRound80Exact as Deg
import DASHI.Physics.Closure.NSTriadKNDavisKahanClusterGapRound80Exact as DK
import DASHI.Physics.Closure.NSTriadKNClusterProjectorDirectionalObservableNoGoRound80Exact as Descend
import DASHI.Physics.Closure.NSTriadKNTraceFreeGapSpectrumRound80Exact as Spectrum
import DASHI.Physics.Closure.NSTriadKNSpectralClusterOrSmallStrainForkRound80Exact as Fork
import DASHI.Physics.Closure.NSTriadKNFoiasRosaTemamSojournBoundaryRound80Exact as Sojourn
import DASHI.Physics.Closure.NSTriadKNSpectralProjectorResidenceWeldRound80Exact as Residence

round80ProjectorsRemoveInternalBasisGauge : Bool
round80ProjectorsRemoveInternalBasisGauge =
  Deg.round80ProjectorsRemoveInternalBasisChoice

round80ProjectorsMakeC4GapFree : Bool
round80ProjectorsMakeC4GapFree =
  Deg.round80ProjectorsRemoveNeedForClusterComplementGap

round80DavisKahanControlsClusters : Bool
round80DavisKahanControlsClusters =
  DK.round80DavisKahanControlsSpectralSubspaces

round80ClusterProjectorDeterminesDirectionalFineObservable : Bool
round80ClusterProjectorDeterminesDirectionalFineObservable =
  Descend.round80ClusterProjectorDeterminesEveryDirectionalObservable

round80TraceFreeGapsDetermineSpectrum : Bool
round80TraceFreeGapsDetermineSpectrum =
  Spectrum.round80AdjacentGapsDetermineTraceFreeSpectrumScaled

round80ClusterOrSmallSpectrumForkConstructed : Bool
round80ClusterOrSmallSpectrumForkConstructed =
  Fork.round80C4HasSeparatedClusterOrSmallSpectrumFork

round80ProjectorTurnoverFeedsExistingResidence : Bool
round80ProjectorTurnoverFeedsExistingResidence =
  Residence.round80ProjectorTurnoverFeedsExistingResidenceTheorem

round80FoiasPositiveSojournClosesSelectedResidence : Bool
round80FoiasPositiveSojournClosesSelectedResidence =
  Sojourn.round80StatisticalPositiveSojournClosesDeterministicC5UpperBound

-- Seven genuine physical/analytic producers remain.
round80SelectedGalerkinTrajectoryExistsGloballyAndIsLiteral : Bool
round80SelectedGalerkinTrajectoryExistsGloballyAndIsLiteral = false

round80SelectedTrajectoryInstantiatesFineStructuredBalance : Bool
round80SelectedTrajectoryInstantiatesFineStructuredBalance = false

round80PhysicalPressureProjectorOrSmallStrainSurplusDepletionClosure : Bool
round80PhysicalPressureProjectorOrSmallStrainSurplusDepletionClosure = false

round80PhysicalNormalizedSixThreeGramEstimate : Bool
round80PhysicalNormalizedSixThreeGramEstimate = false

round80PhysicalHHBadCapacityChargeBound : Bool
round80PhysicalHHBadCapacityChargeBound = false

round80PhysicalSoftDataAndBoundaryClosure : Bool
round80PhysicalSoftDataAndBoundaryClosure = false

round80PhysicalAnnularMultiplierKernelBound : Bool
round80PhysicalAnnularMultiplierKernelBound = false

round80CriticalRatioBarrier : Bool
round80CriticalRatioBarrier = false

round80GenericAubinLionsLimitInterfacesAlreadyPresent : Bool
round80GenericAubinLionsLimitInterfacesAlreadyPresent =
  R79.round79GenericAubinLionsLimitInterfacesAlreadyPresent

round80CriticalToSerrinReducerAlreadyPresent : Bool
round80CriticalToSerrinReducerAlreadyPresent =
  R79.round79CriticalToSerrinReducerAlreadyPresent

round80ClayPromotion : Bool
round80ClayPromotion = false

round80ProjectorsMakeC4GapFreeIsFalse :
  round80ProjectorsMakeC4GapFree ≡ false
round80ProjectorsMakeC4GapFreeIsFalse = refl

round80ClusterProjectorDeterminesDirectionalFineObservableIsFalse :
  round80ClusterProjectorDeterminesDirectionalFineObservable ≡ false
round80ClusterProjectorDeterminesDirectionalFineObservableIsFalse = refl

round80ClusterOrSmallSpectrumForkConstructedIsTrue :
  round80ClusterOrSmallSpectrumForkConstructed ≡ true
round80ClusterOrSmallSpectrumForkConstructedIsTrue = refl

round80ProjectorTurnoverFeedsExistingResidenceIsTrue :
  round80ProjectorTurnoverFeedsExistingResidence ≡ true
round80ProjectorTurnoverFeedsExistingResidenceIsTrue = refl

round80FoiasPositiveSojournClosesSelectedResidenceIsFalse :
  round80FoiasPositiveSojournClosesSelectedResidence ≡ false
round80FoiasPositiveSojournClosesSelectedResidenceIsFalse = refl

round80ClayPromotionIsFalse : round80ClayPromotion ≡ false
round80ClayPromotionIsFalse = refl
