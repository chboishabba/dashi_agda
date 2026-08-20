module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound79Exact where

------------------------------------------------------------------------
-- ROUND79 HIGHEST-ALPHA CUTSET
--
-- Round78 isolated a pressure-resolved scalar B2 surplus. Round79 audits the
-- eigenframe side and finds that producer 3 must carry TWO independent pressure
-- observables on the same selected event:
--
--   stretching amplitude: omega^T H omega;
--   eigenframe rotation: off-diagonal pressure injection / strain gap.
--
-- Exact rational counterexamples prove neither scalar contraction nor
-- trace-free strain ordering supplies the missing rotation denominator.
-- Accordingly the corrected physical producer is division-free:
--
--   |Pi_off| <= R_rotation * spectralGap,
--
-- with the actual positive spectral gap supplied by the selected trajectory.
--
-- PRIMARY SOURCES ADDED / SHARPENED
--
-- Wm. T. Ashurst; A. R. Kerstein; R. M. Kerr; C. H. Gibson,
-- "Alignment of vorticity and scalar gradient with strain rate in simulated
-- Navier-Stokes turbulence", DOI 10.1063/1.866513.
--
-- M. S. Chong; A. E. Perry; B. J. Cantwell,
-- "A general classification of three-dimensional flow fields",
-- DOI 10.1063/1.857730.
--
-- Dhawal Buaria; Alain Pumir; Eberhard Bodenschatz,
-- "Generation of intense dissipation in high Reynolds number turbulence",
-- DOI 10.1098/rsta.2021.0088.
--
-- Dhawal Buaria; Alain Pumir,
-- "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows", DOI 10.1017/jfm.2023.786.
--
-- Andrea Cavazzini,
-- "Self-Frustration of Vortex Stretching and the Architecture of the
-- Navier-Stokes Blow-Up Barrier", DOI 10.5281/zenodo.19158797.
--
-- MATHEMATICAL DELTA
--
-- 1. Full pressure H and deviatoric pressure H^D have exactly the same
--    eigenspaces because H=H^D+cI. Ashurst's strain eigenframe remains distinct.
--
-- 2. The smooth periodic pure-rotation field u=(-sin y,sin x,0) has S=0 but
--    nonzero maximal vorticity at the origin. Therefore no universal pointwise
--    lower bound strainGap >= c |omega| follows from incompressibility/order.
--
-- 3. Two symmetric pressure Hessians can have identical omega^T H omega but
--    different off-diagonal eigenframe injection. Scalar Round78 pressure data
--    therefore cannot determine the coherence-rotation correction.
--
-- 4. The Cavazzini spectral-threshold polynomial 4 gbar g12-M^2 is retained,
--    including the exact restricted factorisation
--      4g^2-M^2=(2g-M)(2g+M),
--    while its denominator gap remains independent physical theorem data.
--
-- 5. Buaria--Pumir--Bodenschatz's third-eigenvalue DNS finding is used only as
--    source guidance for C2: exact accounting compresses the first two signed
--    channels into one cancellation residual and keeps the third channel sharp.
--
-- CORRECTED SHORTEST CUTSET
--
-- 1. SelectedGalerkinTrajectoryExistsGloballyAndIsLiteral.
-- 2. SelectedTrajectoryInstantiatesFineStructuredBalance.
-- 3. PhysicalPressureStretchingRotationSurplusOrDepletionClosure:
--      a. same-object Round78 scalar stretching surplus/depletion;
--      b. same-object off-diagonal pressure injection;
--      c. actual positive strain gap and division-free rotation budget;
--      d. global surplus-vs-residence iteration.
-- 4. PhysicalNormalizedSixThreeGramEstimate.
-- 5. PhysicalHHBadCapacityChargeBound.
-- 6. PhysicalSoftDataAndBoundaryClosure.
-- 7. PhysicalAnnularMultiplierKernelBound.
--
-- The package count remains seven. Round79 does not manufacture producer 3;
-- it removes a hidden denominator assumption from its exact statement.
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound78Exact as R78
import DASHI.Physics.Closure.NSTriadKNPressureIsotropicShiftEigenframeRound79Exact as Shift
import DASHI.Physics.Closure.NSTriadKNPointwiseStrainVorticityLowerBoundNoGoRound79Exact as GapNoGo
import DASHI.Physics.Closure.NSTriadKNPressureContractionInjectionSeparationRound79Exact as Separate
import DASHI.Physics.Closure.NSTriadKNPressureEigenframeRotationGapBudgetRound79Exact as Rotation
import DASHI.Physics.Closure.NSTriadKNPressureStretchingRotationJointTargetRound79Exact as Joint
import DASHI.Physics.Closure.NSTriadKNCavazziniSpectralGapThresholdAuditRound79Exact as Threshold
import DASHI.Physics.Closure.NSTriadKNChongPerryCantwellQRNormalizationRound79Exact as QR
import DASHI.Physics.Closure.NSTriadKNThirdEigenvalueCostCompressionRound79Exact as Third

round79FullAndDeviatoricPressureShareEigenframe : Bool
round79FullAndDeviatoricPressureShareEigenframe =
  Shift.round79FullPressureAndDeviatoricPressureShareEigenframe

round79StrainGapComparableToVorticityFromOrderingAlone : Bool
round79StrainGapComparableToVorticityFromOrderingAlone =
  GapNoGo.round79TraceFreeOrderingAloneForcesStrainGapComparableToVorticity

round79PressureContractionDeterminesFrameInjection : Bool
round79PressureContractionDeterminesFrameInjection =
  Separate.round79PressureContractionDeterminesEigenframeInjection

round79CorrectC3NeedsStretchingAndRotation : Bool
round79CorrectC3NeedsStretchingAndRotation =
  Joint.round79CorrectC3NeedsPressureStretchingAndRotationCoordinates

round79RotationBudgetIsDivisionFree : Bool
round79RotationBudgetIsDivisionFree =
  Rotation.round79DivisionFreeGapBudgetIsRequired

round79CavazziniThresholdAlgebraRetained : Bool
round79CavazziniThresholdAlgebraRetained =
  Threshold.round79CavazziniSpectralThresholdAlgebraRetained

round79VieillefosseCPCNormalizationWelded : Bool
round79VieillefosseCPCNormalizationWelded =
  QR.round79VieillefosseAndCPCUseSameQRDiscriminantLocus

round79C2FirstTwoChannelsCompressedToSignedResidual : Bool
round79C2FirstTwoChannelsCompressedToSignedResidual =
  Third.round79C2MayControlFirstTwoChannelsThroughSignedResidual

-- Seven genuine physical/analytic producers remain.
round79SelectedGalerkinTrajectoryExistsGloballyAndIsLiteral : Bool
round79SelectedGalerkinTrajectoryExistsGloballyAndIsLiteral = false

round79SelectedTrajectoryInstantiatesFineStructuredBalance : Bool
round79SelectedTrajectoryInstantiatesFineStructuredBalance = false

round79PhysicalPressureStretchingRotationSurplusOrDepletionClosure : Bool
round79PhysicalPressureStretchingRotationSurplusOrDepletionClosure = false

round79PhysicalNormalizedSixThreeGramEstimate : Bool
round79PhysicalNormalizedSixThreeGramEstimate = false

round79PhysicalHHBadCapacityChargeBound : Bool
round79PhysicalHHBadCapacityChargeBound = false

round79PhysicalSoftDataAndBoundaryClosure : Bool
round79PhysicalSoftDataAndBoundaryClosure = false

round79PhysicalAnnularMultiplierKernelBound : Bool
round79PhysicalAnnularMultiplierKernelBound = false

round79CriticalRatioBarrier : Bool
round79CriticalRatioBarrier = false

round79GenericAubinLionsLimitInterfacesAlreadyPresent : Bool
round79GenericAubinLionsLimitInterfacesAlreadyPresent =
  R78.round78GenericAubinLionsLimitInterfacesAlreadyPresent

round79CriticalToSerrinReducerAlreadyPresent : Bool
round79CriticalToSerrinReducerAlreadyPresent =
  R78.round78CriticalToSerrinReducerAlreadyPresent

round79ClayPromotion : Bool
round79ClayPromotion = false

round79StrainGapComparableToVorticityFromOrderingAloneIsFalse :
  round79StrainGapComparableToVorticityFromOrderingAlone ≡ false
round79StrainGapComparableToVorticityFromOrderingAloneIsFalse = refl

round79PressureContractionDeterminesFrameInjectionIsFalse :
  round79PressureContractionDeterminesFrameInjection ≡ false
round79PressureContractionDeterminesFrameInjectionIsFalse = refl

round79CorrectC3NeedsStretchingAndRotationIsTrue :
  round79CorrectC3NeedsStretchingAndRotation ≡ true
round79CorrectC3NeedsStretchingAndRotationIsTrue = refl

round79ClayPromotionIsFalse : round79ClayPromotion ≡ false
round79ClayPromotionIsFalse = refl
