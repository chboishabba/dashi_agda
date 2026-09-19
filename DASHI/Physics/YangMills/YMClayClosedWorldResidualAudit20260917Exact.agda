{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayClosedWorldResidualAudit20260917Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CLOSED-WORLD RESIDUAL AUDIT — 2026-09-19 route-Pareto recut
--
-- Search result != theorem authority != physical inhabitant.
--
-- Two honest mass-gap routes now coexist:
--
--   S / direct source-OS route:
--     selected finite T5 source localization
--       -> continuum pair clustering
--       -> SAME reconstructed OS Hamiltonian spectral transfer
--       -> physical mass-gap certificate.
--
--   G / strong finite-gap-recovery route:
--     dense L2 transfer defect
--       -> uniform finite gap
--       -> P_a/E_a + Mosco/recovery
--       -> continuum gap.
--
-- F1-C/F1-D and Sprint P_a/E_a are genuine mathematics on route G, but are
-- not globally mandatory terminal leaves because route S bypasses them.
------------------------------------------------------------------------

data ResidualClass : Set where
  sourceLocalization : ResidualClass
  sameObjectAttachment : ResidualClass
  quantitativeCalibration : ResidualClass
  physicalContinuumConstruction : ResidualClass
  physicalSpectralIdentification : ResidualClass
  physicalCommonCoreConstruction : ResidualClass

data ResidualStatus : Set where
  unpaid : ResidualStatus
  compilerOwned : ResidualStatus
  obsoleteStrength : ResidualStatus
  routeSpecific : ResidualStatus

record ExactResidual : Set where
  constructor exact-residual
  field
    residualClass : ResidualClass
    owner : String
    fieldOrTheorem : String
    status : ResidualStatus
    evidence : String

open ExactResidual public

------------------------------------------------------------------------
-- Shared / direct-source route coordinates.
------------------------------------------------------------------------

sourceSelectedLocalization : ExactResidual
sourceSelectedLocalization = exact-residual
  sourceLocalization
  "R296 / R343-R346 / R387"
  "literal selected two-J magnitude / direct selected spectral upper"
  unpaid
  "R387 is the least-privilege terminal source consumer. Full R339 magnitude equality, source-root presentation and source-envelope coordinates are not terminal fields."

r339MagnitudeEquality : ExactResidual
r339MagnitudeEquality = exact-residual
  sameObjectAttachment
  "BalabanCMP116CanonicalSelectedT5ApplicationRound339Exact.agda"
  "sourceMagnitudeIsSelectedMagnitude"
  obsoleteStrength
  "R343 records sourceMagnitudeEqualityPrimitiveForMassGapConsumer = false."

wilsonR295CarrierEquality : ExactResidual
wilsonR295CarrierEquality = exact-residual
  sameObjectAttachment
  "YMClayF1WilsonR295SameObjectWeldExact.agda"
  "independent Wilson-to-R295 carrier equality"
  compilerOwned
  "R313 builds R296 on the same T5 carrier and R315 supplies the proof-relevant Wilson-cylinder presentation there."

h2aOSIndexedTimeSupport : ExactResidual
h2aOSIndexedTimeSupport = exact-residual
  sameObjectAttachment
  "BalabanOSIndexedPairwiseEuclideanSemanticsRound332Exact.agda"
  "Euclidean time element + supportDistanceIsTime on the OS1 translation action"
  unpaid
  "The translated observable uses the OS1 action definitionally; the remaining physical fields identify integer Euclidean time and the selected support distance."

h2bWilsonCylinderPresentation : ExactResidual
h2bWilsonCylinderPresentation = exact-residual
  sameObjectAttachment
  "BalabanPairwiseWilsonBoundedTestsRound315Exact.agda"
  "PairwiseWilsonCylinderPresentation"
  unpaid
  "Finite Wilson-cylinder boundedness is already imported/compiler-owned. The physical residue is the same-carrier Wilson product/multiplication presentation."

h2cSequentialOrderClosure : ExactResidual
h2cSequentialOrderClosure = exact-residual
  physicalContinuumConstruction
  "BalabanClayCanonicalBFrontierRound330Exact.agda"
  "T5SequentialOrderClosureWeld + shared RationalSequentialOrderClosure"
  unpaid
  "No new YM decay estimate is needed; the one-sided limit passage is a shared analysis capability plus a convergence-carrier weld."

literalMeasureExpectationConvergence : ExactResidual
literalMeasureExpectationConvergence = exact-residual
  physicalContinuumConstruction
  "BalabanClayT5PhysicalMeasureGramContinuityExact.agda"
  "PhysicalMeasureConvergenceData expectation convergence on selected Wilson tests"
  unpaid
  "The direct route still needs the literal finite measures/expectations to converge to the SAME continuum measure. R278 then derives connected-covariance convergence mechanically."

connectedCovarianceLimit : ExactResidual
connectedCovarianceLimit = exact-residual
  physicalContinuumConstruction
  "BalabanConnectedCovarianceExpectationLimitRound278Exact.agda"
  "selectedConnectedCovarianceMagnitudeConverges"
  compilerOwned
  "Once the selected left/right/product expectation convergence and scalar continuity are supplied, covariance-magnitude convergence is machine-checked."

h3OSHamiltonianTransferCoordinate : ExactResidual
h3OSHamiltonianTransferCoordinate = exact-residual
  physicalSpectralIdentification
  "BalabanOSIndexedTransferCoordinateRound331Exact.agda"
  "coordinateOfReconstructedHamiltonian"
  unpaid
  "The remaining H3 theorem is exactly that the decay/energy coordinate is the transfer coordinate OF the SAME OS reconstructed Hamiltonian."

halfRateSpectralTransfer : ExactResidual
halfRateSpectralTransfer = exact-residual
  physicalSpectralIdentification
  "BalabanHalfRateTransferCoordinateMassGapRound316Exact.agda"
  "halfRateClusteringTransfer"
  compilerOwned
  "The concrete q=1/2 clustering-to-spectrum theorem is standard imported spectral mathematics once the same-Hamiltonian transfer coordinate is supplied."

directSourceOSMassGapCompiler : ExactResidual
directSourceOSMassGapCompiler = exact-residual
  physicalSpectralIdentification
  "YMClayDirectSourceOSMassGapFrontierExact.agda / R333"
  "directSourceOSBuildsPhysicalMassGap"
  compilerOwned
  "R333 composes H2a/H2b/H2c/H3 and R316 produces the physical mass-gap certificate. No dense-L2 normalization, finite trajectory-gap calibration or P_a/E_a Mosco recovery is consumed by this direct route."

------------------------------------------------------------------------
-- Route G only: strong finite-gap / Mosco recovery.
------------------------------------------------------------------------

strongRouteF1CTranslatedL2 : ExactResidual
strongRouteF1CTranslatedL2 = exact-residual
  quantitativeCalibration
  "YMClayF1TranslatedPairL2CalibrationExact.agda"
  "selected one-step rooted shell <= c_k * physicalNormSq"
  routeSpecific
  "This is a genuine one-sided physical contraction theorem for the strong finite-gap route. The corrected pair is decode(psi), tau_1 psi; diagonal insertion and envelope equality are both overstrong. R387/R333 do not consume this theorem."

strongRouteF1DTrajectory : ExactResidual
strongRouteF1DTrajectory = exact-residual
  quantitativeCalibration
  "YMClayOutstandingPhysicalFrontierExact.agda"
  "Delta*a_k <= 1-c_k"
  routeSpecific
  "Needed to turn the dense transfer defect into a uniform finite gap. The direct source/OS spectral route does not consume it."

strongRoutePa : ExactResidual
strongRoutePa = exact-residual
  physicalContinuumConstruction
  "YMSprint112ContinuumSamplingProjectionMapCandidate.agda"
  "actual P_a sampling/projection"
  routeSpecific
  "Required by the finite-gap/Mosco recovery route; samplingProjectionMapConstructedHere remains false."

strongRouteEa : ExactResidual
strongRouteEa = exact-residual
  physicalContinuumConstruction
  "YMSprint112RenormalizedInterpolationMapCandidate.agda"
  "actual E_a interpolation"
  routeSpecific
  "Required by the finite-gap/Mosco recovery route; interpolationMapConstructedHere remains false."

strongRouteGaugeNormResidual : ExactResidual
strongRouteGaugeNormResidual = exact-residual
  physicalContinuumConstruction
  "YMSprint113-122 estimate/reducer chain"
  "gauge/quotient + norm + approximate inverse + residual/energy recovery"
  routeSpecific
  "The Sprint reducers remain fail-closed. These estimates construct the actual recovery system, but are not terminal prerequisites of the direct source/OS route."

strongRouteRecoveryCompiler : ExactResidual
strongRouteRecoveryCompiler = exact-residual
  physicalContinuumConstruction
  "BalabanVacuumOrthogonalMoscoRecoveryExact.agda"
  "physicalVacuumGapAfterRecovery"
  compilerOwned
  "Once an actual physical recovery system exists, continuum gap transport is compiler output."

------------------------------------------------------------------------
-- Common downstream physical YM/OS identification.
------------------------------------------------------------------------

f4StressCurrentWard : ExactResidual
f4StressCurrentWard = exact-residual
  physicalCommonCoreConstruction
  "YangMillsStressChargeLocalCoreCutoffStabilizationExact + YangMillsLocalCurrentMicrocausalShellExact"
  "renormalized stress/current + translation Ward/locality data"
  unpaid
  "Generic cutoff stabilization and outer-shell elimination are paid. The actual continuum stress/Ward data remain physical."

f4CommonCoreClosure : ExactResidual
f4CommonCoreClosure = exact-residual
  physicalCommonCoreConstruction
  "YMClayPhysicalStressOSCommonCoreWitnessExact.agda"
  "StressOSCommonCoreData on the actual reconstructed continuum"
  unpaid
  "Need same physical YM and OS core actions and both closure identifications."

f4EvolutionEquality : ExactResidual
f4EvolutionEquality = exact-residual
  physicalCommonCoreConstruction
  "YMClayPhysicalStressOSCommonCoreWitnessExact.agda"
  "physicalSameEvolution"
  compilerOwned
  "Same generator follows from common-core equality; Stone/OS then gives same evolution."

------------------------------------------------------------------------
-- Route-Pareto bookkeeping.
------------------------------------------------------------------------

fullR339MagnitudeEqualityPrimitive : Bool
fullR339MagnitudeEqualityPrimitive = false

directSourceRouteRequiresDenseL2F1C : Bool
directSourceRouteRequiresDenseL2F1C = false

directSourceRouteRequiresTrajectoryF1D : Bool
directSourceRouteRequiresTrajectoryF1D = false

directSourceRouteRequiresPaEaMosco : Bool
directSourceRouteRequiresPaEaMosco = false

directSourceRouteRequiresLiteralMeasureConvergence : Bool
directSourceRouteRequiresLiteralMeasureConvergence = true

directSourceRouteRequiresOSReconstruction : Bool
directSourceRouteRequiresOSReconstruction = true

strongFiniteGapRecoveryRouteStillValid : Bool
strongFiniteGapRecoveryRouteStillValid = true

f4EvolutionEqualityPrimitive : Bool
f4EvolutionEqualityPrimitive = false

fullR339MagnitudeEqualityPrimitiveIsFalse :
  fullR339MagnitudeEqualityPrimitive ≡ false
fullR339MagnitudeEqualityPrimitiveIsFalse = refl

directSourceRouteRequiresDenseL2F1CIsFalse :
  directSourceRouteRequiresDenseL2F1C ≡ false
directSourceRouteRequiresDenseL2F1CIsFalse = refl

directSourceRouteRequiresTrajectoryF1DIsFalse :
  directSourceRouteRequiresTrajectoryF1D ≡ false
directSourceRouteRequiresTrajectoryF1DIsFalse = refl

directSourceRouteRequiresPaEaMoscoIsFalse :
  directSourceRouteRequiresPaEaMosco ≡ false
directSourceRouteRequiresPaEaMoscoIsFalse = refl

unconditionalClayTheoremSupportedBySearchedRepositoryState : Bool
unconditionalClayTheoremSupportedBySearchedRepositoryState = false

unconditionalClayTheoremSupportedBySearchedRepositoryStateIsFalse :
  unconditionalClayTheoremSupportedBySearchedRepositoryState ≡ false
unconditionalClayTheoremSupportedBySearchedRepositoryStateIsFalse = refl

data ClosedWorldResidualAuditPresent : Set where
  closedWorldResidualAuditPresent : ClosedWorldResidualAuditPresent

closedWorldResidualAuditWitness : ClosedWorldResidualAuditPresent
closedWorldResidualAuditWitness = closedWorldResidualAuditPresent
