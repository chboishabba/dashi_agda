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
  physicalClayStressConstruction : ResidualClass
  physicalCommonCoreConstruction : ResidualClass
  physicalGRUnificationConstruction : ResidualClass

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
  "YMClayRouteSH1DirectSelectedMarkedDecayExact.agda / R320 / R398 / R387"
  "R320 mixedDerivativeMagnitudeBelowSelectedShell on the exact selected R318/T5 carrier"
  unpaid
  "Canonical H1 has one theorem-bearing physical/source field. R320 transports it to literal J directions; R398 constructs the exact finite T5 direct shell; R274/R284/R388 compile onward to the R387 terminal ABI. PublishedTwoJLocalization wrappers and separate source magnitude/root/distance applicability are optional stronger producer packaging, not canonical H1 coordinates."

historicalH1PublishedApplicabilityPackaging : ExactResidual
historicalH1PublishedApplicabilityPackaging = exact-residual
  sameObjectAttachment
  "BalabanT5UnlocalizedJSourceLocalizationRound318Exact.agda / R322 / R327"
  "PublishedTwoJLocalizationForBase + separate selected source magnitude/root/distance applicability"
  obsoleteStrength
  "R320 is a strictly smaller consumer-first H1 ABI with one selected-carrier inequality. R322/R327 and the source-authority adapter remain valid producer tactics because they compile into R320."

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
  "full SequentialOrderClosure record + sameConvergence weld"
  obsoleteStrength
  "R330/R333 remain a valid stronger compatibility packaging, but the terminal R387 compiler does not consume this record or the sameConvergence equality."

h2cSelectedLimitUpperClosure : ExactResidual
h2cSelectedLimitUpperClosure = exact-residual
  physicalContinuumConstruction
  "YMClayRouteSSelectedLimitClosureExact.agda / BalabanCMP116R281SourceResponseSameObjectRound342Exact.agda"
  "SelectedLimitUpperClosure on the actual R278/T5 scalar convergence"
  unpaid
  "This is the exact one-sided ordered-limit proposition consumed by R387: Converges sequence target and sequence <= upper imply target <= upper. It is standard/shared analysis rather than a fresh YM decay estimate. PhysicalMeasureConvergenceData alone does not store order-closedness, so an inhabitant is still required."

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
-- Literal Clay local-QFT/stress endpoint.
--
-- OS reconstruction machinery is already extensive.  The Clay-local residual
-- is the existing R127 same-family inhabitant plus physical stress/OPE data on
-- that literal family.  The stronger stress-charge/common-core theorem is a
-- separate optional strengthening, not a primitive Clay payment.
------------------------------------------------------------------------

level2R129SameFamilyRecovery : ExactResidual
level2R129SameFamilyRecovery = exact-residual
  sameObjectAttachment
  "BalabanSectorQFTRecoveryExportRound129Exact.agda / YMClayLevel2SameFamilyStressRecoveryExact.agda"
  "actual R129 same-family recovery package"
  unpaid
  "Once R129 is inhabited, the R127 OS-to-literal weld, literal continuum-limit evidence, literal Schwinger membership and literal stress source-derivative identification are compiler-owned exports. Do not count R127 again as an independent downstream payment."

level2R127AfterR129 : ExactResidual
level2R127AfterR129 = exact-residual
  sameObjectAttachment
  "YMClayLevel2SameFamilyStressRecoveryExact.agda"
  "r129ExportsOSLiteralWeld"
  compilerOwned
  "R129 contains R128, which contains the R127 OSLiteralSchwingerWeld. The same-family equality is therefore an export of the chosen recovery package."

level2OPEProductTailIdentification : ExactResidual
level2OPEProductTailIdentification = exact-residual
  physicalClayStressConstruction
  "YMClayLevel2D1PhysicalMinCutExact.agda"
  "literal Clay opeRemainder = selected R129 compositeInsertionTail"
  unpaid
  "R129 already fixes the same completed composite family. The older auxiliary productRemainder function adds no proof strength: choosing it freely plus two equalities is equivalent to this one direct equality. The compatibility compiler reconstructs the old record and the existing marked-tail theorem then builds the DyadicOPERemainderMajorant. No independent composite carrier and no new analytic inequality are introduced."

level2GlobalAFSecondPayment : ExactResidual
level2GlobalAFSecondPayment = exact-residual
  physicalClayStressConstruction
  "BalabanPointwiseBetaBoundsToFrozenRowAExact.agda / YMClayLevel2WardRGReuseExact.agda"
  "second global asymptotic-freedom trajectory theorem in Row D"
  obsoleteStrength
  "The positive/tuned global AF trajectory is already Row A. Level 2 must not charge another AF theorem; only attachment of the literal OPE coefficient to the already-selected RG mixing/UV coordinate remains."

level2OPECoefficientRGCoordinateAttachment : ExactResidual
level2OPECoefficientRGCoordinateAttachment = exact-residual
  physicalClayStressConstruction
  "YMClayLevel2D2PhysicalMinCutExact.agda / YMClayLevel2LiteralOPECoefficientScaleAttachmentExact.agda"
  "physical composite-operator transport + same operator recurrence + literal position-to-RG-depth coefficient attachment"
  unpaid
  "The repo already owns the CompositeRGParallelTransport interface, so no second mixing-map abstraction is needed. But no physical inhabitant of that transport was found, and the literal Clay opeCoefficient is position-indexed rather than Nat-indexed. D2 therefore requires: instantiate the native operator transport, put physical/reference coefficient trajectories on that same transport with common UV normalization, and certify which short-distance RG depth corresponds to the literal insertion position. All-depth coefficient equality is then compiler-owned."

level2FiniteWardConservation : ExactResidual
level2FiniteWardConservation = exact-residual
  physicalClayStressConstruction
  "YangMillsLatticeStressWardSliceConservationExact.agda"
  "finite periodic Ward balance -> conserved slice charge"
  compilerOwned
  "The finite Ward algebra is already machine-checked and must not be re-proved in Level 2."

level2GeneratedActionStressProvenance : ExactResidual
level2GeneratedActionStressProvenance = exact-residual
  physicalClayStressConstruction
  "BalabanUnifiedGeneratedActionRecoveryRound136Exact.agda / BalabanCompositeStressFirstVariationRound144Exact.agda"
  "same generated action / first variation / localized D1 stress provenance"
  compilerOwned
  "R132-R136 and R142-R144 already provide the compiler spine once their physical source-instantiation fields are inhabited."

level2ContinuumWardTransport : ExactResidual
level2ContinuumWardTransport = exact-residual
  physicalClayStressConstruction
  "YMClayLevel2ContinuumWardTransportExact.agda"
  "for every admissible perturbation h: mapped cutoff-indexed Ward-charge sequence iota_k(Q_k[h]) converges to the recovered continuum stress first variation deltaS_infinity[h]"
  unpaid
  "This is the genuine Ward residue left by archaeology. The finite charge is rational while the recovered stress lives in StressRep.PairingScalar. The charge family must be indexed by the same metric perturbation h, and the rational-to-pairing representation may depend on cutoff k: the target is iota_k(Q_k[h]) -> deltaS_infinity[h]. R131/R136 supplies the exact continuum target but no finite-charge convergence theorem."

level2LiteralClayStressOPECompiler : ExactResidual
level2LiteralClayStressOPECompiler = exact-residual
  physicalClayStressConstruction
  "YangMillsClayStressOPERequirementBoundaryExact.agda / YMClayOSLiteralStressRouteParetoExact.agda"
  "LiteralClayStressOPEEvidence -> stressTensorAndOperatorProductExpansion"
  compilerOwned
  "Once the same-family stress/OPE predicates are physically inhabited, the literal Clay postcondition is machine-checked. No stress-charge/common-core/Stone theorem is consumed."

------------------------------------------------------------------------
-- Optional stronger same-generator theorem.
------------------------------------------------------------------------

strongStressCurrentWard : ExactResidual
strongStressCurrentWard = exact-residual
  physicalCommonCoreConstruction
  "YangMillsStressChargeLocalCoreCutoffStabilizationExact + YangMillsLocalCurrentMicrocausalShellExact"
  "renormalized stress/current + translation Ward/locality data"
  routeSpecific
  "Needed for the stronger local theorem identifying the stress charge with H_OS, not for the literal Clay stress/OPE postcondition."

strongCommonCoreClosure : ExactResidual
strongCommonCoreClosure = exact-residual
  physicalCommonCoreConstruction
  "YMClayPhysicalStressOSCommonCoreWitnessExact.agda"
  "StressOSCommonCoreData on the actual reconstructed continuum"
  routeSpecific
  "Same physical core actions and closure identifications remain genuine inputs for the stronger stress-generator theorem."

strongEvolutionEquality : ExactResidual
strongEvolutionEquality = exact-residual
  physicalCommonCoreConstruction
  "YMClayPhysicalStressOSCommonCoreWitnessExact.agda"
  "physicalSameEvolution"
  compilerOwned
  "On the stronger route, same generator follows from common-core equality and Stone/OS then gives same evolution."

------------------------------------------------------------------------
-- GR / unification consumption is another distinct strengthening.
------------------------------------------------------------------------

grStressIdentification : ExactResidual
grStressIdentification = exact-residual
  physicalGRUnificationConstruction
  "PhysicalRGCFTFullPhysicsBridge.agda / W4MatterStressEnergyInterfaceReceipt.agda"
  "stressTensorMatchesEinsteinStressEnergy + stressWardMatchesContractedBianchi"
  routeSpecific
  "These are bridge fields/receipt targets, not inhabitants. The generic StressEnergyBridgeReceiptSurface contains postulated AQFT target declarations and is intentionally excluded from the trusted YM theorem cone."

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

directSourceTerminalRequiresR330SequentialClosureRecord : Bool
directSourceTerminalRequiresR330SequentialClosureRecord = false

directSourceTerminalRequiresR330SameConvergenceWeld : Bool
directSourceTerminalRequiresR330SameConvergenceWeld = false

directSourceTerminalRequiresSelectedLimitUpperClosure : Bool
directSourceTerminalRequiresSelectedLimitUpperClosure = true

directSourceRouteRequiresOSReconstruction : Bool
directSourceRouteRequiresOSReconstruction = true

strongFiniteGapRecoveryRouteStillValid : Bool
strongFiniteGapRecoveryRouteStillValid = true

strongStressGeneratorRouteIsClayPrimitive : Bool
strongStressGeneratorRouteIsClayPrimitive = false

grStressUnificationRouteIsClayPrimitive : Bool
grStressUnificationRouteIsClayPrimitive = false

literalClayStressOPERequiresCommonCoreGeneratorEquality : Bool
literalClayStressOPERequiresCommonCoreGeneratorEquality = false

literalClayStressOPERequiresStoneEvolutionEquality : Bool
literalClayStressOPERequiresStoneEvolutionEquality = false

osReconstructionMachineryMissing : Bool
osReconstructionMachineryMissing = false

r127IndependentAfterR129Recovery : Bool
r127IndependentAfterR129Recovery = false

dyadicOPERemainderIndependentAfterCompositeTailIdentification : Bool
dyadicOPERemainderIndependentAfterCompositeTailIdentification = false

d1NewCompositeTailDecayTheoremRequired : Bool
d1NewCompositeTailDecayTheoremRequired = false

d1SameCompletedCompositeTailAttachmentStillPhysical : Bool
d1SameCompletedCompositeTailAttachmentStillPhysical = true

d1AuxiliaryProductRemainderFunctionRequired : Bool
d1AuxiliaryProductRemainderFunctionRequired = false

d1IndependentCompositeCarrierAfterR129 : Bool
d1IndependentCompositeCarrierAfterR129 = false

d1IndependentCompositeCompletionAfterR129 : Bool
d1IndependentCompositeCompletionAfterR129 = false

d1NewAnalyticInequalityRequired : Bool
d1NewAnalyticInequalityRequired = false

globalAsymptoticFreedomTrajectoryIndependentInLevel2D : Bool
globalAsymptoticFreedomTrajectoryIndependentInLevel2D = false

finiteWardSliceConservationIndependentInLevel2D : Bool
finiteWardSliceConservationIndependentInLevel2D = false

generatedActionStressProvenanceIndependentAfterR136 : Bool
generatedActionStressProvenanceIndependentAfterR136 = false

allDepthOPECoefficientEqualityIndependentAfterOneStepLaw : Bool
allDepthOPECoefficientEqualityIndependentAfterOneStepLaw = false

d2NewGlobalAFTheoremRequired : Bool
d2NewGlobalAFTheoremRequired = false

d2SecondMixingMapAbstractionRequired : Bool
d2SecondMixingMapAbstractionRequired = false

d2LiteralClayCoefficientIsNatIndexed : Bool
d2LiteralClayCoefficientIsNatIndexed = false

d2PositionDepthSemanticsRequired : Bool
d2PositionDepthSemanticsRequired = true

d3FiniteWardAlgebraNewPhysicalTheorem : Bool
d3FiniteWardAlgebraNewPhysicalTheorem = false

d3FiniteToContinuumSameCurrentTransportStillPhysical : Bool
d3FiniteToContinuumSameCurrentTransportStillPhysical = true

d3PerturbationIndependentWardSequenceWouldBeTooWeak : Bool
d3PerturbationIndependentWardSequenceWouldBeTooWeak = true

d3CutoffIndependentChargeMapRequired : Bool
d3CutoffIndependentChargeMapRequired = false

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
