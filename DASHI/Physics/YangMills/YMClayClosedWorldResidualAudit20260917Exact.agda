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
  "YMClayLevel2CompositeTailWeldExact.agda"
  "literal product remainder on the actual completed composite projection = selected composite marked tail"
  unpaid
  "The same-family carrier is now explicit: the remainder is evaluated on Marked.compositeProjection completedState, not an arbitrary function. The only physical field is equality with Shared.compositeInsertionTail; the literal DyadicOPERemainderMajorant is then compiler output."

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
  "YMClayLevel2OPECoefficientCoordinateWeldExact.agda"
  "literal OPE coefficient = projection of the same RG/composite coordinate"
  unpaid
  "This is a same-object coordinate attachment, not a second global AF proof. Once supplied, all-depth OPE coefficient equality is machine-checked induction."

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
  "mapped finite Ward-charge sequence converges to the recovered continuum stress first variation"
  unpaid
  "This is the genuine Ward residue left by archaeology. The finite charge is rational while the recovered stress lives in StressRep.PairingScalar, so the bridge explicitly supplies the finite-charge representation map and convergence to the exact R131/R136 continuum first-variation target. No carrier equality by name is allowed."

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

d3FiniteWardAlgebraNewPhysicalTheorem : Bool
d3FiniteWardAlgebraNewPhysicalTheorem = false

d3FiniteToContinuumSameCurrentTransportStillPhysical : Bool
d3FiniteToContinuumSameCurrentTransportStillPhysical = true

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
