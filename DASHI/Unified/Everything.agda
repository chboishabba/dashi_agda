module DASHI.Unified.Everything where
import DASHI.Physics.Closure.R2P227729PairOrbit365CanonicalSymmetryExact as Pair365
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as Pairs365Owner
open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe using (just)
import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as ModeNSCut
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Convolution729
import DASHI.Physics.Closure.R2P227729BilinearCyclotomicPadCutExact as Bilinear729
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as OriginalAntipodalSym729
import DASHI.Physics.Closure.R2P227729HermitianThirteenPairFourierCodecExact as HermitianSym729
import DASHI.Physics.Closure.R2P227729HermitianConvolutionTransportExact as HermitianConv729
import DASHI.Physics.Closure.R2P281PlaneHermitianFiveOrbitConvolutionExact as HermitianPlane81
import DASHI.Physics.Closure.R2P2C4C5NyquistAntipodalFixedPointExact as NyquistSym729
import DASHI.Physics.Closure.R2P227729AntipodalThirteenFiveOrbitFourierCutExact as AntipodalSym729
import DASHI.Physics.Closure.R2P227729FourGridRetainedQuadraticParetoExact as FourGridPareto729
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Fourier729Core
import DASHI.Physics.Closure.R2P227729ExistingC3FourierConvolutionReuseExact as PeriodicFourier729
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as Fourier729Owner
import DASHI.Physics.Closure.R2P227729PairSixTritFibreBidiExact as Pair729
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as Fourier729
import DASHI.Physics.Closure.R2P2OpticalLattice369HamiltonianCutExact as R2P2Lattice
import DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact as R2P2Symbolic
import DASHI.Physics.Closure.R2P2369WaveOpticalCombInformationCutExact as R2P2Wave
import DASHI.Physics.Closure.R2P2ThreeClockLoopClosure369Exact as R2P2Loop
import DASHI.Physics.Closure.R2P2ClockBiasIdentifiabilityMaxCutExact as R2P2Bias
import DASHI.Physics.Closure.R2P2369AtomicQuantumDiamondArchitectureExact as R2P2369
import DASHI.Foundations.Base369BinaryTernaryRefinement as RefineR2P2
import DASHI.Physics.Closure.R2P2MountainOpticalClockComparisonExact as R2P2
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as ParetoSnowballTOE
import DASHI.Unified.FleetFormalGapTargetTOEExact as FleetGapTOE
import DASHI.Unified.TOE369MaxCutKernelBidiTernaryExact as MaxCut369

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (_+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; _∷_; [])
open import Data.Empty using (⊥)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
import DASHI.Unified.ArithmeticMoonshine as ArithmeticMoonshine
import DASHI.Unified.BalabanRGTOERegression as BalabanRGTOE
import DASHI.Unified.BalabanRGTOEMaxCutValidation
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Validation
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEValidation
import DASHI.Unified.FleetFormalGapTargetTOEValidation
import DASHI.Unified.Fleet58ManifestAcquisitionExact
import DASHI.Unified.Fleet58ManifestAcquisitionRegression
import DASHI.Unified.TOE369MaxCutKernelBidiTernaryValidation
import DASHI.Unified.SingularBasinCoarseRGTOEValidation
import DASHI.Unified.YMGoal1R559IbrahimTOEValidation
import DASHI.Unified.BrainFMRI as BrainFMRI
import DASHI.Unified.CarrierGrammar as CarrierGrammar
import DASHI.Unified.ChemistrySupervoxel as ChemistrySupervoxel
import DASHI.Unified.CrossScaleMatterPhysics as CrossScaleMatterPhysics
import DASHI.Unified.FormalObjectParents as FormalObjectParents
import DASHI.Unified.InvariantSpine as Spine
import DASHI.Unified.PNFHyperfabric as PNFHyperfabric
import DASHI.Unified.Physics as Physics
import DASHI.Unified.NavierStokesBM2TOEConvergenceExact as NSBM2TOE
import DASHI.Unified.NavierStokesBM2TOEConvergenceValidation
import DASHI.Unified.NavierStokesClayFrontierTOEConvergenceValidation
import DASHI.Physics.Foundations.Round5CompleteBoundary as Round5
canonicalUnifiedObjects : List Spine.UnifiedObjectInvariant
canonicalUnifiedObjects =
  CarrierGrammar.carrierGrammarObject
  ∷ ChemistrySupervoxel.chemistryObject
  ∷ ChemistrySupervoxel.supervoxelChemistryObject
  ∷ PNFHyperfabric.pnfHyperfabricObject
  ∷ BrainFMRI.brainFMRIObject
  ∷ ArithmeticMoonshine.arithmeticMoonshineObject
  ∷ Physics.navierStokesObject
  ∷ Physics.yangMillsObject
  ∷ CrossScaleMatterPhysics.crossScaleMatterPhysicsObject
  ∷ []
record UnifiedObjectTable : Setω where
  field
    objects :
      List Spine.UnifiedObjectInvariant
    objectsAreCanonical :
      objects ≡ canonicalUnifiedObjects
    allJProjectionExternalPromotion :
      Spine.UnifiedObjectInvariant → Bool
    allJProjectionExternalPromotionIsFalse :
      ∀ object → allJProjectionExternalPromotion object ≡ false
    allFormalProjectionExternalPromotion :
      Spine.UnifiedObjectInvariant → Spine.UniversalProjectionKind → Bool
    allFormalProjectionExternalPromotionIsFalse :
      ∀ object kind → allFormalProjectionExternalPromotion object kind ≡ false
    formalObjectParentSurface :
      FormalObjectParents.FormalObjectParentSurface
    crossScaleMatterPhysicsSurface :
      CrossScaleMatterPhysics.CrossScaleMatterPhysicsSurface
    round5FoundationsBoundary :
      Round5.Round5CompleteBoundary
    plainPolicy :
      String
canonicalUnifiedObjectTable : UnifiedObjectTable
canonicalUnifiedObjectTable =
  record
    { objects =
        canonicalUnifiedObjects
    ; objectsAreCanonical =
        refl
    ; allJProjectionExternalPromotion =
        Spine.objectExternalJPromotion
    ; allJProjectionExternalPromotionIsFalse =
        Spine.objectExternalJPromotionIsFalse
    ; allFormalProjectionExternalPromotion =
        Spine.objectProjectionPromotion
    ; allFormalProjectionExternalPromotionIsFalse =
        Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    ; formalObjectParentSurface =
        FormalObjectParents.canonicalFormalObjectParentSurface
    ; crossScaleMatterPhysicsSurface =
        CrossScaleMatterPhysics.canonicalCrossScaleMatterPhysicsSurface
    ; round5FoundationsBoundary =
        Round5.canonicalRound5CompleteBoundary
    ; plainPolicy =
        "Every unified facade object exposes observation, projection, carrier/role vector, residual, proof posture, invariant strength, and the required formal parent projection bundle. The bundle includes modular-j, Hecke, Bott, Kolmogorov, category, quotient, lattice, and operator projections. Literal authority is lane-specific; every formal projection has externalPromotion = false. The cross-scale matter/physics parent records the atoms-to-stellar composition ladder as structural and receipt-gated, with quantitative solar-style counterfactual prediction still blocked. The complete Round Five imports the PR 399 ternary/Yijing/natural-system theorem surface and adds fail-closed constants, dimension, atomic, nuclear, cosmological-observation, GR-QFT, hidden-sector collider, connected tri-to-bi junction, affine-slice, renderer-parity, low-precision search, and graph-to-field boundaries without promoting terminal unification or visual geometry to source ontology."
    }
brainFMRIRemainsNonPromoting :
  Spine.objectExternalJPromotion BrainFMRI.brainFMRIObject ≡ false
brainFMRIRemainsNonPromoting =
  refl
navierStokesRemainsNonPromoting :
  Spine.objectExternalJPromotion Physics.navierStokesObject ≡ false
navierStokesRemainsNonPromoting =
  refl

yangMillsRemainsNonPromoting :
  Spine.objectExternalJPromotion Physics.yangMillsObject ≡ false
yangMillsRemainsNonPromoting =
  refl

brainFMRIFormalProjectionsRemainNonPromoting :
  ∀ kind →
  Spine.objectProjectionPromotion BrainFMRI.brainFMRIObject kind ≡ false
brainFMRIFormalProjectionsRemainNonPromoting =
  Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    BrainFMRI.brainFMRIObject

navierStokesFormalProjectionsRemainNonPromoting :
  ∀ kind →
  Spine.objectProjectionPromotion Physics.navierStokesObject kind ≡ false
navierStokesFormalProjectionsRemainNonPromoting =
  Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    Physics.navierStokesObject

yangMillsFormalProjectionsRemainNonPromoting :
  ∀ kind →
  Spine.objectProjectionPromotion Physics.yangMillsObject kind ≡ false
yangMillsFormalProjectionsRemainNonPromoting =
  Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    Physics.yangMillsObject

------------------------------------------------------------------------
-- Joint Yang-Mills Balaban/R559 TOE receipt.
------------------------------------------------------------------------

import DASHI.Unified.BalabanR559TOEMaxCutExact as BalabanR559TOE
import DASHI.Unified.BalabanR559TOEMaxCutValidation

unifiedBalabanR559MaxCutReceipt :
  BalabanR559TOE.BalabanR559TOEMaxCutReceipt
unifiedBalabanR559MaxCutReceipt =
  BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

unifiedBalabanR559Gate4UnresolvedCount : ℕ
unifiedBalabanR559Gate4UnresolvedCount =
  BalabanR559TOE.gate4UnresolvedCount
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

unifiedBalabanR559Gate4UnresolvedCountIs58 :
  unifiedBalabanR559Gate4UnresolvedCount ≡ 58
unifiedBalabanR559Gate4UnresolvedCountIs58 =
  BalabanR559TOE.gate4UnresolvedCountIs58
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

unifiedBalabanR559Gate4DefinitionLevel : ProofLevel
unifiedBalabanR559Gate4DefinitionLevel =
  BalabanR559TOE.gate4DefinitionLevel
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

unifiedBalabanR559Gate4InhabitantsLevel : ProofLevel
unifiedBalabanR559Gate4InhabitantsLevel =
  BalabanR559TOE.gate4InhabitantsLevel
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

unifiedBalabanScaleTransferNonPromotion :
  BalabanR559TOE.ScaleTransferPromotion → ⊥
unifiedBalabanScaleTransferNonPromotion =
  BalabanR559TOE.scaleTransferPromotionEliminator
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

------------------------------------------------------------------------
-- R559 / Ibrahim / fleet-58 / generic-hyperfabric TOE convergence.
------------------------------------------------------------------------

import DASHI.Unified.R559IbrahimFleetHyperfabricTOEExact as FleetHyperTOE

unifiedR559IbrahimFleetHyperfabricReceipt :
  FleetHyperTOE.R559IbrahimFleetHyperfabricTOEReceipt
unifiedR559IbrahimFleetHyperfabricReceipt =
  FleetHyperTOE.canonicalR559IbrahimFleetHyperfabricTOEReceipt

unifiedYMGate4FormalGapsAre58 :
  FleetHyperTOE.ymGate4FormalGaps ≡ 58
unifiedYMGate4FormalGapsAre58 =
  FleetHyperTOE.ymGate4FormalGapsAre58

unifiedYMGate4PaidReductionLevel : ProofLevel
unifiedYMGate4PaidReductionLevel =
  FleetHyperTOE.ymGate4PaidReductionLevel

unifiedYMGate4InhabitantsLevel : ProofLevel
unifiedYMGate4InhabitantsLevel =
  FleetHyperTOE.ymGate4InhabitantsLevel

unifiedFleet58DoesNotIdentifyYMGate4 :
  FleetHyperTOE.Fleet58EqualsYMGate4SameObject → ⊥
unifiedFleet58DoesNotIdentifyYMGate4 =
  FleetHyperTOE.fleet58CardinalityDoesNotProveYMGate4Identity

unifiedFleetFormalGapsAre58 :
  FleetHyperTOE.fleetFormalGaps ≡ 58
unifiedFleetFormalGapsAre58 =
  FleetHyperTOE.fleetFormalGapsAre58

------------------------------------------------------------------------
-- Implement-A-to-D terminal unified validation.
------------------------------------------------------------------------

import DASHI.Unified.YMImplementAToDTOEMaxCutExact as YMAD
import DASHI.Unified.YMImplementAToDTOEMaxCutValidation

unifiedYMImplementAToDMaxCutReceipt :
  YMAD.YMImplementAToDTOEMaxCutReceipt
unifiedYMImplementAToDMaxCutReceipt =
  YMAD.canonicalYMImplementAToDTOEMaxCutReceipt

------------------------------------------------------------------------
-- Navier-Stokes B / R571 M2 normalized TOE receipt.
------------------------------------------------------------------------

unifiedNavierStokesBM2Receipt :
  NSBM2TOE.NavierStokesBM2TOEReceipt
unifiedNavierStokesBM2Receipt =
  NSBM2TOE.canonicalNavierStokesBM2TOEReceipt

unifiedNavierStokesBM2ZKPFrame :
  NSBM2TOE.NavierStokesBM2TOEZKPFrame
unifiedNavierStokesBM2ZKPFrame =
  NSBM2TOE.canonicalNavierStokesBM2TOEZKPFrame

------------------------------------------------------------------------
-- Typed Balaban continuum and Fleet target aggregate aliases.
------------------------------------------------------------------------

unifiedBalabanContinuumLimitReceipt :
  BalabanRGTOE.BalabanContinuumLimitReceipt
unifiedBalabanContinuumLimitReceipt =
  BalabanRGTOE.balabanContinuumLimitReceipt

unifiedBalabanContinuumLimitPromotionImpossible :
  BalabanRGTOE.BalabanContinuumLimitPromotion → ⊥
unifiedBalabanContinuumLimitPromotionImpossible =
  BalabanRGTOE.balabanContinuumLimitPromotionImpossible

unifiedDepthContinuumLimitReceipt :
  BalabanRGTOE.DepthContinuumLimitReceipt
unifiedDepthContinuumLimitReceipt =
  BalabanRGTOE.depthContinuumLimitReceipt

unifiedDepthContinuumLimitPromotionImpossible :
  BalabanRGTOE.DepthContinuumLimitPromotion → ⊥
unifiedDepthContinuumLimitPromotionImpossible =
  BalabanRGTOE.depthContinuumLimitPromotionImpossible

unifiedFleetDischargedCoreKnowledgeFibres : ℕ
unifiedFleetDischargedCoreKnowledgeFibres =
  FleetGapTOE.dischargedCoreKnowledgeFibres
    FleetGapTOE.canonicalFleetFormalGapTargetReceipt

unifiedFleetDischargedCoreKnowledgeFibresIs584 :
  unifiedFleetDischargedCoreKnowledgeFibres ≡ 584
unifiedFleetDischargedCoreKnowledgeFibresIs584 =
  FleetGapTOE.fleetRecordedDischargedCountIs584

unifiedFleetPolarityContradictionGaps : ℕ
unifiedFleetPolarityContradictionGaps =
  FleetGapTOE.polarityContradictionGaps
    FleetGapTOE.canonicalFleetFormalGapTargetReceipt

unifiedFleetPolarityContradictionGapsIs44 :
  unifiedFleetPolarityContradictionGaps ≡ 44
unifiedFleetPolarityContradictionGapsIs44 =
  FleetGapTOE.fleetRecordedContradictionCountIs44

unifiedFleetUnformalisedFormalGaps : ℕ
unifiedFleetUnformalisedFormalGaps =
  FleetGapTOE.unformalisedFormalGaps
    FleetGapTOE.canonicalFleetFormalGapTargetReceipt

unifiedFleetUnformalisedFormalGapsIs58 :
  unifiedFleetUnformalisedFormalGaps ≡ 58
unifiedFleetUnformalisedFormalGapsIs58 =
  FleetGapTOE.fleetRecordedUnformalisedGapCountIs58

unifiedFleetTargetsOnlyUnformalisedFormalGaps :
  FleetGapTOE.targetOnlyUnformalisedFormalGaps
    FleetGapTOE.canonicalFleetFormalGapTargetReceipt
  ≡ true
unifiedFleetTargetsOnlyUnformalisedFormalGaps =
  FleetGapTOE.fleetTargetsOnlyUnformalisedFormalGaps


------------------------------------------------------------------------
-- Fleet named-manifest acquisition boundary.
------------------------------------------------------------------------

unifiedFleetManifestAcquisitionDemand =
  FleetGapTOE.fleetManifestAcquisitionDemand

unifiedFleetNamedManifestStillMissing :
  FleetGapTOE.namedFormalGapManifestAcquired ≡ false
unifiedFleetNamedManifestStillMissing =
  FleetGapTOE.namedFormalGapManifestAcquiredIsFalse

unifiedFleetPerGapDispatchStillBlocked :
  FleetGapTOE.perGapDispatchEnabled ≡ false
unifiedFleetPerGapDispatchStillBlocked =
  FleetGapTOE.perGapDispatchEnabledIsFalse

unifiedFleetRelatedSymbolsRequired :
  FleetGapTOE.fleetRelatedSymbolsRequired ≡ true
unifiedFleetRelatedSymbolsRequired =
  FleetGapTOE.fleetRelatedSymbolsRequiredIsTrue

unifiedFleetDiscoverRequired :
  FleetGapTOE.fleetDiscoverRequired ≡ true
unifiedFleetDiscoverRequired =
  FleetGapTOE.fleetDiscoverRequiredIsTrue

unifiedFleetRoundLineageRequired :
  FleetGapTOE.fleetRoundLineageRequired ≡ true
unifiedFleetRoundLineageRequired =
  FleetGapTOE.fleetRoundLineageRequiredIsTrue

unifiedFleetCountDoesNotCreateNamedManifest :
  FleetGapTOE.CountCreatesNamedManifest → ⊥
unifiedFleetCountDoesNotCreateNamedManifest =
  FleetGapTOE.fleetCountDoesNotCreateNamedManifest

------------------------------------------------------------------------
-- Direct Pareto / snowball / Ibrahim and ternary-27 non-promotion surface.
------------------------------------------------------------------------

unifiedIbrahimSearchPriorityDoesNotCreateProof :
  ParetoSnowballTOE.SearchPriorityCreatesProof → ⊥
unifiedIbrahimSearchPriorityDoesNotCreateProof =
  ParetoSnowballTOE.searchPriorityDoesNotCreateProof

unifiedIbrahimProducerSourceDoesNotCreateRunReceipt :
  ParetoSnowballTOE.ProducerSourceCreatesRunReceipt → ⊥
unifiedIbrahimProducerSourceDoesNotCreateRunReceipt =
  ParetoSnowballTOE.producerSourceDoesNotCreateRunReceipt

unifiedIbrahimDegree729DoesNotCreateMonsterHZetaRecognition :
  ParetoSnowballTOE.Degree729CreatesMonsterHZetaRecognition → ⊥
unifiedIbrahimDegree729DoesNotCreateMonsterHZetaRecognition =
  ParetoSnowballTOE.degree729DoesNotCreateMonsterHZetaRecognition

unifiedIbrahimPaperOracleDoesNotIdentifyHistoricalDump :
  ParetoSnowballTOE.PaperOracleIdentifiesDump → ⊥
unifiedIbrahimPaperOracleDoesNotIdentifyHistoricalDump =
  ParetoSnowballTOE.paperOracleDoesNotIdentifyHistoricalDump

unifiedIbrahimRoutePreferenceDoesNotCreateExecutionReceipt :
  ParetoSnowballTOE.RoutePreferenceCreatesExecutionReceipt → ⊥
unifiedIbrahimRoutePreferenceDoesNotCreateExecutionReceipt =
  ParetoSnowballTOE.routePreferenceDoesNotCreateExecutionReceipt

unifiedIbrahimMergedLeanSourceDoesNotCreateKernelReceipt :
  ParetoSnowballTOE.MergedLeanSourceCreatesKernelReceipt → ⊥
unifiedIbrahimMergedLeanSourceDoesNotCreateKernelReceipt =
  ParetoSnowballTOE.mergedLeanSourceDoesNotCreateKernelReceipt

unifiedIbrahimOEISDoesNotCreateMultiplicityAction :
  ParetoSnowballTOE.NinetyOEISEqualityCreatesMultiplicityAction → ⊥
unifiedIbrahimOEISDoesNotCreateMultiplicityAction =
  ParetoSnowballTOE.oeisDoesNotCreateMultiplicityAction

unifiedIbrahimFiniteIrreducibilityDoesNotCreateMonsterHZetaRecognition :
  ParetoSnowballTOE.FiniteIrreducibilityCreatesMonsterHZetaRecognition → ⊥
unifiedIbrahimFiniteIrreducibilityDoesNotCreateMonsterHZetaRecognition =
  ParetoSnowballTOE.finiteIrreducibilityDoesNotCreateMonsterHZetaRecognition

unifiedIbrahimCurrentQidDoesNotIdentifyHistoricalTitle :
  ParetoSnowballTOE.CurrentQidIdentifiesHistoricalTitle → ⊥
unifiedIbrahimCurrentQidDoesNotIdentifyHistoricalTitle =
  ParetoSnowballTOE.currentQidDoesNotIdentifyHistoricalTitle

unified369Ternary27MonsterRepresentationNotPromoted =
  MaxCut369.toe27MonsterRepresentationNotPromoted

unified369Ternary27MonsterEmbeddingNotPromoted =
  MaxCut369.toe27MonsterEmbeddingNotPromoted

------------------------------------------------------------------------
-- Live Gate-4 frontier and Fleet target selection.
------------------------------------------------------------------------

unifiedCurrentGate4FrontierLedgerLevel : ProofLevel
unifiedCurrentGate4FrontierLedgerLevel =
  FleetHyperTOE.currentGate4FrontierLedgerLevel

unifiedCurrentGate4ClusteringToTransferGapLevel : ProofLevel
unifiedCurrentGate4ClusteringToTransferGapLevel =
  FleetHyperTOE.currentGate4ClusteringToTransferGapLevel

unifiedFleetFormalGapTargetSelected : Bool
unifiedFleetFormalGapTargetSelected =
  FleetHyperTOE.fleetFormalGapTargetSelected

unifiedHistoricalGate4CountSelectedAsFleetTarget : Bool
unifiedHistoricalGate4CountSelectedAsFleetTarget =
  FleetHyperTOE.historicalGate4CountSelectedAsFleetTarget

unifiedFleetGate4EqualCardinalityDoesNotSelectCanonicalMap :
  FleetHyperTOE.fleetGate4EqualCardinalitySelectsCanonicalMap ≡ false
unifiedFleetGate4EqualCardinalityDoesNotSelectCanonicalMap =
  FleetHyperTOE.fleetGate4EqualCardinalityDoesNotSelectCanonicalMap

------------------------------------------------------------------------
-- R2P2 source-typed optical-clock comparison; do not promote quantum gravity.
------------------------------------------------------------------------

unifiedR2P2NoQGDiscovery :
  R2P2.quantumGravityEstablishedHere R2P2.canonicalR2P2ClockComparisonBoundary ≡ false
unifiedR2P2NoQGDiscovery =
  R2P2.r2p2HasNoClaimedQGDiscovery

unifiedR2P2NoAcceptedClockRatio :
  R2P2.fullClockComparisonUncertaintyAcceptedHere R2P2.canonicalR2P2ClockComparisonBoundary ≡ false
unifiedR2P2NoAcceptedClockRatio =
  R2P2.r2p2HasNoAcceptedClockRatio

------------------------------------------------------------------------
-- R2P2 369/atomic/quantum/diamond source-typed composition.
-- Exact finite index and graph assertions; no promoted GR/QG measurement.
------------------------------------------------------------------------

unifiedR2P2369Architecture :
  R2P2369.R2P2369FullLogicalArchitecture
unifiedR2P2369Architecture =
  R2P2369.canonicalR2P2369FullLogicalArchitecture

unifiedR2P2369RefinementDiamond :
  RefineR2P2.binaryRefine
    (RefineR2P2.ternaryRefine
      RefineR2P2.phase3Resolution)
  ≡ RefineR2P2.ternaryRefine
      (RefineR2P2.binaryRefine
        RefineR2P2.phase3Resolution)
unifiedR2P2369RefinementDiamond =
  R2P2369.resolutionDiamondAgrees

unifiedR2P2369NoQGPromotion :
  R2P2369.fullQGClaimProved unifiedR2P2369Architecture ≡ false
unifiedR2P2369NoQGPromotion =
  R2P2369.fullArchitectureDoesNotConstructQuantumGravity

unifiedR2P2369NoMeasurements :
  R2P2369.externalMeasurementsIngested unifiedR2P2369Architecture ≡ false
unifiedR2P2369NoMeasurements =
  R2P2369.fullArchitectureDoesNotIngestMeasurements

------------------------------------------------------------------------
-- Independent R2P2 max-cut: one-height clock-bias confounding is exact.
-- The second finite height separates only this selected candidate pair.
------------------------------------------------------------------------

unifiedR2P2BiasFiniteAmbiguity :
  R2P2Bias.syntheticRate R2P2Bias.baselineWithLargeBias 3
  ≡ R2P2Bias.syntheticRate R2P2Bias.doubledSlopeWithSmallBias 3
unifiedR2P2BiasFiniteAmbiguity =
  R2P2Bias.oneHeightCannotDiscriminate

unifiedR2P2BiasNoQuantumGravity :
  R2P2Bias.physicalQuantumGravityIdentified
    R2P2Bias.canonicalR2P2BiasIdentifiabilityMaxCut ≡ false
unifiedR2P2BiasNoQuantumGravity =
  R2P2Bias.thisExampleDoesNotProveQuantumGravity

------------------------------------------------------------------------
-- Three-clock ratio-loop integrity: conditional 369 finite witness only.
------------------------------------------------------------------------

unifiedR2P2LoopSyntheticClosure :
  R2P2Loop.loopNumerator ≡ R2P2Loop.loopDenominator
unifiedR2P2LoopSyntheticClosure =
  R2P2Loop.syntheticCycleCloses

unifiedR2P2LoopNullCannotProveCurvature :
  R2P2Loop.threeClockLoopNullImpliesCurvature
    R2P2Loop.canonicalThreeClockLoopSourceBoundary ≡ false
unifiedR2P2LoopNullCannotProveCurvature =
  R2P2Loop.threeClockLoopCannotClaimCurvature

------------------------------------------------------------------------
-- R2P2 / existing 369 wave constructor: exact fibre vs lossy trit.
-- This is not a measured optical phase, unitarity or gravity theorem.
------------------------------------------------------------------------

unifiedR2P2WaveSignedBeatRetained :
  (branch : R2P2Wave.BeatBranch) →
  R2P2Symbolic.decode
    (R2P2Symbolic.encode R2P2Wave.signedBeatWaveCoding branch)
    ≡ branch
unifiedR2P2WaveSignedBeatRetained =
  R2P2Wave.signedBeatEncodeDecode

unifiedR2P2WaveNoPhysicalPhasePromotion :
  R2P2Wave.c3ProvesOpticalCarrierPhaseCalibration
    R2P2Wave.canonicalWaveCombAuthorityBoundary ≡ false
unifiedR2P2WaveNoPhysicalPhasePromotion =
  R2P2Wave.waveBridgeDoesNotCalibratePhysicalPhase

------------------------------------------------------------------------
-- Same-clock optical-lattice control boundary: imported finite witness.
-- Ma 87Sr AA, Bothwell/Ye Sr and R2P2 Yb remain distinct instruments.
------------------------------------------------------------------------

unifiedR2P2FiniteLatticeNoncommuting :
  R2P2Lattice.nearestNeighbourAdjacency
    (R2P2Lattice.siteDependentPotential R2P2Lattice.leftBasisState)
  ≡ R2P2Lattice.siteDependentPotential
    (R2P2Lattice.nearestNeighbourAdjacency R2P2Lattice.leftBasisState)
  → ⊥
unifiedR2P2FiniteLatticeNoncommuting =
  R2P2Lattice.finiteLatticeOperatorsFailToCommute

unifiedR2P2NoInfiniteAAFromFinite3 :
  R2P2Lattice.finiteP3ProvesInfiniteAAThreshold
    R2P2Lattice.canonicalOpticalLattice369PhysicalAuthority ≡ false
unifiedR2P2NoInfiniteAAFromFinite3 =
  R2P2Lattice.latticeCannotProveInfiniteAAThreshold

unifiedR2P2OpticalLatticeNotQuantumGravity :
  R2P2Lattice.measuredQuantumGravityObserved
    R2P2Lattice.canonicalOpticalLattice369PhysicalAuthority ≡ false
unifiedR2P2OpticalLatticeNotQuantumGravity =
  R2P2Lattice.latticeDoesNotObserveQuantumGravity

------------------------------------------------------------------------
-- Ma 2026 S4 supercell N497=18, N813=11, nominal cross-product.
-- Equal number 18 does not identify a physical R2P2/369 wave carrier.
------------------------------------------------------------------------

unifiedMaSupercellNominal18to11 :
  R2P2Lattice.maFirst813Periods * R2P2Lattice.nominal813Nm + 3
  ≡ R2P2Lattice.maFirst497Periods * R2P2Lattice.nominal497Nm
unifiedMaSupercellNominal18to11 =
  R2P2Lattice.maFirstNominalSupercellOffset

unifiedMaSupercell18NotPhysicalC18 :
  R2P2Lattice.paperSupercell18EqualsPhysicalC18Realization
    R2P2Lattice.canonicalOpticalLattice369PhysicalAuthority ≡ false
unifiedMaSupercell18NotPhysicalC18 =
  R2P2Lattice.maSupercell18IsNotAnIdentifiedC18PhysicsRealization

------------------------------------------------------------------------
-- Reused exact balanced trit/binary codec and C3 aliasing NS cut.
-- Mathematical modes are labels. Codec inversion is not quadratic
-- Fourier fidelity, a Yb clock measurement, or a Clay NS theorem.
------------------------------------------------------------------------

unifiedThreeModeBinaryTernaryCodecRoundTrip :
  (m : ModeNSCut.ThreeMode) →
  ModeNSCut.twoBitsToThreeMode (ModeNSCut.threeModeToTwoBits m)
    ≡ just m
unifiedThreeModeBinaryTernaryCodecRoundTrip =
  ModeNSCut.threeModeTwoBitRoundTrip

unifiedThreeModeFourierQuadraticAlias :
  ModeNSCut.periodicQuadraticModeSum ModeNSCut.modePlus ModeNSCut.modePlus
    ≡ ModeNSCut.modeMinus
unifiedThreeModeFourierQuadraticAlias =
  ModeNSCut.positivePositiveAliasesToNegative

unifiedThreeModeBinaryTernaryDoesNotProveNS :
  ModeNSCut.nsClayRegularityProved
    ModeNSCut.canonicalThreeModeCodecNSAuthority ≡ false
unifiedThreeModeBinaryTernaryDoesNotProveNS =
  ModeNSCut.threeModeCodecIsNotAnNSProof

-- Existing framed-27 trit codec is a basis-label representation.
-- Exact NS k in Z^3 must not be confused with its C3^3 sample residue.
unifiedNS27ModeCubeQuadraticAlias :
  ModeNSCut.threeAxisPeriodicallyAliasedPlusXSquare
    ≡ ModeNSCut.threeAxisBalancedModeCube
        ModeNSCut.modeMinus ModeNSCut.modeZero ModeNSCut.modeZero
unifiedNS27ModeCubeQuadraticAlias =
  ModeNSCut.periodicThreeAxisPositiveXSquareWrapsToNegativeX

------------------------------------------------------------------------
-- 27x27 original ternary pair reused as source T^6, not GF(729).
-- Numeric pair incidence, exact integer-frequency output and five-point
-- index recovery are separate from original NS analytic and optical claims.
------------------------------------------------------------------------

unified729ActualInsidePairs :
  Fourier729.countWhereL Fourier729.insidePair27 Fourier729.pair729 ≡ 343
unified729ActualInsidePairs = Fourier729.exact343InWindowPairs

unified729ActualOutsidePairs :
  Fourier729.countWhereL
    (λ pair → Fourier729.notB (Fourier729.insidePair27 pair))
    Fourier729.pair729 ≡ 386
unified729ActualOutsidePairs = Fourier729.exact386OutOfWindowPairs

unified729SixTritPairBidi :
  (pair : Pair729.OrderedPair729) →
  Pair729.sixTritsToOrderedPair (Pair729.orderedPairToSixTrits pair) ≡ pair
unified729SixTritPairBidi =
  Pair729.sixTritsAfterOrderedPairRoundTrip

unified729PairExactConvolution :
  (amplitude : Fourier729.ModeCube27 → Nat)
  (target : Convolution729.WideCube125) →
  Convolution729.fiveIndexRecoveredConvolutionAt amplitude target
    ≡ Convolution729.exactConvolutionAt amplitude target
unified729PairExactConvolution =
  Convolution729.all729PairsFiveIndexRecoveryIsExact

------------------------------------------------------------------------
-- Original exact C3^3 cyclotomic DFT and Parseval are source-owned.
-- This carrier is cyclic; integer NS/Galerkin sums remain separate.
------------------------------------------------------------------------

unifiedExistingC3FourierInverse :
  (f : PeriodicFourier729.ModeCoefficient27)
  (m : Fourier729.ModeCube27) →
  PeriodicFourier729.unpackModeSignal
    (Fourier729Owner.inverseFourier27
      (Fourier729Owner.fourier27 (PeriodicFourier729.packModeSignal f))) m
    ≡ f m
unifiedExistingC3FourierInverse =
  PeriodicFourier729.existingPeriodic27FourierRoundTrip

unifiedExistingC3CyclicConvolution :
  (f g : PeriodicFourier729.ModeCoefficient27)
  (m : Fourier729.ModeCube27) →
  PeriodicFourier729.periodicC3ConvolutionOfModeCoefficients f g m
    ≡ PeriodicFourier729.spectralC3ConvolutionOfModeCoefficients f g m
unifiedExistingC3CyclicConvolution =
  PeriodicFourier729.periodic27DirectEqualsSpectralAtEveryMode

-- Original C3^3 DFT is exact ON THE CYCLIC QUOTIENT. Integer outputs
-- (2,0,0) and (-1,0,0) collide on that quotient.
unifiedCyclic27CannotRecoverTrueWideFourierMode :
  Fourier729Core.ConsumerSufficient
    Convolution729.wideIntegerOutputToThreeResidues (λ w → w)
    → ⊥
unifiedCyclic27CannotRecoverTrueWideFourierMode =
  Convolution729.noDecoderOfActualWideModeFromCyclic27

------------------------------------------------------------------------
-- 4³ = 64 retained-output Pareto vs 5³ = 125 full-output labels.
-- Source-inherited Q(omega) arithmetic, arbitrary distinct inputs.
-- No 4-grid sampled-physical-space DFT/NS/clock/Monster identity.
------------------------------------------------------------------------

unifiedFourGridBilinearRetained :
  (f g : Fourier729.ModeCube27 → Fourier729Owner.Cyclotomic3)
  (target : Fourier729.ModeCube27) →
  Bilinear729.fourGridBilinearRetainedAt Bilinear729.cyclotomicOps f g target
    ≡ Bilinear729.trueBilinearConvolutionAt Bilinear729.cyclotomicOps
        f g (Convolution729.retainedToWide target)
unifiedFourGridBilinearRetained =
  Bilinear729.cyclotomicFourGridRetainedBilinearExact

unifiedFiveGridBilinearFull :
  (f g : Fourier729.ModeCube27 → Fourier729Owner.Cyclotomic3)
  (target : Convolution729.WideCube125) →
  Bilinear729.fiveGridBilinearFullAt Bilinear729.cyclotomicOps f g target
    ≡ Bilinear729.trueBilinearConvolutionAt Bilinear729.cyclotomicOps f g target
unifiedFiveGridBilinearFull =
  Bilinear729.cyclotomicFiveGridFullBilinearExact

unifiedFourGridDoesNotIdentifyOuterTwoFrequencies :
  FourGridPareto729.foldFour ModeNSCut.wideMinusTwo
    ≡ FourGridPareto729.foldFour ModeNSCut.widePlusTwo
unifiedFourGridDoesNotIdentifyOuterTwoFrequencies =
  FourGridPareto729.outerFrequencyCollisionAtFour

------------------------------------------------------------------------
-- Original strict global antipodes: 27=centre+13 pairs and
-- 9=centre+4 pairs. Source Q(omega) Hermitian real-field packing
-- is invertible, but bare orbit labels cannot encode convolution.
-- This is NOT the D4 irreducible-character count or Monster3B action.
------------------------------------------------------------------------

unifiedFiveOrbitNineSymmetry :
  OriginalAntipodalSym729.antipodalClass9Count ≡ 5
unifiedFiveOrbitNineSymmetry =
  AntipodalSym729.sourceFiveNineOrbitCount

unifiedThirteenPairsTwentySevenSymmetry :
  27 ≡ 1 + 13 * 2
unifiedThirteenPairsTwentySevenSymmetry =
  AntipodalSym729.sourceThirteenNonzeroPairs

unifiedHermitianThirteenPairRoundTrip :
  (s : HermitianSym729.Hermitian27)
  (mode : Fourier729.ModeCube27) →
  HermitianSym729.packedMode
    (HermitianSym729.packHermitian27 s) mode
    ≡ HermitianSym729.coefficient s mode
unifiedHermitianThirteenPairRoundTrip =
  HermitianSym729.decodeAfterEncodeHermitian27

unifiedHermitianFiveNineRoundTrip :
  (s : HermitianSym729.Hermitian9)
  (plane : AntipodalSym729.Plane9) →
  HermitianSym729.packedPlane9
    (HermitianSym729.packHermitian9 s) plane
    ≡ HermitianSym729.coefficient9 s plane
unifiedHermitianFiveNineRoundTrip =
  HermitianSym729.decodeAfterEncodeHermitian9

unifiedTrueIntegerPairNegationCovariance :
  (p q : Fourier729.ModeCube27) →
  Convolution729.exactPairOutput
    (AntipodalSym729.negateCube p)
    (AntipodalSym729.negateCube q)
    ≡ AntipodalSym729.negateWideCube
        (Convolution729.exactPairOutput p q)
unifiedTrueIntegerPairNegationCovariance =
  AntipodalSym729.trueIntegerQuadraticPairSumNegationEquivariance

------------------------------------------------------------------------
-- True Hermitian compact Fourier carrier BIDI through the original
-- 729 ordered integer Z3 coefficient interaction consumer. This does
-- not assert a faster 13-only algorithm or global NS/Monster physics.
------------------------------------------------------------------------

unifiedCompact13PairsExactIntegerConvolution :
  (a b : HermitianSym729.Hermitian27)
  (target : Convolution729.WideCube125) →
  HermitianConv729.compactFullBilinearAt
    (HermitianSym729.packHermitian27 a)
    (HermitianSym729.packHermitian27 b) target
    ≡ HermitianConv729.originalFullBilinearAt a b target
unifiedCompact13PairsExactIntegerConvolution =
  HermitianConv729.compact13PairTransportPreservesAll125IntegerOutputs

unifiedCompact13PairsFourGridRetained :
  (a b : HermitianSym729.Hermitian27)
  (target : Fourier729.ModeCube27) →
  HermitianConv729.compactFourGridRetainedAt
    (HermitianSym729.packHermitian27 a)
    (HermitianSym729.packHermitian27 b) target
    ≡ HermitianConv729.originalFullBilinearAt a b
      (Convolution729.retainedToWide target)
unifiedCompact13PairsFourGridRetained =
  HermitianConv729.compact13PairsPreserveFourGridRetainedQuadratic

unifiedCompact13PairsFiveGridFull :
  (a b : HermitianSym729.Hermitian27)
  (target : Convolution729.WideCube125) →
  HermitianConv729.compactFiveGridFullAt
    (HermitianSym729.packHermitian27 a)
    (HermitianSym729.packHermitian27 b) target
    ≡ HermitianConv729.originalFullBilinearAt a b target
unifiedCompact13PairsFiveGridFull =
  HermitianConv729.compact13PairsPreserveFiveGridFullQuadratic

------------------------------------------------------------------------
-- Source-owned five antipodal classes in 9 are a REAL Fourier plane
-- codec with 1 real centre + 4 complex conjugate pairs. All 81
-- ordered quadratic pair coefficients and 25 wide outputs preserved.
------------------------------------------------------------------------

unifiedFiveInNineHermitian81PairConvolution :
  (a b : HermitianSym729.Hermitian9)
  (target : HermitianPlane81.WidePlane25) →
  HermitianPlane81.packedFivePlaneBilinearAt
    (HermitianSym729.packHermitian9 a)
    (HermitianSym729.packHermitian9 b) target
    ≡ HermitianPlane81.truePlaneBilinearAt
        (HermitianSym729.coefficient9 a)
        (HermitianSym729.coefficient9 b) target
unifiedFiveInNineHermitian81PairConvolution =
  HermitianPlane81.fiveOrbitPlaneCodecPreservesAll25QuadraticOutputs

------------------------------------------------------------------------
-- Four-grid cyclic Fourier has eight self-antipodal frequency corners
-- (0 or Nyquist 2 in each axis). Odd C3/5 grids have only one centre.
-- Actual 4th/5th root FFT field transport remains a separate producer.
------------------------------------------------------------------------

unifiedFourGridEightFixedNyquist :
  Fourier729.countWhereL NyquistSym729.fourFixedCube
    NyquistSym729.allFourGridCubes ≡ 8
unifiedFourGridEightFixedNyquist =
  NyquistSym729.fourCubeHasEightFixedAntipodes

unifiedFiveGridOneFixedCentre :
  Fourier729.countWhereL NyquistSym729.fiveFixedCube
    NyquistSym729.allFiveGridCubes ≡ 1
unifiedFiveGridOneFixedCentre =
  NyquistSym729.fiveCubeHasOneFixedAntipode

unifiedFourGrid36OrbitClasses :
  8 + 28 ≡ 36
unifiedFourGrid36OrbitClasses =
  NyquistSym729.fourCubeOrbitClasses36

unifiedFiveGrid63OrbitClasses :
  1 + 62 ≡ 63
unifiedFiveGrid63OrbitClasses =
  NyquistSym729.fiveCubeOrbitClasses63

-- Simultaneous inversion of ordered pair labels: 729 -> 365 classes.
-- This is NOT independent antipodal quotienting of either input mode.
unifiedActual729PositivePairOrbitCount :
  Pairs365Owner.countWhereL Pair365.positivePair Pairs365Owner.pair729 ≡ 365
unifiedActual729PositivePairOrbitCount = Pair365.actualPositivePairRepresentatives


------------------------------------------------------------------------
-- 365 real-Hermitian ordered-pair orbits and conjugate event transport.
-- The global 729-summand permutation proof remains a separate obligation.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P227729OrbitWeighted365ConvolutionExact as OrbitWeighted365

unifiedOrbit365CanonicalPairCount :
  Pairs365Owner.lengthL OrbitWeighted365.canonicalOrderedPairs ≡ 365
unifiedOrbit365CanonicalPairCount =
  OrbitWeighted365.actual365CanonicalPairEntries

unifiedOrbit365EventCount :
  (a b : HermitianSym729.Hermitian27) →
  Pairs365Owner.lengthL (OrbitWeighted365.orbitWeightedEvents a b) ≡ 729
unifiedOrbit365EventCount =
  OrbitWeighted365.actual729WeightedEvents

unifiedOrbit365ReflectedEventExact :
  (a b : HermitianSym729.Hermitian27)
  (pair : Pairs365Owner.ModePair729) →
  OrbitWeighted365.sourceEvent a b
    (AntipodalSym729.simultaneouslyNegateOrderedPair pair)
  ≡ OrbitWeighted365.invertedEvent (OrbitWeighted365.sourceEvent a b pair)
unifiedOrbit365ReflectedEventExact =
  OrbitWeighted365.reflectedEventIsConjugate


-- Five-in-nine plane -> 41 actual ordered pair orbits -> 81 events.
unifiedPlane41CanonicalCount :
  Pairs365Owner.lengthL OrbitWeighted365.canonicalPlaneOrderedPairs ≡ 41
unifiedPlane41CanonicalCount =
  OrbitWeighted365.actual41PlanePairOrbits

unifiedPlane41Emits81Events :
  (a b : HermitianSym729.Hermitian9) →
  Pairs365Owner.lengthL (OrbitWeighted365.orbitWeightedPlaneEvents a b) ≡ 81
unifiedPlane41Emits81Events =
  OrbitWeighted365.actual81WeightedPlaneEvents

unifiedPlane41ConjugateEvent :
  (a b : HermitianSym729.Hermitian9)
  (pair : HermitianPlane81.PlanePair81) →
  OrbitWeighted365.planeSourceEvent a b
    (OrbitWeighted365.negatePlaneOrderedPair pair)
  ≡ OrbitWeighted365.invertedPlaneEvent
      (OrbitWeighted365.planeSourceEvent a b pair)
unifiedPlane41ConjugateEvent =
  OrbitWeighted365.reflectedPlaneEventIsConjugate


------------------------------------------------------------------------
-- New independent Gaussian Q(i) C4³ Fourier character orthogonality.
-- Do not substitute the source-owned Q(omega) C3³ FFT for fourth roots.
-- A fully normalized sampled-product Agda theorem still remains open.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P2C4GaussianFourierCharacterExact as C4Gaussian

unifiedC4GaussianOneDimOrthogonality :
  (k l : FourGridPareto729.FourGridMode) →
  C4Gaussian.inner4 k l ≡ C4Gaussian.delta4 k l
unifiedC4GaussianOneDimOrthogonality =
  C4Gaussian.oneDimensionalCharacterOrthogonality

unifiedC4GaussianCubeOrthogonality :
  (k l : C4Gaussian.Cube4) →
  C4Gaussian.cubeInner4 k l ≡ C4Gaussian.cubeDelta4 k l
unifiedC4GaussianCubeOrthogonality =
  C4Gaussian.cubeCharacterOrthogonality


------------------------------------------------------------------------
-- C4 Gaussian exact 64-sample tensor DFT: both inverse directions.
-- Reuses the C4 Q(i) character owner and the C3 tensor-proof method.
-- No projected quadratic product claim is promoted here.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P2C4GaussianSampledFourierBidiExact as C4Sampled64

unifiedC4SampledForwardInverse :
  (s : C4Sampled64.CubeSignal64) →
  C4Sampled64.fourier64 (C4Sampled64.inverseFourier64 s) ≡ s
unifiedC4SampledForwardInverse =
  C4Sampled64.cubeFourierForwardInverse

unifiedC4SampledInverseForward :
  (s : C4Sampled64.CubeSignal64) →
  C4Sampled64.inverseFourier64 (C4Sampled64.fourier64 s) ≡ s
unifiedC4SampledInverseForward =
  C4Sampled64.cubeFourierInversion


------------------------------------------------------------------------
-- Explicit 27 signed integer Fourier modes -> zero-pad 64 -> C4^3
-- unscaled synthesis -> pointwise sampled product -> normalized forward
-- -> 27 retained outputs. No silent same-object NS promotion.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P2C4RetainedSampledOperatorExact as C4Retained

unifiedC4Pad27RoundTrip :
  (f : Fourier729.ModeCube27 → C4Gaussian.Gaussian4)
  (mode : Fourier729.ModeCube27) →
  C4Retained.readRetained (C4Retained.pad27To64 f) mode ≡ f mode
unifiedC4Pad27RoundTrip = C4Retained.paddingRetainsAll27

unifiedC4RetainedSampledBilinear :
  (Fourier729.ModeCube27 → C4Gaussian.Gaussian4) →
  (Fourier729.ModeCube27 → C4Gaussian.Gaussian4) →
  Fourier729.ModeCube27 → C4Gaussian.Gaussian4
unifiedC4RetainedSampledBilinear =
  C4Retained.retainedSampledBilinear


-- Original polymorphic true integer 729-pair theorem, now at exactly
-- the same Q(i) scalar carrier as the new C4 64-sample FFT.
unifiedC4GaussianIndexPreservesTrueIntegerConvolution :
  (f g : Fourier729.ModeCube27 → C4Gaussian.Gaussian4)
  (target : Fourier729.ModeCube27) →
  C4Retained.fourGridGaussianIndexConvolutionAt f g target
  ≡ C4Retained.trueGaussianIntegerConvolutionAt f g
      (Convolution729.retainedToWide target)
unifiedC4GaussianIndexPreservesTrueIntegerConvolution =
  C4Retained.fourGridGaussianIndexIsTrueIntegerConvolution


------------------------------------------------------------------------
-- Reuse original finite weighted reindexing and physical NS permutation
-- METHOD for the distinct 365/729 simultaneous-inversion action.
-- This is explicitly CONDITIONAL on the actual ordered address
-- permutation; its concrete unique/membership proof remains open.
------------------------------------------------------------------------
import Data.List.Relation.Binary.Permutation.Propositional as PairPerm365
import DASHI.Physics.Closure.R2P227729Orbit365PermutationReductionExact as Orbit365Perm

unifiedExpanded365Has729OrderedAddresses :
  Pairs365Owner.lengthL Orbit365Perm.expandedCanonicalPairs ≡ 729
unifiedExpanded365Has729OrderedAddresses =
  Orbit365Perm.expandedCanonicalPairCount

unifiedFull365HermitianSumGivenAddressPermutation :
  (a b : HermitianSym729.Hermitian27)
  (target : Convolution729.WideCube125) →
  Pairs365Owner.pair729 PairPerm365.↭ Orbit365Perm.expandedCanonicalPairs →
  OrbitWeighted365.unreducedConvolutionAt a b target
    ≡ OrbitWeighted365.orbitWeightedConvolutionAt a b target
unifiedFull365HermitianSumGivenAddressPermutation =
  Orbit365Perm.fullPairSumEqualsOrbitSumGivenPermutation


------------------------------------------------------------------------
-- Source-written unconditional 365 / 729 finite convolution theorem:
-- exact dense rank-sorted 729 address permutation; the prior
-- hypothesis-bearing permutation boundary is now supplied in source.
-- Exact-head Agda kernel validation remains necessary.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P227729Orbit365RankSortPermutationExact as Orbit365Rank

unifiedActual729AddressesPermuteFrom365 :
  Pairs365Owner.pair729 PairPerm365.↭ Orbit365Perm.expandedCanonicalPairs
unifiedActual729AddressesPermuteFrom365 =
  Orbit365Rank.actualOriginal729PermutesToExpanded365

unifiedOrbit365FullHermitianConvolutionMatches729 :
  (a b : HermitianSym729.Hermitian27)
  (k : Convolution729.WideCube125) →
  OrbitWeighted365.unreducedConvolutionAt a b k
    ≡ OrbitWeighted365.orbitWeightedConvolutionAt a b k
unifiedOrbit365FullHermitianConvolutionMatches729 =
  Orbit365Rank.orbit365FullHermitianConvolutionEquals729


------------------------------------------------------------------------
-- Independently source-written complete five-in-nine / 41-in-81 plane
-- Hermitian Q(omega) operator identity for the original 25 integer
-- outputs. Uses the SAME generic rank-sort permutation proof as 3D.
-- Kernel execution pending. Does not imply D4 or physical NS.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P281PlaneOrbit41RankSortConvolutionExact as Plane41Rank

unifiedOriginal81PlanePermutesFrom41 :
  HermitianPlane81.planePairs81 PairPerm365.↭ Plane41Rank.expanded41PlanePairs
unifiedOriginal81PlanePermutesFrom41 =
  Plane41Rank.originalPlanePairsPermuteToExpanded41

unifiedOriginalFiveInNineConvolutionMatches41 :
  (a b : HermitianSym729.Hermitian9)
  (target : HermitianPlane81.WidePlane25) →
  HermitianPlane81.truePlaneBilinearAt
    (HermitianSym729.coefficient9 a)
    (HermitianSym729.coefficient9 b) target
  ≡ OrbitWeighted365.orbitWeightedPlaneConvolutionAt a b target
unifiedOriginalFiveInNineConvolutionMatches41 =
  Plane41Rank.sourceFiveInNineTrueConvolutionEqualsOrbit41


------------------------------------------------------------------------
-- Original C5 group indexed at real five-point residues, with NEW
-- exact Q(zeta_5) character algebra and 125-point tensor orthogonality.
-- No imported C3/4 character or Monster same-object shortcut.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P2C5CyclotomicFullFourierCharacterExact as C5Character125

unifiedC5FifthRootExact :
  C5Character125._*5_ C5Character125.zetaFourth C5Character125.zeta5
  ≡ C5Character125.one5
unifiedC5FifthRootExact = C5Character125.zetaFifthLaw

unifiedC5Full125CharacterOrthogonality :
  (k l : Convolution729.GridCube125) →
  C5Character125.cubeInner5 k l ≡ C5Character125.cubeDelta5 k l
unifiedC5Full125CharacterOrthogonality =
  C5Character125.cubeCharacterOrthogonality


------------------------------------------------------------------------
-- Full 125-sample Q(zeta5) actual finite FFT, input 27-to-125 padding,
-- pointwise spectral multiplication and original coefficient-polymorphic
-- 729 pair / 125 exact integer outputs. SAME scalar carrier only.
-- The sample-to-index equation is still a separate analytic-algebraic
-- finite kernel obligation; never replace it by a synthetic receipt.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P2C5FullSampledFourierBidiExact as C5Sampled125
import DASHI.Physics.Closure.R2P2C5FullSampledIntegerOperatorExact as C5FullOperator

unifiedC5Actual125SampledForwardInverse :
  (s : C5Sampled125.CubeSignal125) →
  C5Sampled125.fourier125 (C5Sampled125.inverseFourier125 s) ≡ s
unifiedC5Actual125SampledForwardInverse =
  C5Sampled125.cubeFourierForwardInverse

unifiedC5Actual125SampledInverseForward :
  (s : C5Sampled125.CubeSignal125) →
  C5Sampled125.inverseFourier125 (C5Sampled125.fourier125 s) ≡ s
unifiedC5Actual125SampledInverseForward =
  C5Sampled125.cubeFourierInversion

unifiedC5Pad27RetainsCoefficients :
  (f : Fourier729.ModeCube27 → C5Character125.Cyclotomic5)
  (k : Fourier729.ModeCube27) →
  C5FullOperator.readRetained (C5FullOperator.pad27To125 f) k ≡ f k
unifiedC5Pad27RetainsCoefficients =
  C5FullOperator.paddingRetainsAll27

unifiedC5FullIndexedEqualsOriginalInteger :
  (f g : Fourier729.ModeCube27 → C5Character125.Cyclotomic5)
  (k : Convolution729.WideCube125) →
  C5FullOperator.indexedFiveGridBilinearAt f g k
    ≡ C5FullOperator.originalTrue125BilinearAt f g k
unifiedC5FullIndexedEqualsOriginalInteger =
  C5FullOperator.indexedFiveGridEqualsTrueFullInteger

unifiedC5ActualFull125SampledOperator :
  (Fourier729.ModeCube27 → C5Character125.Cyclotomic5) →
  (Fourier729.ModeCube27 → C5Character125.Cyclotomic5) →
  Convolution729.WideCube125 → C5Character125.Cyclotomic5
unifiedC5ActualFull125SampledOperator =
  C5FullOperator.fullSampledBilinear125


------------------------------------------------------------------------
-- Source-written C5 Q(zeta5) one-axis ACTUAL sampled multiplication
-- equals original five-group cyclic convolution, arbitrary inputs.
-- Preserves the three-axis sampled/index and NS analytic gates.
------------------------------------------------------------------------
unifiedC5OneAxisSampledConvolutionEqualsIndexed :
  (a b : C5Sampled125.Quint C5Character125.Cyclotomic5) →
  C5Sampled125.sampledConvolution5 a b
    ≡ C5Sampled125.cyclicConvolution5 a b
unifiedC5OneAxisSampledConvolutionEqualsIndexed =
  C5Sampled125.oneAxisSampledConvolutionIsCyclic


------------------------------------------------------------------------
-- New actual 27-by-27 distributive expansion on 729 ORIGINAL ordered
-- Fourier pairs, instantiated separately over the existing Q(i)
-- and Q(zeta5) scalar owners. Proves a finite source-level step toward
-- sampled/index equality; DOES NOT claim the missing character sum step.
------------------------------------------------------------------------
import Data.Product as FourierPairProjection

unifiedC4Actual729ProductExpansion :
  (f g : Fourier729.ModeCube27 → C4Gaussian.Gaussian4) →
  C4Gaussian._*G_
    (Bilinear729.sumAll C4Retained.gaussianCoefficientOps Fourier729.cube27 f)
    (Bilinear729.sumAll C4Retained.gaussianCoefficientOps Fourier729.cube27 g)
  ≡ Bilinear729.sumAll C4Retained.gaussianCoefficientOps Fourier729.pair729
    (λ pair → C4Gaussian._*G_
      (f (FourierPairProjection.proj₁ pair))
      (g (FourierPairProjection.proj₂ pair)))
unifiedC4Actual729ProductExpansion =
  C4Retained.gaussianActual729InputProductExpansion

unifiedC5Actual729ProductExpansion :
  (f g : Fourier729.ModeCube27 → C5Character125.Cyclotomic5) →
  C5Character125._*5_
    (Bilinear729.sumAll C5FullOperator.cyclotomicFiveOps Fourier729.cube27 f)
    (Bilinear729.sumAll C5FullOperator.cyclotomicFiveOps Fourier729.cube27 g)
  ≡ Bilinear729.sumAll C5FullOperator.cyclotomicFiveOps Fourier729.pair729
    (λ pair → C5Character125._*5_
      (f (FourierPairProjection.proj₁ pair))
      (g (FourierPairProjection.proj₂ pair)))
unifiedC5Actual729ProductExpansion =
  C5FullOperator.cyclotomicFiveActual729InputProductExpansion


------------------------------------------------------------------------
-- Literal 27-into-729 Fourier CHARACTER-WEIGHTED product at each sample.
-- Source Fubini + original character-addition law; no premature
-- normalized sampled→indexed/physical NS promotion.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P227729FourGridRetainedQuadraticParetoExact as SampledC4Group

unifiedC4Source729CharacterWeightedSample :
  (f g : Fourier729.ModeCube27 → C4Gaussian.Gaussian4)
  (x : SampledC4Group.FourGridCube64) →
  C4Gaussian._*G_
    (C4Retained.gaussianOriginal27UnscaledSynthesisAt f x)
    (C4Retained.gaussianOriginal27UnscaledSynthesisAt g x)
  ≡ Bilinear729.sumAll C4Retained.gaussianCoefficientOps Fourier729.pair729
      (C4Retained.gaussianOriginal729PhaseContribution f g x)
unifiedC4Source729CharacterWeightedSample =
  C4Retained.gaussianSourceSampledProductExpands729

unifiedC5Source729CharacterWeightedSample :
  (f g : Fourier729.ModeCube27 → C5Character125.Cyclotomic5)
  (x : Convolution729.GridCube125) →
  C5Character125._*5_
    (C5FullOperator.cyclotomicFiveOriginal27UnscaledSynthesisAt f x)
    (C5FullOperator.cyclotomicFiveOriginal27UnscaledSynthesisAt g x)
  ≡ Bilinear729.sumAll C5FullOperator.cyclotomicFiveOps Fourier729.pair729
      (C5FullOperator.cyclotomicFiveOriginal729PhaseContribution f g x)
unifiedC5Source729CharacterWeightedSample =
  C5FullOperator.cyclotomicFiveSourceSampledProductExpands729


------------------------------------------------------------------------
-- CONDITIONAL extraction is deliberately typed with an unresolved
-- C4/C5 finite character-resolution payment, not an inferred proof.
-- This isolates the remaining source sample-sum/index step before the
-- independently open actual FFT tensor-array identification.
------------------------------------------------------------------------

unifiedC4CharacterResolutionExtractsSourceIndexed :
  (f g : Fourier729.ModeCube27 → C4Gaussian.Gaussian4)
  (k : Fourier729.ModeCube27) →
  C4Retained.gaussianActualCharacterResolution k →
  C4Retained.gaussianSourceNormalizedSampledAt f g k
    ≡ C4Retained.fourGridGaussianIndexConvolutionAt f g k
unifiedC4CharacterResolutionExtractsSourceIndexed =
  C4Retained.gaussianSourceSampledEqualsIndexedGivenResolution

unifiedC5CharacterResolutionExtractsSourceIndexed :
  (f g : Fourier729.ModeCube27 → C5Character125.Cyclotomic5)
  (k : Convolution729.WideCube125) →
  C5FullOperator.cyclotomicFiveActualCharacterResolution k →
  C5FullOperator.cyclotomicFiveSourceNormalizedSampledAt f g k
    ≡ C5FullOperator.indexedFiveGridBilinearAt f g k
unifiedC5CharacterResolutionExtractsSourceIndexed =
  C5FullOperator.cyclotomicFiveSourceSampledEqualsIndexedGivenResolution
