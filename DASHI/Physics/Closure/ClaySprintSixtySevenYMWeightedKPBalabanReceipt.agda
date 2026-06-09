module DASHI.Physics.Closure.ClaySprintSixtySevenYMWeightedKPBalabanReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintSixtyFourYMWeightedKPBalabanPathReceipt
  as Sprint64YM

------------------------------------------------------------------------
-- Sprint 67C YM weighted KP/Balaban algebra receipt.
--
-- This receipt pins the current YM obstruction: q<1 is not enough; weighted
-- KP needs eta*q<1.  The live route is now entropy counting: generic
-- Holley-Stroock eta=8 fails, while a spatial-only anisotropic Balaban L=2
-- entropy factor eta_eff=4 would close the arithmetic.  No YM, mass-gap, or
-- Clay promotion follows.

Scalar : Set
Scalar = String

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data Sprint67YMBranch : Set where
  branchTemporalIntegralFactorization :
    Sprint67YMBranch
  branchSharpenEntropyFactor :
    Sprint67YMBranch
  branchAnisotropicL2EntropyCounting :
    Sprint67YMBranch
  branchClosedArithmeticLemmas :
    Sprint67YMBranch
  branchHolleyStroockOscillationTightening :
    Sprint67YMBranch
  branchAnisotropicBalabanTransferCompatibility :
    Sprint67YMBranch
  branchBalabanRGTransferToThreshold :
    Sprint67YMBranch
  branchAllDiameterKPCertificate :
    Sprint67YMBranch
  branchContinuumOSWightmanMassGap :
    Sprint67YMBranch

canonicalSprint67YMBranches :
  List Sprint67YMBranch
canonicalSprint67YMBranches =
  branchTemporalIntegralFactorization
  ∷ branchSharpenEntropyFactor
  ∷ branchAnisotropicL2EntropyCounting
  ∷ branchClosedArithmeticLemmas
  ∷ branchHolleyStroockOscillationTightening
  ∷ branchAnisotropicBalabanTransferCompatibility
  ∷ branchBalabanRGTransferToThreshold
  ∷ branchAllDiameterKPCertificate
  ∷ branchContinuumOSWightmanMassGap
  ∷ []

data Sprint67YMRouteDecision : Set where
  currentQBelowOneButInsufficient :
    Sprint67YMRouteDecision
  weightedKPCurrentFails :
    Sprint67YMRouteDecision
  entropyFactorEightIsLoadBearing :
    Sprint67YMRouteDecision
  etaBelow431WouldCloseCurrentQ :
    Sprint67YMRouteDecision
  betaGapFramingDemoted :
    Sprint67YMRouteDecision
  anisotropicL2EntropyArithmeticCloses :
    Sprint67YMRouteDecision
  betaBlockedCurrentBelowRequired :
    Sprint67YMRouteDecision
  kNinetyEightIsFirstSafeDiagnosticScale :
    Sprint67YMRouteDecision
  erikssonCompatibilityGateRecorded :
    Sprint67YMRouteDecision
  paperIILargeFieldSuppressionConditionalOnly :
    Sprint67YMRouteDecision
  temporalFactorizationIsFirstGate :
    Sprint67YMRouteDecision
  noYangMillsPromotion :
    Sprint67YMRouteDecision

canonicalSprint67YMRouteDecisions :
  List Sprint67YMRouteDecision
canonicalSprint67YMRouteDecisions =
  currentQBelowOneButInsufficient
  ∷ weightedKPCurrentFails
  ∷ entropyFactorEightIsLoadBearing
  ∷ etaBelow431WouldCloseCurrentQ
  ∷ betaGapFramingDemoted
  ∷ anisotropicL2EntropyArithmeticCloses
  ∷ betaBlockedCurrentBelowRequired
  ∷ kNinetyEightIsFirstSafeDiagnosticScale
  ∷ erikssonCompatibilityGateRecorded
  ∷ paperIILargeFieldSuppressionConditionalOnly
  ∷ temporalFactorizationIsFirstGate
  ∷ noYangMillsPromotion
  ∷ []

data Sprint67YMOpenGate : Set where
  gateTemporalIntegralFactorization :
    Sprint67YMOpenGate
  gateCarrierSupportTemporalBoundaryExclusion :
    Sprint67YMOpenGate
  gateSpatialSlabPartitionOfUnity :
    Sprint67YMOpenGate
  gateSpatialSlowFieldIdentification :
    Sprint67YMOpenGate
  gatePaperIILargeFieldSuppressionTransfer :
    Sprint67YMOpenGate
  gateWeightedKPConvergesConditional :
    Sprint67YMOpenGate
  gateAllDiameterKPFromRatioConditional :
    Sprint67YMOpenGate
  gateEntropySharpeningClosesKPConditional :
    Sprint67YMOpenGate
  gateBetaThresholdClosesWeightedKPConditional :
    Sprint67YMOpenGate
  gateKScaleThresholdClosesWeightedKPConditional :
    Sprint67YMOpenGate
  gateAnisotropicL2EntropyClosesKPConditional :
    Sprint67YMOpenGate
  gateSpatialOnlyCoarseningHalvesEntropyAtL2 :
    Sprint67YMOpenGate
  gateAnisotropicBalabanPartitionIdentity :
    Sprint67YMOpenGate
  gateTemporalTransferMatrixCompatibleWithSpatialBlocking :
    Sprint67YMOpenGate
  gateSmallFieldBoundsSurviveAnisotropicBlocking :
    Sprint67YMOpenGate
  gateAnisotropicWeightedKPCertificate :
    Sprint67YMOpenGate
  gateLatticeMassGapFromAnisotropicKP :
    Sprint67YMOpenGate
  gateSharpenedEntropyBoundBelowEight :
    Sprint67YMOpenGate
  gateSharpenedEntropyBoundBelow431 :
    Sprint67YMOpenGate
  gateHolleyStroockOscillationTightening :
    Sprint67YMOpenGate
  gateAnisotropicBalabanTransferMatrixCompatibility :
    Sprint67YMOpenGate
  gateBalabanBareSixToBlocked19252 :
    Sprint67YMOpenGate
  gateActivityLeakagePreservation :
    Sprint67YMOpenGate
  gateAllDiameterKPCertificate :
    Sprint67YMOpenGate
  gateContinuumRhoLeakage :
    Sprint67YMOpenGate
  gateOSWightmanReconstruction :
    Sprint67YMOpenGate
  gateMassGapSurvival :
    Sprint67YMOpenGate

canonicalSprint67YMOpenGates :
  List Sprint67YMOpenGate
canonicalSprint67YMOpenGates =
  gateTemporalIntegralFactorization
  ∷ gateCarrierSupportTemporalBoundaryExclusion
  ∷ gateSpatialSlabPartitionOfUnity
  ∷ gateSpatialSlowFieldIdentification
  ∷ gatePaperIILargeFieldSuppressionTransfer
  ∷ gateWeightedKPConvergesConditional
  ∷ gateAllDiameterKPFromRatioConditional
  ∷ gateEntropySharpeningClosesKPConditional
  ∷ gateBetaThresholdClosesWeightedKPConditional
  ∷ gateKScaleThresholdClosesWeightedKPConditional
  ∷ gateAnisotropicL2EntropyClosesKPConditional
  ∷ gateSpatialOnlyCoarseningHalvesEntropyAtL2
  ∷ gateAnisotropicBalabanPartitionIdentity
  ∷ gateTemporalTransferMatrixCompatibleWithSpatialBlocking
  ∷ gateSmallFieldBoundsSurviveAnisotropicBlocking
  ∷ gateAnisotropicWeightedKPCertificate
  ∷ gateLatticeMassGapFromAnisotropicKP
  ∷ gateSharpenedEntropyBoundBelowEight
  ∷ gateSharpenedEntropyBoundBelow431
  ∷ gateHolleyStroockOscillationTightening
  ∷ gateAnisotropicBalabanTransferMatrixCompatibility
  ∷ gateBalabanBareSixToBlocked19252
  ∷ gateActivityLeakagePreservation
  ∷ gateAllDiameterKPCertificate
  ∷ gateContinuumRhoLeakage
  ∷ gateOSWightmanReconstruction
  ∷ gateMassGapSurvival
  ∷ []

data Sprint67YMPromotion : Set where

sprint67YMPromotionImpossibleHere :
  Sprint67YMPromotion →
  ⊥
sprint67YMPromotionImpossibleHere ()

sprint67YMAlgebraContract : String
sprint67YMAlgebraContract =
  "Current q=0.23178189475262734 gives 8q=1.8542551580210187>1; weighted KP requires q<1/8=0.125."

sprint67YMBranchContract : String
sprint67YMBranchContract =
  "The live branch is entropy counting, not beta running: prove spatial-only anisotropic Balaban L=2 reduces eta from 8 to 4 while preserving partition identity, temporal transfer factorization, small-field bounds, and reflection positivity."

sprint67YMClosedArithmeticContract : String
sprint67YMClosedArithmeticContract =
  "Closed conditional arithmetic: eta*q<1 implies weighted KP convergence; eta<4.31440083388422038 closes current q; eta=4 gives 4q=0.9271275790105094<1 with margin 0.07287242098949064; beta/k thresholds are retained only as secondary diagnostics."

sprint67YMAnisotropicEntropyContract : String
sprint67YMAnisotropicEntropyContract =
  "Generic eta=8 fails since 8q=1.8542551580210187; spatial-only L=2 anisotropic Balaban counting predicts eta_eff=8/2=4, so eta_eff*q=0.9271275790105094<1. The load-bearing theorem is SpatialOnlyCoarseningHalvesEntropyAtL2 plus anisotropic Balaban/transfer-matrix compatibility."

sprint67YMTemporalFactorizationContract : String
sprint67YMTemporalFactorizationContract =
  "TemporalIntegralFactors is the first Sprint 67C gate: DASHI admissibility must imply no admissible polymer simultaneously crosses a spatial block boundary and a temporal link, so temporal and spatial functional integrals commute for the anisotropic block decomposition."

sprint67YMTemporalFaceSupportContract : String
sprint67YMTemporalFaceSupportContract =
  "TemporalFaceSupport is the sharpened first check: no admissible polymer may have support on both top and bottom temporal faces of the same spatial block; support non-creation is the candidate mechanism."

sprint67YMSupervoxelGeometryContract : String
sprint67YMSupervoxelGeometryContract =
  "Supervoxel face geometry: for L=3, spatial sites L^3=27, spatial face plaquettes L^2=9 with six sides giving 54, temporal faces have L^3=27 each with top+bottom giving 54; anisotropic partition must split temporal faces from spatial faces."

sprint67YMPaperIICalibration : String
sprint67YMPaperIICalibration =
  "Eriksson Paper II proves the large-field suppression hypothesis for isotropic Balaban blocking only. DASHI may inherit it for spatial-only blocking only after slab partition of unity, spatial slow-field identification, temporal factorization, and small-field bounds are reverified."

sprint67YMBetaOneLoopCalibration : String
sprint67YMBetaOneLoopCalibration =
  "For SU3, beta_bare=2Nc=6 and the one-loop natural scale is 11Nc/2=33/2=16.5; beta_required-33/2=2.7515829890895525, about 0.9171943296965175*Nc, so the KP threshold lies just above the first natural one-loop plateau."

sprint67YMErikssonCalibration : String
sprint67YMErikssonCalibration =
  "Eriksson Feb 2026 lattice mass-gap series is recorded as conditional calibration only: Balaban RG plus Holley-Stroock/orbit Ricci plus transfer-matrix scaling, with anisotropic RG/temporal transfer compatibility as the caveat."

sprint67YMCompatibilityGate : String
sprint67YMCompatibilityGate =
  "Dependency graph: TemporalIntegralFactors -> AnisotropicBalabanPartitionIdentity -> EntropyFactorBelow431 -> AllDiameterWeightedKP -> BalabanRGReachesWKPThreshold -> TransferSpectralGapImpliesLatticeMassGap -> OSWightmanReconstruction plus MassGapSurvival."

sprint67YMKTranslation : String
sprint67YMKTranslation =
  "Using beta(k)=6+0.1355488k, k_required~=97.7624515236546, so k=98 is first safe: beta(98)=19.2837824, q=0.12402975293679427, 8q=0.9922380234943542."

sprint67YMBetaKTable : String
sprint67YMBetaKTable =
  "k67 beta15.0817696 q0.3428896164570517 8q2.7431169316564135 fail; k70 beta15.488416 q0.3107535482480182 8q2.4860283859841457 fail; k80 beta16.843904 q0.22384907504811435 8q1.7907926003849148 fail; k90 beta18.199392 q0.16124806517061532 8q1.2899845213649226 fail; k98 beta19.2837824 q0.12402975293679427 8q0.9922380234943542 pass; k100 beta19.55488 q0.11615387964269382 8q0.9292310371415505 pass; k120 beta22.265856 q0.06027151889347521 8q0.48217215114780165 strong-pass."

sprint67YMEntropyTable : String
sprint67YMEntropyTable =
  "At q=0.23178189475262734: eta8 gives etaq1.8542551580210187 betaNeeded19.251582989089552; eta7 gives 1.6224732632683914 betaNeeded18.699800374938636; eta6 gives 1.390691368515764 betaNeeded18.06281409466071; eta5 gives 1.1589094737631367 betaNeeded17.309419231875772; eta4.31440083388422038 gives 1.0 betaNeeded16.7; eta4 gives 0.9271275790105094 already-safe; eta3 gives 0.695345684257882 already-safe."

sprint67YMAnisotropicLTable : String
sprint67YMAnisotropicLTable =
  "If eta_eff=8/L, then L1 eta8 etaq1.8542551580210187 fail; L2 eta4 etaq0.9271275790105094 pass; L3 eta2.6666666666666665 etaq0.6180850526736729 pass; L4 eta2 etaq0.4635637895052547 pass; L5 eta1.6 etaq0.37085103160420375 pass; L8 eta1 etaq0.23178189475262734 pass."

sprint67YMBoundary : String
sprint67YMBoundary =
  "Sprint 67C pins the YM weighted KP/Balaban algebra and demotes the beta-gap framing: the live obstruction is entropy factor eta=8. Current q needs eta<4.31440083388422038. A single spatial-only anisotropic Balaban L=2 step would give eta_eff=4 and 4q=0.9271275790105094<1 with margin 0.07287242098949064. The load-bearing open theorem is TemporalFaceSupport/TemporalIntegralFactors leading to anisotropic Balaban compatibility. Beta=33/2 and 9-vs-27 face geometry are calibration only. Weighted KP arithmetic is conditionally closed at eta=4, but anisotropic compatibility, lattice mass gap, continuum reconstruction, and Clay/YM promotion remain unproved."

record ClaySprintSixtySevenYMWeightedKPBalabanReceipt : Set₁ where
  field
    sprint64YMNoPromotion :
      Sprint64YM.clayYangMillsPromoted ≡ false

    qCurrent :
      Scalar
    qCurrentIsCanonical :
      qCurrent ≡ "0.23178189475262734"

    weightedEightQCurrent :
      Scalar
    weightedEightQCurrentIsCanonical :
      weightedEightQCurrent ≡ "1.8542551580210187"

    qRequired :
      Scalar
    qRequiredIsOneEighth :
      qRequired ≡ "0.125"

    qReductionFactorNeeded :
      Scalar
    qReductionFactorNeededIsCanonical :
      qReductionFactorNeeded ≡ "0.5393001042355275"

    effectiveQReductionPercentNeeded :
      Scalar
    effectiveQReductionPercentNeededIsCanonical :
      effectiveQReductionPercentNeeded ≡ "0.46069989576447246"

    entropyFactorCurrent :
      Scalar
    entropyFactorCurrentIsEight :
      entropyFactorCurrent ≡ "8"

    genericWeightedEightQCurrent :
      Scalar
    genericWeightedEightQCurrentIsCanonical :
      genericWeightedEightQCurrent ≡ "1.8542551580210187"

    entropyFactorNeededForCurrentQ :
      Scalar
    entropyFactorNeededForCurrentQIsCanonical :
      entropyFactorNeededForCurrentQ ≡ "4.31440083388422038"

    anisotropicBlockingFactorL :
      Scalar
    anisotropicBlockingFactorLIsTwo :
      anisotropicBlockingFactorL ≡ "2"

    anisotropicEntropyFactorL2 :
      Scalar
    anisotropicEntropyFactorL2IsFour :
      anisotropicEntropyFactorL2 ≡ "4.0"

    anisotropicWeightedFourQCurrent :
      Scalar
    anisotropicWeightedFourQCurrentIsCanonical :
      anisotropicWeightedFourQCurrent ≡ "0.9271275790105094"

    anisotropicKPMargin :
      Scalar
    anisotropicKPMarginIsCanonical :
      anisotropicKPMargin ≡ "0.07287242098949064"

    anisotropicEntropyReduction :
      Scalar
    anisotropicEntropyReductionIsHalf :
      anisotropicEntropyReduction ≡ "0.5"

    eta431TimesQ :
      Scalar
    eta431TimesQIsCanonical :
      eta431TimesQ ≡ "0.9989799663838237"

    supervoxelL3SpatialSites :
      Scalar
    supervoxelL3SpatialSitesIs27 :
      supervoxelL3SpatialSites ≡ "27"

    supervoxelL3SpatialFacePlaquettes :
      Scalar
    supervoxelL3SpatialFacePlaquettesIs9 :
      supervoxelL3SpatialFacePlaquettes ≡ "9"

    supervoxelL3SixSpatialFaces :
      Scalar
    supervoxelL3SixSpatialFacesIs54 :
      supervoxelL3SixSpatialFaces ≡ "54"

    supervoxelL3TemporalFacePlaquettes :
      Scalar
    supervoxelL3TemporalFacePlaquettesIs27 :
      supervoxelL3TemporalFacePlaquettes ≡ "27"

    supervoxelL3TwoTemporalFaces :
      Scalar
    supervoxelL3TwoTemporalFacesIs54 :
      supervoxelL3TwoTemporalFaces ≡ "54"

    supervoxelL2SpatialSites :
      Scalar
    supervoxelL2SpatialSitesIs8 :
      supervoxelL2SpatialSites ≡ "8"

    supervoxelL2SpatialFacePlaquettes :
      Scalar
    supervoxelL2SpatialFacePlaquettesIs4 :
      supervoxelL2SpatialFacePlaquettes ≡ "4"

    supervoxelL2TemporalFacePlaquettes :
      Scalar
    supervoxelL2TemporalFacePlaquettesIs8 :
      supervoxelL2TemporalFacePlaquettes ≡ "8"

    betaBare :
      Scalar
    betaBareIsSix :
      betaBare ≡ "6.0"

    nc :
      Scalar
    ncIsThree :
      nc ≡ "3"

    betaBareAsTwoNc :
      Scalar
    betaBareAsTwoNcIsCanonical :
      betaBareAsTwoNc ≡ "2*Nc=6"

    betaOneLoopPlateau :
      Scalar
    betaOneLoopPlateauIsCanonical :
      betaOneLoopPlateau ≡ "11*Nc/2=33/2=16.5"

    betaCurrentApproxOneLoopPlateau :
      Bool
    betaCurrentApproxOneLoopPlateauIsTrue :
      betaCurrentApproxOneLoopPlateau ≡ true

    betaRequiredMinusOneLoopPlateau :
      Scalar
    betaRequiredMinusOneLoopPlateauIsCanonical :
      betaRequiredMinusOneLoopPlateau ≡ "2.7515829890895525"

    betaRequiredMinusOneLoopOverNc :
      Scalar
    betaRequiredMinusOneLoopOverNcIsCanonical :
      betaRequiredMinusOneLoopOverNc ≡ "0.9171943296965175"

    betaBlockedCurrent :
      Scalar
    betaBlockedCurrentIsCanonical :
      betaBlockedCurrent ≡ "16.7"

    betaRequired :
      Scalar
    betaRequiredIsCanonical :
      betaRequired ≡ "19.251582989089552"

    betaGap :
      Scalar
    betaGapIsCanonical :
      betaGap ≡ "2.551582989089552"

    betaRequiredOverBare :
      Scalar
    betaRequiredOverBareIsCanonical :
      betaRequiredOverBare ≡ "3.2085971648482587"

    betaRunningLaw :
      Scalar
    betaRunningLawIsCanonical :
      betaRunningLaw ≡ "beta(k)=6+0.1355488*k"

    kRequired :
      Scalar
    kRequiredIsCanonical :
      kRequired ≡ "97.7624515236546"

    kFirstSafeInteger :
      Scalar
    kFirstSafeIntegerIs98 :
      kFirstSafeInteger ≡ "98"

    betaAtK98 :
      Scalar
    betaAtK98IsCanonical :
      betaAtK98 ≡ "19.2837824"

    qAtK98 :
      Scalar
    qAtK98IsCanonical :
      qAtK98 ≡ "0.12402975293679427"

    weightedEightQAtK98 :
      Scalar
    weightedEightQAtK98IsCanonical :
      weightedEightQAtK98 ≡ "0.9922380234943542"

    weightedKPCurrentConverges :
      Bool
    weightedKPCurrentConvergesIsFalse :
      weightedKPCurrentConverges ≡ false

    genericWeightedKPFails :
      Bool
    genericWeightedKPFailsIsTrue :
      genericWeightedKPFails ≡ true

    anisotropicL2KPArithmeticCloses :
      Bool
    anisotropicL2KPArithmeticClosesIsTrue :
      anisotropicL2KPArithmeticCloses ≡ true

    entropyFactorSharpenedBelowEight :
      Bool
    entropyFactorSharpenedBelowEightIsFalse :
      entropyFactorSharpenedBelowEight ≡ false

    entropyFactorSharpenedBelow431 :
      Bool
    entropyFactorSharpenedBelow431IsFalse :
      entropyFactorSharpenedBelow431 ≡ false

    holleyStroockOscillationTightened :
      Bool
    holleyStroockOscillationTightenedIsFalse :
      holleyStroockOscillationTightened ≡ false

    anisotropicBalabanTransferCompatible :
      Bool
    anisotropicBalabanTransferCompatibleIsFalse :
      anisotropicBalabanTransferCompatible ≡ false

    temporalIntegralFactorization :
      Bool
    temporalIntegralFactorizationIsFalse :
      temporalIntegralFactorization ≡ false

    carrierSupportTemporalBoundaryExclusion :
      Bool
    carrierSupportTemporalBoundaryExclusionIsFalse :
      carrierSupportTemporalBoundaryExclusion ≡ false

    spatialSlabPartitionOfUnity :
      Bool
    spatialSlabPartitionOfUnityIsFalse :
      spatialSlabPartitionOfUnity ≡ false

    spatialSlowFieldIdentification :
      Bool
    spatialSlowFieldIdentificationIsFalse :
      spatialSlowFieldIdentification ≡ false

    paperIILargeFieldSuppressionTransferred :
      Bool
    paperIILargeFieldSuppressionTransferredIsFalse :
      paperIILargeFieldSuppressionTransferred ≡ false

    anisotropicBalabanPartitionIdentity :
      Bool
    anisotropicBalabanPartitionIdentityIsFalse :
      anisotropicBalabanPartitionIdentity ≡ false

    temporalTransferMatrixCompatibleWithSpatialBlocking :
      Bool
    temporalTransferMatrixCompatibleWithSpatialBlockingIsFalse :
      temporalTransferMatrixCompatibleWithSpatialBlocking ≡ false

    smallFieldBoundsSurviveAnisotropicBlocking :
      Bool
    smallFieldBoundsSurviveAnisotropicBlockingIsFalse :
      smallFieldBoundsSurviveAnisotropicBlocking ≡ false

    anisotropicWeightedKPCertificate :
      Bool
    anisotropicWeightedKPCertificateIsFalse :
      anisotropicWeightedKPCertificate ≡ false

    latticeMassGapFromAnisotropicKP :
      Bool
    latticeMassGapFromAnisotropicKPIsFalse :
      latticeMassGapFromAnisotropicKP ≡ false

    balabanRGScaleTransfer :
      Bool
    balabanRGScaleTransferIsFalse :
      balabanRGScaleTransfer ≡ false

    activityLeakagePreservation :
      Bool
    activityLeakagePreservationIsFalse :
      activityLeakagePreservation ≡ false

    allDiameterKPCertificate :
      Bool
    allDiameterKPCertificateIsFalse :
      allDiameterKPCertificate ≡ false

    continuumOSWightmanMassGap :
      Bool
    continuumOSWightmanMassGapIsFalse :
      continuumOSWightmanMassGap ≡ false

    osWightmanReconstruction :
      Bool
    osWightmanReconstructionIsFalse :
      osWightmanReconstruction ≡ false

    massGapSurvival :
      Bool
    massGapSurvivalIsFalse :
      massGapSurvival ≡ false

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    algebraContract :
      String
    algebraContractIsCanonical :
      algebraContract ≡ sprint67YMAlgebraContract

    branchContract :
      String
    branchContractIsCanonical :
      branchContract ≡ sprint67YMBranchContract

    anisotropicEntropyContract :
      String
    anisotropicEntropyContractIsCanonical :
      anisotropicEntropyContract ≡ sprint67YMAnisotropicEntropyContract

    temporalFactorizationContract :
      String
    temporalFactorizationContractIsCanonical :
      temporalFactorizationContract ≡ sprint67YMTemporalFactorizationContract

    temporalFaceSupportContract :
      String
    temporalFaceSupportContractIsCanonical :
      temporalFaceSupportContract ≡ sprint67YMTemporalFaceSupportContract

    supervoxelGeometryContract :
      String
    supervoxelGeometryContractIsCanonical :
      supervoxelGeometryContract ≡ sprint67YMSupervoxelGeometryContract

    paperIICalibration :
      String
    paperIICalibrationIsCanonical :
      paperIICalibration ≡ sprint67YMPaperIICalibration

    betaOneLoopCalibration :
      String
    betaOneLoopCalibrationIsCanonical :
      betaOneLoopCalibration ≡ sprint67YMBetaOneLoopCalibration

    erikssonCalibration :
      String
    erikssonCalibrationIsCanonical :
      erikssonCalibration ≡ sprint67YMErikssonCalibration

    compatibilityGate :
      String
    compatibilityGateIsCanonical :
      compatibilityGate ≡ sprint67YMCompatibilityGate

    kTranslation :
      String
    kTranslationIsCanonical :
      kTranslation ≡ sprint67YMKTranslation

    closedArithmeticContract :
      String
    closedArithmeticContractIsCanonical :
      closedArithmeticContract ≡ sprint67YMClosedArithmeticContract

    betaKTable :
      String
    betaKTableIsCanonical :
      betaKTable ≡ sprint67YMBetaKTable

    entropyTable :
      String
    entropyTableIsCanonical :
      entropyTable ≡ sprint67YMEntropyTable

    anisotropicLTable :
      String
    anisotropicLTableIsCanonical :
      anisotropicLTable ≡ sprint67YMAnisotropicLTable

    branches :
      List Sprint67YMBranch
    branchesAreCanonical :
      branches ≡ canonicalSprint67YMBranches

    routeDecisions :
      List Sprint67YMRouteDecision
    routeDecisionsAreCanonical :
      routeDecisions ≡ canonicalSprint67YMRouteDecisions

    openGates :
      List Sprint67YMOpenGate
    openGatesAreCanonical :
      openGates ≡ canonicalSprint67YMOpenGates

    promotions :
      List Sprint67YMPromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      Sprint67YMPromotion → ⊥

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint67YMBoundary

canonicalSprint67YMReceipt :
  ClaySprintSixtySevenYMWeightedKPBalabanReceipt
canonicalSprint67YMReceipt =
  record
    { sprint64YMNoPromotion = refl
    ; qCurrent = "0.23178189475262734"
    ; qCurrentIsCanonical = refl
    ; weightedEightQCurrent = "1.8542551580210187"
    ; weightedEightQCurrentIsCanonical = refl
    ; qRequired = "0.125"
    ; qRequiredIsOneEighth = refl
    ; qReductionFactorNeeded = "0.5393001042355275"
    ; qReductionFactorNeededIsCanonical = refl
    ; effectiveQReductionPercentNeeded = "0.46069989576447246"
    ; effectiveQReductionPercentNeededIsCanonical = refl
    ; entropyFactorCurrent = "8"
    ; entropyFactorCurrentIsEight = refl
    ; genericWeightedEightQCurrent = "1.8542551580210187"
    ; genericWeightedEightQCurrentIsCanonical = refl
    ; entropyFactorNeededForCurrentQ = "4.31440083388422038"
    ; entropyFactorNeededForCurrentQIsCanonical = refl
    ; anisotropicBlockingFactorL = "2"
    ; anisotropicBlockingFactorLIsTwo = refl
    ; anisotropicEntropyFactorL2 = "4.0"
    ; anisotropicEntropyFactorL2IsFour = refl
    ; anisotropicWeightedFourQCurrent = "0.9271275790105094"
    ; anisotropicWeightedFourQCurrentIsCanonical = refl
    ; anisotropicKPMargin = "0.07287242098949064"
    ; anisotropicKPMarginIsCanonical = refl
    ; anisotropicEntropyReduction = "0.5"
    ; anisotropicEntropyReductionIsHalf = refl
    ; eta431TimesQ = "0.9989799663838237"
    ; eta431TimesQIsCanonical = refl
    ; supervoxelL3SpatialSites = "27"
    ; supervoxelL3SpatialSitesIs27 = refl
    ; supervoxelL3SpatialFacePlaquettes = "9"
    ; supervoxelL3SpatialFacePlaquettesIs9 = refl
    ; supervoxelL3SixSpatialFaces = "54"
    ; supervoxelL3SixSpatialFacesIs54 = refl
    ; supervoxelL3TemporalFacePlaquettes = "27"
    ; supervoxelL3TemporalFacePlaquettesIs27 = refl
    ; supervoxelL3TwoTemporalFaces = "54"
    ; supervoxelL3TwoTemporalFacesIs54 = refl
    ; supervoxelL2SpatialSites = "8"
    ; supervoxelL2SpatialSitesIs8 = refl
    ; supervoxelL2SpatialFacePlaquettes = "4"
    ; supervoxelL2SpatialFacePlaquettesIs4 = refl
    ; supervoxelL2TemporalFacePlaquettes = "8"
    ; supervoxelL2TemporalFacePlaquettesIs8 = refl
    ; betaBare = "6.0"
    ; betaBareIsSix = refl
    ; nc = "3"
    ; ncIsThree = refl
    ; betaBareAsTwoNc = "2*Nc=6"
    ; betaBareAsTwoNcIsCanonical = refl
    ; betaOneLoopPlateau = "11*Nc/2=33/2=16.5"
    ; betaOneLoopPlateauIsCanonical = refl
    ; betaCurrentApproxOneLoopPlateau = true
    ; betaCurrentApproxOneLoopPlateauIsTrue = refl
    ; betaRequiredMinusOneLoopPlateau = "2.7515829890895525"
    ; betaRequiredMinusOneLoopPlateauIsCanonical = refl
    ; betaRequiredMinusOneLoopOverNc = "0.9171943296965175"
    ; betaRequiredMinusOneLoopOverNcIsCanonical = refl
    ; betaBlockedCurrent = "16.7"
    ; betaBlockedCurrentIsCanonical = refl
    ; betaRequired = "19.251582989089552"
    ; betaRequiredIsCanonical = refl
    ; betaGap = "2.551582989089552"
    ; betaGapIsCanonical = refl
    ; betaRequiredOverBare = "3.2085971648482587"
    ; betaRequiredOverBareIsCanonical = refl
    ; betaRunningLaw = "beta(k)=6+0.1355488*k"
    ; betaRunningLawIsCanonical = refl
    ; kRequired = "97.7624515236546"
    ; kRequiredIsCanonical = refl
    ; kFirstSafeInteger = "98"
    ; kFirstSafeIntegerIs98 = refl
    ; betaAtK98 = "19.2837824"
    ; betaAtK98IsCanonical = refl
    ; qAtK98 = "0.12402975293679427"
    ; qAtK98IsCanonical = refl
    ; weightedEightQAtK98 = "0.9922380234943542"
    ; weightedEightQAtK98IsCanonical = refl
    ; weightedKPCurrentConverges = false
    ; weightedKPCurrentConvergesIsFalse = refl
    ; genericWeightedKPFails = true
    ; genericWeightedKPFailsIsTrue = refl
    ; anisotropicL2KPArithmeticCloses = true
    ; anisotropicL2KPArithmeticClosesIsTrue = refl
    ; entropyFactorSharpenedBelowEight = false
    ; entropyFactorSharpenedBelowEightIsFalse = refl
    ; entropyFactorSharpenedBelow431 = false
    ; entropyFactorSharpenedBelow431IsFalse = refl
    ; holleyStroockOscillationTightened = false
    ; holleyStroockOscillationTightenedIsFalse = refl
    ; anisotropicBalabanTransferCompatible = false
    ; anisotropicBalabanTransferCompatibleIsFalse = refl
    ; temporalIntegralFactorization = false
    ; temporalIntegralFactorizationIsFalse = refl
    ; carrierSupportTemporalBoundaryExclusion = false
    ; carrierSupportTemporalBoundaryExclusionIsFalse = refl
    ; spatialSlabPartitionOfUnity = false
    ; spatialSlabPartitionOfUnityIsFalse = refl
    ; spatialSlowFieldIdentification = false
    ; spatialSlowFieldIdentificationIsFalse = refl
    ; paperIILargeFieldSuppressionTransferred = false
    ; paperIILargeFieldSuppressionTransferredIsFalse = refl
    ; anisotropicBalabanPartitionIdentity = false
    ; anisotropicBalabanPartitionIdentityIsFalse = refl
    ; temporalTransferMatrixCompatibleWithSpatialBlocking = false
    ; temporalTransferMatrixCompatibleWithSpatialBlockingIsFalse = refl
    ; smallFieldBoundsSurviveAnisotropicBlocking = false
    ; smallFieldBoundsSurviveAnisotropicBlockingIsFalse = refl
    ; anisotropicWeightedKPCertificate = false
    ; anisotropicWeightedKPCertificateIsFalse = refl
    ; latticeMassGapFromAnisotropicKP = false
    ; latticeMassGapFromAnisotropicKPIsFalse = refl
    ; balabanRGScaleTransfer = false
    ; balabanRGScaleTransferIsFalse = refl
    ; activityLeakagePreservation = false
    ; activityLeakagePreservationIsFalse = refl
    ; allDiameterKPCertificate = false
    ; allDiameterKPCertificateIsFalse = refl
    ; continuumOSWightmanMassGap = false
    ; continuumOSWightmanMassGapIsFalse = refl
    ; osWightmanReconstruction = false
    ; osWightmanReconstructionIsFalse = refl
    ; massGapSurvival = false
    ; massGapSurvivalIsFalse = refl
    ; clayYangMillsPromotedIsFalse = refl
    ; algebraContract = sprint67YMAlgebraContract
    ; algebraContractIsCanonical = refl
    ; branchContract = sprint67YMBranchContract
    ; branchContractIsCanonical = refl
    ; anisotropicEntropyContract = sprint67YMAnisotropicEntropyContract
    ; anisotropicEntropyContractIsCanonical = refl
    ; temporalFactorizationContract = sprint67YMTemporalFactorizationContract
    ; temporalFactorizationContractIsCanonical = refl
    ; temporalFaceSupportContract = sprint67YMTemporalFaceSupportContract
    ; temporalFaceSupportContractIsCanonical = refl
    ; supervoxelGeometryContract = sprint67YMSupervoxelGeometryContract
    ; supervoxelGeometryContractIsCanonical = refl
    ; paperIICalibration = sprint67YMPaperIICalibration
    ; paperIICalibrationIsCanonical = refl
    ; betaOneLoopCalibration = sprint67YMBetaOneLoopCalibration
    ; betaOneLoopCalibrationIsCanonical = refl
    ; erikssonCalibration = sprint67YMErikssonCalibration
    ; erikssonCalibrationIsCanonical = refl
    ; compatibilityGate = sprint67YMCompatibilityGate
    ; compatibilityGateIsCanonical = refl
    ; kTranslation = sprint67YMKTranslation
    ; kTranslationIsCanonical = refl
    ; closedArithmeticContract = sprint67YMClosedArithmeticContract
    ; closedArithmeticContractIsCanonical = refl
    ; betaKTable = sprint67YMBetaKTable
    ; betaKTableIsCanonical = refl
    ; entropyTable = sprint67YMEntropyTable
    ; entropyTableIsCanonical = refl
    ; anisotropicLTable = sprint67YMAnisotropicLTable
    ; anisotropicLTableIsCanonical = refl
    ; branches = canonicalSprint67YMBranches
    ; branchesAreCanonical = refl
    ; routeDecisions = canonicalSprint67YMRouteDecisions
    ; routeDecisionsAreCanonical = refl
    ; openGates = canonicalSprint67YMOpenGates
    ; openGatesAreCanonical = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = sprint67YMPromotionImpossibleHere
    ; boundary = sprint67YMBoundary
    ; boundaryIsCanonical = refl
    }
