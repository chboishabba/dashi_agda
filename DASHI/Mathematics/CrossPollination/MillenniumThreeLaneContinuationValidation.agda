module DASHI.Mathematics.CrossPollination.MillenniumThreeLaneContinuationValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as PNP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as Hodge
import DASHI.Mathematics.Automorphic.EllipticInfiniteLFunctionRoadExact as BSDAnalytic
import DASHI.Mathematics.Arithmetic.EllipticTwoDescentRoadExact as BSDArithmetic

pnpConcreteFiniteMachineCarrierPaid :
  PNP.finiteMachineCarrierPaid
    PNP.canonicalConcreteTapeMachineLocalityBoundary
  ≡ true
pnpConcreteFiniteMachineCarrierPaid = refl

pnpGenericAdapterStillOpen :
  PNP.genericMachineAdapterPaid
    PNP.canonicalConcreteTapeMachineLocalityBoundary
  ≡ false
pnpGenericAdapterStillOpen = refl

pnpStillOpen :
  PNP.pVsNPResolved
    PNP.canonicalConcreteTapeMachineLocalityBoundary
  ≡ false
pnpStillOpen = refl

hodgeHomogeneousPresentationPaid :
  Hodge.homogeneousCoordinatePresentationPaid
    Hodge.canonicalProjectiveSpaceGeometryComparisonBoundary
  ≡ true
hodgeHomogeneousPresentationPaid = refl

hodgeComparisonStillOpen :
  Hodge.singularDeRhamComparisonPaid
    Hodge.canonicalProjectiveSpaceGeometryComparisonBoundary
  ≡ false
hodgeComparisonStillOpen = refl

generalHodgeStillOpen :
  Hodge.generalHodgeConjecturePaid
    Hodge.canonicalProjectiveSpaceGeometryComparisonBoundary
  ≡ false
generalHodgeStillOpen = refl

bsdInfiniteRoadTyped :
  BSDAnalytic.infiniteRoadInterfacePaid
    BSDAnalytic.canonicalEllipticInfiniteAnalyticRoadBoundary
  ≡ true
bsdInfiniteRoadTyped = refl

bsdMellinStillOpen :
  BSDAnalytic.mellinRealizationPaid
    BSDAnalytic.canonicalEllipticInfiniteAnalyticRoadBoundary
  ≡ false
bsdMellinStillOpen = refl

bsdTwoDescentCarrierPaid :
  BSDArithmetic.globalLocalCarrierPaid
    BSDArithmetic.canonicalEllipticTwoDescentRoadBoundary
  ≡ true
bsdTwoDescentCarrierPaid = refl

bsdGlobalDescentStillOpen :
  BSDArithmetic.globalExactSequencePaid
    BSDArithmetic.canonicalEllipticTwoDescentRoadBoundary
  ≡ false
bsdGlobalDescentStillOpen = refl

------------------------------------------------------------------------
-- SECOND CONTINUATION: concrete index geometry and existing-proof reuse.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as PNPIndex
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineGenericCycleClassWeldExact as HodgeP1Weld
import DASHI.Mathematics.Automorphic.EllipticEulerCauchyToLimitExact as BSDCauchy
import DASHI.Mathematics.Arithmetic.EllipticFiniteSeedToSelmerExact as BSDSeed

pnpIndexedWindowGeometryPaid :
  PNPIndex.indexedWindowGeometryPaid
    PNPIndex.canonicalConcreteTapeIndexedWindowBoundary
  ≡ true
pnpIndexedWindowGeometryPaid = refl

pnpAllWindowLocalityStillOpen :
  PNPIndex.allWindowLocalityEquivalencePaid
    PNPIndex.canonicalConcreteTapeIndexedWindowBoundary
  ≡ false
pnpAllWindowLocalityStillOpen = refl

hodgeP1GenericWeldCompilerPaid :
  HodgeP1Weld.projectiveLineGenericCycleWeldCompilerPaid
    HodgeP1Weld.canonicalProjectiveLineGenericCycleWeldBoundary
  ≡ true
hodgeP1GenericWeldCompilerPaid = refl

hodgeCPnComparisonStillOpen :
  HodgeP1Weld.literalCPnComparisonPaid
    HodgeP1Weld.canonicalProjectiveLineGenericCycleWeldBoundary
  ≡ false
hodgeCPnComparisonStillOpen = refl

bsdCauchyCompletionCompilerPaid :
  BSDCauchy.cauchyToConstructiveLimitCompilerPaid
    BSDCauchy.canonicalEllipticEulerCauchyToLimitBoundary
  ≡ true
bsdCauchyCompletionCompilerPaid = refl

bsdEulerCauchyEstimateStillOpen :
  BSDCauchy.eulerCauchyEstimatePaid
    BSDCauchy.canonicalEllipticEulerCauchyToLimitBoundary
  ≡ false
bsdEulerCauchyEstimateStillOpen = refl

bsdFiniteSeedSelmerCompilerPaid :
  BSDSeed.finiteSeedToSelmerCompilerPaid
    BSDSeed.canonicalEllipticFiniteSeedToSelmerBoundary
  ≡ true
bsdFiniteSeedSelmerCompilerPaid = refl

bsdActualGlobalSelmerStillOpen :
  BSDSeed.actualGlobalSelmerInhabitantPaid
    BSDSeed.canonicalEllipticFiniteSeedToSelmerBoundary
  ≡ false
bsdActualGlobalSelmerStillOpen = refl


------------------------------------------------------------------------
-- THIRD CONTINUATION: exact coordinate derivation, quotient weld, and
-- application-neutral convergence / all-place descent reuse.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as PNPCoord
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceSetoidQuotientWeldExact as HodgeQuot
import DASHI.Mathematics.Automorphic.EllipticEulerSummableIncrementExact as BSDInc
import DASHI.Mathematics.Arithmetic.EllipticRationalPlaceSelmerExact as BSDPlaces

pnpRewriteCoordinateDerived :
  PNPCoord.rewriteCoordinateDerivationPaid
    PNPCoord.canonicalConcreteTapeOccurrenceCoordinateBoundary
  ≡ true
pnpRewriteCoordinateDerived = refl

pnpAllOverlappingWindowsStillOpen :
  PNPCoord.allOverlappingWindowsCharacterized
    PNPCoord.canonicalConcreteTapeOccurrenceCoordinateBoundary
  ≡ false
pnpAllOverlappingWindowsStillOpen = refl

hodgeSetoidQuotientCompilerPaid :
  HodgeQuot.setoidQuotientToLiteralProjectiveSpaceCompilerPaid
    HodgeQuot.canonicalProjectiveSpaceSetoidQuotientWeldBoundary
  ≡ true
hodgeSetoidQuotientCompilerPaid = refl

hodgeConcreteQuotientStillOpen :
  HodgeQuot.concreteProjectiveQuotientInhabitantPaid
    HodgeQuot.canonicalProjectiveSpaceSetoidQuotientWeldBoundary
  ≡ false
hodgeConcreteQuotientStillOpen = refl

bsdSummableIncrementCompilerPaid :
  BSDInc.summableIncrementToEulerCauchyCompilerPaid
    BSDInc.canonicalEllipticEulerSummableIncrementBoundary
  ≡ true
bsdSummableIncrementCompilerPaid = refl

bsdEllipticIncrementEstimateStillOpen :
  BSDInc.ellipticIncrementMajorantPaid
    BSDInc.canonicalEllipticEulerSummableIncrementBoundary
  ≡ false
bsdEllipticIncrementEstimateStillOpen = refl

bsdRationalPlaceSplitPaid :
  BSDPlaces.rationalPlaceSplitPaid
    BSDPlaces.canonicalEllipticRationalPlaceSelmerBoundary
  ≡ true
bsdRationalPlaceSplitPaid = refl

bsdActualLocalFieldsStillOpen :
  BSDPlaces.actualQvKummerRealizationPaid
    BSDPlaces.canonicalEllipticRationalPlaceSelmerBoundary
  ≡ false
bsdActualLocalFieldsStillOpen = refl


------------------------------------------------------------------------
-- FOURTH CONTINUATION: repair exact projective semantics, enforce the unique
-- tape head invariant, and replace finite-place Nat labels by literal primes.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as PNPWF

pnpUniqueHeadInvariantPaid :
  PNPWF.uniqueHeadConfigurationInvariantPaid
    PNPWF.canonicalConcreteTapeWellFormedBoundary
  ≡ true
pnpUniqueHeadInvariantPaid = refl

pnpWellFormedAllWindowReverseStillOpen :
  PNPWF.wellFormedAllWindowReversePaid
    PNPWF.canonicalConcreteTapeWellFormedBoundary
  ≡ false
pnpWellFormedAllWindowReverseStillOpen = refl

hodgeExactRescalingEquivalencePaid :
  HodgeQuot.concreteRescalingEquivalencePaid
    HodgeQuot.canonicalProjectiveSpaceSetoidQuotientWeldBoundary
  ≡ true
hodgeExactRescalingEquivalencePaid = refl

bsdFinitePlacesAreLiteralPrimes :
  BSDPlaces.primePredicateOnFiniteLabelsPaid
    BSDPlaces.canonicalEllipticRationalPlaceSelmerBoundary
  ≡ true
bsdFinitePlacesAreLiteralPrimes = refl


------------------------------------------------------------------------
-- FIFTH CONTINUATION: exact overlapping local-pattern grammar.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as PNPPatterns

pnpDirectionalOverlapGrammarPaid :
  PNPPatterns.completeDirectionalOverlapPatternGrammarPaid
    PNPPatterns.canonicalConcreteTapeLocalWindowPatternsBoundary
  ≡ true
pnpDirectionalOverlapGrammarPaid = refl

pnpWholeRowWindowScanStillOpen :
  PNPPatterns.wholeRowAllWindowScanPaid
    PNPPatterns.canonicalConcreteTapeLocalWindowPatternsBoundary
  ≡ false
pnpWholeRowWindowScanStillOpen = refl


------------------------------------------------------------------------
-- BSD literal rational square-class setoid.
------------------------------------------------------------------------

import DASHI.Mathematics.Arithmetic.RationalSquareClassSetoidExact as BSDSquare

bsdRationalSquareClassRelationPaid :
  BSDSquare.rationalSquareClassSetoidPaid
    BSDSquare.canonicalRationalSquareClassBoundary
  ≡ true
bsdRationalSquareClassRelationPaid = refl

bsdRationalSquareClassQuotientStillOpen :
  BSDSquare.quotientCarrierConstructed
    BSDSquare.canonicalRationalSquareClassBoundary
  ≡ false
bsdRationalSquareClassQuotientStillOpen = refl


------------------------------------------------------------------------
-- SIXTH CONTINUATION: recursive whole-row scanner + forward locality theorem.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as PNPWhole

pnpRecursiveWholeRowScannerPaid :
  PNPWhole.recursiveWholeRowScanPaid
    PNPWhole.canonicalConcreteTapeWholeRowLocalityBoundary
  ≡ true
pnpRecursiveWholeRowScannerPaid = refl

pnpMachineStepImpliesWholeRowLegalPaid :
  PNPWhole.wellFormedStepImpliesAllWindowsPaid
    PNPWhole.canonicalConcreteTapeWholeRowLocalityBoundary
  ≡ true
pnpMachineStepImpliesWholeRowLegalPaid = refl

pnpReverseWholeRowReconstructionStillOpen :
  PNPWhole.globalTransitionScanToUniqueRewritePaid
    PNPWhole.canonicalConcreteTapeWholeRowLocalityBoundary
  ≡ false
pnpReverseWholeRowReconstructionStillOpen = refl


pnpGlobalTransitionForwardPaid :
  PNPWhole.wellFormedStepImpliesGlobalTransitionScanPaid
    PNPWhole.canonicalConcreteTapeWholeRowLocalityBoundary
  ≡ true
pnpGlobalTransitionForwardPaid = refl


------------------------------------------------------------------------
-- BSD rational Kummer map on the nonexceptional affine locus.
------------------------------------------------------------------------

import DASHI.Mathematics.Arithmetic.EllipticRationalKummerOpenExact as BSDKummer

bsdNonexceptionalRationalKummerPaid :
  BSDKummer.nonexceptionalRationalKummerMapPaid
    BSDKummer.canonicalEllipticRationalKummerOpenBoundary
  ≡ true
bsdNonexceptionalRationalKummerPaid = refl

bsdExceptionalTorsionKummerStillOpen :
  BSDKummer.exceptionalTwoTorsionValuesPaid
    BSDKummer.canonicalEllipticRationalKummerOpenBoundary
  ≡ false
bsdExceptionalTorsionKummerStillOpen = refl


------------------------------------------------------------------------
-- Hodge CP1 verticalization: exact homogeneous-vector <-> pair equivalence.
------------------------------------------------------------------------

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact as HodgeP1Pair

hodgeP1HomogeneousPairEquivalencePaid :
  HodgeP1Pair.homogeneousVectorPairEquivalencePaid
    HodgeP1Pair.canonicalProjectiveLineHomogeneousPairBoundary
  ≡ true
hodgeP1HomogeneousPairEquivalencePaid = refl

hodgeP1ActualQuotientStillOpen :
  HodgeP1Pair.projectiveLineQuotientInhabited
    HodgeP1Pair.canonicalProjectiveLineHomogeneousPairBoundary
  ≡ false
hodgeP1ActualQuotientStillOpen = refl


------------------------------------------------------------------------
-- SEVENTH CONTINUATION: extract the global aligned occurrence represented by
-- a centered window in the recursive whole-row scan.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeCenteredWindowExtractionExact as PNPCenter

pnpCenteredScanExtractionPaid :
  PNPCenter.centeredScanGlobalExtractionPaid
    PNPCenter.canonicalConcreteTapeCenteredWindowExtractionBoundary
  ≡ true
pnpCenteredScanExtractionPaid = refl

pnpOutsideEqualityStillOpen :
  PNPCenter.legalContextForcesCommonOutsidePaid
    PNPCenter.canonicalConcreteTapeCenteredWindowExtractionBoundary
  ≡ false
pnpOutsideEqualityStillOpen = refl


------------------------------------------------------------------------
-- Hodge CP1 affine chart normalization.
------------------------------------------------------------------------

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineAffineChartsExact as HodgeCharts

hodgeP1FirstChartNormalizationPaid :
  HodgeCharts.firstAffineChartNormalizationPaid
    HodgeCharts.canonicalProjectiveLineAffineChartsBoundary
  ≡ true
hodgeP1FirstChartNormalizationPaid = refl

hodgeP1SecondChartNormalizationPaid :
  HodgeCharts.secondAffineChartNormalizationPaid
    HodgeCharts.canonicalProjectiveLineAffineChartsBoundary
  ≡ true
hodgeP1SecondChartNormalizationPaid = refl

hodgeP1GlobalQuotientStillOpen :
  HodgeCharts.globalProjectiveLineQuotientPaid
    HodgeCharts.canonicalProjectiveLineAffineChartsBoundary
  ≡ false
hodgeP1GlobalQuotientStillOpen = refl


------------------------------------------------------------------------
-- BSD analytic: literal Basel majorant -> constructive Dirichlet convergence.
------------------------------------------------------------------------

import DASHI.Mathematics.Automorphic.EllipticDirichletBaselMajorantExact as BSDBasel

bsdBaselMajorantCompilerPaid :
  BSDBasel.baselMajorantToDirichletConvergencePaid
    BSDBasel.canonicalEllipticDirichletBaselMajorantBoundary
  ≡ true
bsdBaselMajorantCompilerPaid = refl

bsdActualEllipticCoefficientMajorantStillOpen :
  BSDBasel.actualEllipticCoefficientMajorantPaid
    BSDBasel.canonicalEllipticDirichletBaselMajorantBoundary
  ≡ false
bsdActualEllipticCoefficientMajorantStillOpen = refl


------------------------------------------------------------------------
-- EIGHTH CONTINUATION: centered occurrence + common outside context -> actual
-- well-formed machine step.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeGlobalRewriteReconstructionExact as PNPReconstruct

pnpCommonOutsideCompilesToStep :
  PNPReconstruct.commonOutsideContextToWellFormedStepPaid
    PNPReconstruct.canonicalConcreteTapeGlobalRewriteReconstructionBoundary
  ≡ true
pnpCommonOutsideCompilesToStep = refl

pnpGlobalLegalityOutsideEqualityStillOpen :
  PNPReconstruct.globalLegalityForcesOutsideAgreementPaid
    PNPReconstruct.canonicalConcreteTapeGlobalRewriteReconstructionBoundary
  ≡ false
pnpGlobalLegalityOutsideEqualityStillOpen = refl


------------------------------------------------------------------------
-- NINTH CONTINUATION: global legal scan forces the entire pre-transition
-- outside context to agree.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeGlobalPrefixAgreementExact as PNPPrefix

pnpGlobalPrefixAgreementPaid :
  PNPPrefix.globalLegalityForcesPrefixAgreementPaid
    PNPPrefix.canonicalConcreteTapeGlobalPrefixAgreementBoundary
  ≡ true
pnpGlobalPrefixAgreementPaid = refl

pnpGlobalSuffixAgreementStillOpen :
  PNPPrefix.globalLegalityForcesSuffixAgreementPaid
    PNPPrefix.canonicalConcreteTapeGlobalPrefixAgreementBoundary
  ≡ false
pnpGlobalSuffixAgreementStillOpen = refl


------------------------------------------------------------------------
-- TENTH CONTINUATION: global legality forces suffix agreement and closes the
-- semantic whole-row step reconstruction.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeGlobalSuffixAgreementExact as PNPSuffix

pnpGlobalSuffixAgreementPaid :
  PNPSuffix.globalLegalityForcesSuffixAgreementPaid
    PNPSuffix.canonicalConcreteTapeGlobalSuffixAgreementBoundary
  ≡ true
pnpGlobalSuffixAgreementPaid = refl

pnpGlobalReverseLocalityPaid :
  PNPSuffix.globalTransitionScanToWellFormedStepPaid
    PNPSuffix.canonicalConcreteTapeGlobalSuffixAgreementBoundary
  ≡ true
pnpGlobalReverseLocalityPaid = refl

pnpSATWeldStillOpen :
  PNPSuffix.canonicalSATWeldPaid
    PNPSuffix.canonicalConcreteTapeGlobalSuffixAgreementBoundary
  ≡ false
pnpSATWeldStillOpen = refl


------------------------------------------------------------------------
-- ELEVENTH CONTINUATION: centered transition is derived from local legality
-- at the unique interior head; semantic whole-row locality is now bidirectional.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as PNPIff

pnpCenteredTransitionDerivedFromLegality :
  PNPIff.centeredTransitionDerivedFromLegalityPaid
    PNPIff.canonicalConcreteTapeLocalityCharacterizationBoundary
  ≡ true
pnpCenteredTransitionDerivedFromLegality = refl

pnpWholeRowLocalityIffPaid :
  PNPIff.semanticWholeRowLocalityIffPaid
    PNPIff.canonicalConcreteTapeLocalityCharacterizationBoundary
  ≡ true
pnpWholeRowLocalityIffPaid = refl

pnpBooleanRecognizerStillOpen :
  PNPIff.booleanLocalRecognizerPaid
    PNPIff.canonicalConcreteTapeLocalityCharacterizationBoundary
  ≡ false
pnpBooleanRecognizerStillOpen = refl


------------------------------------------------------------------------
-- TWELFTH CONTINUATION: literal CP1 overlap inversion + rational two-torsion
-- Kummer dictionary.
------------------------------------------------------------------------

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineChartOverlapExact as HodgeOverlap
import DASHI.Mathematics.Arithmetic.EllipticRationalTwoTorsionKummerExact as BSDTorsionKummer

hodgeP1OverlapInversionPaid :
  HodgeOverlap.chartOverlapProductIsOnePaid
    HodgeOverlap.canonicalProjectiveLineChartOverlapBoundary
  ≡ true
hodgeP1OverlapInversionPaid = refl

hodgeP1QuotientStillOpenAfterOverlap :
  HodgeOverlap.globalProjectiveLineQuotientPaid
    HodgeOverlap.canonicalProjectiveLineChartOverlapBoundary
  ≡ false
hodgeP1QuotientStillOpenAfterOverlap = refl

bsdLiteralTwoTorsionKummerDictionaryPaid :
  BSDTorsionKummer.literalTwoTorsionKummerDictionaryPaid
    BSDTorsionKummer.canonicalEllipticRationalTwoTorsionKummerBoundary
  ≡ true
bsdLiteralTwoTorsionKummerDictionaryPaid = refl

bsdLocalKummerStillOpenAfterDictionary :
  BSDTorsionKummer.localKummerMapsPaid
    BSDTorsionKummer.canonicalEllipticRationalTwoTorsionKummerBoundary
  ≡ false
bsdLocalKummerStillOpenAfterDictionary = refl


------------------------------------------------------------------------
-- THIRTEENTH CONTINUATION: total Boolean recognizer over the exact local
-- grammar; semantic legality reflects forward to Boolean truth.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowBoolExact as PNPBool

pnpLegalWindowBoolTotal :
  PNPBool.totalBooleanRecognizerPaid
    PNPBool.canonicalConcreteTapeLegalWindowBoolBoundary
  ≡ true
pnpLegalWindowBoolTotal = refl

pnpSemanticToBooleanReflectionPaid :
  PNPBool.semanticToBooleanReflectionPaid
    PNPBool.canonicalConcreteTapeLegalWindowBoolBoundary
  ≡ true
pnpSemanticToBooleanReflectionPaid = refl

pnpBooleanToSemanticReflectionStillOpen :
  PNPBool.booleanToSemanticReflectionPaid
    PNPBool.canonicalConcreteTapeLegalWindowBoolBoundary
  ≡ false
pnpBooleanToSemanticReflectionStillOpen = refl


------------------------------------------------------------------------
-- FOURTEENTH CONTINUATION: proof-carrying Boolean recognition closes the local
-- semantic <-> Bool reflection theorem.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowReflectionExact as PNPReflect

pnpFullLegalWindowReflectionPaid :
  PNPReflect.fullLegalWindowBooleanIffPaid
    PNPReflect.canonicalConcreteTapeLegalWindowReflectionBoundary
  ≡ true
pnpFullLegalWindowReflectionPaid = refl

pnpCanonicalSATWeldStillNext :
  PNPReflect.canonicalSATWeldPaid
    PNPReflect.canonicalConcreteTapeLegalWindowReflectionBoundary
  ≡ false
pnpCanonicalSATWeldStillNext = refl


------------------------------------------------------------------------
-- FIFTEENTH CONTINUATION: CP1 atlas gluing relation from literal inversion.
------------------------------------------------------------------------

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineAtlasGluingExact as HodgeGlue

hodgeP1AtlasGluingPaid :
  HodgeGlue.literalAtlasGluingRelationPaid
    HodgeGlue.canonicalProjectiveLineAtlasGluingBoundary
  ≡ true
hodgeP1AtlasGluingPaid = refl

hodgeP1OverlapRepresentativesRelated :
  HodgeGlue.overlapRepresentativesGluePaid
    HodgeGlue.canonicalProjectiveLineAtlasGluingBoundary
  ≡ true
hodgeP1OverlapRepresentativesRelated = refl

hodgeP1QuotientCarrierStillOpen :
  HodgeGlue.quotientCarrierInhabitedPaid
    HodgeGlue.canonicalProjectiveLineAtlasGluingBoundary
  ≡ false
hodgeP1QuotientCarrierStillOpen = refl


------------------------------------------------------------------------
-- SIXTEENTH CONTINUATION: generic fixed-width codec -> reflected local CNF.
-- This is the exact remote side of the missing canonical Cell/Bits weld.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as PNPCNF

pnpCodecToCNFSemanticEquivalencePaid :
  PNPCNF.codecCNFSemanticEquivalencePaid
    PNPCNF.canonicalConcreteTapeWindowCodecCNFWeldBoundary
  ≡ true
pnpCodecToCNFSemanticEquivalencePaid = refl

pnpCanonicalConcreteCodecStillExternal :
  PNPCNF.canonicalConcreteWindowCodecPaid
    PNPCNF.canonicalConcreteTapeWindowCodecCNFWeldBoundary
  ≡ false
pnpCanonicalConcreteCodecStillExternal = refl
