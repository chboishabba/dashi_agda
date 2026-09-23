module DASHI.Moonshine.JInvariant369CanonicalInterpretationExact where

------------------------------------------------------------------------
-- CANONICAL INTERPRETATION OF THE JMD 3/6/9/27 STRUCTURE
--
-- The formal development now separates two genuine structures that share the
-- numeral 3 but are not automatically the same object.
--
-- PHASE LANE
--
--   weight-12 Delta reflection
--      -> sixfold phase constraint modulo half-turn
--      -> orientation-forgetting C6 -> C3 quotient.
--
-- LEVEL-FIBRE LANE
--
--   Gamma(27) subset Gamma(9) subset Gamma(3)
--      -> cusp fibres Z/27 -> Z/9 -> Z/3
--      -> same-point level observers with translation/reflection equivariance.
--
-- KEY NO-GO
--
-- j is modular invariant, hence any observer that is only a function of jPhase
-- is invariant under T.  The genuine cusp-translation coordinates at levels
-- 3, 9 and 27 have no fixed points under their T generators.  Therefore no
-- globally phase-only C3/C9/C27 renderer observer can be identified with those
-- nontrivial principal-level cusp coordinates.
--
-- Consequently the mathematically honest 369 picture is a fibred one:
--
--       continuous Delta/j data at z
--            |                 |
--       phase quotient      level lift
--            |                 |
--        C6 -> C3          C27 -> C9 -> C3
--
-- The two C3 carriers may be related by an additional same-point calibration
-- in contexts where the modular action is not being identified with the
-- nontrivial cusp translation, but they are NOT canonically equal from jPhase
-- alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.DeltaUnitCircleReflectionPhaseExact as Phase
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as LevelTower
import DASHI.Moonshine.JInvariant369PrincipalLevelTowerExact as Principal
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as Separation
import DASHI.Moonshine.JInvariant369LevelNonDescentThroughJExact as NonDescent
import DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact as Repair
import DASHI.Moonshine.JInvariant369SignedSSPFRACTRANPhaseFibreExact as SignedSSP
import DASHI.Moonshine.JInvariant369JointPhaseLevelBundleExact as JointBundle
import DASHI.Moonshine.JSameWeightQuotientReflectionExact as JReflection
import DASHI.Moonshine.JInvariant369JointJReflectionWeldExact as JointJReflection
import DASHI.Moonshine.JInvariantAnalyticNormalizedKleinAdapterExact as NormalizedKlein
import DASHI.Moonshine.JInvariant369NormalizedAnalyticRendererExact as NormalizedRenderer
import DASHI.Moonshine.JInvariant369NormalizedRendererReadoutFactorizationExact as ReadoutFactor
import DASHI.Moonshine.JInvariant369NormalizedRendererCanonicalReflectionExact as CanonicalReflection
import DASHI.Moonshine.JInvariant369CanonicalJointReflectionMinimalExact as MinimalReflection
import DASHI.Moonshine.JInvariant369SSPLevelDihedralIntertwinerExact as SSPLevel
import DASHI.Moonshine.JInvariant369JointFibredObserverExact as JointFibred
import DASHI.Moonshine.JInvariant369JointBundleLegacyFibreBridgeExact as LegacyBridge
import DASHI.Moonshine.JInvariant369JointFibreBifiltrationExact as JointBif
import DASHI.Moonshine.JInvariantSmithChartObserverCrossPollinationExact as SmithCross
import DASHI.Moonshine.JInvariantSmithChartActionSeparationExact as SmithAction
import DASHI.Moonshine.JInvariantSmithChartMobiusMatrixBridgeExact as SmithMatrix
import DASHI.Moonshine.JInvariant369C6TenRankWeightTwelveCrossPollinationExact as Cross
import DASHI.Moonshine.JInvariant369NeutralCuspRelationCrossPollinationExact as NeutralCusp

record Canonical369InterpretationBoundary : Set where
  constructor canonical-369-interpretation-boundary
  field
    deltaWeight12ReflectionOwnsSixfoldPhaseRoute : Bool
    c6ToC3OrientationQuotientIsCanonical : Bool

    gamma27SubsetGamma9SubsetGamma3Owned : Bool
    cusp27To9To3TowerOwned : Bool
    levelTranslationEquivarianceOwned : Bool
    levelReflectionEquivarianceOwned : Bool
    samePointNineTwentySevenFibreObserversOwned : Bool

    phaseOnlyC3EqualsNontrivialLevel3 : Bool
    phaseOnlyC9EqualsNontrivialLevel9 : Bool
    phaseOnlyC27EqualsNontrivialLevel27 : Bool

    directPhaseC3ToPrincipalLevel9RefinementCanonical : Bool
    fibredPhaseAndLevelInterpretationRequired : Bool

    fullAnalyticModularCurvesConstructed : Bool
    fullDeckGroupsCollapsedToCyclic : Bool
    c27EqualsC3CubedAsGroup : Bool

    signedSSPPhaseObserverOwned : Bool
    signedSSPNegationSpectralConjugationOwned : Bool
    signedSpectralToLevelTranslationIntertwinerExists : Bool
    signedSSPAutomaticallyIsPrincipalLevel3Fibre : Bool

    jointJPhaseLevelBundleConstructed : Bool
    phaseAndLevelC3TypeRolesSeparated : Bool
    tActionFixesJPhaseButTranslatesLevelTower : Bool
    jointReflectionNegatesPhaseAndLevelCoordinates : Bool
    modularTIsIdentityOnPhaseLane : Bool
    modularTTranslatesLevelLane : Bool
    jointRTRIsTInverseCoordinatewise : Bool
    phaseInternalC3CycleIdentifiedWithModularT : Bool

    sameWeightJReflectionCompilerOwned : Bool
    fixedLocusJConjugationFixedCompilerOwned : Bool
    analyticJReflectionCompilesIntoJointBundle : Bool
    rendererFixedPointCompilesToJointJConjugationFixed : Bool
    normalizedStandardJKleinAdapterOwned : Bool
    normalizedRendererJDefinitionallyStandardJ : Bool
    normalizedRendererJointReflectionCompilerOwned : Bool
    normalizedRendererContinuousPresentationFactorizationOwned : Bool
    leanConcreteContinuousJReadoutParityRecorded : Bool
    leanContinuousPhaseReflectionOwned : Bool
    normalizedRendererCanonicalReflectionCompilerOwned : Bool
    jointReflectionPointAlignmentDefinitional : Bool
    normalizedRendererReflectionPointAlignmentCompilerDefinitional : Bool
    canonicalReflectionNeedsPhase9Quantizer : Bool
    canonicalReflectionNeedsPhase27Quantizer : Bool
    canonicalReflectionPhaseC3DerivedFromC6 : Bool
    canonicalReflectionLevel9DerivedFromLevel27 : Bool
    canonicalReflectionLevel3DerivedFromLevel27 : Bool
    concreteRendererAnalyticJSameObjectWeldInhabited : Bool
    normalizedRendererReadoutInhabited : Bool
    normalizedRendererReflectionPointAlignmentInhabited : Bool
    concreteJRealAxisInterpretationTransported : Bool

    sspC3CycleIntertwinesLevelTranslation : Bool
    sspC2AntipodeIntertwinesLevelInversion : Bool
    sspLevel3FiniteDihedralEquivalenceOwned : Bool
    signedMagnitudeFactorsThroughLevel3 : Bool

    jointPhaseLevelSignedFibreConstructed : Bool
    jointFiniteDihedralLawOwned : Bool
    level27FactorsThroughBaseJSurface : Bool
    genericInvariantBaseNoLevelDescentCompilerOwned : Bool
    level3CannotFactorThroughJ : Bool
    level9CannotFactorThroughJ : Bool
    level27CannotFactorThroughJ : Bool
    phaseReadoutMayStillFactorThroughJ : Bool

    jointFibreResolutionProductConstructed : Bool
    resolutionCoarseningCommutesWithModularActions : Bool
    oldRelational369EqualsPrincipalLevelTower : Bool

    canonicalSampleToLegacySignedFibreBridgeOwned : Bool
    legacyBridgeRestrictedToCanonicalSamples : Bool
    legacyBridgeIntertwinesTranslationCoordinatewise : Bool
    legacyBridgeIntertwinesReflectionCoordinatewise : Bool
    legacyBridgeTranslationCommutingSquareOwned : Bool
    legacyBridgeReflectionCommutingSquareOwned : Bool
    legacyBridgeRecoversPhaseC3FromLevelC3 : Bool
    legacyFibreEquivalentToCanonicalJointBundle : Bool

    smithObserverCrossPollinationOwned : Bool
    smithHalfTurnDistinctFromModularTOnC6 : Bool
    smithHalfTurnDistinctFromModularReflectionOnC6 : Bool
    c3QuotientCanEraseSmithHalfTurn : Bool
    c3ObserverDoesNotDetermineUnderlyingC6Action : Bool
    smithGammaHasExactMobiusMatrixPresentation : Bool
    smithAdmittanceHasExactMobiusMatrixPresentation : Bool
    smithMobiusMatrixToC6CompilerOwned : Bool
    smithMobiusMatrixC3ForgetsHalfTurn : Bool
    engineeringJIdentifiedWithModularJInvariant : Bool
    smithGammaIdentifiedWithModularJInvariant : Bool

open Canonical369InterpretationBoundary public

canonicalCanonical369InterpretationBoundary :
  Canonical369InterpretationBoundary
canonicalCanonical369InterpretationBoundary =
  record
    { deltaWeight12ReflectionOwnsSixfoldPhaseRoute = true
    ; c6ToC3OrientationQuotientIsCanonical = true

    ; gamma27SubsetGamma9SubsetGamma3Owned = true
    ; cusp27To9To3TowerOwned = true
    ; levelTranslationEquivarianceOwned = true
    ; levelReflectionEquivarianceOwned = true
    ; samePointNineTwentySevenFibreObserversOwned = true

    ; phaseOnlyC3EqualsNontrivialLevel3 = false
    ; phaseOnlyC9EqualsNontrivialLevel9 = false
    ; phaseOnlyC27EqualsNontrivialLevel27 = false

    ; directPhaseC3ToPrincipalLevel9RefinementCanonical = false
    ; fibredPhaseAndLevelInterpretationRequired = true

    ; fullAnalyticModularCurvesConstructed = false
    ; fullDeckGroupsCollapsedToCyclic = false
    ; c27EqualsC3CubedAsGroup = false

    ; signedSSPPhaseObserverOwned = true
    ; signedSSPNegationSpectralConjugationOwned = true
    ; signedSpectralToLevelTranslationIntertwinerExists = false
    ; signedSSPAutomaticallyIsPrincipalLevel3Fibre = false

    ; jointJPhaseLevelBundleConstructed = true
    ; phaseAndLevelC3TypeRolesSeparated = true
    ; tActionFixesJPhaseButTranslatesLevelTower = true
    ; jointReflectionNegatesPhaseAndLevelCoordinates = true
    ; modularTIsIdentityOnPhaseLane = true
    ; modularTTranslatesLevelLane = true
    ; jointRTRIsTInverseCoordinatewise = true
    ; phaseInternalC3CycleIdentifiedWithModularT = false

    ; sameWeightJReflectionCompilerOwned = true
    ; fixedLocusJConjugationFixedCompilerOwned = true
    ; analyticJReflectionCompilesIntoJointBundle = true
    ; rendererFixedPointCompilesToJointJConjugationFixed = true
    ; normalizedStandardJKleinAdapterOwned = true
    ; normalizedRendererJDefinitionallyStandardJ = true
    ; normalizedRendererJointReflectionCompilerOwned = true
    ; normalizedRendererContinuousPresentationFactorizationOwned = true
    ; leanConcreteContinuousJReadoutParityRecorded = true
    ; leanContinuousPhaseReflectionOwned = true
    ; normalizedRendererCanonicalReflectionCompilerOwned = true
    ; jointReflectionPointAlignmentDefinitional = true
    ; normalizedRendererReflectionPointAlignmentCompilerDefinitional = true
    ; canonicalReflectionNeedsPhase9Quantizer = false
    ; canonicalReflectionNeedsPhase27Quantizer = false
    ; canonicalReflectionPhaseC3DerivedFromC6 = true
    ; canonicalReflectionLevel9DerivedFromLevel27 = true
    ; canonicalReflectionLevel3DerivedFromLevel27 = true
    ; concreteRendererAnalyticJSameObjectWeldInhabited = false
    ; normalizedRendererReadoutInhabited = false
    ; normalizedRendererReflectionPointAlignmentInhabited = false
    ; concreteJRealAxisInterpretationTransported = false

    ; sspC3CycleIntertwinesLevelTranslation = true
    ; sspC2AntipodeIntertwinesLevelInversion = true
    ; sspLevel3FiniteDihedralEquivalenceOwned = true
    ; signedMagnitudeFactorsThroughLevel3 = false

    ; jointPhaseLevelSignedFibreConstructed = true
    ; jointFiniteDihedralLawOwned = true
    ; level27FactorsThroughBaseJSurface = false
    ; genericInvariantBaseNoLevelDescentCompilerOwned = true
    ; level3CannotFactorThroughJ = true
    ; level9CannotFactorThroughJ = true
    ; level27CannotFactorThroughJ = true
    ; phaseReadoutMayStillFactorThroughJ = true

    ; jointFibreResolutionProductConstructed = true
    ; resolutionCoarseningCommutesWithModularActions = true
    ; oldRelational369EqualsPrincipalLevelTower = false

    ; canonicalSampleToLegacySignedFibreBridgeOwned = true
    ; legacyBridgeRestrictedToCanonicalSamples = true
    ; legacyBridgeIntertwinesTranslationCoordinatewise = true
    ; legacyBridgeIntertwinesReflectionCoordinatewise = true
    ; legacyBridgeTranslationCommutingSquareOwned = true
    ; legacyBridgeReflectionCommutingSquareOwned = true
    ; legacyBridgeRecoversPhaseC3FromLevelC3 = false
    ; legacyFibreEquivalentToCanonicalJointBundle = false

    ; smithObserverCrossPollinationOwned = true
    ; smithHalfTurnDistinctFromModularTOnC6 = true
    ; smithHalfTurnDistinctFromModularReflectionOnC6 = true
    ; c3QuotientCanEraseSmithHalfTurn = true
    ; c3ObserverDoesNotDetermineUnderlyingC6Action = true
    ; smithGammaHasExactMobiusMatrixPresentation = true
    ; smithAdmittanceHasExactMobiusMatrixPresentation = true
    ; smithMobiusMatrixToC6CompilerOwned = true
    ; smithMobiusMatrixC3ForgetsHalfTurn = true
    ; engineeringJIdentifiedWithModularJInvariant = false
    ; smithGammaIdentifiedWithModularJInvariant = false
    }

------------------------------------------------------------------------
-- Query-stable architecture receipts.
------------------------------------------------------------------------

phaseOnlyC3IsNotPrincipalLevel3 :
  phaseOnlyC3EqualsNontrivialLevel3
    canonicalCanonical369InterpretationBoundary
  ≡ false
phaseOnlyC3IsNotPrincipalLevel3 = refl


signedMagnitudeDoesNotFactorThroughLevel3 :
  signedMagnitudeFactorsThroughLevel3
    canonicalCanonical369InterpretationBoundary
  ≡ false
signedMagnitudeDoesNotFactorThroughLevel3 = refl

principalLevel3DoesNotDescendThroughJ :
  level3CannotFactorThroughJ
    canonicalCanonical369InterpretationBoundary
  ≡ true
principalLevel3DoesNotDescendThroughJ = refl

principalLevel9DoesNotDescendThroughJ :
  level9CannotFactorThroughJ
    canonicalCanonical369InterpretationBoundary
  ≡ true
principalLevel9DoesNotDescendThroughJ = refl

principalLevel27DoesNotDescendThroughJ :
  level27CannotFactorThroughJ
    canonicalCanonical369InterpretationBoundary
  ≡ true
principalLevel27DoesNotDescendThroughJ = refl

phaseReadoutRemainsAFunctionOfJ :
  phaseReadoutMayStillFactorThroughJ
    canonicalCanonical369InterpretationBoundary
  ≡ true
phaseReadoutRemainsAFunctionOfJ = refl

modularTIsTrivialOnPhaseLane :
  modularTIsIdentityOnPhaseLane
    canonicalCanonical369InterpretationBoundary
  ≡ true
modularTIsTrivialOnPhaseLane = refl

modularTTranslatesPrincipalLevelLane :
  modularTTranslatesLevelLane
    canonicalCanonical369InterpretationBoundary
  ≡ true
modularTTranslatesPrincipalLevelLane = refl

phaseInternalCycleIsNotModularT :
  phaseInternalC3CycleIdentifiedWithModularT
    canonicalCanonical369InterpretationBoundary
  ≡ false
phaseInternalCycleIsNotModularT = refl

jointModularDihedralLawIsOwned :
  jointRTRIsTInverseCoordinatewise
    canonicalCanonical369InterpretationBoundary
  ≡ true
jointModularDihedralLawIsOwned = refl


analyticJReflectionFeedsJointBundle :
  analyticJReflectionCompilesIntoJointBundle
    canonicalCanonical369InterpretationBoundary
  ≡ true
analyticJReflectionFeedsJointBundle = refl

jointRendererAnalyticJWeldStillOpen :
  concreteRendererAnalyticJSameObjectWeldInhabited
    canonicalCanonical369InterpretationBoundary
  ≡ false
jointRendererAnalyticJWeldStillOpen = refl


normalizedRendererOwnsStandardJDefinitionally :
  normalizedRendererJDefinitionallyStandardJ
    canonicalCanonical369InterpretationBoundary
  ≡ true
normalizedRendererOwnsStandardJDefinitionally = refl

normalizedRendererReflectionNeedsOnlyAlignment :
  normalizedRendererJointReflectionCompilerOwned
    canonicalCanonical369InterpretationBoundary
  ≡ true
normalizedRendererReflectionNeedsOnlyAlignment = refl

normalizedRendererReadoutStillOpen :
  normalizedRendererReadoutInhabited
    canonicalCanonical369InterpretationBoundary
  ≡ false
normalizedRendererReadoutStillOpen = refl

normalizedRendererReflectionAlignmentStillOpen :
  normalizedRendererReflectionPointAlignmentInhabited
    canonicalCanonical369InterpretationBoundary
  ≡ false
normalizedRendererReflectionAlignmentStillOpen = refl

fullDeckGroupIsNotCollapsedToCyclic :
  fullDeckGroupsCollapsedToCyclic
    canonicalCanonical369InterpretationBoundary
  ≡ false
fullDeckGroupIsNotCollapsedToCyclic = refl

oldRelational369IsNotPrincipalLevelTower :
  oldRelational369EqualsPrincipalLevelTower
    canonicalCanonical369InterpretationBoundary
  ≡ false
oldRelational369IsNotPrincipalLevelTower = refl


legacyBridgeIsCanonicalSampleOnly :
  legacyBridgeRestrictedToCanonicalSamples
    canonicalCanonical369InterpretationBoundary
  ≡ true
legacyBridgeIsCanonicalSampleOnly = refl

legacyBridgePreservesModularActions :
  legacyBridgeIntertwinesTranslationCoordinatewise
    canonicalCanonical369InterpretationBoundary
  ≡ true
legacyBridgePreservesModularActions = refl

legacyBridgePreservesReflectionAction :
  legacyBridgeIntertwinesReflectionCoordinatewise
    canonicalCanonical369InterpretationBoundary
  ≡ true
legacyBridgePreservesReflectionAction = refl


legacyBridgeTranslationSquareIsOwned :
  legacyBridgeTranslationCommutingSquareOwned
    canonicalCanonical369InterpretationBoundary
  ≡ true
legacyBridgeTranslationSquareIsOwned = refl

legacyBridgeReflectionSquareIsOwned :
  legacyBridgeReflectionCommutingSquareOwned
    canonicalCanonical369InterpretationBoundary
  ≡ true
legacyBridgeReflectionSquareIsOwned = refl

legacyBridgeDoesNotRecoverPhaseC3 :
  legacyBridgeRecoversPhaseC3FromLevelC3
    canonicalCanonical369InterpretationBoundary
  ≡ false
legacyBridgeDoesNotRecoverPhaseC3 = refl

legacyFibreIsNotDeclaredEquivalentToCanonicalBundle :
  legacyFibreEquivalentToCanonicalJointBundle
    canonicalCanonical369InterpretationBoundary
  ≡ false
legacyFibreIsNotDeclaredEquivalentToCanonicalBundle = refl

------------------------------------------------------------------------
-- Research interpretation:
--
-- * 6 is analytically forced by weight 12 plus reciprocal-conjugate reflection.
-- * 3 in the phase lane is a genuine C3 quotient after forgetting orientation.
-- * 9 and 27 have a genuine modular-level interpretation on cusp fibres.
-- * but 9/27 are NOT phase-only refinements of j hue: the T-action proves a
--   no-go against such an identification.
-- * therefore the substantive structure is a phase object fibred together with
--   principal-level data, not one scalar phase quantized at 3/6/9/27.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Signed SSP / FRACTRAN placement.
------------------------------------------------------------------------

signedSSP369FibreBoundary :
  SignedSSP.SignedSSP369FibreBoundary
signedSSP369FibreBoundary =
  SignedSSP.canonicalSignedSSP369FibreBoundary

signedSSPCannotCollapseSpectralConjugationToLevelTranslation :
  SignedSSP.SignedPhaseToLevel3Intertwiner →
  Separation.Empty
signedSSPCannotCollapseSpectralConjugationToLevelTranslation =
  SignedSSP.signedSpectralConjugationCannotEqualLevel3Translation

------------------------------------------------------------------------
-- Positive generator-matched SSP <-> level-3 finite action bridge.
------------------------------------------------------------------------

sspLevel3DihedralBoundary :
  SSPLevel.SSPLevel3DihedralIntertwinerBoundary
sspLevel3DihedralBoundary =
  SSPLevel.canonicalSSPLevel3DihedralIntertwinerBoundary

------------------------------------------------------------------------
-- First-class joint phase/level/signed fibre.
------------------------------------------------------------------------

joint369FibredObserverBoundary :
  JointFibred.Joint369FibredObserverBoundary
joint369FibredObserverBoundary =
  JointFibred.canonicalJoint369FibredObserverBoundary


------------------------------------------------------------------------
-- Joint bundle / J reflection receipts.
------------------------------------------------------------------------

jointPhaseLevelBoundary : JointBundle.JointPhaseLevelBoundary
jointPhaseLevelBoundary = JointBundle.canonicalJointPhaseLevelBoundary

jReflectionBoundary : JReflection.JReflectionBoundary
jReflectionBoundary = JReflection.canonicalJReflectionBoundary


jointJReflectionWeldBoundary :
  JointJReflection.JointJReflectionWeldBoundary
jointJReflectionWeldBoundary =
  JointJReflection.canonicalJointJReflectionWeldBoundary


normalizedKleinBoundary :
  NormalizedKlein.AnalyticNormalizedKleinBoundary
normalizedKleinBoundary =
  NormalizedKlein.canonicalAnalyticNormalizedKleinBoundary

normalizedRendererBoundary :
  NormalizedRenderer.NormalizedAnalyticRendererBoundary
normalizedRendererBoundary =
  NormalizedRenderer.canonicalNormalizedAnalyticRendererBoundary


normalizedRendererReadoutFactorizationBoundary :
  ReadoutFactor.NormalizedReadoutFactorizationBoundary
normalizedRendererReadoutFactorizationBoundary =
  ReadoutFactor.canonicalNormalizedReadoutFactorizationBoundary


normalizedRendererCanonicalReflectionBoundary :
  CanonicalReflection.CanonicalNormalizedReflectionBoundary
normalizedRendererCanonicalReflectionBoundary =
  CanonicalReflection.canonicalCanonicalNormalizedReflectionBoundary


minimalCanonicalJointReflectionBoundary :
  MinimalReflection.MinimalCanonicalReflectionBoundary
minimalCanonicalJointReflectionBoundary =
  MinimalReflection.canonicalMinimalCanonicalReflectionBoundary

phase9IsNotARequiredCanonicalPhaseReflectionObserver :
  canonicalReflectionNeedsPhase9Quantizer
    canonicalCanonical369InterpretationBoundary
  ≡ false
phase9IsNotARequiredCanonicalPhaseReflectionObserver = refl

phase27IsNotARequiredCanonicalPhaseReflectionObserver :
  canonicalReflectionNeedsPhase27Quantizer
    canonicalCanonical369InterpretationBoundary
  ≡ false
phase27IsNotARequiredCanonicalPhaseReflectionObserver = refl

canonicalPhaseC3ReflectionComesFromC6 :
  canonicalReflectionPhaseC3DerivedFromC6
    canonicalCanonical369InterpretationBoundary
  ≡ true
canonicalPhaseC3ReflectionComesFromC6 = refl

normalizedRendererReflectionPointNoLongerIndependent :
  normalizedRendererReflectionPointAlignmentCompilerDefinitional
    canonicalCanonical369InterpretationBoundary
  ≡ true
normalizedRendererReflectionPointNoLongerIndependent = refl

jointReflectionPointNoLongerIndependent :
  jointReflectionPointAlignmentDefinitional
    canonicalCanonical369InterpretationBoundary
  ≡ true
jointReflectionPointNoLongerIndependent = refl

normalizedRendererReadoutIsNowSplitByRole :
  normalizedRendererContinuousPresentationFactorizationOwned
    canonicalCanonical369InterpretationBoundary
  ≡ true
normalizedRendererReadoutIsNowSplitByRole = refl

leanOwnsConcreteContinuousJPhaseReadout :
  leanConcreteContinuousJReadoutParityRecorded
    canonicalCanonical369InterpretationBoundary
  ≡ true
leanOwnsConcreteContinuousJPhaseReadout = refl

leanOwnsContinuousJPhaseReflection :
  leanContinuousPhaseReflectionOwned
    canonicalCanonical369InterpretationBoundary
  ≡ true
leanOwnsContinuousJPhaseReflection = refl


levelNonDescentThroughJBoundary :
  NonDescent.LevelNonDescentThroughJBoundary
levelNonDescentThroughJBoundary =
  NonDescent.canonicalLevelNonDescentThroughJBoundary

------------------------------------------------------------------------
-- Orthogonal composition with the pre-existing SSP/J resolution bifiltration.
------------------------------------------------------------------------

jointFibreBifiltrationBoundary :
  JointBif.JointFibreBifiltrationBoundary
jointFibreBifiltrationBoundary =
  JointBif.canonicalJointFibreBifiltrationBoundary


legacyBridgeBoundary :
  LegacyBridge.LegacyBridgeBoundary
legacyBridgeBoundary =
  LegacyBridge.canonicalLegacyBridgeBoundary


------------------------------------------------------------------------
-- Electrical-engineering / Smith-chart cross-pollination.
------------------------------------------------------------------------

smithObserverCrossPollinationBoundary :
  SmithCross.JSmithArrayCrossPollinationBoundary
smithObserverCrossPollinationBoundary =
  SmithCross.canonicalJSmithArrayCrossPollinationBoundary

smithActionSeparationBoundary :
  SmithAction.SmithModularActionSeparationBoundary
smithActionSeparationBoundary =
  SmithAction.canonicalSmithModularActionSeparationBoundary


smithMobiusMatrixBridgeBoundary :
  SmithMatrix.SmithMobiusMatrixBridgeBoundary
smithMobiusMatrixBridgeBoundary =
  SmithMatrix.canonicalSmithMobiusMatrixBridgeBoundary

smithGammaIsGenuineFractionalLinearCoordinate :
  smithGammaHasExactMobiusMatrixPresentation
    canonicalCanonical369InterpretationBoundary
  ≡ true
smithGammaIsGenuineFractionalLinearCoordinate = refl

smithAdmittanceMobiusShadowIsObservedAtC6 :
  smithMobiusMatrixToC6CompilerOwned
    canonicalCanonical369InterpretationBoundary
  ≡ true
smithAdmittanceMobiusShadowIsObservedAtC6 = refl

smithAdmittanceHalfTurnCanDisappearAtC3 :
  smithMobiusMatrixC3ForgetsHalfTurn
    canonicalCanonical369InterpretationBoundary
  ≡ true
smithAdmittanceHalfTurnCanDisappearAtC3 = refl

smithHalfTurnIsNotModularT :
  smithHalfTurnDistinctFromModularTOnC6
    canonicalCanonical369InterpretationBoundary
  ≡ true
smithHalfTurnIsNotModularT = refl

smithHalfTurnIsNotModularReflection :
  smithHalfTurnDistinctFromModularReflectionOnC6
    canonicalCanonical369InterpretationBoundary
  ≡ true
smithHalfTurnIsNotModularReflection = refl

coarseC3CanHideSmithHalfTurn :
  c3QuotientCanEraseSmithHalfTurn
    canonicalCanonical369InterpretationBoundary
  ≡ true
coarseC3CanHideSmithHalfTurn = refl


coarseC3DoesNotDetermineUnderlyingC6Action :
  c3ObserverDoesNotDetermineUnderlyingC6Action
    canonicalCanonical369InterpretationBoundary
  ≡ true
coarseC3DoesNotDetermineUnderlyingC6Action = refl

engineeringJRemainsDistinctFromModularJ :
  engineeringJIdentifiedWithModularJInvariant
    canonicalCanonical369InterpretationBoundary
  ≡ false
engineeringJRemainsDistinctFromModularJ = refl

smithGammaRemainsDistinctFromModularJ :
  smithGammaIdentifiedWithModularJInvariant
    canonicalCanonical369InterpretationBoundary
  ≡ false
smithGammaRemainsDistinctFromModularJ = refl


------------------------------------------------------------------------
-- C6 / ten-state / rank-17 / weight-12 cross-pollination receipt.
------------------------------------------------------------------------

c6TenRankWeightTwelveBoundary :
  Cross.C6TenRankWeightTwelveBoundary
c6TenRankWeightTwelveBoundary =
  Cross.canonicalC6TenRankWeightTwelveBoundary

smithAndModularReflectionCommuteAtC6 :
  Cross.smithAndModularReflectionCommuteOnC6
    c6TenRankWeightTwelveBoundary
  ≡ true
smithAndModularReflectionCommuteAtC6 = refl

rank14BalancedCarryIsRetained :
  Cross.rank14BalancedCarryPaid
    c6TenRankWeightTwelveBoundary
  ≡ true
rank14BalancedCarryIsRetained = refl

weightTwelveDoesNotCollapseToStageTwelve :
  Cross.equalTwelveNumeralCreatesSemanticIdentity
    c6TenRankWeightTwelveBoundary
  ≡ false
weightTwelveDoesNotCollapseToStageTwelve = refl


------------------------------------------------------------------------
-- Neutral/oriented finite phase + eta24 cusp + relation constructor receipt.
------------------------------------------------------------------------

neutralCuspRelationBoundary :
  NeutralCusp.NeutralCuspRelationBoundary
neutralCuspRelationBoundary =
  NeutralCusp.canonicalNeutralCuspRelationBoundary

phaseFifteenReallySplitsNeutralFivePlusOrientedTen :
  NeutralCusp.phase15SplitsAsNeutral5PlusOriented10
    neutralCuspRelationBoundary
  ≡ true
phaseFifteenReallySplitsNeutralFivePlusOrientedTen = refl

eta24CuspZeroIsCompilerOwnedInLean :
  NeutralCusp.eta24CuspZeroOwnedInLean
    neutralCuspRelationBoundary
  ≡ true
eta24CuspZeroIsCompilerOwnedInLean = refl

eta24NormalizedDeltaSameObjectIsCompilerOwnedInLean :
  NeutralCusp.eta24NormalizedDeltaSameObjectOwnedInLean
    neutralCuspRelationBoundary
  ≡ true
eta24NormalizedDeltaSameObjectIsCompilerOwnedInLean = refl

finiteZeroDoesNotCollapseToCuspZero :
  NeutralCusp.finiteZeroEqualsCuspZero
    neutralCuspRelationBoundary
  ≡ false
finiteZeroDoesNotCollapseToCuspZero = refl

cuspZeroDoesNotCollapseToRelationDiagonal :
  NeutralCusp.cuspZeroEqualsRelationDiagonal
    neutralCuspRelationBoundary
  ≡ false
cuspZeroDoesNotCollapseToRelationDiagonal = refl
