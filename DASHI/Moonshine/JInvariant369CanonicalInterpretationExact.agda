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
import DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact as Repair
import DASHI.Moonshine.JInvariant369SignedSSPFRACTRANPhaseFibreExact as SignedSSP
import DASHI.Moonshine.JInvariant369JointPhaseLevelBundleExact as JointBundle
import DASHI.Moonshine.JSameWeightQuotientReflectionExact as JReflection
import DASHI.Moonshine.JInvariant369SSPLevelDihedralIntertwinerExact as SSPLevel
import DASHI.Moonshine.JInvariant369JointFibredObserverExact as JointFibred
import DASHI.Moonshine.JInvariant369JointBundleLegacyFibreBridgeExact as LegacyBridge
import DASHI.Moonshine.JInvariant369JointFibreBifiltrationExact as JointBif

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
    concreteJRealAxisInterpretationTransported : Bool

    sspC3CycleIntertwinesLevelTranslation : Bool
    sspC2AntipodeIntertwinesLevelInversion : Bool
    sspLevel3FiniteDihedralEquivalenceOwned : Bool
    signedMagnitudeFactorsThroughLevel3 : Bool

    jointPhaseLevelSignedFibreConstructed : Bool
    jointFiniteDihedralLawOwned : Bool
    level27FactorsThroughBaseJSurface : Bool

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
    ; concreteJRealAxisInterpretationTransported = false

    ; sspC3CycleIntertwinesLevelTranslation = true
    ; sspC2AntipodeIntertwinesLevelInversion = true
    ; sspLevel3FiniteDihedralEquivalenceOwned = true
    ; signedMagnitudeFactorsThroughLevel3 = true

    ; jointPhaseLevelSignedFibreConstructed = true
    ; jointFiniteDihedralLawOwned = true
    ; level27FactorsThroughBaseJSurface = false

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
    }

------------------------------------------------------------------------
-- Query-stable architecture receipts.
------------------------------------------------------------------------

phaseOnlyC3IsNotPrincipalLevel3 :
  phaseOnlyC3EqualsNontrivialLevel3
    canonicalCanonical369InterpretationBoundary
  ≡ false
phaseOnlyC3IsNotPrincipalLevel3 = refl

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
