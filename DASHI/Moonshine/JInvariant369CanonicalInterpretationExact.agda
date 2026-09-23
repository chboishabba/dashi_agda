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

import DASHI.Moonshine.DeltaUnitCircleReflectionPhaseExact as Phase
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as LevelTower
import DASHI.Moonshine.JInvariant369PrincipalLevelTowerExact as Principal
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as Separation
import DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact as Repair
import DASHI.Moonshine.JInvariant369SignedSSPFRACTRANPhaseFibreExact as SignedSSP

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

open Canonical369InterpretationBoundary public

canonicalCanonical369InterpretationBoundary :
  Canonical369InterpretationBoundary
canonicalCanonical369InterpretationBoundary =
  canonical-369-interpretation-boundary
    true true
    true true true true true
    false false false
    true true false false
    false true
    false false false

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
  ⊥
signedSSPCannotCollapseSpectralConjugationToLevelTranslation =
  SignedSSP.signedSpectralConjugationCannotEqualLevel3Translation
