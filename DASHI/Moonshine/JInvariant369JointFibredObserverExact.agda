module DASHI.Moonshine.JInvariant369JointFibredObserverExact where

------------------------------------------------------------------------
-- JOINT FINITE FIBRE FOR THE CANONICAL 369 INTERPRETATION
--
-- This module makes the post-no-go architecture first-class:
--
--   * phase/reflection coordinate: C6
--   * principal-level coordinate: C27, reducing canonically to C9 and C3
--   * signed SSP/FRACTRAN coordinate: full signed multiplicity
--
-- Translation and reflection act differently on these coordinates.
--
-- T leaves the phase/SSP coordinates fixed and translates only the level
-- fibre.  R reflects C6, inverts the level fibre, and negates signed SSP.
--
-- The resulting fibre therefore records two distinct kinds of information
-- forgotten by a base j-value: phase/reflection information and level-lift
-- information.  Signed FRACTRAN magnitude is a further residual above its
-- coarse ternary/spectral observer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Canonical
import DASHI.Moonshine.JInvariant369SSPLevelDihedralIntertwinerExact as SSPLevel
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as Separation
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- 1. The finite joint fibre.
------------------------------------------------------------------------

record Joint369FiniteFibre : Set where
  constructor joint369FiniteFibre
  field
    phase6Coordinate :
      Base.HexTruth
    level27Coordinate :
      Level.level27CuspFibre
    signedSSPCoordinate :
      Signed.SignedMultiplicity

open Joint369FiniteFibre public

jointLevel9 :
  Joint369FiniteFibre →
  Level.level9CuspFibre
jointLevel9 fibre =
  Level.level27To9CoveringProjection
    (level27Coordinate fibre)

jointLevel3 :
  Joint369FiniteFibre →
  Level.level3CuspFibre
jointLevel3 fibre =
  Level.level9To3CoveringProjection
    (jointLevel9 fibre)

jointSignedLevel3 :
  Joint369FiniteFibre →
  Level.level3CuspFibre
jointSignedLevel3 fibre =
  SSPLevel.signedMultiplicityLevel3Observer
    (signedSSPCoordinate fibre)

------------------------------------------------------------------------
-- 2. Translation and reflection.
------------------------------------------------------------------------

translateJoint :
  Joint369FiniteFibre →
  Joint369FiniteFibre
translateJoint fibre =
  joint369FiniteFibre
    (phase6Coordinate fibre)
    (Level.translateTriadic Q.three
      (level27Coordinate fibre))
    (signedSSPCoordinate fibre)

translateJointInverse :
  Joint369FiniteFibre →
  Joint369FiniteFibre
translateJointInverse fibre =
  joint369FiniteFibre
    (phase6Coordinate fibre)
    (Arithmetic.addResidue
      (Arithmetic.negateResidue (Level.oneResidue Q.three))
      (level27Coordinate fibre))
    (signedSSPCoordinate fibre)

reflectJoint :
  Joint369FiniteFibre →
  Joint369FiniteFibre
reflectJoint fibre =
  joint369FiniteFibre
    (Level.reflect6 (phase6Coordinate fibre))
    (Arithmetic.negateResidue
      (level27Coordinate fibre))
    (Signed.negateMultiplicity
      (signedSSPCoordinate fibre))

------------------------------------------------------------------------
-- 3. Coordinatewise dihedral law.
------------------------------------------------------------------------

jointPhaseRTR :
  (fibre : Joint369FiniteFibre) →
  phase6Coordinate
    (reflectJoint (translateJoint (reflectJoint fibre)))
  ≡
  phase6Coordinate (translateJointInverse fibre)
jointPhaseRTR fibre =
  Level.reflect6Involutive (phase6Coordinate fibre)

jointLevel27RTR :
  (fibre : Joint369FiniteFibre) →
  level27Coordinate
    (reflectJoint (translateJoint (reflectJoint fibre)))
  ≡
  level27Coordinate (translateJointInverse fibre)
jointLevel27RTR fibre =
  Level.inversionConjugatesTranslationToInverse
    Level.canonicalCuspDihedralAt27
    (level27Coordinate fibre)

jointSignedSSPRTR :
  (fibre : Joint369FiniteFibre) →
  signedSSPCoordinate
    (reflectJoint (translateJoint (reflectJoint fibre)))
  ≡
  signedSSPCoordinate (translateJointInverse fibre)
jointSignedSSPRTR
  (joint369FiniteFibre phase level (Signed.negativeMultiplicity n)) = refl
jointSignedSSPRTR
  (joint369FiniteFibre phase level Signed.zeroMultiplicity) = refl
jointSignedSSPRTR
  (joint369FiniteFibre phase level (Signed.positiveMultiplicity n)) = refl

record Joint369DihedralLaw : Set where
  constructor joint369-dihedral-law
  field
    phaseRTR :
      (fibre : Joint369FiniteFibre) →
      phase6Coordinate
        (reflectJoint (translateJoint (reflectJoint fibre)))
      ≡
      phase6Coordinate (translateJointInverse fibre)

    levelRTR :
      (fibre : Joint369FiniteFibre) →
      level27Coordinate
        (reflectJoint (translateJoint (reflectJoint fibre)))
      ≡
      level27Coordinate (translateJointInverse fibre)

    signedRTR :
      (fibre : Joint369FiniteFibre) →
      signedSSPCoordinate
        (reflectJoint (translateJoint (reflectJoint fibre)))
      ≡
      signedSSPCoordinate (translateJointInverse fibre)

open Joint369DihedralLaw public

canonicalJoint369DihedralLaw :
  Joint369DihedralLaw
canonicalJoint369DihedralLaw =
  joint369-dihedral-law
    jointPhaseRTR
    jointLevel27RTR
    jointSignedSSPRTR

------------------------------------------------------------------------
-- 4. A joint lift over the renderer's base point / j-value.
------------------------------------------------------------------------

record Joint369Lift
    (R : Render.JPhaseRenderingAlgebra) : Set where
  constructor joint369Lift
  field
    basePoint :
      Klein.Point (Render.klein R)
    fibre :
      Joint369FiniteFibre

open Joint369Lift public

forgetJointFibre :
  ∀ {R} →
  Joint369Lift R →
  Klein.Point (Render.klein R)
forgetJointFibre = basePoint

jointJValue :
  ∀ {R} →
  Joint369Lift R →
  Klein.Value (Render.klein R)
jointJValue {R} state =
  Render.jValue R (basePoint state)

translateJointLift :
  ∀ {R} →
  Joint369Lift R →
  Joint369Lift R
translateJointLift state =
  joint369Lift
    (basePoint state)
    (translateJoint (fibre state))

translationIsInvisibleToBase :
  ∀ {R} (state : Joint369Lift R) →
  forgetJointFibre (translateJointLift state)
  ≡
  forgetJointFibre state
translationIsInvisibleToBase state = refl

translationIsInvisibleToJValue :
  ∀ {R} (state : Joint369Lift R) →
  jointJValue (translateJointLift state)
  ≡
  jointJValue state
translationIsInvisibleToJValue state = refl

------------------------------------------------------------------------
-- 5. The level lift provably does not factor through the base projection.
--
-- This is an abstract same-base-point witness for every supplied base point:
-- translating the level fibre leaves the base/j surface unchanged while the
-- level coordinate changes.
------------------------------------------------------------------------

baseObserver :
  ∀ {R} →
  Joint369Lift R →
  Klein.Point (Render.klein R)
baseObserver = basePoint

level27Consumer :
  ∀ {R} →
  Joint369Lift R →
  Level.level27CuspFibre
level27Consumer state =
  level27Coordinate (fibre state)

translatedLevelDiffers :
  (level : Level.level27CuspFibre) →
  Level.translateTriadic Q.three level
  ≡ level →
  ⊥
translatedLevelDiffers =
  Separation.level27TranslationNoFixedPoint

jointBaseLevelNonDescent :
  ∀ {R}
    (z : Klein.Point (Render.klein R))
    (phase : Base.HexTruth)
    (level : Level.level27CuspFibre)
    (signed : Signed.SignedMultiplicity) →
  Descent.ConsumerNonDescentWitness
    (baseObserver {R})
    (level27Consumer {R})
jointBaseLevelNonDescent z phase level signed =
  Descent.consumerNonDescentWitness
    (joint369Lift z (joint369FiniteFibre phase level signed))
    (joint369Lift z
      (joint369FiniteFibre
        phase
        (Level.translateTriadic Q.three level)
        signed))
    refl
    (λ alleged →
      translatedLevelDiffers level (sym alleged))

level27CannotFactorThroughBase :
  ∀ {R}
    (z : Klein.Point (Render.klein R))
    (phase : Base.HexTruth)
    (level : Level.level27CuspFibre)
    (signed : Signed.SignedMultiplicity) →
  Descent.FactorsThrough
    (baseObserver {R})
    (level27Consumer {R}) →
  ⊥
level27CannotFactorThroughBase z phase level signed =
  Descent.nonDescentWitnessBlocksFactorization
    (jointBaseLevelNonDescent z phase level signed)

------------------------------------------------------------------------
-- 6. Exact claim boundary.
------------------------------------------------------------------------

record Joint369FibredObserverBoundary : Set where
  constructor joint369-fibred-observer-boundary
  field
    phase6AndLevel27AndSignedSSPJointStateConstructed : Bool
    level9AndLevel3DerivedFromLevel27 : Bool
    translationActsOnlyOnLevelFibre : Bool
    reflectionActsOnPhaseLevelAndSignedSSP : Bool
    jointFiniteDihedralLawPaid : Bool

    translationInvisibleToBaseJSurface : Bool
    level27FactorsThroughBaseJSurface : Bool

    phase6IsConcreteAnalyticDeltaPhaseHere : Bool
    reflectionActionOnAnalyticBasePointConstructedHere : Bool
    signedMagnitudeCollapsedToLevel3 : Bool
    fullDeckGroupEqualsJointFiniteDihedralAction : Bool

open Joint369FibredObserverBoundary public

canonicalJoint369FibredObserverBoundary :
  Joint369FibredObserverBoundary
canonicalJoint369FibredObserverBoundary =
  joint369-fibred-observer-boundary
    true true true true true
    true false
    false false false false
