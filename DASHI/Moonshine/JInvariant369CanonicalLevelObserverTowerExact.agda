module DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact where

------------------------------------------------------------------------
-- CANONICAL 6 -> 3 AND 27 -> 9 -> 3 MODULAR OBSERVER TOWER
--
-- This module sharpens the mathematically meaningful part of the 369 story.
--
-- Existing authority:
--   * JInvariant369ModularLevelCuspObserversExact owns the canonical cusp
--     translation fibres Z/3, Z/9, Z/27 and their covering projections;
--   * the level-6 carrier is identified with C2 x C3 by CRT;
--   * JInvariantFormulaic369FibreObserverRepairExact allows 9/27 observers to
--     depend on the same analytic point rather than hue alone.
--
-- New result:
--
--   1. C6 -> C3 is the literal quotient that forgets the C2 orientation
--      coordinate in the CRT decomposition, and it intertwines translation.
--
--   2. A single genuine level-27 lift at each analytic point canonically
--      determines the level-9 and level-3 observers by the covering maps
--
--           Z/27 -> Z/9 -> Z/3.
--
--      Therefore 9 and 27 are theorem-bearing modular-level observations only
--      when such a level lift is supplied.  They are not inferred from colour
--      sector counts.
--
--   3. The resulting same-point 9/27 renderer observers satisfy the covering
--      compatibility by construction.  Agreement with legacy phase-only bins
--      remains a separate calibration witness.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Product using (proj₂)

import Base369 as Base
import DASHI.Biology.EisensteinNineRingInterferenceExact as EisensteinPhase
import DASHI.Biology.TriadicKernelLiftQuotientExact as Kernel
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact as Repair
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Balanced
import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3

------------------------------------------------------------------------
-- 1. The canonical 6 -> 3 quotient is orientation-forgetting.
------------------------------------------------------------------------

level6To3 :
  Base.HexTruth → Level.level3CuspFibre
level6To3 x =
  proj₂ (Level.hexToCRT6 x)

level6To3IsOrientationQuotient :
  (x : Base.HexTruth) →
  level6To3 x
  ≡
  proj₂ (Level.hexToCRT6 x)
level6To3IsOrientationQuotient x = refl

level6To3TranslationCommutes :
  (x : Base.HexTruth) →
  level6To3 (Level.translate6 x)
  ≡
  Level.translateTriadic Q.one (level6To3 x)
level6To3TranslationCommutes x =
  cong proj₂ (Level.level6TranslationIsCRT x)

------------------------------------------------------------------------
-- 2. The quotient genuinely leaves a C3 action, not merely three labels.
------------------------------------------------------------------------

translateLevel3Residue :
  Level.level3CuspFibre →
  Level.level3CuspFibre
translateLevel3Residue =
  Level.translateTriadic Q.one

translateLevel3ThreeTimes :
  (x : Level.level3CuspFibre) →
  translateLevel3Residue
    (translateLevel3Residue
      (translateLevel3Residue x))
  ≡ x
translateLevel3ThreeTimes (Balanced.neg ∷ []) = refl
translateLevel3ThreeTimes (Balanced.zer ∷ []) = refl
translateLevel3ThreeTimes (Balanced.pos ∷ []) = refl

level3CyclicAction :
  C3.OrderThreeAction Level.level3CuspFibre
level3CyclicAction =
  record
    { C3.rotate = translateLevel3Residue
    ; C3.rotateCubed = translateLevel3ThreeTimes
    }

level6To3GeneratorIntertwines :
  (x : Base.HexTruth) →
  level6To3 (Level.translate6 x)
  ≡
  C3.rotate level3CyclicAction (level6To3 x)
level6To3GeneratorIntertwines =
  level6To3TranslationCommutes

level6To3ReflectionCommutes :
  (x : Base.HexTruth) →
  level6To3 (Level.reflect6 x)
  ≡
  Arithmetic.negateResidue (level6To3 x)
level6To3ReflectionCommutes Base.hex-0 = refl
level6To3ReflectionCommutes Base.hex-1 = refl
level6To3ReflectionCommutes Base.hex-2 = refl
level6To3ReflectionCommutes Base.hex-3 = refl
level6To3ReflectionCommutes Base.hex-4 = refl
level6To3ReflectionCommutes Base.hex-5 = refl

------------------------------------------------------------------------
-- 3. Orientation fibres of C6 -> C3.
--
-- The quotient has exactly the two CRT orientation representatives over each
-- level-3 residue.  We expose them constructively rather than asserting a
-- cardinality division.
------------------------------------------------------------------------

positiveLift6 :
  Level.level3CuspFibre →
  Base.HexTruth
positiveLift6 residue =
  Level.crt6ToHex (EisensteinPhase.positive , residue)

negativeLift6 :
  Level.level3CuspFibre →
  Base.HexTruth
negativeLift6 residue =
  Level.crt6ToHex (EisensteinPhase.negative , residue)

positiveLiftProjects :
  (residue : Level.level3CuspFibre) →
  level6To3 (positiveLift6 residue) ≡ residue
positiveLiftProjects residue =
  cong proj₂ (Level.crt6HexRoundTrip (EisensteinPhase.positive , residue))

negativeLiftProjects :
  (residue : Level.level3CuspFibre) →
  level6To3 (negativeLift6 residue) ≡ residue
negativeLiftProjects residue =
  cong proj₂ (Level.crt6HexRoundTrip (EisensteinPhase.negative , residue))

positiveNegativeLiftsAreOrientationPair :
  (residue : Level.level3CuspFibre) →
  Level.hexToCRT6 (positiveLift6 residue)
  ≡
  EisensteinPhase.positive , residue
  ×
  Level.hexToCRT6 (negativeLift6 residue)
  ≡
  EisensteinPhase.negative , residue
positiveNegativeLiftsAreOrientationPair residue =
  Level.crt6HexRoundTrip (EisensteinPhase.positive , residue)
  ,
  Level.crt6HexRoundTrip (EisensteinPhase.negative , residue)

------------------------------------------------------------------------
-- 4. One genuine level-27 lift determines the entire triadic level tower.
------------------------------------------------------------------------

record CanonicalLevel27Lift
    (R : Render.JPhaseRenderingAlgebra) : Set₁ where
  constructor canonical-level27-lift
  field
    level27At :
      Klein.Point (Render.klein R) →
      Level.level27CuspFibre

open CanonicalLevel27Lift public

canonicalLevel9At :
  ∀ {R} →
  CanonicalLevel27Lift R →
  Klein.Point (Render.klein R) →
  Level.level9CuspFibre
canonicalLevel9At L z =
  Level.level27To9CoveringProjection (level27At L z)

canonicalLevel3At :
  ∀ {R} →
  CanonicalLevel27Lift R →
  Klein.Point (Render.klein R) →
  Level.level3CuspFibre
canonicalLevel3At L z =
  Level.level9To3CoveringProjection
    (canonicalLevel9At L z)

canonicalObserver27At :
  ∀ {R} →
  CanonicalLevel27Lift R →
  Klein.Point (Render.klein R) →
  Fabric.Ternary27Point
canonicalObserver27At L z =
  Level.level27ToObserver27 (level27At L z)

canonicalObserver9At :
  ∀ {R} →
  CanonicalLevel27Lift R →
  Klein.Point (Render.klein R) →
  Kernel.NineSheet
canonicalObserver9At L z =
  Level.level9ToObserver9 (canonicalLevel9At L z)

canonicalObserver3At :
  ∀ {R} →
  CanonicalLevel27Lift R →
  Klein.Point (Render.klein R) →
  Kernel.KernelTrit
canonicalObserver3At L z =
  Level.level3ToObserver3 (canonicalLevel3At L z)

------------------------------------------------------------------------
-- 5. The 27 -> 9 -> 3 covering equations now hold at every analytic point.
------------------------------------------------------------------------

canonical27To9Commutes :
  ∀ {R}
    (L : CanonicalLevel27Lift R)
    (z : Klein.Point (Render.klein R)) →
  Level.observer27ToObserver9ViaLevel
    (canonicalObserver27At L z)
  ≡
  canonicalObserver9At L z
canonical27To9Commutes L z =
  cong Level.level9ToObserver9
    (cong Level.level27To9CoveringProjection
      (Level.level27ObserverRoundTrip (level27At L z)))

canonical9To3Commutes :
  ∀ {R}
    (L : CanonicalLevel27Lift R)
    (z : Klein.Point (Render.klein R)) →
  Level.observer9ToObserver3ViaLevel
    (canonicalObserver9At L z)
  ≡
  canonicalObserver3At L z
canonical9To3Commutes L z =
  cong Level.level3ToObserver3
    (cong Level.level9To3CoveringProjection
      (Level.level9ObserverRoundTrip (canonicalLevel9At L z)))

------------------------------------------------------------------------
-- 6. Same-point renderer repair instantiated canonically from the level lift.
------------------------------------------------------------------------

canonicalSamePointFibreObservers :
  ∀ {R} →
  CanonicalLevel27Lift R →
  Repair.SamePointFibreObservers R
canonicalSamePointFibreObservers L =
  Repair.same-point-fibre-observers
    (canonicalObserver9At L)
    (canonicalObserver27At L)

canonicalFibreSample :
  ∀ {R} →
  (L : CanonicalLevel27Lift R) →
  (z : Klein.Point (Render.klein R)) →
  Repair.J369FibreRenderSample
    R
    (canonicalSamePointFibreObservers L)
canonicalFibreSample {R} L z =
  Repair.renderFibreAt
    R
    (canonicalSamePointFibreObservers L)
    z

canonicalFibre27To9Commutes :
  ∀ {R}
    (L : CanonicalLevel27Lift R)
    (z : Klein.Point (Render.klein R)) →
  Level.observer27ToObserver9ViaLevel
    (Repair.fibreObserver27 (canonicalFibreSample L z))
  ≡
  Repair.fibreObserver9 (canonicalFibreSample L z)
canonicalFibre27To9Commutes L z =
  canonical27To9Commutes L z

------------------------------------------------------------------------
-- 7. Optional compatibility with the renderer's phase-only C3 observer.
--
-- j itself forgets the level coordinate, so this agreement is NOT automatic.
-- It is exactly the calibration needed before calling the old hue-derived
-- phase3 output the same observer as the level-3 cusp coordinate.
------------------------------------------------------------------------

record CanonicalLevelPhase3Calibration
    (R : Render.JPhaseRenderingAlgebra)
    (L : CanonicalLevel27Lift R) : Set₁ where
  field
    phase3Agrees :
      (z : Klein.Point (Render.klein R)) →
      Render.phase3 R (Render.jPhase R z)
      ≡
      canonicalObserver3At L z

open CanonicalLevelPhase3Calibration public

------------------------------------------------------------------------
-- 8. Translation-equivariant level lift.
--
-- The base j-value is invariant under T; the level fibre moves.  We therefore
-- formulate equivariance on the lifted coordinate, not as a rotation of jPhase.
------------------------------------------------------------------------

record Level27TranslationLift
    (R : Render.JPhaseRenderingAlgebra)
    (L : CanonicalLevel27Lift R) : Set₁ where
  field
    translatePoint :
      Klein.Point (Render.klein R) →
      Klein.Point (Render.klein R)

    level27Translation :
      (z : Klein.Point (Render.klein R)) →
      level27At L (translatePoint z)
      ≡
      Level.translateTriadic Q.three (level27At L z)

open Level27TranslationLift public

level9TranslationDerived :
  ∀ {R}
    {L : CanonicalLevel27Lift R} →
  (T : Level27TranslationLift R L) →
  (z : Klein.Point (Render.klein R)) →
  canonicalLevel9At L (translatePoint T z)
  ≡
  Level.translateTriadic Q.two (canonicalLevel9At L z)
level9TranslationDerived T z =
  trans
    (cong Level.level27To9CoveringProjection
      (level27Translation T z))
    (Level.level27To9TranslationEquivariant (level27At _ z))

level3TranslationDerived :
  ∀ {R}
    {L : CanonicalLevel27Lift R} →
  (T : Level27TranslationLift R L) →
  (z : Klein.Point (Render.klein R)) →
  canonicalLevel3At L (translatePoint T z)
  ≡
  Level.translateTriadic Q.one (canonicalLevel3At L z)
level3TranslationDerived T z =
  trans
    (cong Level.level9To3CoveringProjection
      (level9TranslationDerived T z))
    (Level.level9To3TranslationEquivariant (canonicalLevel9At _ z))

observer27TranslationCommutes :
  ∀ {R}
    {L : CanonicalLevel27Lift R} →
  (T : Level27TranslationLift R L) →
  (z : Klein.Point (Render.klein R)) →
  canonicalObserver27At L (translatePoint T z)
  ≡
  Level.translateObserver27 (canonicalObserver27At L z)
observer27TranslationCommutes T z =
  trans
    (cong Level.level27ToObserver27
      (level27Translation T z))
    (sym
      (cong Level.level27ToObserver27
        (cong (Level.translateTriadic Q.three)
          (Level.level27ObserverRoundTrip (level27At _ z)))))

observer9TranslationCommutes :
  ∀ {R}
    {L : CanonicalLevel27Lift R} →
  (T : Level27TranslationLift R L) →
  (z : Klein.Point (Render.klein R)) →
  canonicalObserver9At L (translatePoint T z)
  ≡
  Level.translateObserver9 (canonicalObserver9At L z)
observer9TranslationCommutes T z =
  trans
    (cong Level.level9ToObserver9
      (level9TranslationDerived T z))
    (sym
      (cong Level.level9ToObserver9
        (cong (Level.translateTriadic Q.two)
          (Level.level9ObserverRoundTrip (canonicalLevel9At _ z)))))

------------------------------------------------------------------------
-- 9. Reflection-equivariant level lift.
--
-- Reflection on the modular cusp coordinate is additive inversion.  One
-- level-27 reflection law therefore forces compatible laws at levels 9 and 3.
------------------------------------------------------------------------

reduceNegate :
  ∀ {depth}
    (x : Q.Residue3Pow (suc depth)) →
  Q.reduce (Arithmetic.negateResidue x)
  ≡
  Arithmetic.negateResidue (Q.reduce x)
reduceNegate {zero} (digit Balanced.∷ []) = refl
reduceNegate {suc depth} (digit Balanced.∷ rest)
  rewrite reduceNegate rest = refl

record Level27ReflectionLift
    (R : Render.JPhaseRenderingAlgebra)
    (L : CanonicalLevel27Lift R) : Set₁ where
  field
    reflectPoint :
      Klein.Point (Render.klein R) →
      Klein.Point (Render.klein R)

    level27Reflection :
      (z : Klein.Point (Render.klein R)) →
      level27At L (reflectPoint z)
      ≡
      Arithmetic.negateResidue (level27At L z)

open Level27ReflectionLift public

level9ReflectionDerived :
  ∀ {R}
    {L : CanonicalLevel27Lift R} →
  (S : Level27ReflectionLift R L) →
  (z : Klein.Point (Render.klein R)) →
  canonicalLevel9At L (reflectPoint S z)
  ≡
  Arithmetic.negateResidue (canonicalLevel9At L z)
level9ReflectionDerived S z =
  trans
    (cong Level.level27To9CoveringProjection
      (level27Reflection S z))
    (reduceNegate (level27At _ z))

level3ReflectionDerived :
  ∀ {R}
    {L : CanonicalLevel27Lift R} →
  (S : Level27ReflectionLift R L) →
  (z : Klein.Point (Render.klein R)) →
  canonicalLevel3At L (reflectPoint S z)
  ≡
  Arithmetic.negateResidue (canonicalLevel3At L z)
level3ReflectionDerived S z =
  trans
    (cong Level.level9To3CoveringProjection
      (level9ReflectionDerived S z))
    (reduceNegate (canonicalLevel9At _ z))

canonicalObserver27ReflectionCommutes :
  ∀ {R}
    {L : CanonicalLevel27Lift R} →
  (S : Level27ReflectionLift R L) →
  (z : Klein.Point (Render.klein R)) →
  canonicalObserver27At L (reflectPoint S z)
  ≡
  Level.reflectObserver27 (canonicalObserver27At L z)
canonicalObserver27ReflectionCommutes S z =
  trans
    (cong Level.level27ToObserver27
      (level27Reflection S z))
    (trans
      (cong Level.level27ToObserver27
        (sym
          (Level.observer27ReflectionIsCuspInversion
            (canonicalObserver27At _ z))))
      (Level.observer27LevelRoundTrip
        (Level.reflectObserver27 (canonicalObserver27At _ z))))

canonicalObserver9ReflectionCommutes :
  ∀ {R}
    {L : CanonicalLevel27Lift R} →
  (S : Level27ReflectionLift R L) →
  (z : Klein.Point (Render.klein R)) →
  canonicalObserver9At L (reflectPoint S z)
  ≡
  Kernel.negateNine (canonicalObserver9At L z)
canonicalObserver9ReflectionCommutes S z =
  trans
    (cong Level.level9ToObserver9
      (level9ReflectionDerived S z))
    (trans
      (cong Level.level9ToObserver9
        (sym
          (Level.observer9ReflectionIsCuspInversion
            (canonicalObserver9At _ z))))
      (Level.observer9LevelRoundTrip
        (Kernel.negateNine (canonicalObserver9At _ z))))

canonicalObserver3ReflectionCommutes :
  ∀ {R}
    {L : CanonicalLevel27Lift R} →
  (S : Level27ReflectionLift R L) →
  (z : Klein.Point (Render.klein R)) →
  canonicalObserver3At L (reflectPoint S z)
  ≡
  Kernel.negateTrit (canonicalObserver3At L z)
canonicalObserver3ReflectionCommutes S z =
  trans
    (cong Level.level3ToObserver3
      (level3ReflectionDerived S z))
    (trans
      (cong Level.level3ToObserver3
        (sym
          (Level.observer3ReflectionIsCuspInversion
            (canonicalObserver3At _ z))))
      (Level.observer3LevelRoundTrip
        (Kernel.negateTrit (canonicalObserver3At _ z))))

------------------------------------------------------------------------
-- 9. Boundary.
------------------------------------------------------------------------

record Canonical369LevelObserverBoundary : Set where
  constructor canonical-369-level-observer-boundary
  field
    c6ToC3IsOrientationForgettingQuotient : Bool
    c6ToC3TranslationEquivariant : Bool
    c3ActionOrderThree : Bool
    c6FibresExposeTwoOrientations : Bool

    oneLevel27LiftDeterminesLevel9AndLevel3 : Bool
    level27To9ObserverCoveringCommutesPointwise : Bool
    level9To3ObserverCoveringCommutesPointwise : Bool
    canonicalSamePointNineTwentySevenObserversConstructed : Bool

    translationAt27ImpliesTranslationAt9And3 : Bool
    observer27TranslationEquivarianceDerived : Bool
    observer9TranslationEquivarianceDerived : Bool
    level3GenericOrderThreeActionOwned : Bool
    c6ToC3GeneratorIntertwinerOwned : Bool
    c6ToC3ReflectionIntertwinerOwned : Bool

    level27ReflectionImpliesLevel9And3 : Bool
    observer27ReflectionEquivarianceDerived : Bool
    observer9ReflectionEquivarianceDerived : Bool
    observer3ReflectionEquivarianceDerived : Bool

    legacyPhase3AgreementAutomatic : Bool
    fullModularCurveDeckGroupClaimedCyclic : Bool
    c27ClaimedEqualToC3CubedAsGroup : Bool

open Canonical369LevelObserverBoundary public

canonicalCanonical369LevelObserverBoundary :
  Canonical369LevelObserverBoundary
canonicalCanonical369LevelObserverBoundary =
  canonical-369-level-observer-boundary
    true true true true
    true true true true
    true true true
    true true true
    true true true true
    false false false
