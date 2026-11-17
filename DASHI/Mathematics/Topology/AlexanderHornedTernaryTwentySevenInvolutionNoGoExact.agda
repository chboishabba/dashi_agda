module DASHI.Mathematics.Topology.AlexanderHornedTernaryTwentySevenInvolutionNoGoExact where

------------------------------------------------------------------------
-- BOTH T^3 AND C3_sector × T^2 HAVE 27 STATES, BUT THEIR INVOLUTIONS
-- ARE NOT EQUIVARIANTLY BIJECTIVE.
--
-- A: reflect the three signed ternary coordinates simultaneously;
-- B: preserve the C3 sector but reflect the two internal ternary
-- digits. On A, EXACTLY ONE address is fixed. On B, THREE are fixed.
--
-- This is a CONSTRUCTIVE NO-INJECTION theorem: no injective map
-- intertwines B with A, since it would take TWO distinct B-fixed
-- points to A's UNIQUE fixed point.
--
-- 13/27 + central singleton yields 14 antipodal orbits on A.
-- 12 pairs + 3 fixed sectors yields 15 on B.
-- The source formal proof needs neither cardinality axioms nor a
-- conjectured Monster representation; it is an actual obstruction.
--
-- Owners: existing C3/trit/native 27 address levels, #1407 orbit
-- numerical background, #1244 Alexander-Hatcher binary geometry.
-- Source-written / Agda kernel pending, no protected ESD edits.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End

Address27 : Set
Address27 = End.BalancedLevel 2

-- Use c1 as the reflection-fixed *central* external sector.
-- This is an involution on the 27 carrier, not sector C3 rotation.
reflectSector : C3.C3 → C3.C3
reflectSector C3.c0 = C3.c2
reflectSector C3.c1 = C3.c1
reflectSector C3.c2 = C3.c0

reflectSectorTwice : (c : C3.C3) →
  reflectSector (reflectSector c) ≡ c
reflectSectorTwice C3.c0 = refl
reflectSectorTwice C3.c1 = refl
reflectSectorTwice C3.c2 = refl

-- Both actions use the SAME 27 address carrier, differing ONLY in
-- whether sign reversal touches the external sector coordinate.
reflectAllThreeCoordinates : Address27 → Address27
reflectAllThreeCoordinates (c , x ∷ y ∷ []) =
  reflectSector c , Trit.negate x ∷ Trit.negate y ∷ []

reflectOnlyInternalCoordinates : Address27 → Address27
reflectOnlyInternalCoordinates (c , x ∷ y ∷ []) =
  c , Trit.negate x ∷ Trit.negate y ∷ []

-- The all-coordinate sign map has exactly ONE fixed state:
-- (centre sector, neutral trit, neutral trit).
globalFixed : Address27
globalFixed = C3.c1 , Trit.zero ∷ Trit.zero ∷ []

globalFixedReallyFixed :
  reflectAllThreeCoordinates globalFixed ≡ globalFixed
globalFixedReallyFixed = refl

uniqueGlobalFixedPoint :
  (x : Address27) →
  reflectAllThreeCoordinates x ≡ x → x ≡ globalFixed
uniqueGlobalFixedPoint (C3.c0 , Trit.neg ∷ Trit.neg ∷ []) ()
uniqueGlobalFixedPoint (C3.c0 , Trit.neg ∷ Trit.zero ∷ []) ()
uniqueGlobalFixedPoint (C3.c0 , Trit.neg ∷ Trit.pos ∷ []) ()
uniqueGlobalFixedPoint (C3.c0 , Trit.zero ∷ Trit.neg ∷ []) ()
uniqueGlobalFixedPoint (C3.c0 , Trit.zero ∷ Trit.zero ∷ []) ()
uniqueGlobalFixedPoint (C3.c0 , Trit.zero ∷ Trit.pos ∷ []) ()
uniqueGlobalFixedPoint (C3.c0 , Trit.pos ∷ Trit.neg ∷ []) ()
uniqueGlobalFixedPoint (C3.c0 , Trit.pos ∷ Trit.zero ∷ []) ()
uniqueGlobalFixedPoint (C3.c0 , Trit.pos ∷ Trit.pos ∷ []) ()
uniqueGlobalFixedPoint (C3.c1 , Trit.neg ∷ Trit.neg ∷ []) ()
uniqueGlobalFixedPoint (C3.c1 , Trit.neg ∷ Trit.zero ∷ []) ()
uniqueGlobalFixedPoint (C3.c1 , Trit.neg ∷ Trit.pos ∷ []) ()
uniqueGlobalFixedPoint (C3.c1 , Trit.zero ∷ Trit.neg ∷ []) ()
uniqueGlobalFixedPoint (C3.c1 , Trit.zero ∷ Trit.zero ∷ []) proof = refl
uniqueGlobalFixedPoint (C3.c1 , Trit.zero ∷ Trit.pos ∷ []) ()
uniqueGlobalFixedPoint (C3.c1 , Trit.pos ∷ Trit.neg ∷ []) ()
uniqueGlobalFixedPoint (C3.c1 , Trit.pos ∷ Trit.zero ∷ []) ()
uniqueGlobalFixedPoint (C3.c1 , Trit.pos ∷ Trit.pos ∷ []) ()
uniqueGlobalFixedPoint (C3.c2 , Trit.neg ∷ Trit.neg ∷ []) ()
uniqueGlobalFixedPoint (C3.c2 , Trit.neg ∷ Trit.zero ∷ []) ()
uniqueGlobalFixedPoint (C3.c2 , Trit.neg ∷ Trit.pos ∷ []) ()
uniqueGlobalFixedPoint (C3.c2 , Trit.zero ∷ Trit.neg ∷ []) ()
uniqueGlobalFixedPoint (C3.c2 , Trit.zero ∷ Trit.zero ∷ []) ()
uniqueGlobalFixedPoint (C3.c2 , Trit.zero ∷ Trit.pos ∷ []) ()
uniqueGlobalFixedPoint (C3.c2 , Trit.pos ∷ Trit.neg ∷ []) ()
uniqueGlobalFixedPoint (C3.c2 , Trit.pos ∷ Trit.zero ∷ []) ()
uniqueGlobalFixedPoint (C3.c2 , Trit.pos ∷ Trit.pos ∷ []) ()

-- In contrast the internal-only involution has three fixed addresses,
-- one in each sector. Two are enough for the no-injection proof.
firstInternalFixed secondInternalFixed : Address27
firstInternalFixed = C3.c0 , Trit.zero ∷ Trit.zero ∷ []
secondInternalFixed = C3.c1 , Trit.zero ∷ Trit.zero ∷ []

firstInternalReallyFixed :
  reflectOnlyInternalCoordinates firstInternalFixed ≡ firstInternalFixed
firstInternalReallyFixed = refl

secondInternalReallyFixed :
  reflectOnlyInternalCoordinates secondInternalFixed ≡ secondInternalFixed
secondInternalReallyFixed = refl

internalFixedPointsAreDifferent :
  firstInternalFixed ≡ secondInternalFixed → ⊥
internalFixedPointsAreDifferent ()

-- Any equivariant injection maps fixed points to fixed points, but
-- the target has only the unique globalFixed; contradiction.
noEquivariantInjectionFromInternalToAll :
  (f : Address27 → Address27) →
  ((x : Address27) →
    f (reflectOnlyInternalCoordinates x)
    ≡ reflectAllThreeCoordinates (f x)) →
  ((x y : Address27) → f x ≡ f y → x ≡ y) → ⊥
noEquivariantInjectionFromInternalToAll f equiv injective =
  internalFixedPointsAreDifferent
    (injective firstInternalFixed secondInternalFixed equalImages)
  where
    fixedImageIsGlobal : (x : Address27) →
      reflectOnlyInternalCoordinates x ≡ x →
      f x ≡ globalFixed
    fixedImageIsGlobal x fixedHere =
      uniqueGlobalFixedPoint (f x)
        (trans (sym (equiv x)) (cong f fixedHere))

    equalImages : f firstInternalFixed ≡ f secondInternalFixed
    equalImages =
      trans
        (fixedImageIsGlobal firstInternalFixed firstInternalReallyFixed)
        (sym
          (fixedImageIsGlobal secondInternalFixed secondInternalReallyFixed))

-- In particular there cannot be an equivariant bijection in this
-- direction. Nothing follows about all possible OTHER actions on
-- 27 states or the original wild embedding.
