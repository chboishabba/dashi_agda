module DASHI.Foundations.PolyhedralRegularRepresentationShiftExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- DASHI CONTRIBUTION
--
-- Isolate the common mechanism behind the D4, octahedral/S4 and
-- icosahedral/A5 control scans.
--
-- The SO(3) character at a rotation of angle theta is periodic in j with a
-- period dividing the rotation order.  For these proper rotation groups the
-- least common period e of the nonidentity rotation classes satisfies
--
--   2*e = |G|.
--
-- Since dim(V_(j+e)) - dim(V_j) = 2*e, one period adds |G| at the identity
-- while adding zero on every nonidentity class: precisely the regular
-- character.  The companion finite tables witness the resulting laws
--
--   D4 : e=4,  |G|=8,
--   O  : e=12, |G|=24,
--   I  : e=30, |G|=60.
--
-- This module records the common exact finite pattern; it does not claim a
-- generic classification theorem for every finite subgroup of SO(3).
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.D4SO3RestrictionJ0To35Exact as D4
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico

data PolyhedralRotationGroup : Set where
  rotationalD4 rotationalOctahedral rotationalIcosahedral : PolyhedralRotationGroup

rotationGroupOrder : PolyhedralRotationGroup → Nat
rotationGroupOrder rotationalD4 = 8
rotationGroupOrder rotationalOctahedral = 24
rotationGroupOrder rotationalIcosahedral = 60

nonidentityCharacterPeriod : PolyhedralRotationGroup → Nat
nonidentityCharacterPeriod rotationalD4 = 4
nonidentityCharacterPeriod rotationalOctahedral = 12
nonidentityCharacterPeriod rotationalIcosahedral = 30

twicePeriodIsOrder :
  (group : PolyhedralRotationGroup) →
  2 * nonidentityCharacterPeriod group ≡ rotationGroupOrder group
twicePeriodIsOrder rotationalD4 = refl
twicePeriodIsOrder rotationalOctahedral = refl
twicePeriodIsOrder rotationalIcosahedral = refl

regularDimensionD4 :
  D4.branchingDimension D4.regularSpectrum ≡ rotationGroupOrder rotationalD4
regularDimensionD4 = refl

regularDimensionOctahedral :
  Oct.branchingDimension Oct.regularSpectrum
  ≡ rotationGroupOrder rotationalOctahedral
regularDimensionOctahedral = refl

regularDimensionIcosahedral :
  Ico.branchingDimension Ico.regularSpectrum
  ≡ rotationGroupOrder rotationalIcosahedral
regularDimensionIcosahedral = refl

record PolyhedralRegularShiftBoundary : Set where
  field
    d4RegularShiftProvedOnJ0To35 : Bool
    d4RegularShiftProvedOnJ0To35IsTrue :
      d4RegularShiftProvedOnJ0To35 ≡ true

    octahedralRegularShiftProvedOnJ0To35 : Bool
    octahedralRegularShiftProvedOnJ0To35IsTrue :
      octahedralRegularShiftProvedOnJ0To35 ≡ true

    icosahedralRegularShiftProvedWhereShiftFitsScan : Bool
    icosahedralRegularShiftProvedWhereShiftFitsScanIsTrue :
      icosahedralRegularShiftProvedWhereShiftFitsScan ≡ true

    regularQuotientExpectedToBePeriodic : Bool
    regularQuotientExpectedToBePeriodicIsTrue :
      regularQuotientExpectedToBePeriodic ≡ true

    periodicFixedGroupQuotientClaimedToExplainOggAlone : Bool
    periodicFixedGroupQuotientClaimedToExplainOggAloneIsFalse :
      periodicFixedGroupQuotientClaimedToExplainOggAlone ≡ false

canonicalPolyhedralRegularShiftBoundary : PolyhedralRegularShiftBoundary
canonicalPolyhedralRegularShiftBoundary =
  record
    { d4RegularShiftProvedOnJ0To35 = true
    ; d4RegularShiftProvedOnJ0To35IsTrue = refl
    ; octahedralRegularShiftProvedOnJ0To35 = true
    ; octahedralRegularShiftProvedOnJ0To35IsTrue = refl
    ; icosahedralRegularShiftProvedWhereShiftFitsScan = true
    ; icosahedralRegularShiftProvedWhereShiftFitsScanIsTrue = refl
    ; regularQuotientExpectedToBePeriodic = true
    ; regularQuotientExpectedToBePeriodicIsTrue = refl
    ; periodicFixedGroupQuotientClaimedToExplainOggAlone = false
    ; periodicFixedGroupQuotientClaimedToExplainOggAloneIsFalse = refl
    }
