module DASHI.Foundations.Base369FiveModePhaseQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Construct the finite carrier behind 5 x 2 = 9 + 1.  The five labels are the
-- five irreducible types of D4.  Binary orientation gives ten states.  The two
-- orientations of the distinguished trivial type A1 are identified in a
-- nine-state quotient; before quotienting, the second A1 representative is a
-- pointed completion state j.  This is a carrier theorem, not a Monster-local
-- representation theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data D4IrreducibleType : Set where
  A1 A2 B1 B2 E : D4IrreducibleType

data BinaryOrientation : Set where
  negativeOrientation
  positiveOrientation : BinaryOrientation

record OrientedMode : Set where
  constructor orientedMode
  field
    mode : D4IrreducibleType
    orientation : BinaryOrientation

open OrientedMode public

-- Nine ordinary cells plus one distinguished completion point.
data PointedNonary10 : Set where
  ordinary0 ordinary1 ordinary2 ordinary3 ordinary4
  ordinary5 ordinary6 ordinary7 ordinary8
  completionJ : PointedNonary10

pointedNonaryToOrientedMode : PointedNonary10 → OrientedMode
pointedNonaryToOrientedMode ordinary0 =
  orientedMode A1 negativeOrientation
pointedNonaryToOrientedMode completionJ =
  orientedMode A1 positiveOrientation
pointedNonaryToOrientedMode ordinary1 =
  orientedMode A2 negativeOrientation
pointedNonaryToOrientedMode ordinary2 =
  orientedMode A2 positiveOrientation
pointedNonaryToOrientedMode ordinary3 =
  orientedMode B1 negativeOrientation
pointedNonaryToOrientedMode ordinary4 =
  orientedMode B1 positiveOrientation
pointedNonaryToOrientedMode ordinary5 =
  orientedMode B2 negativeOrientation
pointedNonaryToOrientedMode ordinary6 =
  orientedMode B2 positiveOrientation
pointedNonaryToOrientedMode ordinary7 =
  orientedMode E negativeOrientation
pointedNonaryToOrientedMode ordinary8 =
  orientedMode E positiveOrientation

orientedModeToPointedNonary : OrientedMode → PointedNonary10
orientedModeToPointedNonary (orientedMode A1 negativeOrientation) = ordinary0
orientedModeToPointedNonary (orientedMode A1 positiveOrientation) = completionJ
orientedModeToPointedNonary (orientedMode A2 negativeOrientation) = ordinary1
orientedModeToPointedNonary (orientedMode A2 positiveOrientation) = ordinary2
orientedModeToPointedNonary (orientedMode B1 negativeOrientation) = ordinary3
orientedModeToPointedNonary (orientedMode B1 positiveOrientation) = ordinary4
orientedModeToPointedNonary (orientedMode B2 negativeOrientation) = ordinary5
orientedModeToPointedNonary (orientedMode B2 positiveOrientation) = ordinary6
orientedModeToPointedNonary (orientedMode E negativeOrientation) = ordinary7
orientedModeToPointedNonary (orientedMode E positiveOrientation) = ordinary8

pointedNonaryRoundTrip :
  (state : PointedNonary10) →
  orientedModeToPointedNonary (pointedNonaryToOrientedMode state) ≡ state
pointedNonaryRoundTrip ordinary0 = refl
pointedNonaryRoundTrip ordinary1 = refl
pointedNonaryRoundTrip ordinary2 = refl
pointedNonaryRoundTrip ordinary3 = refl
pointedNonaryRoundTrip ordinary4 = refl
pointedNonaryRoundTrip ordinary5 = refl
pointedNonaryRoundTrip ordinary6 = refl
pointedNonaryRoundTrip ordinary7 = refl
pointedNonaryRoundTrip ordinary8 = refl
pointedNonaryRoundTrip completionJ = refl

orientedModeRoundTrip :
  (state : OrientedMode) →
  pointedNonaryToOrientedMode (orientedModeToPointedNonary state) ≡ state
orientedModeRoundTrip (orientedMode A1 negativeOrientation) = refl
orientedModeRoundTrip (orientedMode A1 positiveOrientation) = refl
orientedModeRoundTrip (orientedMode A2 negativeOrientation) = refl
orientedModeRoundTrip (orientedMode A2 positiveOrientation) = refl
orientedModeRoundTrip (orientedMode B1 negativeOrientation) = refl
orientedModeRoundTrip (orientedMode B1 positiveOrientation) = refl
orientedModeRoundTrip (orientedMode B2 negativeOrientation) = refl
orientedModeRoundTrip (orientedMode B2 positiveOrientation) = refl
orientedModeRoundTrip (orientedMode E negativeOrientation) = refl
orientedModeRoundTrip (orientedMode E positiveOrientation) = refl

-- Quotient by the duplicated orientation of the distinguished identity mode.
data ModePhaseQuotient9 : Set where
  identityMode
  A2negative A2positive
  B1negative B1positive
  B2negative B2positive
  Enegative Epositive : ModePhaseQuotient9

quotientOrientedMode : OrientedMode → ModePhaseQuotient9
quotientOrientedMode (orientedMode A1 negativeOrientation) = identityMode
quotientOrientedMode (orientedMode A1 positiveOrientation) = identityMode
quotientOrientedMode (orientedMode A2 negativeOrientation) = A2negative
quotientOrientedMode (orientedMode A2 positiveOrientation) = A2positive
quotientOrientedMode (orientedMode B1 negativeOrientation) = B1negative
quotientOrientedMode (orientedMode B1 positiveOrientation) = B1positive
quotientOrientedMode (orientedMode B2 negativeOrientation) = B2negative
quotientOrientedMode (orientedMode B2 positiveOrientation) = B2positive
quotientOrientedMode (orientedMode E negativeOrientation) = Enegative
quotientOrientedMode (orientedMode E positiveOrientation) = Epositive

quotientRepresentative : ModePhaseQuotient9 → OrientedMode
quotientRepresentative identityMode = orientedMode A1 positiveOrientation
quotientRepresentative A2negative = orientedMode A2 negativeOrientation
quotientRepresentative A2positive = orientedMode A2 positiveOrientation
quotientRepresentative B1negative = orientedMode B1 negativeOrientation
quotientRepresentative B1positive = orientedMode B1 positiveOrientation
quotientRepresentative B2negative = orientedMode B2 negativeOrientation
quotientRepresentative B2positive = orientedMode B2 positiveOrientation
quotientRepresentative Enegative = orientedMode E negativeOrientation
quotientRepresentative Epositive = orientedMode E positiveOrientation

quotientAfterRepresentative :
  (state : ModePhaseQuotient9) →
  quotientOrientedMode (quotientRepresentative state) ≡ state
quotientAfterRepresentative identityMode = refl
quotientAfterRepresentative A2negative = refl
quotientAfterRepresentative A2positive = refl
quotientAfterRepresentative B1negative = refl
quotientAfterRepresentative B1positive = refl
quotientAfterRepresentative B2negative = refl
quotientAfterRepresentative B2positive = refl
quotientAfterRepresentative Enegative = refl
quotientAfterRepresentative Epositive = refl

identityOrientationDuplicationCollapsed :
  quotientOrientedMode (orientedMode A1 negativeOrientation)
  ≡ quotientOrientedMode (orientedMode A1 positiveOrientation)
identityOrientationDuplicationCollapsed = refl
