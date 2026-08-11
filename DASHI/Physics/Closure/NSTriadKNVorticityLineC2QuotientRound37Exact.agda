module DASHI.Physics.Closure.NSTriadKNVorticityLineC2QuotientRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Make the orientation quotient behind the Round-37 projector geometry
-- literal.  Vorticity *line* coherence should identify xi and -xi.  The two
-- element orientation action below is an exact C2 action on unit directions:
--
--   flip (flip xi) = xi.
--
-- The rank-one projector is constant on each C2 orbit, and the projector
-- defect between two lines is invariant under independently flipping either
-- representative.  Thus the HH-good geometric carrier is genuinely an
-- unoriented line quotient rather than a conventionally normalized vector.
--
-- This is the finite/projective analogue requested by the quotient analysis;
-- no claim is made here about the much larger rotational stabilizer group.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNDirectionalProjectorStabilizerRound37Exact as Projector

data Orientation : Set where
  preserve reverse : Orientation

orientVector : Orientation → V.Vector3 → V.Vector3
orientVector preserve vector = vector
orientVector reverse vector = Projector.negateVector vector

orientationActionInvolutive : ∀ orientation vector →
  orientVector orientation (orientVector orientation vector) ≡ vector
orientationActionInvolutive preserve vector = refl
orientationActionInvolutive reverse (V.v3 vx vy vz) =
  V.vectorExt
    (solve (vx ∷ []))
    (solve (vy ∷ []))
    (solve (vz ∷ []))

orientUnit : Orientation → Projector.UnitDirection → Projector.UnitDirection
orientUnit preserve direction = direction
orientUnit reverse direction = Projector.negateUnitDirection direction

orientationProjectorInvariant : ∀ orientation direction →
  Projector.rankOneProjector
    (Projector.vector (orientUnit orientation direction))
  ≡ Projector.rankOneProjector (Projector.vector direction)
orientationProjectorInvariant preserve direction = refl
orientationProjectorInvariant reverse direction =
  Projector.oppositeDirectionSameProjector direction

projectorDefectRepresentativeInvariant :
  ∀ leftOrientation rightOrientation left right →
  Projector.unitProjectorDefectSquared
    (orientUnit leftOrientation left)
    (orientUnit rightOrientation right)
  ≡ Projector.unitProjectorDefectSquared left right
projectorDefectRepresentativeInvariant
    leftOrientation rightOrientation left right =
  cong₂
    (λ leftProjector rightProjector →
      Projector.frobeniusSquared
        (Projector.matrixSubtract leftProjector rightProjector))
    (orientationProjectorInvariant leftOrientation left)
    (orientationProjectorInvariant rightOrientation right)

record VorticityLine : Set where
  constructor vorticity-line
  field
    representative : Projector.UnitDirection

open VorticityLine public

lineProjector : VorticityLine → Matrix.Matrix3
lineProjector line =
  Projector.rankOneProjector (Projector.vector (representative line))

-- A representative change by the C2 action changes only the fibre coordinate;
-- the coarse line projector is propositionally unchanged.
changeRepresentative : Orientation → VorticityLine → VorticityLine
changeRepresentative orientation line =
  vorticity-line (orientUnit orientation (representative line))

lineProjectorRepresentativeIndependent : ∀ orientation line →
  lineProjector (changeRepresentative orientation line) ≡ lineProjector line
lineProjectorRepresentativeIndependent orientation line =
  orientationProjectorInvariant orientation (representative line)

vorticityLineC2QuotientClosed : Bool
vorticityLineC2QuotientClosed = true

vorticityLineC2QuotientClosedIsTrue :
  vorticityLineC2QuotientClosed ≡ true
vorticityLineC2QuotientClosedIsTrue = refl
