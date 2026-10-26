module DASHI.Mathematics.Symmetry.TetragonalPrimitiveSeitzExact where

-- Primitive tetragonal (symmorphic P4/mmm-type) affine-coordinate
-- candidate. Point group D4h, translation lattice Z^3.
--
-- Classical Seitz semidirect multiplication:
--   (g,t)(h,u) = (gh, t + g u)
-- on points p: (g,t) p = g p + t.
-- The full group law still needs the coordinate actCompose proof;
-- none is asserted by mere construction of these operations.
-- This does not model diamond Fd-3m fractional translations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ)
import DASHI.Physics.Closure.NSIntegerFourierLattice as NS
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.TetragonalFourierLatticeBridgeExact as F

record PrimitiveSeitz : Set where
  constructor seitz
  field
    linearPart : D.D4h
    integerTranslation : NS.FourierMode
open PrimitiveSeitz public

seitzIdentity : PrimitiveSeitz
seitzIdentity = seitz D.identity NS.zeroMode

seitzMultiply : PrimitiveSeitz → PrimitiveSeitz → PrimitiveSeitz
seitzMultiply (seitz g t) (seitz h u) =
  seitz (D.compose g h) (NS.addMode t (F.actMode g u))

seitzApply : PrimitiveSeitz → NS.FourierMode → NS.FourierMode
seitzApply (seitz g t) p =
  NS.addMode t (F.actMode g p)

pureTranslation : NS.FourierMode → PrimitiveSeitz
pureTranslation t = seitz D.identity t

purePointOperation : D.D4h → PrimitiveSeitz
purePointOperation g = seitz g NS.zeroMode

seitzTranslationApplies :
  (t : NS.FourierMode) (p : NS.FourierMode) →
  seitzApply (pureTranslation t) p ≡ NS.addMode t p
seitzTranslationApplies (NS.mode tx ty tz) (NS.mode x y z) = refl

-- A translation does not alter the reciprocal wavevector *index*.
-- A Bloch state nonetheless acquires a translation-dependent phase,
-- which is not modelled by this raw integer-lattice action.
reciprocalIndex : PrimitiveSeitz → NS.FourierMode → NS.FourierMode
reciprocalIndex s k = F.actMode (linearPart s) k

reciprocalTranslationIsIdentity :
  (t : NS.FourierMode) (k : NS.FourierMode) →
  reciprocalIndex (pureTranslation t) k ≡ k
reciprocalTranslationIsIdentity t (NS.mode kx ky kz) = refl

-- A mathematical primitive lattice Z³ with a tP metric is not a
-- specific experimentally identified solid. Atomic 369 decoration,
-- tI centring, Bloch phases, magnetic groups, and fractional
-- nonsymmorphic translations remain independently typed consumers.
