module DASHI.Physics.Plasma.KSW668SparseModeLookupNegationExact where

------------------------------------------------------------------------
-- A1: original all-integer-mode equality selector under conjugate pairing.
--
-- A finite-support Fourier field is defined using Output.modeEqual on
-- the ACTUAL Z^3 FourierMode, not a finite indexed surrogate. This lemma
-- is the universal source-level bridge from the selected positive mode
-- to its negative, a prerequisite to full RealityCondition and modewise
-- transversality of the KSW668 actual C3 Elsasser source.
--
-- This works for EVERY mode and EVERY selected mode; no finite bounding
-- cube, arbitrary lookup receipt, or postulate is introduced.
-- Adapted from the established Round719 source special case for zeroMode.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Plasma.KSW668RationalThreeModeSourceExact as Source

sourceModeEqualNegateCorrespondence :
  (mode selected : Z3.FourierMode) →
  Output.modeEqual (Z3.negateMode mode) selected
    ≡ Output.modeEqual mode (Z3.negateMode selected)
sourceModeEqualNegateCorrespondence mode selected
  with Output.modeEqual (Z3.negateMode mode) selected in negative
     | Output.modeEqual mode (Z3.negateMode selected) in original
... | true | true = refl
... | true | false =
  let
    negativeSame : Z3.negateMode mode ≡ selected
    negativeSame = Output.modeEqualSound negative

    originalSame : mode ≡ Z3.negateMode selected
    originalSame =
      trans
        (sym (Symmetry.negateModeInvolutive mode))
        (cong Z3.negateMode negativeSame)
  in
  ⊥-elim
    (Output.falseNotTrue
      (trans
        (sym original)
        (Output.modeEqualComplete originalSame)))
... | false | true =
  let
    originalSame : mode ≡ Z3.negateMode selected
    originalSame = Output.modeEqualSound original

    negativeSame : Z3.negateMode mode ≡ selected
    negativeSame =
      trans
        (cong Z3.negateMode originalSame)
        (Symmetry.negateModeInvolutive selected)
  in
  ⊥-elim
    (Output.falseNotTrue
      (trans
        (sym negative)
        (Output.modeEqualComplete negativeSame)))
... | false | false = refl

-- Useful explicit positive/negative selector equivalences on exactly the
-- selected triad source p,q,k; these are the actual same-object identifiers.

pLookupAtNegatedMode :
  (mode : Z3.FourierMode) →
  Output.modeEqual (Z3.negateMode mode) Source.p
    ≡ Output.modeEqual mode (Z3.negateMode Source.p)
pLookupAtNegatedMode mode =
  sourceModeEqualNegateCorrespondence mode Source.p

qLookupAtNegatedMode :
  (mode : Z3.FourierMode) →
  Output.modeEqual (Z3.negateMode mode) Source.q
    ≡ Output.modeEqual mode (Z3.negateMode Source.q)
qLookupAtNegatedMode mode =
  sourceModeEqualNegateCorrespondence mode Source.q

kLookupAtNegatedMode :
  (mode : Z3.FourierMode) →
  Output.modeEqual (Z3.negateMode mode) Source.k
    ≡ Output.modeEqual mode (Z3.negateMode Source.k)
kLookupAtNegatedMode mode =
  sourceModeEqualNegateCorrespondence mode Source.k

------------------------------------------------------------------------
-- Source lookup normalization established. To inhabit the original
-- IdealElsasserFourierState still requires ALL-MODE C3 conjugation of
-- sourceZPlus/sourceZMinus, ALL-MODE bilinear k·z=0 and an actual
-- rational inverse-norm owner; none is replaced by a Bool marker.
------------------------------------------------------------------------
