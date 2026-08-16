module DASHI.Moonshine.OggTetrahedralReductionControlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires", Seminaire Delange-Pisot-Poitou,
-- 1974/75, exp. 7.  No DOI asserted.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Supply the tetrahedral A4 analogue of the S4/A5 regular-quotient no-go.
-- The Ogg dimension 3 (j=1) and non-Ogg dimension 15 (j=7) differ by one
-- regular A4 representation after restriction.  Hence any selector invariant
-- under adding Reg_A4 cannot distinguish that control pair.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import MonsterOntos as Monster
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.TetrahedralSO3RestrictionJ0To35Exact as Tet
import DASHI.Moonshine.OggPolyhedralReductionControlExact as Control

dimension3IsOgg : Control.OggDimensionWitness 3
dimension3IsOgg = Monster.p3 , refl

dimension15IsNotOgg : Control.OggDimensionWitness 15 → ⊥
dimension15IsNotOgg (Monster.p2 , ())
dimension15IsNotOgg (Monster.p3 , ())
dimension15IsNotOgg (Monster.p5 , ())
dimension15IsNotOgg (Monster.p7 , ())
dimension15IsNotOgg (Monster.p11 , ())
dimension15IsNotOgg (Monster.p13 , ())
dimension15IsNotOgg (Monster.p17 , ())
dimension15IsNotOgg (Monster.p19 , ())
dimension15IsNotOgg (Monster.p23 , ())
dimension15IsNotOgg (Monster.p29 , ())
dimension15IsNotOgg (Monster.p31 , ())
dimension15IsNotOgg (Monster.p41 , ())
dimension15IsNotOgg (Monster.p47 , ())
dimension15IsNotOgg (Monster.p59 , ())
dimension15IsNotOgg (Monster.p71 , ())

record TetrahedralRegularQuotientSelector : Set where
  field
    select : Tet.TetrahedralSpectrum → Bool
    regularInvariant :
      (spectrum : Tet.TetrahedralSpectrum) →
      select (Tet.addSpectrum Tet.regularSpectrum spectrum) ≡ select spectrum

open TetrahedralRegularQuotientSelector public

tetrahedral3To15Collision :
  (selector : TetrahedralRegularQuotientSelector) →
  select selector (Tet.branchingSpectrum Spin.j7)
  ≡ select selector (Tet.branchingSpectrum Spin.j1)
tetrahedral3To15Collision selector =
  trans
    (cong (select selector) Tet.j1ToJ7IsOneRegularShift)
    (regularInvariant selector (Tet.branchingSpectrum Spin.j1))

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

noExactOggTetrahedralRegularQuotientSelector :
  (selector : TetrahedralRegularQuotientSelector) →
  select selector (Tet.branchingSpectrum Spin.j1) ≡ true →
  select selector (Tet.branchingSpectrum Spin.j7) ≡ false →
  ⊥
noExactOggTetrahedralRegularQuotientSelector selector selects3 rejects15 =
  trueNotFalse
    (trans
      (sym selects3)
      (trans
        (sym (tetrahedral3To15Collision selector))
        rejects15))

record OggTetrahedralControlBoundary : Set where
  field
    dimensionThreeOggControlPresent : Bool
    dimensionThreeOggControlPresentIsTrue : dimensionThreeOggControlPresent ≡ true
    dimensionFifteenNonOggControlPresent : Bool
    dimensionFifteenNonOggControlPresentIsTrue : dimensionFifteenNonOggControlPresent ≡ true
    fixedA4RegularQuotientCanSelectOggExactly : Bool
    fixedA4RegularQuotientCanSelectOggExactlyIsFalse :
      fixedA4RegularQuotientCanSelectOggExactly ≡ false

canonicalOggTetrahedralControlBoundary : OggTetrahedralControlBoundary
canonicalOggTetrahedralControlBoundary =
  record
    { dimensionThreeOggControlPresent = true
    ; dimensionThreeOggControlPresentIsTrue = refl
    ; dimensionFifteenNonOggControlPresent = true
    ; dimensionFifteenNonOggControlPresentIsTrue = refl
    ; fixedA4RegularQuotientCanSelectOggExactly = false
    ; fixedA4RegularQuotientCanSelectOggExactlyIsFalse = refl
    }
