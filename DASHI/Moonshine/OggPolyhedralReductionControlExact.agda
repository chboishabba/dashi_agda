module DASHI.Moonshine.OggPolyhedralReductionControlExact where

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
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- DASHI CONTRIBUTION
--
-- Use non-Ogg dimensions as actual controls for the proposed SSP symmetry-
-- reduction selector.  The result is a no-go for two overly weak selectors:
--
-- * clean/multiplicity-free restriction to one fixed finite subgroup;
-- * branching data modulo copies of that subgroup's regular representation.
--
-- Exact collisions:
--
--   O ~= S4: dim 5 (j=2, Ogg) and dim 53 (j=26, non-Ogg)
--             differ by two regular representations;
--
--   I ~= A5: dim 7 (j=3, Ogg) and dim 67 (j=33, non-Ogg)
--             differ by one regular representation.
--
-- This is not a refutation of a p-indexed or Hecke-coupled reduction thesis.
-- It proves that the final selector must retain more information than either
-- of these fixed-subgroup regular-quotient signatures.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import MonsterOntos as Monster
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico

OggDimensionWitness : Nat → Set
OggDimensionWitness dimension =
  Σ Monster.SSP (λ prime → Monster.toNat prime ≡ dimension)

dimension5IsOgg : OggDimensionWitness 5
dimension5IsOgg = Monster.p5 , refl

dimension7IsOgg : OggDimensionWitness 7
dimension7IsOgg = Monster.p7 , refl

dimension9IsNotOgg : OggDimensionWitness 9 → ⊥
dimension9IsNotOgg (Monster.p2 , ())
dimension9IsNotOgg (Monster.p3 , ())
dimension9IsNotOgg (Monster.p5 , ())
dimension9IsNotOgg (Monster.p7 , ())
dimension9IsNotOgg (Monster.p11 , ())
dimension9IsNotOgg (Monster.p13 , ())
dimension9IsNotOgg (Monster.p17 , ())
dimension9IsNotOgg (Monster.p19 , ())
dimension9IsNotOgg (Monster.p23 , ())
dimension9IsNotOgg (Monster.p29 , ())
dimension9IsNotOgg (Monster.p31 , ())
dimension9IsNotOgg (Monster.p41 , ())
dimension9IsNotOgg (Monster.p47 , ())
dimension9IsNotOgg (Monster.p59 , ())
dimension9IsNotOgg (Monster.p71 , ())

dimension53IsNotOgg : OggDimensionWitness 53 → ⊥
dimension53IsNotOgg (Monster.p2 , ())
dimension53IsNotOgg (Monster.p3 , ())
dimension53IsNotOgg (Monster.p5 , ())
dimension53IsNotOgg (Monster.p7 , ())
dimension53IsNotOgg (Monster.p11 , ())
dimension53IsNotOgg (Monster.p13 , ())
dimension53IsNotOgg (Monster.p17 , ())
dimension53IsNotOgg (Monster.p19 , ())
dimension53IsNotOgg (Monster.p23 , ())
dimension53IsNotOgg (Monster.p29 , ())
dimension53IsNotOgg (Monster.p31 , ())
dimension53IsNotOgg (Monster.p41 , ())
dimension53IsNotOgg (Monster.p47 , ())
dimension53IsNotOgg (Monster.p59 , ())
dimension53IsNotOgg (Monster.p71 , ())

dimension67IsNotOgg : OggDimensionWitness 67 → ⊥
dimension67IsNotOgg (Monster.p2 , ())
dimension67IsNotOgg (Monster.p3 , ())
dimension67IsNotOgg (Monster.p5 , ())
dimension67IsNotOgg (Monster.p7 , ())
dimension67IsNotOgg (Monster.p11 , ())
dimension67IsNotOgg (Monster.p13 , ())
dimension67IsNotOgg (Monster.p17 , ())
dimension67IsNotOgg (Monster.p19 , ())
dimension67IsNotOgg (Monster.p23 , ())
dimension67IsNotOgg (Monster.p29 , ())
dimension67IsNotOgg (Monster.p31 , ())
dimension67IsNotOgg (Monster.p41 , ())
dimension67IsNotOgg (Monster.p47 , ())
dimension67IsNotOgg (Monster.p59 , ())
dimension67IsNotOgg (Monster.p71 , ())

------------------------------------------------------------------------
-- Clean branching is not enough: non-Ogg dimension 9 is multiplicity-free.
------------------------------------------------------------------------

nineIsCleanOctahedralControl :
  Oct.MultiplicityFree (Oct.branchingSpectrum Spin.j4)
nineIsCleanOctahedralControl = Oct.j4NineIsMultiplicityFree

------------------------------------------------------------------------
-- No selector invariant under regular-representation addition can be exact
-- on the exhibited Ogg/non-Ogg control pairs.
------------------------------------------------------------------------

record OctahedralRegularQuotientSelector : Set where
  field
    select : Oct.OctahedralSpectrum → Bool
    regularInvariant :
      (spectrum : Oct.OctahedralSpectrum) →
      select (Oct.addSpectrum Oct.regularSpectrum spectrum) ≡ select spectrum

open OctahedralRegularQuotientSelector public

octahedralControlCollision :
  (selector : OctahedralRegularQuotientSelector) →
  select selector (Oct.branchingSpectrum Spin.j26)
  ≡ select selector (Oct.branchingSpectrum Spin.j2)
octahedralControlCollision selector =
  trans
    (cong (select selector) Oct.j2ToJ26IsTwoRegularShifts)
    (trans
      (regularInvariant selector
        (Oct.addSpectrum Oct.regularSpectrum
          (Oct.branchingSpectrum Spin.j2)))
      (regularInvariant selector (Oct.branchingSpectrum Spin.j2)))

record IcosahedralRegularQuotientSelector : Set where
  field
    select : Ico.IcosahedralSpectrum → Bool
    regularInvariant :
      (spectrum : Ico.IcosahedralSpectrum) →
      select (Ico.addSpectrum Ico.regularSpectrum spectrum) ≡ select spectrum

open IcosahedralRegularQuotientSelector public

icosahedralControlCollision :
  (selector : IcosahedralRegularQuotientSelector) →
  select selector (Ico.branchingSpectrum Spin.j33)
  ≡ select selector (Ico.branchingSpectrum Spin.j3)
icosahedralControlCollision selector =
  trans
    (cong (select selector) Ico.j3ToJ33IsOneRegularShift)
    (regularInvariant selector (Ico.branchingSpectrum Spin.j3))

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

noExactOggOctahedralRegularQuotientSelector :
  (selector : OctahedralRegularQuotientSelector) →
  select selector (Oct.branchingSpectrum Spin.j2) ≡ true →
  select selector (Oct.branchingSpectrum Spin.j26) ≡ false →
  ⊥
noExactOggOctahedralRegularQuotientSelector selector selects5 rejects53 =
  trueNotFalse
    (trans
      (sym selects5)
      (trans
        (sym (octahedralControlCollision selector))
        rejects53))

noExactOggIcosahedralRegularQuotientSelector :
  (selector : IcosahedralRegularQuotientSelector) →
  select selector (Ico.branchingSpectrum Spin.j3) ≡ true →
  select selector (Ico.branchingSpectrum Spin.j33) ≡ false →
  ⊥
noExactOggIcosahedralRegularQuotientSelector selector selects7 rejects67 =
  trueNotFalse
    (trans
      (sym selects7)
      (trans
        (sym (icosahedralControlCollision selector))
        rejects67))

record OggPolyhedralReductionControlBoundary : Set where
  field
    nonOggControlsComputed : Bool
    nonOggControlsComputedIsTrue : nonOggControlsComputed ≡ true
    multiplicityFreeAloneSelectsOgg : Bool
    multiplicityFreeAloneSelectsOggIsFalse : multiplicityFreeAloneSelectsOgg ≡ false
    fixedOctahedralRegularQuotientSelectsOgg : Bool
    fixedOctahedralRegularQuotientSelectsOggIsFalse : fixedOctahedralRegularQuotientSelectsOgg ≡ false
    fixedIcosahedralRegularQuotientSelectsOgg : Bool
    fixedIcosahedralRegularQuotientSelectsOggIsFalse : fixedIcosahedralRegularQuotientSelectsOgg ≡ false
    pIndexedOrHeckeCoupledSelectorRefuted : Bool
    pIndexedOrHeckeCoupledSelectorRefutedIsFalse : pIndexedOrHeckeCoupledSelectorRefuted ≡ false

canonicalOggPolyhedralReductionControlBoundary :
  OggPolyhedralReductionControlBoundary
canonicalOggPolyhedralReductionControlBoundary =
  record
    { nonOggControlsComputed = true
    ; nonOggControlsComputedIsTrue = refl
    ; multiplicityFreeAloneSelectsOgg = false
    ; multiplicityFreeAloneSelectsOggIsFalse = refl
    ; fixedOctahedralRegularQuotientSelectsOgg = false
    ; fixedOctahedralRegularQuotientSelectsOggIsFalse = refl
    ; fixedIcosahedralRegularQuotientSelectsOgg = false
    ; fixedIcosahedralRegularQuotientSelectsOggIsFalse = refl
    ; pIndexedOrHeckeCoupledSelectorRefuted = false
    ; pIndexedOrHeckeCoupledSelectorRefutedIsFalse = refl
    }
