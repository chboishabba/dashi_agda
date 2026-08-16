module DASHI.Foundations.PolyhedralInvariantFixedSpaceSignatureExact where

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
-- Form a genuine fixed-space signature from the trivial-isotypic
-- multiplicities in four independently computed SO(3) restrictions:
--
--   (dim V_j^D4, dim V_j^A4, dim V_j^S4, dim V_j^A5).
--
-- The result gives a strong control collision inside the j=0..35 scan:
--
--   j=14, dim=29 -> (4,2,1,0)
--   j=17, dim=35 -> (4,2,1,0).
--
-- Dimension 29 is in the Ogg set while 35 is not.  Therefore even this
-- four-lens invariant-subspace signature cannot by itself characterize Ogg.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import MonsterOntos as Monster
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.D4SO3RestrictionJ0To35Exact as D4
import DASHI.Foundations.TetrahedralSO3RestrictionJ0To35Exact as Tet
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico
import DASHI.Moonshine.OggPolyhedralReductionControlExact as Control

record InvariantFixedSpaceSignature : Set where
  constructor invariant-signature
  field
    d4InvariantDimension : Nat
    tetrahedralInvariantDimension : Nat
    octahedralInvariantDimension : Nat
    icosahedralInvariantDimension : Nat

open InvariantFixedSpaceSignature public

invariantSignature :
  Spin.AngularMomentum0To35 → InvariantFixedSpaceSignature
invariantSignature j =
  invariant-signature
    (D4.multiplicityA1 (D4.branchingSpectrum j))
    (Tet.multiplicityT1 (Tet.branchingSpectrum j))
    (Oct.multiplicityA1 (Oct.branchingSpectrum j))
    (Ico.multiplicityI1 (Ico.branchingSpectrum j))

j14InvariantSignature :
  invariantSignature Spin.j14 ≡ invariant-signature 4 2 1 0
j14InvariantSignature = refl

j17InvariantSignature :
  invariantSignature Spin.j17 ≡ invariant-signature 4 2 1 0
j17InvariantSignature = refl

ogg29AndNonOgg35HaveSameFixedSpaceSignature :
  invariantSignature Spin.j14 ≡ invariantSignature Spin.j17
ogg29AndNonOgg35HaveSameFixedSpaceSignature = refl

dimension29IsOgg : Control.OggDimensionWitness 29
dimension29IsOgg = Monster.p29 , refl

dimension35IsNotOgg : Control.OggDimensionWitness 35 → ⊥
dimension35IsNotOgg (Monster.p2 , ())
dimension35IsNotOgg (Monster.p3 , ())
dimension35IsNotOgg (Monster.p5 , ())
dimension35IsNotOgg (Monster.p7 , ())
dimension35IsNotOgg (Monster.p11 , ())
dimension35IsNotOgg (Monster.p13 , ())
dimension35IsNotOgg (Monster.p17 , ())
dimension35IsNotOgg (Monster.p19 , ())
dimension35IsNotOgg (Monster.p23 , ())
dimension35IsNotOgg (Monster.p29 , ())
dimension35IsNotOgg (Monster.p31 , ())
dimension35IsNotOgg (Monster.p41 , ())
dimension35IsNotOgg (Monster.p47 , ())
dimension35IsNotOgg (Monster.p59 , ())
dimension35IsNotOgg (Monster.p71 , ())

record FixedSpaceSignatureSelector : Set where
  field
    select : InvariantFixedSpaceSignature → Bool

open FixedSpaceSignatureSelector public

selectorCannotSeparate29From35 :
  (selector : FixedSpaceSignatureSelector) →
  select selector (invariantSignature Spin.j14)
  ≡ select selector (invariantSignature Spin.j17)
selectorCannotSeparate29From35 selector =
  cong (select selector) ogg29AndNonOgg35HaveSameFixedSpaceSignature

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

noExactOggFixedSpaceSignatureSelector :
  (selector : FixedSpaceSignatureSelector) →
  select selector (invariantSignature Spin.j14) ≡ true →
  select selector (invariantSignature Spin.j17) ≡ false →
  ⊥
noExactOggFixedSpaceSignatureSelector selector selects29 rejects35 =
  trueNotFalse
    (trans
      (sym selects29)
      (trans
        (selectorCannotSeparate29From35 selector)
        rejects35))

record PolyhedralInvariantSignatureBoundary : Set where
  field
    fourActualFixedSpaceLensesCombined : Bool
    fourActualFixedSpaceLensesCombinedIsTrue :
      fourActualFixedSpaceLensesCombined ≡ true
    combinedFixedSpaceSignatureCharacterizesOgg : Bool
    combinedFixedSpaceSignatureCharacterizesOggIsFalse :
      combinedFixedSpaceSignatureCharacterizesOgg ≡ false
    fullBranchingSpectrumRefutedByThisCollision : Bool
    fullBranchingSpectrumRefutedByThisCollisionIsFalse :
      fullBranchingSpectrumRefutedByThisCollision ≡ false
    primeIndexedArithmeticCouplingRefutedByThisCollision : Bool
    primeIndexedArithmeticCouplingRefutedByThisCollisionIsFalse :
      primeIndexedArithmeticCouplingRefutedByThisCollision ≡ false

canonicalPolyhedralInvariantSignatureBoundary :
  PolyhedralInvariantSignatureBoundary
canonicalPolyhedralInvariantSignatureBoundary =
  record
    { fourActualFixedSpaceLensesCombined = true
    ; fourActualFixedSpaceLensesCombinedIsTrue = refl
    ; combinedFixedSpaceSignatureCharacterizesOgg = false
    ; combinedFixedSpaceSignatureCharacterizesOggIsFalse = refl
    ; fullBranchingSpectrumRefutedByThisCollision = false
    ; fullBranchingSpectrumRefutedByThisCollisionIsFalse = refl
    ; primeIndexedArithmeticCouplingRefutedByThisCollision = false
    ; primeIndexedArithmeticCouplingRefutedByThisCollisionIsFalse = refl
    }
