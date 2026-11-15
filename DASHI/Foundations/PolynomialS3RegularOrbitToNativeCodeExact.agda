module DASHI.Foundations.PolynomialS3RegularOrbitToNativeCodeExact where

-- TRUE regular-orbit receiver for the EXACT 6x6 Fourier certificate.
-- Each of three existing size-six S3 functional-graph orbits is
-- freely and transitively represented by the same six group labels.
-- Reuses ORIGINAL canonical representatives and conjugation laws;
-- not a new isomorphism of roots, Hatcher wild ends or Monster3B.
-- SOURCE WRITTEN; Agda kernel verification PENDING.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.TernaryEndomorphismS3ActionLawsExact as ActionLaws
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Foundations.PolynomialS3RegularRationalBlockCertificateExact as Block

data RegularFamily : Set where
  rank2OneFixed rank2TwoFixed rank2TwoCycle : RegularFamily

regularShape : RegularFamily → Shape.ShapeOrbit7
regularShape rank2OneFixed = Shape.rank2OneFixedShape
regularShape rank2TwoFixed = Shape.rank2TwoFixedShape
regularShape rank2TwoCycle = Shape.rank2TwoCycleShape

regularRepresentative : RegularFamily → Tower.LevelTwoCode
regularRepresentative name = Shape.shapeRepresentative (regularShape name)

regularCode : RegularFamily → Block.Six → Tower.LevelTwoCode
regularCode fam index =
  Shape.conjugateCode (Block.rowPermutation index) (regularRepresentative fam)

-- Group multiplication after identifying Block.Six with the EXACT
-- existing original TriPermutation type.
leftMultiplyIndex :
  Shape.TriPermutation → Block.Six → Block.Six
leftMultiplyIndex p i =
  Block.permutationRow (S3._∙_ p (Block.rowPermutation i))

nativeRegularActionIntertwines :
  (p : Shape.TriPermutation) (fam : RegularFamily)
  (i : Block.Six) →
  Shape.conjugateCode p (regularCode fam i)
    ≡ regularCode fam (leftMultiplyIndex p i)
nativeRegularActionIntertwines p fam i =
  trans
    (sym (ActionLaws.conjugateComposition
      p (Block.rowPermutation i) (regularRepresentative fam)))
    (cong (λ q → Shape.conjugateCode q (regularRepresentative fam))
      (sym (Block.permutationRowRoundTrip
        (S3._∙_ p (Block.rowPermutation i)))))

-- The original shape classifier restricts to the correct family
-- on all eighteen transported source codes, reusing the exact
-- existing seven-shape S3 orbit-class invariance owner.
regularCodeShape :
  (fam : RegularFamily) (i : Block.Six) →
  Shape.shapeClass (regularCode fam i) ≡ regularShape fam
regularCodeShape fam i =
  trans
    (Shape.representativeOrbitStaysClass
      (Block.rowPermutation i) (regularShape fam))
    refl

-- Three distinct size-six families: every pair of the six
-- left-regular group labels yields a different underlying code.
regularCodeFree :
  (fam : RegularFamily) (i j : Block.Six) →
  regularCode fam i ≡ regularCode fam j → i ≡ j
regularCodeFree rank2OneFixed Block.slot0 Block.slot0 eq = refl
regularCodeFree rank2OneFixed Block.slot0 Block.slot1 ()
regularCodeFree rank2OneFixed Block.slot0 Block.slot2 ()
regularCodeFree rank2OneFixed Block.slot0 Block.slot3 ()
regularCodeFree rank2OneFixed Block.slot0 Block.slot4 ()
regularCodeFree rank2OneFixed Block.slot0 Block.slot5 ()
regularCodeFree rank2OneFixed Block.slot1 Block.slot0 ()
regularCodeFree rank2OneFixed Block.slot1 Block.slot1 eq = refl
regularCodeFree rank2OneFixed Block.slot1 Block.slot2 ()
regularCodeFree rank2OneFixed Block.slot1 Block.slot3 ()
regularCodeFree rank2OneFixed Block.slot1 Block.slot4 ()
regularCodeFree rank2OneFixed Block.slot1 Block.slot5 ()
regularCodeFree rank2OneFixed Block.slot2 Block.slot0 ()
regularCodeFree rank2OneFixed Block.slot2 Block.slot1 ()
regularCodeFree rank2OneFixed Block.slot2 Block.slot2 eq = refl
regularCodeFree rank2OneFixed Block.slot2 Block.slot3 ()
regularCodeFree rank2OneFixed Block.slot2 Block.slot4 ()
regularCodeFree rank2OneFixed Block.slot2 Block.slot5 ()
regularCodeFree rank2OneFixed Block.slot3 Block.slot0 ()
regularCodeFree rank2OneFixed Block.slot3 Block.slot1 ()
regularCodeFree rank2OneFixed Block.slot3 Block.slot2 ()
regularCodeFree rank2OneFixed Block.slot3 Block.slot3 eq = refl
regularCodeFree rank2OneFixed Block.slot3 Block.slot4 ()
regularCodeFree rank2OneFixed Block.slot3 Block.slot5 ()
regularCodeFree rank2OneFixed Block.slot4 Block.slot0 ()
regularCodeFree rank2OneFixed Block.slot4 Block.slot1 ()
regularCodeFree rank2OneFixed Block.slot4 Block.slot2 ()
regularCodeFree rank2OneFixed Block.slot4 Block.slot3 ()
regularCodeFree rank2OneFixed Block.slot4 Block.slot4 eq = refl
regularCodeFree rank2OneFixed Block.slot4 Block.slot5 ()
regularCodeFree rank2OneFixed Block.slot5 Block.slot0 ()
regularCodeFree rank2OneFixed Block.slot5 Block.slot1 ()
regularCodeFree rank2OneFixed Block.slot5 Block.slot2 ()
regularCodeFree rank2OneFixed Block.slot5 Block.slot3 ()
regularCodeFree rank2OneFixed Block.slot5 Block.slot4 ()
regularCodeFree rank2OneFixed Block.slot5 Block.slot5 eq = refl
regularCodeFree rank2TwoFixed Block.slot0 Block.slot0 eq = refl
regularCodeFree rank2TwoFixed Block.slot0 Block.slot1 ()
regularCodeFree rank2TwoFixed Block.slot0 Block.slot2 ()
regularCodeFree rank2TwoFixed Block.slot0 Block.slot3 ()
regularCodeFree rank2TwoFixed Block.slot0 Block.slot4 ()
regularCodeFree rank2TwoFixed Block.slot0 Block.slot5 ()
regularCodeFree rank2TwoFixed Block.slot1 Block.slot0 ()
regularCodeFree rank2TwoFixed Block.slot1 Block.slot1 eq = refl
regularCodeFree rank2TwoFixed Block.slot1 Block.slot2 ()
regularCodeFree rank2TwoFixed Block.slot1 Block.slot3 ()
regularCodeFree rank2TwoFixed Block.slot1 Block.slot4 ()
regularCodeFree rank2TwoFixed Block.slot1 Block.slot5 ()
regularCodeFree rank2TwoFixed Block.slot2 Block.slot0 ()
regularCodeFree rank2TwoFixed Block.slot2 Block.slot1 ()
regularCodeFree rank2TwoFixed Block.slot2 Block.slot2 eq = refl
regularCodeFree rank2TwoFixed Block.slot2 Block.slot3 ()
regularCodeFree rank2TwoFixed Block.slot2 Block.slot4 ()
regularCodeFree rank2TwoFixed Block.slot2 Block.slot5 ()
regularCodeFree rank2TwoFixed Block.slot3 Block.slot0 ()
regularCodeFree rank2TwoFixed Block.slot3 Block.slot1 ()
regularCodeFree rank2TwoFixed Block.slot3 Block.slot2 ()
regularCodeFree rank2TwoFixed Block.slot3 Block.slot3 eq = refl
regularCodeFree rank2TwoFixed Block.slot3 Block.slot4 ()
regularCodeFree rank2TwoFixed Block.slot3 Block.slot5 ()
regularCodeFree rank2TwoFixed Block.slot4 Block.slot0 ()
regularCodeFree rank2TwoFixed Block.slot4 Block.slot1 ()
regularCodeFree rank2TwoFixed Block.slot4 Block.slot2 ()
regularCodeFree rank2TwoFixed Block.slot4 Block.slot3 ()
regularCodeFree rank2TwoFixed Block.slot4 Block.slot4 eq = refl
regularCodeFree rank2TwoFixed Block.slot4 Block.slot5 ()
regularCodeFree rank2TwoFixed Block.slot5 Block.slot0 ()
regularCodeFree rank2TwoFixed Block.slot5 Block.slot1 ()
regularCodeFree rank2TwoFixed Block.slot5 Block.slot2 ()
regularCodeFree rank2TwoFixed Block.slot5 Block.slot3 ()
regularCodeFree rank2TwoFixed Block.slot5 Block.slot4 ()
regularCodeFree rank2TwoFixed Block.slot5 Block.slot5 eq = refl
regularCodeFree rank2TwoCycle Block.slot0 Block.slot0 eq = refl
regularCodeFree rank2TwoCycle Block.slot0 Block.slot1 ()
regularCodeFree rank2TwoCycle Block.slot0 Block.slot2 ()
regularCodeFree rank2TwoCycle Block.slot0 Block.slot3 ()
regularCodeFree rank2TwoCycle Block.slot0 Block.slot4 ()
regularCodeFree rank2TwoCycle Block.slot0 Block.slot5 ()
regularCodeFree rank2TwoCycle Block.slot1 Block.slot0 ()
regularCodeFree rank2TwoCycle Block.slot1 Block.slot1 eq = refl
regularCodeFree rank2TwoCycle Block.slot1 Block.slot2 ()
regularCodeFree rank2TwoCycle Block.slot1 Block.slot3 ()
regularCodeFree rank2TwoCycle Block.slot1 Block.slot4 ()
regularCodeFree rank2TwoCycle Block.slot1 Block.slot5 ()
regularCodeFree rank2TwoCycle Block.slot2 Block.slot0 ()
regularCodeFree rank2TwoCycle Block.slot2 Block.slot1 ()
regularCodeFree rank2TwoCycle Block.slot2 Block.slot2 eq = refl
regularCodeFree rank2TwoCycle Block.slot2 Block.slot3 ()
regularCodeFree rank2TwoCycle Block.slot2 Block.slot4 ()
regularCodeFree rank2TwoCycle Block.slot2 Block.slot5 ()
regularCodeFree rank2TwoCycle Block.slot3 Block.slot0 ()
regularCodeFree rank2TwoCycle Block.slot3 Block.slot1 ()
regularCodeFree rank2TwoCycle Block.slot3 Block.slot2 ()
regularCodeFree rank2TwoCycle Block.slot3 Block.slot3 eq = refl
regularCodeFree rank2TwoCycle Block.slot3 Block.slot4 ()
regularCodeFree rank2TwoCycle Block.slot3 Block.slot5 ()
regularCodeFree rank2TwoCycle Block.slot4 Block.slot0 ()
regularCodeFree rank2TwoCycle Block.slot4 Block.slot1 ()
regularCodeFree rank2TwoCycle Block.slot4 Block.slot2 ()
regularCodeFree rank2TwoCycle Block.slot4 Block.slot3 ()
regularCodeFree rank2TwoCycle Block.slot4 Block.slot4 eq = refl
regularCodeFree rank2TwoCycle Block.slot4 Block.slot5 ()
regularCodeFree rank2TwoCycle Block.slot5 Block.slot0 ()
regularCodeFree rank2TwoCycle Block.slot5 Block.slot1 ()
regularCodeFree rank2TwoCycle Block.slot5 Block.slot2 ()
regularCodeFree rank2TwoCycle Block.slot5 Block.slot3 ()
regularCodeFree rank2TwoCycle Block.slot5 Block.slot4 ()
regularCodeFree rank2TwoCycle Block.slot5 Block.slot5 eq = refl

-- All 108 clauses are elementary constructor discriminations.
-- With the faithful Six-index chart, each copy of the certified
-- Q[S3] regular block corresponds to an ACTUAL named 27-code orbit.
