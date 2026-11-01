module DASHI.Physics.Closure.NSTriadKNComplex3HermitianNondegeneracy where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Six-probe real-Hermitian nondegeneracy for the exact C3 carrier".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a repository-original finite-dimensional
-- coordinate proof.
-- Uses: the convention <u,v> = conjugate(u) dot v, the real coordinate probes
-- e1,e2,e3, and the imaginary coordinate probes i e1,i e2,i e3.
-- Relationship: proves that equality of all real Hermitian tests separates C3
-- vectors over every repository RealField.  No extra one-not-zero axiom is
-- needed: the probes recover each coordinate directly, and the conclusion is
-- also valid for a degenerate one-element carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNLiteralVectorAdjointCandidates as Adjoints

cong₃ :
  ∀ {a b c d : Level}
    {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (f : A → B → C → D)
    {x x' : A} {y y' : B} {z z' : C} →
  x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

basisX : ∀ {r} (F : C3.RealField r) → C3.Complex3 F
basisX F =
  C3.complex3 (C3.complexOne F) (C3.complexZero F) (C3.complexZero F)

basisY : ∀ {r} (F : C3.RealField r) → C3.Complex3 F
basisY F =
  C3.complex3 (C3.complexZero F) (C3.complexOne F) (C3.complexZero F)

basisZ : ∀ {r} (F : C3.RealField r) → C3.Complex3 F
basisZ F =
  C3.complex3 (C3.complexZero F) (C3.complexZero F) (C3.complexOne F)

imaginaryBasisX : ∀ {r} (F : C3.RealField r) → C3.Complex3 F
imaginaryBasisX F =
  C3.complex3 (C3.complexI F) (C3.complexZero F) (C3.complexZero F)

imaginaryBasisY : ∀ {r} (F : C3.RealField r) → C3.Complex3 F
imaginaryBasisY F =
  C3.complex3 (C3.complexZero F) (C3.complexI F) (C3.complexZero F)

imaginaryBasisZ : ∀ {r} (F : C3.RealField r) → C3.Complex3 F
imaginaryBasisZ F =
  C3.complex3 (C3.complexZero F) (C3.complexZero F) (C3.complexI F)

imaginaryPartEmbed :
  ∀ {r} (F : C3.RealField r) → C3.Complex F → C3.Complex F
imaginaryPartEmbed F z = C3.realEmbed F (C3.imaginary z)

complexConjugateIIsMinusI :
  ∀ {r} (F : C3.RealField r) →
  C3.complexConjugate (C3.complexI F)
  ≡ C3.complexNegate (C3.complexI F)
complexConjugateIIsMinusI F rewrite C3.negateZero F = refl

complexRealPartMinusIMultiply :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.complexRealPart
    (C3.complexMultiply (C3.complexNegate (C3.complexI F)) z)
  ≡ imaginaryPartEmbed F z
complexRealPartMinusIMultiply {F = F} (C3.complex real imaginary)
  rewrite C3.negateZero F
        | Algebra.realMultiplyZeroLeft F real
        | C3.addZeroLeft F
            (C3.negate F
              (C3.multiply F (C3.negate F (C3.one F)) imaginary)) =
  cong (λ value → C3.complex value (C3.zero F)) realCoordinate
  where
    minusOneMultiply :
      C3.multiply F (C3.negate F (C3.one F)) imaginary
      ≡ C3.negate F imaginary
    minusOneMultiply =
      trans
        (sym (Algebra.realNegateMultiplyLeft F (C3.one F) imaginary))
        (cong (C3.negate F) (C3.multiplyOneLeft F imaginary))

    realCoordinate :
      C3.negate F
        (C3.multiply F (C3.negate F (C3.one F)) imaginary)
      ≡ imaginary
    realCoordinate =
      trans
        (cong (C3.negate F) minusOneMultiply)
        (C3.negateInvolutive F imaginary)

basisXRealProbe :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complexRealPart (C3.hermitianPairing3 (basisX F) v)
  ≡ C3.complexRealPart (C3.x v)
basisXRealProbe {F = F} (C3.complex3 vx vy vz)
  rewrite Hermitian.complexConjugateOne F
        | Hermitian.complexConjugateZero F
        | Hermitian.complexMultiplyOneLeft vx
        | Hermitian.complexMultiplyZeroLeft vy
        | Hermitian.complexMultiplyZeroLeft vz
        | Algebra.complexAddZeroRight vx = refl

basisYRealProbe :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complexRealPart (C3.hermitianPairing3 (basisY F) v)
  ≡ C3.complexRealPart (C3.y v)
basisYRealProbe {F = F} (C3.complex3 vx vy vz)
  rewrite Hermitian.complexConjugateZero F
        | Hermitian.complexConjugateOne F
        | Hermitian.complexMultiplyZeroLeft vx
        | Hermitian.complexMultiplyOneLeft vy
        | Hermitian.complexMultiplyZeroLeft vz
        | Algebra.complexAddZeroLeft vy
        | Algebra.complexAddZeroRight vy = refl

basisZRealProbe :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complexRealPart (C3.hermitianPairing3 (basisZ F) v)
  ≡ C3.complexRealPart (C3.z v)
basisZRealProbe {F = F} (C3.complex3 vx vy vz)
  rewrite Hermitian.complexConjugateZero F
        | Hermitian.complexConjugateOne F
        | Hermitian.complexMultiplyZeroLeft vx
        | Hermitian.complexMultiplyZeroLeft vy
        | Hermitian.complexMultiplyOneLeft vz
        | Algebra.complexAddZeroLeft (C3.complexZero F)
        | Algebra.complexAddZeroLeft vz = refl

imaginaryBasisXRealProbe :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complexRealPart (C3.hermitianPairing3 (imaginaryBasisX F) v)
  ≡ imaginaryPartEmbed F (C3.x v)
imaginaryBasisXRealProbe {F = F} (C3.complex3 vx vy vz)
  rewrite complexConjugateIIsMinusI F
        | Hermitian.complexConjugateZero F
        | Hermitian.complexMultiplyZeroLeft vy
        | Hermitian.complexMultiplyZeroLeft vz
        | Algebra.complexAddZeroRight
            (C3.complexMultiply (C3.complexNegate (C3.complexI F)) vx)
        | complexRealPartMinusIMultiply vx = refl

imaginaryBasisYRealProbe :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complexRealPart (C3.hermitianPairing3 (imaginaryBasisY F) v)
  ≡ imaginaryPartEmbed F (C3.y v)
imaginaryBasisYRealProbe {F = F} (C3.complex3 vx vy vz)
  rewrite Hermitian.complexConjugateZero F
        | complexConjugateIIsMinusI F
        | Hermitian.complexMultiplyZeroLeft vx
        | Hermitian.complexMultiplyZeroLeft vz
        | Algebra.complexAddZeroLeft
            (C3.complexMultiply (C3.complexNegate (C3.complexI F)) vy)
        | Algebra.complexAddZeroRight
            (C3.complexMultiply (C3.complexNegate (C3.complexI F)) vy)
        | complexRealPartMinusIMultiply vy = refl

imaginaryBasisZRealProbe :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complexRealPart (C3.hermitianPairing3 (imaginaryBasisZ F) v)
  ≡ imaginaryPartEmbed F (C3.z v)
imaginaryBasisZRealProbe {F = F} (C3.complex3 vx vy vz)
  rewrite Hermitian.complexConjugateZero F
        | complexConjugateIIsMinusI F
        | Hermitian.complexMultiplyZeroLeft vx
        | Hermitian.complexMultiplyZeroLeft vy
        | Algebra.complexAddZeroLeft (C3.complexZero F)
        | Algebra.complexAddZeroLeft
            (C3.complexMultiply (C3.complexNegate (C3.complexI F)) vz)
        | complexRealPartMinusIMultiply vz = refl

realHermitianTestsSeparateVectors :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  (∀ test →
    C3.complexRealPart (C3.hermitianPairing3 test u)
    ≡ C3.complexRealPart (C3.hermitianPairing3 test v)) →
  u ≡ v
realHermitianTestsSeparateVectors {F = F}
  u@(C3.complex3 ux uy uz)
  v@(C3.complex3 vx vy vz)
  separates =
  cong₃ C3.complex3 xEqual yEqual zEqual
  where
    xRealPart : C3.complexRealPart ux ≡ C3.complexRealPart vx
    xRealPart =
      trans (sym (basisXRealProbe u))
        (trans (separates (basisX F)) (basisXRealProbe v))

    xImaginaryPart : imaginaryPartEmbed F ux ≡ imaginaryPartEmbed F vx
    xImaginaryPart =
      trans (sym (imaginaryBasisXRealProbe u))
        (trans (separates (imaginaryBasisX F))
          (imaginaryBasisXRealProbe v))

    xEqual : ux ≡ vx
    xEqual = Algebra.cong₂ C3.complex
      (cong C3.real xRealPart)
      (cong C3.real xImaginaryPart)

    yRealPart : C3.complexRealPart uy ≡ C3.complexRealPart vy
    yRealPart =
      trans (sym (basisYRealProbe u))
        (trans (separates (basisY F)) (basisYRealProbe v))

    yImaginaryPart : imaginaryPartEmbed F uy ≡ imaginaryPartEmbed F vy
    yImaginaryPart =
      trans (sym (imaginaryBasisYRealProbe u))
        (trans (separates (imaginaryBasisY F))
          (imaginaryBasisYRealProbe v))

    yEqual : uy ≡ vy
    yEqual = Algebra.cong₂ C3.complex
      (cong C3.real yRealPart)
      (cong C3.real yImaginaryPart)

    zRealPart : C3.complexRealPart uz ≡ C3.complexRealPart vz
    zRealPart =
      trans (sym (basisZRealProbe u))
        (trans (separates (basisZ F)) (basisZRealProbe v))

    zImaginaryPart : imaginaryPartEmbed F uz ≡ imaginaryPartEmbed F vz
    zImaginaryPart =
      trans (sym (imaginaryBasisZRealProbe u))
        (trans (separates (imaginaryBasisZ F))
          (imaginaryBasisZRealProbe v))

    zEqual : uz ≡ vz
    zEqual = Algebra.cong₂ C3.complex
      (cong C3.real zRealPart)
      (cong C3.real zImaginaryPart)

complex3RealHermitianNondegeneracy :
  ∀ {r} (F : C3.RealField r) → Adjoints.RealHermitianNondegeneracy F
complex3RealHermitianNondegeneracy F = record
  { realHermitianTestsSeparateVectors = realHermitianTestsSeparateVectors }

pairingRepresentativesUnique :
  ∀ {r} {F : C3.RealField r}
    (first second : C3.Complex3 F) →
  (∀ test →
    C3.complexRealPart (C3.hermitianPairing3 test first)
    ≡ C3.complexRealPart (C3.hermitianPairing3 test second)) →
  first ≡ second
pairingRepresentativesUnique = realHermitianTestsSeparateVectors

concreteRealHermitianNondegeneracyClosed : Bool
concreteRealHermitianNondegeneracyClosed = true

concreteRealHermitianNondegeneracyClosedIsTrue :
  concreteRealHermitianNondegeneracyClosed ≡ true
concreteRealHermitianNondegeneracyClosedIsTrue = refl

concreteVectorAdjointUniquenessClosed : Bool
concreteVectorAdjointUniquenessClosed = false

concreteVectorAdjointUniquenessClosedIsFalse :
  concreteVectorAdjointUniquenessClosed ≡ false
concreteVectorAdjointUniquenessClosedIsFalse = refl
