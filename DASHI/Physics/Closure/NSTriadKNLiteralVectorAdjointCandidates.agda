module DASHI.Physics.Closure.NSTriadKNLiteralVectorAdjointCandidates where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; DASHI repository contributors.
-- Title: "Literal vector-valued partial-adjoint candidates for the periodic
-- Navier--Stokes triad coefficient".
-- Venue/year: Grafakos--Torres transpose framework and DASHI formal
-- development, 2026.
-- DOI: 10.1006/aima.2001.2028 for the general transpose framework;
-- not applicable for the repository-original Fourier formulas.
-- Uses: the exact signed coefficient -i P_k[(u_p dot q)u_q], the convention
-- that hermitianPairing3 conjugates its first argument, and real self-adjoint
-- Leray projections.
-- Relationship: defines the literal T*1 and T*2 vectors and the full
-- ordered-pair first adjoint.  A separate exact finite verifier checks the
-- polynomial pairing identities.  Agda-level uniqueness still requires a
-- nondegenerate real-Hermitian pairing law for the selected nontrivial field.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

minusImaginary :
  ∀ {r} (F : C3.RealField r) → C3.Complex F
minusImaginary F = C3.complexNegate (C3.complexI F)

directFirstAdjointScalar :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex F
directFirstAdjointScalar {F = F} uQ testK =
  C3.complexMultiply
    (C3.complexI F)
    (C3.hermitianPairing3 uQ testK)

directFirstAdjointVector :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F
directFirstAdjointVector {F = F} E I p q testK uQ =
  C3.lerayProject3 E I p
    (C3.complex3Scale
      (C3.complexMultiply
        (C3.complexI F)
        (C3.hermitianPairing3 uQ testK))
      (C3.modeVector E q))

secondAdjointScalar :
  ∀ {r} {F : C3.RealField r}
    (uP : C3.Complex3 F)
    (qVector : C3.Complex3 F) →
  C3.Complex F
secondAdjointScalar {F = F} uP qVector =
  C3.complexConjugate
    (C3.complexMultiply
      (minusImaginary F)
      (C3.bilinearDot3 uP qVector))

secondAdjointVector :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F
secondAdjointVector E I q uP testK =
  C3.lerayProject3 E I q
    (C3.complex3Scale
      (secondAdjointScalar uP (C3.modeVector E q))
      testK)

swappedFirstAdjointScalar :
  ∀ {r} {F : C3.RealField r}
    (uQ : C3.Complex3 F)
    (pVector : C3.Complex3 F) →
  C3.Complex F
swappedFirstAdjointScalar {F = F} uQ pVector =
  C3.complexConjugate
    (C3.complexMultiply
      (minusImaginary F)
      (C3.bilinearDot3 uQ pVector))

swappedFirstAdjointVector :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F
swappedFirstAdjointVector E I p testK uQ =
  C3.lerayProject3 E I p
    (C3.complex3Scale
      (swappedFirstAdjointScalar uQ (C3.modeVector E p))
      testK)

symmetrisedFirstAdjointVector :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F
symmetrisedFirstAdjointVector E I p q testK uQ =
  C3.complex3Add
    (directFirstAdjointVector E I p q testK uQ)
    (swappedFirstAdjointVector E I p testK uQ)

record VectorAdjointPairingCutset
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    complexMultiplyAssociative : Set r
    conjugateMultiplicationReverses : Set r
    hermitianPairingConjugateSymmetric : Set r
    hermitianPairingScaleRight : Set r
    bilinearDotAgainstRealMode : Set r
    realPartConjugateInvariant : Set r

    lerayProjectionSelfAdjoint : Set r
    outputTransverseTestFixed : Set r
    leftTransverseTestFixed : Set r
    rightTransverseTestFixed : Set r

    directFirstAdjointPairingIdentity : Set r
    swappedFirstAdjointPairingIdentity : Set r
    secondAdjointPairingIdentity : Set r
    symmetrisedFirstAdjointPairingIdentity : Set r

open VectorAdjointPairingCutset public

record RealHermitianNondegeneracy
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    realHermitianTestsSeparateVectors :
      ∀ u v →
      (∀ test →
        C3.complexRealPart (C3.hermitianPairing3 test u)
        ≡
        C3.complexRealPart (C3.hermitianPairing3 test v)) →
      u ≡ v

open RealHermitianNondegeneracy public

record VectorAdjointUniquenessCutset
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    fieldIsNontrivial : Set r
    pairingNondegeneracy : RealHermitianNondegeneracy F
    firstVectorTransposeUnique : Set r
    secondVectorTransposeUnique : Set r

open VectorAdjointUniquenessCutset public

literalVectorAdjointCandidatesDefined : Bool
literalVectorAdjointCandidatesDefined = true

literalVectorAdjointCandidatesDefinedIsTrue :
  literalVectorAdjointCandidatesDefined ≡ true
literalVectorAdjointCandidatesDefinedIsTrue = refl

orderedPairFirstAdjointFormulaDefined : Bool
orderedPairFirstAdjointFormulaDefined = true

orderedPairFirstAdjointFormulaDefinedIsTrue :
  orderedPairFirstAdjointFormulaDefined ≡ true
orderedPairFirstAdjointFormulaDefinedIsTrue = refl

exactFiniteVectorAdjointPairingAuditPassed : Bool
exactFiniteVectorAdjointPairingAuditPassed = true

exactFiniteVectorAdjointPairingAuditPassedIsTrue :
  exactFiniteVectorAdjointPairingAuditPassed ≡ true
exactFiniteVectorAdjointPairingAuditPassedIsTrue = refl

agdaVectorAdjointPairingTheoremsClosed : Bool
agdaVectorAdjointPairingTheoremsClosed = false

agdaVectorAdjointPairingTheoremsClosedIsFalse :
  agdaVectorAdjointPairingTheoremsClosed ≡ false
agdaVectorAdjointPairingTheoremsClosedIsFalse = refl

vectorAdjointUniquenessClosed : Bool
vectorAdjointUniquenessClosed = false

vectorAdjointUniquenessClosedIsFalse :
  vectorAdjointUniquenessClosed ≡ false
vectorAdjointUniquenessClosedIsFalse = refl
