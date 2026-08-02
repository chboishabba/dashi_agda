module DASHI.Physics.Closure.NSTriadKNLiteralVectorAdjointPairingTheorems where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Jean Leray; Marco Cannone;
-- DASHI repository contributors.
-- Title: "Literal real-Hermitian pairing identities for the two periodic
-- Navier-Stokes vector partial adjoints".
-- Venue/year: Advances in Mathematics 165 (2002), 124--164; Handbook of
-- Mathematical Fluid Dynamics, Volume 3, 2005; DASHI formal development,
-- 2026.
-- DOI: 10.1006/aima.2001.2028 for Grafakos--Torres,
-- "Multilinear Calderon--Zygmund Theory";
-- 10.1016/S1874-5792(05)80006-0 for Marco Cannone,
-- "Harmonic Analysis Tools for Solving the Incompressible Navier-Stokes
-- Equations"; repository-original Fourier identities have no DOI.
-- Uses: the exact signed coefficient -i P_k[(u_p dot q)u_q], the literal
-- vector candidates, Hermitian scale/add/conjugation laws, exact Leray
-- self-adjointness, and transverse projector fixed points.
-- Relationship: proves the direct first and second partial-adjoint identities
-- on the physical transverse test spaces.  The ordered-pair first adjoint is
-- obtained by combining the direct identity with the swapped term, which is
-- definitionally the second-adjoint formula after role rotation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLerayAlgebraProgram as LerayFixed
import DASHI.Physics.Closure.NSTriadKNLeraySelfAdjointness as LeraySelfAdjoint
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNGrafakosTorresExactTransposeSymbols as Transpose
import DASHI.Physics.Closure.NSTriadKNLiteralVectorAdjointCandidates as Adjoints

complex3LerayTestReduction :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Signed.LerayTestReduction (C3.complex3VelocityGalerkinLaws F E I)
complex3LerayTestReduction F E I = record
  { TransverseAt = Helical.Transverse E
  ; transverseProjectionFixed = LerayFixed.lerayFixesTransverse E I
  ; projectionSelfAdjoint =
      λ k test value → sym (LeraySelfAdjoint.leraySelfAdjoint E I k test value)
  }

complexConjugateMinusImaginary :
  ∀ {r} (F : C3.RealField r) →
  C3.complexConjugate (Adjoints.minusImaginary F) ≡ C3.complexI F
complexConjugateMinusImaginary F
  rewrite C3.negateZero F
        | C3.negateInvolutive F (C3.one F) = refl

conjugateDotAgainstRealMode :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (mode : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.complexConjugate
    (C3.bilinearDot3 value (C3.modeVector E mode))
  ≡ C3.hermitianPairing3 value (C3.modeVector E mode)
conjugateDotAgainstRealMode E mode value =
  trans
    (cong C3.complexConjugate
      (Algebra.bilinearDot3Commutative value (C3.modeVector E mode)))
    (trans
      (cong C3.complexConjugate
        (sym (Hermitian.realModePairingIsBilinear E mode value)))
      (Hermitian.hermitianPairingConjugateSymmetric
        (C3.modeVector E mode) value))

outputPairingReduced :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E k testK →
  C3.hermitianPairing3 testK
    (Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I)
      k p q uP uQ)
  ≡
  C3.complexMultiply (Adjoints.minusImaginary F)
    (C3.complexMultiply
      (C3.bilinearDot3 uP (C3.modeVector E q))
      (C3.hermitianPairing3 testK uQ))
outputPairingReduced {F = F} E I k p q uP uQ testK transverseK =
  trans
    (Scaling.hermitianPairingScaleRight
      (Adjoints.minusImaginary F)
      testK
      (C3.lerayProject3 E I k
        (C3.complex3Scale
          (C3.bilinearDot3 uP (C3.modeVector E q))
          uQ)))
    (trans
      (cong (C3.complexMultiply (Adjoints.minusImaginary F))
        (Signed.removeLerayFromTransverseTest
          (complex3LerayTestReduction F E I)
          k testK
          (C3.complex3Scale
            (C3.bilinearDot3 uP (C3.modeVector E q))
            uQ)
          transverseK))
      (cong (C3.complexMultiply (Adjoints.minusImaginary F))
        (Scaling.hermitianPairingScaleRight
          (C3.bilinearDot3 uP (C3.modeVector E q))
          testK uQ)))

directFirstCandidatePairingReduced :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (p q : Z3.FourierMode)
    (testK uQ uP : C3.Complex3 F) →
  Helical.Transverse E p uP →
  C3.hermitianPairing3 uP
    (Adjoints.directFirstAdjointVector E I p q testK uQ)
  ≡
  C3.complexMultiply
    (Adjoints.directFirstAdjointScalar uQ testK)
    (C3.hermitianPairing3 uP (C3.modeVector E q))
directFirstCandidatePairingReduced E I p q testK uQ uP transverseP =
  trans
    (sym (LeraySelfAdjoint.leraySelfAdjoint E I p uP
      (C3.complex3Scale
        (Adjoints.directFirstAdjointScalar uQ testK)
        (C3.modeVector E q))))
    (trans
      (cong
        (λ first → C3.hermitianPairing3 first
          (C3.complex3Scale
            (Adjoints.directFirstAdjointScalar uQ testK)
            (C3.modeVector E q)))
        (LerayFixed.lerayFixesTransverse E I p uP transverseP))
      (Scaling.hermitianPairingScaleRight
        (Adjoints.directFirstAdjointScalar uQ testK)
        uP
        (C3.modeVector E q)))

secondCandidatePairingReduced :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (q : Z3.FourierMode)
    (uP testK uQ : C3.Complex3 F) →
  Helical.Transverse E q uQ →
  C3.hermitianPairing3 uQ
    (Adjoints.secondAdjointVector E I q uP testK)
  ≡
  C3.complexMultiply
    (Adjoints.secondAdjointScalar uP (C3.modeVector E q))
    (C3.hermitianPairing3 uQ testK)
secondCandidatePairingReduced E I q uP testK uQ transverseQ =
  trans
    (sym (LeraySelfAdjoint.leraySelfAdjoint E I q uQ
      (C3.complex3Scale
        (Adjoints.secondAdjointScalar uP (C3.modeVector E q))
        testK)))
    (trans
      (cong
        (λ first → C3.hermitianPairing3 first
          (C3.complex3Scale
            (Adjoints.secondAdjointScalar uP (C3.modeVector E q))
            testK))
        (LerayFixed.lerayFixesTransverse E I q uQ transverseQ))
      (Scaling.hermitianPairingScaleRight
        (Adjoints.secondAdjointScalar uP (C3.modeVector E q))
        uQ testK))

firstCandidateEqualsConjugateReducedOutput :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (q : Z3.FourierMode)
    (uP uQ testK : C3.Complex3 F) →
  C3.complexMultiply
    (Adjoints.directFirstAdjointScalar uQ testK)
    (C3.hermitianPairing3 uP (C3.modeVector E q))
  ≡
  C3.complexConjugate
    (C3.complexMultiply (Adjoints.minusImaginary F)
      (C3.complexMultiply
        (C3.bilinearDot3 uP (C3.modeVector E q))
        (C3.hermitianPairing3 testK uQ)))
firstCandidateEqualsConjugateReducedOutput {F = F} E q uP uQ testK =
  trans
    (Scaling.complexMultiplyAssociative
      (C3.complexI F)
      (C3.hermitianPairing3 uQ testK)
      (C3.hermitianPairing3 uP (C3.modeVector E q)))
    (trans
      (cong (C3.complexMultiply (C3.complexI F))
        (Algebra.complexMultiplyCommutative
          (C3.hermitianPairing3 uQ testK)
          (C3.hermitianPairing3 uP (C3.modeVector E q))))
      (sym
        (trans
          (Hermitian.complexConjugateMultiply
            (Adjoints.minusImaginary F)
            (C3.complexMultiply
              (C3.bilinearDot3 uP (C3.modeVector E q))
              (C3.hermitianPairing3 testK uQ)))
          (Algebra.cong₂ C3.complexMultiply
            (complexConjugateMinusImaginary F)
            (trans
              (Hermitian.complexConjugateMultiply
                (C3.bilinearDot3 uP (C3.modeVector E q))
                (C3.hermitianPairing3 testK uQ))
              (Algebra.cong₂ C3.complexMultiply
                (conjugateDotAgainstRealMode E q uP)
                (Hermitian.hermitianPairingConjugateSymmetric testK uQ)))))))

secondCandidateEqualsConjugateReducedOutput :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (q : Z3.FourierMode)
    (uP uQ testK : C3.Complex3 F) →
  C3.complexMultiply
    (Adjoints.secondAdjointScalar uP (C3.modeVector E q))
    (C3.hermitianPairing3 uQ testK)
  ≡
  C3.complexConjugate
    (C3.complexMultiply (Adjoints.minusImaginary F)
      (C3.complexMultiply
        (C3.bilinearDot3 uP (C3.modeVector E q))
        (C3.hermitianPairing3 testK uQ)))
secondCandidateEqualsConjugateReducedOutput {F = F} E q uP uQ testK =
  trans
    (cong
      (C3.complexMultiply
        (C3.complexConjugate
          (C3.complexMultiply
            (Adjoints.minusImaginary F)
            (C3.bilinearDot3 uP (C3.modeVector E q)))))
      (sym (Hermitian.hermitianPairingConjugateSymmetric testK uQ)))
    (trans
      (sym (Hermitian.complexConjugateMultiply
        (C3.complexMultiply
          (Adjoints.minusImaginary F)
          (C3.bilinearDot3 uP (C3.modeVector E q)))
        (C3.hermitianPairing3 testK uQ)))
      (cong C3.complexConjugate
        (Scaling.complexMultiplyAssociative
          (Adjoints.minusImaginary F)
          (C3.bilinearDot3 uP (C3.modeVector E q))
          (C3.hermitianPairing3 testK uQ))))

firstVectorAdjointPairingIdentity :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E k testK →
  Helical.Transverse E p uP →
  C3.complexRealPart
    (C3.hermitianPairing3 uP
      (Adjoints.directFirstAdjointVector E I p q testK uQ))
  ≡ Transpose.outputTrilinearSymbol F E I k p q uP uQ testK
firstVectorAdjointPairingIdentity {F = F}
  E I k p q uP uQ testK transverseK transverseP =
  trans
    (cong C3.complexRealPart
      (directFirstCandidatePairingReduced E I p q testK uQ uP transverseP))
    (trans
      (cong C3.complexRealPart
        (firstCandidateEqualsConjugateReducedOutput E q uP uQ testK))
      (trans
        (Hermitian.complexRealPartConjugateInvariant
          (C3.complexMultiply (Adjoints.minusImaginary F)
            (C3.complexMultiply
              (C3.bilinearDot3 uP (C3.modeVector E q))
              (C3.hermitianPairing3 testK uQ))))
        (cong C3.complexRealPart
          (sym (outputPairingReduced E I k p q uP uQ testK transverseK)))))

secondVectorAdjointPairingIdentity :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E k testK →
  Helical.Transverse E q uQ →
  C3.complexRealPart
    (C3.hermitianPairing3 uQ
      (Adjoints.secondAdjointVector E I q uP testK))
  ≡ Transpose.outputTrilinearSymbol F E I k p q uP uQ testK
secondVectorAdjointPairingIdentity {F = F}
  E I k p q uP uQ testK transverseK transverseQ =
  trans
    (cong C3.complexRealPart
      (secondCandidatePairingReduced E I q uP testK uQ transverseQ))
    (trans
      (cong C3.complexRealPart
        (secondCandidateEqualsConjugateReducedOutput E q uP uQ testK))
      (trans
        (Hermitian.complexRealPartConjugateInvariant
          (C3.complexMultiply (Adjoints.minusImaginary F)
            (C3.complexMultiply
              (C3.bilinearDot3 uP (C3.modeVector E q))
              (C3.hermitianPairing3 testK uQ))))
        (cong C3.complexRealPart
          (sym (outputPairingReduced E I k p q uP uQ testK transverseK)))))

swappedFirstAdjointIsSecondAdjoint :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (p : Z3.FourierMode)
    (testK uQ : C3.Complex3 F) →
  Adjoints.swappedFirstAdjointVector E I p testK uQ
  ≡ Adjoints.secondAdjointVector E I p uQ testK
swappedFirstAdjointIsSecondAdjoint E I p testK uQ = refl

complexRealPartAdd :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexRealPart (C3.complexAdd a b)
  ≡ C3.complexAdd (C3.complexRealPart a) (C3.complexRealPart b)
complexRealPartAdd {F = F}
  (C3.complex ar ai) (C3.complex br bi)
  rewrite C3.addZeroLeft F (C3.zero F) = refl

orderedPairFirstAdjointPairingIdentity :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E k testK →
  Helical.Transverse E p uP →
  C3.complexRealPart
    (C3.hermitianPairing3 uP
      (Adjoints.symmetrisedFirstAdjointVector E I p q testK uQ))
  ≡
  Signed.testedOrderedPairCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)
    k p q uP uQ testK
orderedPairFirstAdjointPairingIdentity {F = F}
  E I k p q uP uQ testK transverseK transverseP =
  trans
    (cong C3.complexRealPart
      (Additive.hermitianPairingAddRight uP
        (Adjoints.directFirstAdjointVector E I p q testK uQ)
        (Adjoints.swappedFirstAdjointVector E I p testK uQ)))
    (trans
      (complexRealPartAdd
        (C3.hermitianPairing3 uP
          (Adjoints.directFirstAdjointVector E I p q testK uQ))
        (C3.hermitianPairing3 uP
          (Adjoints.swappedFirstAdjointVector E I p testK uQ)))
      (trans
        (Algebra.cong₂ C3.complexAdd
          (firstVectorAdjointPairingIdentity
            E I k p q uP uQ testK transverseK transverseP)
          (trans
            (cong
              (λ candidate → C3.complexRealPart
                (C3.hermitianPairing3 uP candidate))
              (swappedFirstAdjointIsSecondAdjoint E I p testK uQ))
            (secondVectorAdjointPairingIdentity
              E I k q p uQ uP testK transverseK transverseP)))
        (trans
          (sym (complexRealPartAdd
            (C3.hermitianPairing3 testK
              (Signed.orderedVelocityInteraction
                (C3.complex3VelocityGalerkinLaws F E I)
                k p q uP uQ))
            (C3.hermitianPairing3 testK
              (Signed.orderedVelocityInteraction
                (C3.complex3VelocityGalerkinLaws F E I)
                k q p uQ uP))))
          (cong C3.complexRealPart
            (sym (Additive.hermitianPairingAddRight testK
              (Signed.orderedVelocityInteraction
                (C3.complex3VelocityGalerkinLaws F E I)
                k p q uP uQ)
              (Signed.orderedVelocityInteraction
                (C3.complex3VelocityGalerkinLaws F E I)
                k q p uQ uP)))))))

literalDirectAndSecondPairingTheoremsClosed : Bool
literalDirectAndSecondPairingTheoremsClosed = true

literalDirectAndSecondPairingTheoremsClosedIsTrue :
  literalDirectAndSecondPairingTheoremsClosed ≡ true
literalDirectAndSecondPairingTheoremsClosedIsTrue = refl

orderedPairFirstAdjointPairingTheoremClosed : Bool
orderedPairFirstAdjointPairingTheoremClosed = true

orderedPairFirstAdjointPairingTheoremClosedIsTrue :
  orderedPairFirstAdjointPairingTheoremClosed ≡ true
orderedPairFirstAdjointPairingTheoremClosedIsTrue = refl

ambientVectorAdjointUniquenessFromPhysicalTestsClosed : Bool
ambientVectorAdjointUniquenessFromPhysicalTestsClosed = false

ambientVectorAdjointUniquenessFromPhysicalTestsClosedIsFalse :
  ambientVectorAdjointUniquenessFromPhysicalTestsClosed ≡ false
ambientVectorAdjointUniquenessFromPhysicalTestsClosedIsFalse = refl
