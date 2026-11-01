module DASHI.Physics.Closure.NSTriadKNOrderedInteractionRealityRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Prove the local nonlinear Fourier-reality law for the repository's literal
-- ordered velocity interaction
--
--   - i P_k [ (u_p dot q) u_q ].
--
-- Under u_-p = conjugate(u_p), u_-q = conjugate(u_q), the wavevector q and
-- output k both change sign.  The q sign supplies one minus sign inside the
-- bilinear dot; the Leray projector is even in k and commutes with complex
-- conjugation; the remaining minus combines with the outer -i exactly so that
--
--   N_{-k,-p,-q}(conj u_p,conj u_q)
--     = conjugate(N_{k,p,q}(u_p,u_q)).
--
-- This closes the genuinely nonlinear *single-triad* reality calculation.
-- The finite output-fibre reindexing needed to turn it into the full summed
-- `projectedNonlinearity(-k)=conjugate(projectedNonlinearity(k))` theorem is
-- left as a separate finite permutation theorem, not hidden in this module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans; module ≡-Reasoning)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3RealityLawsRound35Exact as RealityLaws

complexNegateAdd :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) →
  C3.complexNegate (C3.complexAdd a b)
  ≡ C3.complexAdd (C3.complexNegate a) (C3.complexNegate b)
complexNegateAdd {F = F}
    (C3.complex ar ai) (C3.complex br bi) =
  Algebra.complexExt
    (R.solve 2
      (λ x y → R.⊝ (x R.⊕ y) R.⊜ ((R.⊝ x) R.⊕ (R.⊝ y)))
      refl ar br)
    (R.solve 2
      (λ x y → R.⊝ (x R.⊕ y) R.⊜ ((R.⊝ x) R.⊕ (R.⊝ y)))
      refl ai bi)
  where module R = Algebra.Solver F

complex3NegateAdd :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  C3.complex3Negate (C3.complex3Add u v)
  ≡ C3.complex3Add (C3.complex3Negate u) (C3.complex3Negate v)
complex3NegateAdd
    (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (complexNegateAdd ux vx)
    (complexNegateAdd uy vy)
    (complexNegateAdd uz vz)

complex3NegateInvolutive :
  ∀ {r} {F : C3.RealField r}
    (value : C3.Complex3 F) →
  C3.complex3Negate (C3.complex3Negate value) ≡ value
complex3NegateInvolutive (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (Algebra.complexNegateInvolutive vx)
    (Algebra.complexNegateInvolutive vy)
    (Algebra.complexNegateInvolutive vz)

complex3SubtractDoubleNegate :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex3 F) →
  C3.complex3Subtract
    (C3.complex3Negate left)
    (C3.complex3Negate right)
  ≡ C3.complex3Negate (C3.complex3Subtract left right)
complex3SubtractDoubleNegate left right =
  trans
    (cong
      (C3.complex3Add (C3.complex3Negate left))
      (complex3NegateInvolutive right))
    (sym
      (trans
        (complex3NegateAdd left (C3.complex3Negate right))
        (cong
          (C3.complex3Add (C3.complex3Negate left))
          (complex3NegateInvolutive right))))

lerayCorrectionNegate :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.complex3Scale
    (C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I k))
      (C3.bilinearDot3
        (C3.modeVector E k)
        (C3.complex3Negate value)))
    (C3.modeVector E k)
  ≡ C3.complex3Negate
      (C3.complex3Scale
        (C3.complexMultiply
          (C3.realEmbed F (C3.inverseNormSquared I k))
          (C3.bilinearDot3 (C3.modeVector E k) value))
        (C3.modeVector E k))
lerayCorrectionNegate {F = F} E I k value =
  let
    realInverse = C3.realEmbed F (C3.inverseNormSquared I k)
    pairing = C3.bilinearDot3 (C3.modeVector E k) value
  in
  trans
    (cong
      (λ dotValue →
        C3.complex3Scale
          (C3.complexMultiply realInverse dotValue)
          (C3.modeVector E k))
      (Algebra.bilinearDotNegateRight (C3.modeVector E k) value))
    (trans
      (cong
        (λ scalar → C3.complex3Scale scalar (C3.modeVector E k))
        (Algebra.complexNegateMultiplyRight realInverse pairing))
      (sym
        (Algebra.complex3NegateScale
          (C3.complexMultiply realInverse pairing)
          (C3.modeVector E k))))

lerayProjectNegate :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.lerayProject3 E I k (C3.complex3Negate value)
  ≡ C3.complex3Negate (C3.lerayProject3 E I k value)
lerayProjectNegate E I k value =
  trans
    (cong
      (C3.complex3Subtract (C3.complex3Negate value))
      (lerayCorrectionNegate E I k value))
    (complex3SubtractDoubleNegate value correction)
  where
  correction =
    C3.complex3Scale
      (C3.complexMultiply
        (C3.realEmbed _ (C3.inverseNormSquared I k))
        (C3.bilinearDot3 (C3.modeVector E k) value))
      (C3.modeVector E k)

conjugatedModeDot :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (q : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.bilinearDot3
    (C3.complex3Conjugate value)
    (C3.modeVector E q)
  ≡ C3.complexConjugate
      (C3.bilinearDot3 value (C3.modeVector E q))
conjugatedModeDot E q value =
  trans
    (cong
      (C3.bilinearDot3 (C3.complex3Conjugate value))
      (sym (C3.modeVectorConjugate E q)))
    (Algebra.bilinearDotConjugate value (C3.modeVector E q))

conjugatedNegatedModeDot :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (q : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.bilinearDot3
    (C3.complex3Conjugate value)
    (C3.modeVector E (Z3.negateMode q))
  ≡ C3.complexNegate
      (C3.complexConjugate
        (C3.bilinearDot3 value (C3.modeVector E q)))
conjugatedNegatedModeDot E q value =
  trans
    (cong
      (C3.bilinearDot3 (C3.complex3Conjugate value))
      (C3.modeVectorNegation E q))
    (trans
      (Algebra.bilinearDotNegateRight
        (C3.complex3Conjugate value) (C3.modeVector E q))
      (cong C3.complexNegate (conjugatedModeDot E q value)))

scaleNegativeConjugate :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (value : C3.Complex3 F) →
  C3.complex3Scale
    (C3.complexNegate (C3.complexConjugate scalar))
    (C3.complex3Conjugate value)
  ≡ C3.complex3Negate
      (C3.complex3Conjugate (C3.complex3Scale scalar value))
scaleNegativeConjugate scalar value =
  trans
    (sym
      (Algebra.complex3NegateScale
        (C3.complexConjugate scalar)
        (C3.complex3Conjugate value)))
    (cong C3.complex3Negate
      (sym (Scaling.complex3ConjugateScale scalar value)))

rawInteractionInputReality :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F) →
  C3.complex3Scale
    (C3.bilinearDot3
      (C3.complex3Conjugate uP)
      (C3.modeVector E (Z3.negateMode q)))
    (C3.complex3Conjugate uQ)
  ≡ C3.complex3Negate
      (C3.complex3Conjugate
        (C3.complex3Scale
          (C3.bilinearDot3 uP (C3.modeVector E q))
          uQ))
rawInteractionInputReality E q uP uQ =
  trans
    (cong
      (λ scalar →
        C3.complex3Scale scalar (C3.complex3Conjugate uQ))
      (conjugatedNegatedModeDot E q uP))
    (scaleNegativeConjugate
      (C3.bilinearDot3 uP (C3.modeVector E q)) uQ)

projectedRawInteractionReality :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F) →
  C3.lerayProject3 E I (Z3.negateMode k)
    (C3.complex3Scale
      (C3.bilinearDot3
        (C3.complex3Conjugate uP)
        (C3.modeVector E (Z3.negateMode q)))
      (C3.complex3Conjugate uQ))
  ≡ C3.complex3Negate
      (C3.complex3Conjugate
        (C3.lerayProject3 E I k
          (C3.complex3Scale
            (C3.bilinearDot3 uP (C3.modeVector E q)) uQ)))
projectedRawInteractionReality E I k q uP uQ =
  let
    raw =
      C3.complex3Scale
        (C3.bilinearDot3 uP (C3.modeVector E q)) uQ
  in
  trans
    (RealityLaws.lerayProjectModeEven E I k _)
    (trans
      (cong (C3.lerayProject3 E I k)
        (rawInteractionInputReality E q uP uQ))
      (trans
        (lerayProjectNegate E I k (C3.complex3Conjugate raw))
        (cong C3.complex3Negate
          (RealityLaws.lerayProjectConjugation E I k raw))))

complexConjugateI :
  ∀ {r} (F : C3.RealField r) →
  C3.complexConjugate (C3.complexI F)
  ≡ C3.complexNegate (C3.complexI F)
complexConjugateI F rewrite C3.negateZero F = refl

conjugateMinusImaginary :
  ∀ {r} (F : C3.RealField r) →
  C3.complexConjugate
    (C3.complexNegate (C3.complexI F))
  ≡ C3.complexI F
conjugateMinusImaginary F =
  trans
    (Algebra.complexConjugateNegate (C3.complexI F))
    (trans
      (cong C3.complexNegate (complexConjugateI F))
      (Algebra.complexNegateInvolutive (C3.complexI F)))

outerMinusImaginaryReality :
  ∀ {r} {F : C3.RealField r}
    (value : C3.Complex3 F) →
  C3.complex3Scale
    (C3.complexNegate (C3.complexI F))
    (C3.complex3Negate (C3.complex3Conjugate value))
  ≡ C3.complex3Conjugate
      (C3.complex3Scale
        (C3.complexNegate (C3.complexI F)) value)
outerMinusImaginaryReality {F = F} value =
  trans
    (RealityLaws.complex3ScaleDoubleNegate
      (C3.complexI F) (C3.complex3Conjugate value))
    (sym
      (trans
        (Scaling.complex3ConjugateScale
          (C3.complexNegate (C3.complexI F)) value)
        (cong
          (λ scalar → C3.complex3Scale scalar (C3.complex3Conjugate value))
          (conjugateMinusImaginary F))))

orderedVelocityInteractionReality :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F) →
  Signed.orderedVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I)
    (Z3.negateMode k) (Z3.negateMode p) (Z3.negateMode q)
    (C3.complex3Conjugate uP) (C3.complex3Conjugate uQ)
  ≡ C3.complex3Conjugate
      (Signed.orderedVelocityInteraction
        (C3.complex3VelocityGalerkinLaws F E I)
        k p q uP uQ)
orderedVelocityInteractionReality F E I k p q uP uQ =
  trans
    (cong
      (C3.complex3Scale (C3.complexNegate (C3.complexI F)))
      (projectedRawInteractionReality E I k q uP uQ))
    (outerMinusImaginaryReality
      (C3.lerayProject3 E I k
        (C3.complex3Scale
          (C3.bilinearDot3 uP (C3.modeVector E q)) uQ)))

projectedOrderedTermConjugateTriad :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityReality : Reality.RealityCondition (Audit.velocity system))
    (incidence : Physical.PhysicalTriadIncidence) →
  Audit.projectedOrderedTerm system (Symmetry.conjugateTriad incidence)
  ≡ C3.complex3Conjugate (Audit.projectedOrderedTerm system incidence)
projectedOrderedTermConjugateTriad {F = F} {E = E} {I = I}
    system velocityReality incidence
  rewrite velocityReality (Physical.p incidence)
        | velocityReality (Physical.q incidence) =
  orderedVelocityInteractionReality F E I
    (Physical.k incidence)
    (Physical.p incidence)
    (Physical.q incidence)
    (Audit.velocity system (Physical.p incidence))
    (Audit.velocity system (Physical.q incidence))

orderedInteractionRealityClosed : Bool
orderedInteractionRealityClosed = true

summedProjectedNonlinearityRealityConstructed : Bool
summedProjectedNonlinearityRealityConstructed = false

orderedInteractionRealityClosedIsTrue :
  orderedInteractionRealityClosed ≡ true
orderedInteractionRealityClosedIsTrue = refl

summedProjectedNonlinearityRealityConstructedIsFalse :
  summedProjectedNonlinearityRealityConstructed ≡ false
summedProjectedNonlinearityRealityConstructedIsFalse = refl
