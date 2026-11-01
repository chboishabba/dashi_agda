module DASHI.Physics.Closure.NSTriadKNPhysicalTransportCoefficientSkewRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Prove the literal modal identity behind skew-adjoint incompressible
-- transport, rather than merely assuming the physical-space integration by
-- parts slogan.  For a real divergence-free advector coefficient a_m and a
-- resonance
--
--   m + q = k,
--
-- the transport matrix coefficient from q to k is
--
--   c(k,q) = i (q . a_m).
--
-- The reverse coefficient uses the reality partner a_-m = conjugate(a_m):
--
--   c(q,k) = i (k . a_-m).
--
-- Divergence freedom gives m.a_m=0, hence k.a_m=q.a_m.  Reality and the real
-- wavevector then give
--
--   conjugate(c(q,k)) = - c(k,q).
--
-- This is exactly the entrywise condition T*=-T required by Round 40's Com
-- adjoint collapse.  It is proved on the repository's literal Complex3 and
-- integer Fourier carriers with no continuum integration authority.  The
-- final theorem below consumes the repository's actual `RealityCondition` and
-- `DivergenceFreeCondition`, so the coefficient witness cannot be supplied
-- independently of the physical velocity state.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Laws
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit

modeDot :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode →
  C3.Complex3 F →
  C3.Complex F
modeDot E mode value = C3.bilinearDot3 (C3.modeVector E mode) value

modeDotAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (left right : Z3.FourierMode)
    (value : C3.Complex3 F) →
  modeDot E (Z3.addMode left right) value
  ≡ C3.complexAdd (modeDot E left value) (modeDot E right value)
modeDotAdd E left right value =
  trans
    (cong
      (λ wave → C3.bilinearDot3 wave value)
      (Laws.modeVectorAdd E left right))
    (trans
      (Algebra.bilinearDotCommutative
        (C3.complex3Add (C3.modeVector E left) (C3.modeVector E right))
        value)
      (trans
        (Laws.bilinearDot3RightAdd
          value (C3.modeVector E left) (C3.modeVector E right))
        (cong₂ C3.complexAdd
          (Algebra.bilinearDotCommutative value (C3.modeVector E left))
          (Algebra.bilinearDotCommutative value (C3.modeVector E right)))))

resonantDerivativeRelocation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (advector input output : Z3.FourierMode)
    (value : C3.Complex3 F) →
  Z3.addMode advector input ≡ output →
  modeDot E advector value ≡ C3.complexZero F →
  modeDot E output value ≡ modeDot E input value
resonantDerivativeRelocation {F = F}
    E advector input output value resonance divergenceFree =
  trans
    (cong (λ mode → modeDot E mode value) (sym resonance))
    (trans
      (modeDotAdd E advector input value)
      (trans
        (cong
          (λ first → C3.complexAdd first (modeDot E input value))
          divergenceFree)
        (Algebra.complexAddZeroLeft (modeDot E input value))))

conjugateImaginaryUnitIsNegative :
  ∀ {r} (F : C3.RealField r) →
  C3.complexConjugate (C3.complexI F)
  ≡ C3.complexNegate (C3.complexI F)
conjugateImaginaryUnitIsNegative F
  rewrite C3.negateZero F = refl

conjugateModeDotConjugateValue :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (mode : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.complexConjugate
    (modeDot E mode (C3.complex3Conjugate value))
  ≡ modeDot E mode value
conjugateModeDotConjugateValue E mode value =
  let
    first :
      modeDot E mode (C3.complex3Conjugate value)
      ≡ C3.complexConjugate (modeDot E mode value)
    first =
      trans
        (cong
          (λ wave → C3.bilinearDot3 wave (C3.complex3Conjugate value))
          (sym (C3.modeVectorConjugate E mode)))
        (Algebra.bilinearDotConjugate (C3.modeVector E mode) value)
  in
  trans
    (cong C3.complexConjugate first)
    (C3.complexConjugateInvolutive (modeDot E mode value))

transportCoefficient :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode →
  C3.Complex3 F →
  C3.Complex F
transportCoefficient {F = F} E derivativeMode advectorCoefficient =
  C3.complexMultiply
    (C3.complexI F)
    (modeDot E derivativeMode advectorCoefficient)

record ResonantRealDivergenceFreeAdvector
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (advector input output : Z3.FourierMode) : Set r where
  field
    coefficient : C3.Complex3 F
    negativeCoefficient : C3.Complex3 F
    resonance : Z3.addMode advector input ≡ output
    divergenceFree :
      modeDot E advector coefficient ≡ C3.complexZero F
    reality :
      negativeCoefficient ≡ C3.complex3Conjugate coefficient

open ResonantRealDivergenceFreeAdvector public

forwardCoefficient :
  ∀ {r F E advector input output} →
  ResonantRealDivergenceFreeAdvector
    {r} {F} E advector input output →
  C3.Complex F
forwardCoefficient {E = E} {input = input} witness =
  transportCoefficient E input (coefficient witness)

reverseCoefficient :
  ∀ {r F E advector input output} →
  ResonantRealDivergenceFreeAdvector
    {r} {F} E advector input output →
  C3.Complex F
reverseCoefficient {E = E} {output = output} witness =
  transportCoefficient E output (negativeCoefficient witness)

physicalTransportCoefficientSkew :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {advector input output : Z3.FourierMode}
    (witness : ResonantRealDivergenceFreeAdvector
      E advector input output) →
  C3.complexConjugate (reverseCoefficient witness)
  ≡ C3.complexNegate (forwardCoefficient witness)
physicalTransportCoefficientSkew {F = F} {E = E}
    {advector} {input} {output} witness =
  let
    relocate :
      modeDot E output (coefficient witness)
      ≡ modeDot E input (coefficient witness)
    relocate = resonantDerivativeRelocation
      E advector input output (coefficient witness)
      (resonance witness) (divergenceFree witness)

    conjugateReverseDot :
      C3.complexConjugate
        (modeDot E output (negativeCoefficient witness))
      ≡ modeDot E output (coefficient witness)
    conjugateReverseDot =
      trans
        (cong
          (λ selected →
            C3.complexConjugate (modeDot E output selected))
          (reality witness))
        (conjugateModeDotConjugateValue E output (coefficient witness))
  in
  trans
    (Algebra.complexConjugateMultiply
      (C3.complexI F)
      (modeDot E output (negativeCoefficient witness)))
    (trans
      (cong₂ C3.complexMultiply
        (conjugateImaginaryUnitIsNegative F)
        conjugateReverseDot)
      (trans
        (cong
          (C3.complexMultiply (C3.complexNegate (C3.complexI F)))
          relocate)
        (Algebra.complexNegateMultiplyLeft
          (C3.complexI F)
          (modeDot E input (coefficient witness)))))

physicalStateAdvectorWitness :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (advector input output : Z3.FourierMode) →
  Z3.addMode advector input ≡ output →
  ResonantRealDivergenceFreeAdvector E advector input output
physicalStateAdvectorWitness {E = E}
    velocity reality divergenceFree advector input output resonance = record
  { coefficient = velocity advector
  ; negativeCoefficient = velocity (Z3.negateMode advector)
  ; resonance = resonance
  ; divergenceFree =
      trans
        (Algebra.bilinearDotCommutative
          (C3.modeVector E advector) (velocity advector))
        (divergenceFree advector)
  ; reality = reality advector
  }

physicalVelocityTransportCoefficientSkew :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  (reality : Audit.RealityCondition velocity) →
  (divergenceFree : Audit.DivergenceFreeCondition E velocity) →
  (advector input output : Z3.FourierMode) →
  (resonance : Z3.addMode advector input ≡ output) →
  C3.complexConjugate
    (transportCoefficient E output
      (velocity (Z3.negateMode advector)))
  ≡ C3.complexNegate
      (transportCoefficient E input (velocity advector))
physicalVelocityTransportCoefficientSkew
    velocity reality divergenceFree advector input output resonance =
  physicalTransportCoefficientSkew
    (physicalStateAdvectorWitness
      velocity reality divergenceFree advector input output resonance)

physicalTransportCoefficientSkewClosed : Bool
physicalTransportCoefficientSkewClosed = true

physicalLowTransportSkewAdjointEntrywiseConstructed : Bool
physicalLowTransportSkewAdjointEntrywiseConstructed = true

physicalLowTransportGlobalMatrixSkewAdjointConstructed : Bool
physicalLowTransportGlobalMatrixSkewAdjointConstructed = false

physicalTransportCoefficientSkewClosedIsTrue :
  physicalTransportCoefficientSkewClosed ≡ true
physicalTransportCoefficientSkewClosedIsTrue = refl

physicalLowTransportSkewAdjointEntrywiseConstructedIsTrue :
  physicalLowTransportSkewAdjointEntrywiseConstructed ≡ true
physicalLowTransportSkewAdjointEntrywiseConstructedIsTrue = refl
