module DASHI.Physics.Closure.NSTriadKNCurlRealityHelicalTransportRound93Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Andrew Majda.
-- Title: "The Beltrami spectrum for incompressible fluid flows".
-- Communications in Mathematical Physics 115 (1988), 435--456.
-- DOI: 10.1007/BF01218019.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND93 / REALITY TRANSPORT OF HELICAL EIGENMODES
--
-- The p- and q-energy legs use -q and -p Fourier modes.  To keep the Waleffe
-- signed eigenvalue on the same physical reality orbit we prove directly
--
--   curl_{-k}(conjugate u_k) = conjugate(curl_k u_k).
--
-- Therefore if curl_k u_k = lambda u_k with real lambda, the reality mate at
-- -k has the SAME signed eigenvalue lambda.  No helical-projector law is taken
-- as a record field here; the result is derived from the literal Complex3 curl
-- symbol, mode-vector reality, and complex conjugation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNComplex3ScalarTripleOrbitRound93Exact as Triple
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv

crossNegateLeft :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  Cross.complex3Cross (C3.complex3Negate u) v
  ≡ C3.complex3Negate (Cross.complex3Cross u v)
crossNegateLeft {F = F}
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (trans
      (cong₂ C3.complexSubtract
        (Algebra.complexNegateMultiplyLeft uy vz)
        (Algebra.complexNegateMultiplyLeft uz vy))
      scalarDifference)
    (trans
      (cong₂ C3.complexSubtract
        (Algebra.complexNegateMultiplyLeft uz vx)
        (Algebra.complexNegateMultiplyLeft ux vz))
      scalarDifferenceYZ)
    (trans
      (cong₂ C3.complexSubtract
        (Algebra.complexNegateMultiplyLeft ux vy)
        (Algebra.complexNegateMultiplyLeft uy vx))
      scalarDifferenceZX)
  where
  scalarDifference :
    C3.complexSubtract
      (C3.complexNegate (C3.complexMultiply uy vz))
      (C3.complexNegate (C3.complexMultiply uz vy))
    ≡
    C3.complexNegate
      (C3.complexSubtract
        (C3.complexMultiply uy vz) (C3.complexMultiply uz vy))
  scalarDifference = scalarNegatedDifference
    (C3.complexMultiply uy vz) (C3.complexMultiply uz vy)

  scalarDifferenceYZ :
    C3.complexSubtract
      (C3.complexNegate (C3.complexMultiply uz vx))
      (C3.complexNegate (C3.complexMultiply ux vz))
    ≡
    C3.complexNegate
      (C3.complexSubtract
        (C3.complexMultiply uz vx) (C3.complexMultiply ux vz))
  scalarDifferenceYZ = scalarNegatedDifference
    (C3.complexMultiply uz vx) (C3.complexMultiply ux vz)

  scalarDifferenceZX :
    C3.complexSubtract
      (C3.complexNegate (C3.complexMultiply ux vy))
      (C3.complexNegate (C3.complexMultiply uy vx))
    ≡
    C3.complexNegate
      (C3.complexSubtract
        (C3.complexMultiply ux vy) (C3.complexMultiply uy vx))
  scalarDifferenceZX = scalarNegatedDifference
    (C3.complexMultiply ux vy) (C3.complexMultiply uy vx)

  scalarNegatedDifference :
    (a b : C3.Complex F) →
    C3.complexSubtract (C3.complexNegate a) (C3.complexNegate b)
    ≡ C3.complexNegate (C3.complexSubtract a b)
  scalarNegatedDifference a b =
    let module P = Algebra.Polynomial F in
    Algebra.complexExt
      (P.R.solve 4
        (λ ar ai br bi →
          ((P.R.⊝ ar) P.R.⊕ (P.R.⊝ (P.R.⊝ br)))
          P.R.⊜ P.R.⊝ (ar P.R.⊕ (P.R.⊝ br)))
        refl (C3.real a) (C3.imaginary a) (C3.real b) (C3.imaginary b))
      (P.R.solve 4
        (λ ar ai br bi →
          ((P.R.⊝ ai) P.R.⊕ (P.R.⊝ (P.R.⊝ bi)))
          P.R.⊜ P.R.⊝ (ai P.R.⊕ (P.R.⊝ bi)))
        refl (C3.real a) (C3.imaginary a) (C3.real b) (C3.imaginary b))

conjugateIIsMinusI :
  ∀ {r} (F : C3.RealField r) →
  C3.complexConjugate (C3.complexI F)
  ≡ C3.complexNegate (C3.complexI F)
conjugateIIsMinusI F rewrite C3.negateZero F = refl

scaleIOfNegate :
  ∀ {r} {F : C3.RealField r}
    (v : C3.Complex3 F) →
  C3.complex3Scale (C3.complexI F) (C3.complex3Negate v)
  ≡ C3.complex3Scale (C3.complexNegate (C3.complexI F)) v
scaleIOfNegate (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (trans
      (Algebra.complexNegateMultiplyRight (C3.complexI _) vx)
      (sym (Algebra.complexNegateMultiplyLeft (C3.complexI _) vx)))
    (trans
      (Algebra.complexNegateMultiplyRight (C3.complexI _) vy)
      (sym (Algebra.complexNegateMultiplyLeft (C3.complexI _) vy)))
    (trans
      (Algebra.complexNegateMultiplyRight (C3.complexI _) vz)
      (sym (Algebra.complexNegateMultiplyLeft (C3.complexI _) vz)))

curlRealityCompatible :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (u : C3.Complex3 F) →
  Conv.curlFromWave
    (C3.modeVector E (Z3.negateMode k))
    (C3.complex3Conjugate u)
  ≡
  C3.complex3Conjugate
    (Conv.curlFromWave (C3.modeVector E k) u)
curlRealityCompatible {F = F} E k u =
  let
    wave = C3.modeVector E k
    crossConj = Cross.complex3Cross wave (C3.complex3Conjugate u)

    leftToCanonical :
      Conv.curlFromWave
        (C3.modeVector E (Z3.negateMode k))
        (C3.complex3Conjugate u)
      ≡
      C3.complex3Scale (C3.complexNegate (C3.complexI F)) crossConj
    leftToCanonical =
      trans
        (cong
          (λ selectedWave →
            Conv.curlFromWave selectedWave (C3.complex3Conjugate u))
          (C3.modeVectorNegation E k))
        (trans
          (cong (C3.complex3Scale (C3.complexI F))
            (crossNegateLeft wave (C3.complex3Conjugate u)))
          (scaleIOfNegate crossConj))

    rightToCanonical :
      C3.complex3Conjugate
        (Conv.curlFromWave wave u)
      ≡
      C3.complex3Scale (C3.complexNegate (C3.complexI F)) crossConj
    rightToCanonical =
      trans
        (Scaling.complex3ConjugateScale
          (C3.complexI F) (Cross.complex3Cross wave u))
        (cong₂ C3.complex3Scale
          (conjugateIIsMinusI F)
          (trans
            (sym (Triple.crossConjugate wave u))
            (cong
              (λ selectedWave →
                Cross.complex3Cross selectedWave (C3.complex3Conjugate u))
              (C3.modeVectorConjugate E k))))
  in
  trans leftToCanonical (sym rightToCanonical)

negativeModePreservesRealHelicalEigenvalue :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (reality : Audit.RealityCondition velocity)
    (k : Z3.FourierMode)
    (lambda : C3.Carrier F) →
  Conv.curlFromWave (C3.modeVector E k) (velocity k)
    ≡ C3.complex3Scale (C3.realEmbed F lambda) (velocity k) →
  Conv.curlFromWave
      (C3.modeVector E (Z3.negateMode k))
      (velocity (Z3.negateMode k))
    ≡ C3.complex3Scale
      (C3.realEmbed F lambda)
      (velocity (Z3.negateMode k))
negativeModePreservesRealHelicalEigenvalue {F = F}
  E velocity reality k lambda eigen =
  trans
    (cong
      (Conv.curlFromWave (C3.modeVector E (Z3.negateMode k)))
      (reality k))
    (trans
      (curlRealityCompatible E k (velocity k))
      (trans
        (cong C3.complex3Conjugate eigen)
        (trans
          (Scaling.complex3ConjugateScale
            (C3.realEmbed F lambda) (velocity k))
          (cong₂ C3.complex3Scale
            (C3.realEmbedConjugate F lambda)
            (sym (reality k))))))

round93CurlRealityCompatibilityClosed : Bool
round93CurlRealityCompatibilityClosed = true

round93NegativeModePreservesSignedHelicalEigenvalue : Bool
round93NegativeModePreservesSignedHelicalEigenvalue = true

round93CurlRealityCompatibilityClosedIsTrue :
  round93CurlRealityCompatibilityClosed ≡ true
round93CurlRealityCompatibilityClosedIsTrue = refl

round93NegativeModePreservesSignedHelicalEigenvalueIsTrue :
  round93NegativeModePreservesSignedHelicalEigenvalue ≡ true
round93NegativeModePreservesSignedHelicalEigenvalueIsTrue = refl
