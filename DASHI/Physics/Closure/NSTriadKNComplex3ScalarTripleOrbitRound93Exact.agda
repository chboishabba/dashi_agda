module DASHI.Physics.Closure.NSTriadKNComplex3ScalarTripleOrbitRound93Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND93 / GEOMETRIC COMMON-AMPLITUDE ORBIT
--
-- The literal ordered-pair Waleffe factor has geometric phase carrier
--
--      A_k = <u_k , u_p x u_q>.
--
-- The other two energy legs use Fourier-reality mates.  Their geometric
-- factors are therefore
--
--      A_p = <u_p , u_k x conjugate(u_q)>,
--      A_q = <u_q , u_k x conjugate(u_p)>.
--
-- This module proves, on the exact Complex3 carrier,
--
--      A_p = - conjugate(A_k),
--      A_q =   conjugate(A_k).
--
-- Hence all three legs have the SAME real phase amplitude up to the sign that
-- is already absorbed by their cyclic signed-eigenvalue difference.  The
-- proof is pure scalar-triple cyclicity, antisymmetry, and conjugation; no
-- turbulence statistic or continuum estimate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross

complexConjugateSubtract :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexConjugate (C3.complexSubtract a b)
  ≡ C3.complexSubtract (C3.complexConjugate a) (C3.complexConjugate b)
complexConjugateSubtract a b =
  trans
    (Hermitian.complexConjugateAdd a (C3.complexNegate b))
    (cong
      (C3.complexAdd (C3.complexConjugate a))
      (Hermitian.complexConjugateNegate b))

crossConjugate :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  Cross.complex3Cross (C3.complex3Conjugate u) (C3.complex3Conjugate v)
  ≡ C3.complex3Conjugate (Cross.complex3Cross u v)
crossConjugate
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (sym
      (trans
        (complexConjugateSubtract
          (C3.complexMultiply uy vz) (C3.complexMultiply uz vy))
        (cong₂ C3.complexSubtract
          (Hermitian.complexConjugateMultiply uy vz)
          (Hermitian.complexConjugateMultiply uz vy))))
    (sym
      (trans
        (complexConjugateSubtract
          (C3.complexMultiply uz vx) (C3.complexMultiply ux vz))
        (cong₂ C3.complexSubtract
          (Hermitian.complexConjugateMultiply uz vx)
          (Hermitian.complexConjugateMultiply ux vz))))
    (sym
      (trans
        (complexConjugateSubtract
          (C3.complexMultiply ux vy) (C3.complexMultiply uy vx))
        (cong₂ C3.complexSubtract
          (Hermitian.complexConjugateMultiply ux vy)
          (Hermitian.complexConjugateMultiply uy vx))))

scalarTriple :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
scalarTriple a b c = C3.bilinearDot3 a (Cross.complex3Cross b c)

scalarTripleRotateLeft :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex3 F) →
  scalarTriple a b c ≡ scalarTriple b c a
scalarTripleRotateLeft {F = F}
  (C3.complex3 ax ay az)
  (C3.complex3 bx by bz)
  (C3.complex3 cx cy cz) =
  R.solve 9
    (λ ax ay az bx by bz cx cy cz →
      (ax R.⊗ ((by R.⊗ cz) R.⊕ (R.⊝ (bz R.⊗ cy))))
      R.⊕ (ay R.⊗ ((bz R.⊗ cx) R.⊕ (R.⊝ (bx R.⊗ cz))))
      R.⊕ (az R.⊗ ((bx R.⊗ cy) R.⊕ (R.⊝ (by R.⊗ cx))))
      R.⊜
      (bx R.⊗ ((cy R.⊗ az) R.⊕ (R.⊝ (cz R.⊗ ay))))
      R.⊕ (by R.⊗ ((cz R.⊗ ax) R.⊕ (R.⊝ (cx R.⊗ az))))
      R.⊕ (bz R.⊗ ((cx R.⊗ ay) R.⊕ (R.⊝ (cy R.⊗ ax)))))
    refl ax ay az bx by bz cx cy cz
  where module R = Ring.Solver F

scalarTripleRotateRight :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex3 F) →
  scalarTriple a b c ≡ scalarTriple c a b
scalarTripleRotateRight a b c =
  trans
    (scalarTripleRotateLeft a b c)
    (scalarTripleRotateLeft b c a)

scalarTripleSwapLast :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex3 F) →
  scalarTriple a b c ≡ C3.complexNegate (scalarTriple a c b)
scalarTripleSwapLast {F = F}
  (C3.complex3 ax ay az)
  (C3.complex3 bx by bz)
  (C3.complex3 cx cy cz) =
  R.solve 9
    (λ ax ay az bx by bz cx cy cz →
      (ax R.⊗ ((by R.⊗ cz) R.⊕ (R.⊝ (bz R.⊗ cy))))
      R.⊕ (ay R.⊗ ((bz R.⊗ cx) R.⊕ (R.⊝ (bx R.⊗ cz))))
      R.⊕ (az R.⊗ ((bx R.⊗ cy) R.⊕ (R.⊝ (by R.⊗ cx))))
      R.⊜
      R.⊝
        ((ax R.⊗ ((cy R.⊗ bz) R.⊕ (R.⊝ (cz R.⊗ by))))
        R.⊕ (ay R.⊗ ((cz R.⊗ bx) R.⊕ (R.⊝ (cx R.⊗ bz))))
        R.⊕ (az R.⊗ ((cx R.⊗ by) R.⊕ (R.⊝ (cy R.⊗ bx))))))
    refl ax ay az bx by bz cx cy cz
  where module R = Ring.Solver F

scalarTripleConjugate :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex3 F) →
  C3.complexConjugate (scalarTriple a b c)
  ≡
  scalarTriple
    (C3.complex3Conjugate a)
    (C3.complex3Conjugate b)
    (C3.complex3Conjugate c)
scalarTripleConjugate a b c =
  trans
    (Hermitian.bilinearDot3Conjugate a (Cross.complex3Cross b c))
    (cong
      (C3.bilinearDot3 (C3.complex3Conjugate a))
      (sym (crossConjugate b c)))

baseGeometricAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
baseGeometricAmplitude uP uQ uK =
  C3.hermitianPairing3 uK (Cross.complex3Cross uP uQ)

pEnergyGeometricAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
pEnergyGeometricAmplitude uP uQ uK =
  C3.hermitianPairing3 uP
    (Cross.complex3Cross uK (C3.complex3Conjugate uQ))

qEnergyGeometricAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
qEnergyGeometricAmplitude uP uQ uK =
  C3.hermitianPairing3 uQ
    (Cross.complex3Cross uK (C3.complex3Conjugate uP))

conjugateBaseAsTriple :
  ∀ {r} {F : C3.RealField r}
    (uP uQ uK : C3.Complex3 F) →
  C3.complexConjugate (baseGeometricAmplitude uP uQ uK)
  ≡
  scalarTriple uK
    (C3.complex3Conjugate uP)
    (C3.complex3Conjugate uQ)
conjugateBaseAsTriple uP uQ uK =
  trans
    (scalarTripleConjugate
      (C3.complex3Conjugate uK) uP uQ)
    (cong
      (λ first → scalarTriple first
        (C3.complex3Conjugate uP)
        (C3.complex3Conjugate uQ))
      (C3.complex3ConjugateInvolutive uK))

qEnergyAmplitudeIsConjugateBase :
  ∀ {r} {F : C3.RealField r}
    (uP uQ uK : C3.Complex3 F) →
  qEnergyGeometricAmplitude uP uQ uK
  ≡ C3.complexConjugate (baseGeometricAmplitude uP uQ uK)
qEnergyAmplitudeIsConjugateBase uP uQ uK =
  trans
    (scalarTripleRotateLeft
      (C3.complex3Conjugate uQ) uK (C3.complex3Conjugate uP))
    (sym (conjugateBaseAsTriple uP uQ uK))

pEnergyAmplitudeIsNegativeConjugateBase :
  ∀ {r} {F : C3.RealField r}
    (uP uQ uK : C3.Complex3 F) →
  pEnergyGeometricAmplitude uP uQ uK
  ≡ C3.complexNegate
      (C3.complexConjugate (baseGeometricAmplitude uP uQ uK))
pEnergyAmplitudeIsNegativeConjugateBase uP uQ uK =
  trans
    (scalarTripleSwapLast
      (C3.complex3Conjugate uP) uK (C3.complex3Conjugate uQ))
    (cong C3.complexNegate
      (trans
        (scalarTripleRotateRight
          (C3.complex3Conjugate uP)
          (C3.complex3Conjugate uQ)
          uK)
        (sym (conjugateBaseAsTriple uP uQ uK))))

round93ScalarTripleOrbitClosed : Bool
round93ScalarTripleOrbitClosed = true

round93EnergyLegAmplitudesReduceToBaseConjugacy : Bool
round93EnergyLegAmplitudesReduceToBaseConjugacy = true

round93ScalarTripleOrbitClosedIsTrue :
  round93ScalarTripleOrbitClosed ≡ true
round93ScalarTripleOrbitClosedIsTrue = refl

round93EnergyLegAmplitudesReduceToBaseConjugacyIsTrue :
  round93EnergyLegAmplitudesReduceToBaseConjugacy ≡ true
round93EnergyLegAmplitudesReduceToBaseConjugacyIsTrue = refl
