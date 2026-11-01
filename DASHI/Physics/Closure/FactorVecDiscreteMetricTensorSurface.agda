module DASHI.Physics.Closure.FactorVecDiscreteMetricTensorSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (List; _∷_; [])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational as R using (_/_)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary.Decidable.Core using (yes; no)

import Data.Rational.Properties as Rₚ
open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71; _≟_)
open import DASHI.Core.Q using (ℚ; zeroℚ; oneℚ; twoℚ; _+ℚ_; _-ℚ_; _*ℚ_)
import Ontology.GodelLattice as GL
import Ontology.Hecke.FactorVecInstances as FVI
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt as W4Stress

------------------------------------------------------------------------
-- FactorVec tangent metric tensor surface.
--
-- The tangent directions are the finite SSP prime lanes over the FactorVec
-- base.  This is deliberately theorem-thin: it supplies a symmetric rational
-- bilinear-form surface and a finite Koszul/Christoffel witness for the flat
-- seed connection, then records the exact gates still needed before any
-- contracted-Bianchi or GR promotion can be claimed.

FactorVecTangentDirection : Set
FactorVecTangentDirection = SSP

factorVecTangentBasis :
  List FactorVecTangentDirection
factorVecTangentBasis =
  p2
  ∷ p3
  ∷ p5
  ∷ p7
  ∷ p11
  ∷ p13
  ∷ p17
  ∷ p19
  ∷ p23
  ∷ p29
  ∷ p31
  ∷ p41
  ∷ p47
  ∷ p59
  ∷ p71
  ∷ []

record FactorVecQCoefficientVector : Set where
  constructor qv15
  field
    q2 :
      ℚ
    q3 :
      ℚ
    q5 :
      ℚ
    q7 :
      ℚ
    q11 :
      ℚ
    q13 :
      ℚ
    q17 :
      ℚ
    q19 :
      ℚ
    q23 :
      ℚ
    q29 :
      ℚ
    q31 :
      ℚ
    q41 :
      ℚ
    q47 :
      ℚ
    q59 :
      ℚ
    q71 :
      ℚ

open FactorVecQCoefficientVector public

factorVecQZeroVector :
  FactorVecQCoefficientVector
factorVecQZeroVector =
  qv15
    zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
    zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
    zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ

factorVecQAdd :
  FactorVecQCoefficientVector →
  FactorVecQCoefficientVector →
  FactorVecQCoefficientVector
factorVecQAdd
  (qv15 x2 x3 x5 x7 x11 x13 x17 x19 x23 x29 x31 x41 x47 x59 x71)
  (qv15 y2 y3 y5 y7 y11 y13 y17 y19 y23 y29 y31 y41 y47 y59 y71) =
  qv15
    (x2 +ℚ y2)
    (x3 +ℚ y3)
    (x5 +ℚ y5)
    (x7 +ℚ y7)
    (x11 +ℚ y11)
    (x13 +ℚ y13)
    (x17 +ℚ y17)
    (x19 +ℚ y19)
    (x23 +ℚ y23)
    (x29 +ℚ y29)
    (x31 +ℚ y31)
    (x41 +ℚ y41)
    (x47 +ℚ y47)
    (x59 +ℚ y59)
    (x71 +ℚ y71)

factorVecQScale :
  ℚ →
  FactorVecQCoefficientVector →
  FactorVecQCoefficientVector
factorVecQScale
  a
  (qv15 x2 x3 x5 x7 x11 x13 x17 x19 x23 x29 x31 x41 x47 x59 x71) =
  qv15
    (a *ℚ x2)
    (a *ℚ x3)
    (a *ℚ x5)
    (a *ℚ x7)
    (a *ℚ x11)
    (a *ℚ x13)
    (a *ℚ x17)
    (a *ℚ x19)
    (a *ℚ x23)
    (a *ℚ x29)
    (a *ℚ x31)
    (a *ℚ x41)
    (a *ℚ x47)
    (a *ℚ x59)
    (a *ℚ x71)

factorVecQCoordinate :
  FactorVecTangentDirection →
  FactorVecQCoefficientVector →
  ℚ
factorVecQCoordinate p2 v =
  q2 v
factorVecQCoordinate p3 v =
  q3 v
factorVecQCoordinate p5 v =
  q5 v
factorVecQCoordinate p7 v =
  q7 v
factorVecQCoordinate p11 v =
  q11 v
factorVecQCoordinate p13 v =
  q13 v
factorVecQCoordinate p17 v =
  q17 v
factorVecQCoordinate p19 v =
  q19 v
factorVecQCoordinate p23 v =
  q23 v
factorVecQCoordinate p29 v =
  q29 v
factorVecQCoordinate p31 v =
  q31 v
factorVecQCoordinate p41 v =
  q41 v
factorVecQCoordinate p47 v =
  q47 v
factorVecQCoordinate p59 v =
  q59 v
factorVecQCoordinate p71 v =
  q71 v

factorVecQBasisVector :
  FactorVecTangentDirection →
  FactorVecQCoefficientVector
factorVecQBasisVector p2 =
  qv15 oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p3 =
  qv15 zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p5 =
  qv15 zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p7 =
  qv15 zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p11 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p13 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p17 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p19 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p23 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p29 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p31 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p41 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ
factorVecQBasisVector p47 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ
factorVecQBasisVector p59 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ
factorVecQBasisVector p71 =
  qv15 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ oneℚ

factorVecZeroMetric :
  GL.FactorVec →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecZeroMetric _ _ _ =
  zeroℚ

factorVecReciprocalPrimeWeight :
  FactorVecTangentDirection →
  ℚ
factorVecReciprocalPrimeWeight p2 =
  (+ 1) R./ 2
factorVecReciprocalPrimeWeight p3 =
  (+ 1) R./ 3
factorVecReciprocalPrimeWeight p5 =
  (+ 1) R./ 5
factorVecReciprocalPrimeWeight p7 =
  (+ 1) R./ 7
factorVecReciprocalPrimeWeight p11 =
  (+ 1) R./ 11
factorVecReciprocalPrimeWeight p13 =
  (+ 1) R./ 13
factorVecReciprocalPrimeWeight p17 =
  (+ 1) R./ 17
factorVecReciprocalPrimeWeight p19 =
  (+ 1) R./ 19
factorVecReciprocalPrimeWeight p23 =
  (+ 1) R./ 23
factorVecReciprocalPrimeWeight p29 =
  (+ 1) R./ 29
factorVecReciprocalPrimeWeight p31 =
  (+ 1) R./ 31
factorVecReciprocalPrimeWeight p41 =
  (+ 1) R./ 41
factorVecReciprocalPrimeWeight p47 =
  (+ 1) R./ 47
factorVecReciprocalPrimeWeight p59 =
  (+ 1) R./ 59
factorVecReciprocalPrimeWeight p71 =
  (+ 1) R./ 71

factorVecConstantDiagonalReciprocalPrimeMetric :
  GL.FactorVec →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecConstantDiagonalReciprocalPrimeMetric _ mu nu with mu ≟ nu
... | yes _ =
  factorVecReciprocalPrimeWeight mu
... | no _ =
  zeroℚ

factorVecConstantDiagonalReciprocalPrimeMatrix :
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecConstantDiagonalReciprocalPrimeMatrix mu nu with mu ≟ nu
... | yes _ =
  factorVecReciprocalPrimeWeight mu
... | no _ =
  zeroℚ

factorVecConstantDiagonalReciprocalPrimeMatrixComponentLaw :
  (base : GL.FactorVec) →
  (mu nu : FactorVecTangentDirection) →
  factorVecConstantDiagonalReciprocalPrimeMatrix mu nu
  ≡
  factorVecConstantDiagonalReciprocalPrimeMetric base mu nu
factorVecConstantDiagonalReciprocalPrimeMatrixComponentLaw _ mu nu with mu ≟ nu
... | yes _ =
  refl
... | no _ =
  refl

factorVecConstantDiagonalReciprocalPrimeMetricSymmetric :
  (base : GL.FactorVec) →
  (mu nu : FactorVecTangentDirection) →
  factorVecConstantDiagonalReciprocalPrimeMetric base mu nu
  ≡
  factorVecConstantDiagonalReciprocalPrimeMetric base nu mu
factorVecConstantDiagonalReciprocalPrimeMetricSymmetric _ mu nu
  with mu ≟ nu | nu ≟ mu
... | yes refl | yes _ =
  refl
... | yes eq | no neq =
  ⊥-elim (neq (sym eq))
... | no neq | yes eq =
  ⊥-elim (neq (sym eq))
... | no _ | no _ =
  refl

factorVecConstantDiagonalSelfComponent :
  (base : GL.FactorVec) →
  (mu : FactorVecTangentDirection) →
  factorVecConstantDiagonalReciprocalPrimeMetric base mu mu
  ≡
  factorVecReciprocalPrimeWeight mu
factorVecConstantDiagonalSelfComponent _ mu with mu ≟ mu
... | yes refl =
  refl
... | no neq =
  ⊥-elim (neq refl)

factorVecConstantDiagonalOffDiagonalZero :
  (base : GL.FactorVec) →
  (mu nu : FactorVecTangentDirection) →
  (mu ≡ nu → ⊥) →
  factorVecConstantDiagonalReciprocalPrimeMetric base mu nu
  ≡
  zeroℚ
factorVecConstantDiagonalOffDiagonalZero _ mu nu neq with mu ≟ nu
... | yes eq =
  ⊥-elim (neq eq)
... | no _ =
  refl

data FactorVecReciprocalPrimeDeterminantProductExpression : Set where
  determinantProductOfFifteenReciprocalPrimes :
    FactorVecReciprocalPrimeDeterminantProductExpression

factorVecValuationDepth :
  GL.FactorVec →
  FactorVecTangentDirection →
  GL.Exponent
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p2 =
  e2
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p3 =
  e3
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p5 =
  e5
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p7 =
  e7
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p11 =
  e11
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p13 =
  e13
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p17 =
  e17
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p19 =
  e19
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p23 =
  e23
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p29 =
  e29
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p31 =
  e31
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p41 =
  e41
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p47 =
  e47
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p59 =
  e59
factorVecValuationDepth
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  p71 =
  e71

factorVecValuationScale :
  GL.Exponent →
  ℚ
factorVecValuationScale zero =
  zeroℚ
factorVecValuationScale (suc n) =
  oneℚ +ℚ factorVecValuationScale n

data FactorVecPositiveExponent : GL.Exponent → Set where
  positiveExponent :
    (n : GL.Exponent) →
    FactorVecPositiveExponent (suc n)

data FactorVecP2LorentzInertiaLane : Set where
  timeLikeP2Lane :
    FactorVecP2LorentzInertiaLane
  spatialLikeNonP2Lane :
    FactorVecTangentDirection →
    FactorVecP2LorentzInertiaLane

factorVecUnitValuationSupportBase :
  GL.FactorVec
factorVecUnitValuationSupportBase =
  GL.v15
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)
    (suc zero)

factorVecUnitValuationDepthNonzero :
  (mu : FactorVecTangentDirection) →
  FactorVecPositiveExponent
    (factorVecValuationDepth factorVecUnitValuationSupportBase mu)
factorVecUnitValuationDepthNonzero p2 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p3 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p5 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p7 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p11 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p13 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p17 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p19 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p23 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p29 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p31 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p41 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p47 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p59 =
  positiveExponent zero
factorVecUnitValuationDepthNonzero p71 =
  positiveExponent zero

data FactorVecCommittedTimePrime : Set where
  timePrimeP2 :
    FactorVecCommittedTimePrime

factorVecCommittedTimeDirection :
  FactorVecTangentDirection
factorVecCommittedTimeDirection =
  p2

factorVecValuationDiagonalWeight :
  GL.FactorVec →
  FactorVecTangentDirection →
  ℚ
factorVecValuationDiagonalWeight base mu =
  factorVecValuationScale (factorVecValuationDepth base mu)
  *ℚ
  factorVecReciprocalPrimeWeight mu

factorVecP2LorentzSignedValuationWeight :
  GL.FactorVec →
  FactorVecTangentDirection →
  ℚ
factorVecP2LorentzSignedValuationWeight base mu with mu ≟ p2
... | yes _ =
  zeroℚ -ℚ factorVecValuationDiagonalWeight base mu
... | no _ =
  factorVecValuationDiagonalWeight base mu

factorVecP2LorentzSignedValuationWeightTime :
  (base : GL.FactorVec) →
  factorVecP2LorentzSignedValuationWeight base p2
  ≡
  (zeroℚ -ℚ factorVecValuationDiagonalWeight base p2)
factorVecP2LorentzSignedValuationWeightTime base with p2 ≟ p2
... | yes refl =
  refl
... | no neq =
  ⊥-elim (neq refl)

factorVecP2LorentzSignedValuationWeightSpatial :
  (base : GL.FactorVec) →
  (mu : FactorVecTangentDirection) →
  (mu ≡ p2 → ⊥) →
  factorVecP2LorentzSignedValuationWeight base mu
  ≡
  factorVecValuationDiagonalWeight base mu
factorVecP2LorentzSignedValuationWeightSpatial _ p2 notTime =
  ⊥-elim (notTime refl)
factorVecP2LorentzSignedValuationWeightSpatial _ p3 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p5 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p7 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p11 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p13 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p17 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p19 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p23 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p29 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p31 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p41 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p47 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p59 _ =
  refl
factorVecP2LorentzSignedValuationWeightSpatial _ p71 _ =
  refl

factorVecValuationDependentP2LorentzMetric :
  GL.FactorVec →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecValuationDependentP2LorentzMetric base mu nu with mu ≟ nu
... | yes _ =
  factorVecP2LorentzSignedValuationWeight base mu
... | no _ =
  zeroℚ

factorVecValuationDependentP2LorentzMetricSymmetric :
  (base : GL.FactorVec) →
  (mu nu : FactorVecTangentDirection) →
  factorVecValuationDependentP2LorentzMetric base mu nu
  ≡
  factorVecValuationDependentP2LorentzMetric base nu mu
factorVecValuationDependentP2LorentzMetricSymmetric _ mu nu
  with mu ≟ nu | nu ≟ mu
... | yes refl | yes _ =
  refl
... | yes eq | no neq =
  ⊥-elim (neq (sym eq))
... | no neq | yes eq =
  ⊥-elim (neq (sym eq))
... | no _ | no _ =
  refl

factorVecValuationP2LorentzSelfComponent :
  (base : GL.FactorVec) →
  (mu : FactorVecTangentDirection) →
  factorVecValuationDependentP2LorentzMetric base mu mu
  ≡
  factorVecP2LorentzSignedValuationWeight base mu
factorVecValuationP2LorentzSelfComponent _ mu with mu ≟ mu
... | yes refl =
  refl
... | no neq =
  ⊥-elim (neq refl)

factorVecValuationP2LorentzTimeComponent :
  (base : GL.FactorVec) →
  factorVecValuationDependentP2LorentzMetric base p2 p2
  ≡
  (zeroℚ -ℚ factorVecValuationDiagonalWeight base p2)
factorVecValuationP2LorentzTimeComponent base with p2 ≟ p2 | p2 ≟ p2
... | yes refl | yes refl =
  refl
... | yes refl | no neq =
  ⊥-elim (neq refl)
... | no neq | _ =
  ⊥-elim (neq refl)

factorVecValuationP2LorentzSpatialSelfComponent :
  (base : GL.FactorVec) →
  (mu : FactorVecTangentDirection) →
  (mu ≡ p2 → ⊥) →
  factorVecValuationDependentP2LorentzMetric base mu mu
  ≡
  factorVecValuationDiagonalWeight base mu
factorVecValuationP2LorentzSpatialSelfComponent _ p2 notTime =
  ⊥-elim (notTime refl)
factorVecValuationP2LorentzSpatialSelfComponent _ p3 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p5 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p7 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p11 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p13 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p17 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p19 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p23 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p29 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p31 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p41 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p47 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p59 _ =
  refl
factorVecValuationP2LorentzSpatialSelfComponent _ p71 _ =
  refl

factorVecValuationP2LorentzOffDiagonalZero :
  (base : GL.FactorVec) →
  (mu nu : FactorVecTangentDirection) →
  (mu ≡ nu → ⊥) →
  factorVecValuationDependentP2LorentzMetric base mu nu
  ≡
  zeroℚ
factorVecValuationP2LorentzOffDiagonalZero _ mu nu neq with mu ≟ nu
... | yes eq =
  ⊥-elim (neq eq)
... | no _ =
  refl

factorVecMetricSymmetric :
  (base : GL.FactorVec) →
  (mu nu : FactorVecTangentDirection) →
  factorVecZeroMetric base mu nu
  ≡
  factorVecZeroMetric base nu mu
factorVecMetricSymmetric _ _ _ =
  refl

factorVecMetricFiniteDifference :
  GL.FactorVec →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecMetricFiniteDifference _ _ _ _ =
  zeroℚ

factorVecKoszulExpression :
  GL.FactorVec →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecKoszulExpression _ _ _ _ =
  zeroℚ

factorVecChristoffelSymbol :
  GL.FactorVec →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecChristoffelSymbol _ _ _ _ =
  zeroℚ

factorVecScaledChristoffelSymbol :
  GL.FactorVec →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecScaledChristoffelSymbol _ _ _ _ =
  zeroℚ

factorVecKoszulChristoffelWitness :
  (base : GL.FactorVec) →
  (lambda mu nu : FactorVecTangentDirection) →
  factorVecScaledChristoffelSymbol base lambda mu nu
  ≡
  factorVecKoszulExpression base lambda mu nu
factorVecKoszulChristoffelWitness _ _ _ _ =
  refl

factorVecChristoffelTorsionFree :
  (base : GL.FactorVec) →
  (lambda mu nu : FactorVecTangentDirection) →
  factorVecChristoffelSymbol base lambda mu nu
  ≡
  factorVecChristoffelSymbol base lambda nu mu
factorVecChristoffelTorsionFree _ _ _ _ =
  refl

factorVecMetricCompatibilityWitness :
  (base : GL.FactorVec) →
  (lambda mu nu : FactorVecTangentDirection) →
  factorVecMetricFiniteDifference base lambda mu nu
  ≡
  zeroℚ
factorVecMetricCompatibilityWitness _ _ _ _ =
  refl

factorVecPrimeTransport :
  FactorVecTangentDirection →
  GL.FactorVec →
  GL.FactorVec
factorVecPrimeTransport =
  FVI.primeBump

record FactorVecSymmetricRationalBilinearMetric : Setω where
  field
    BasePoint :
      Set

    TangentDirection :
      Set

    basePointIsFactorVec :
      BasePoint
      ≡
      GL.FactorVec

    tangentDirectionIsSSP :
      TangentDirection
      ≡
      SSP

    rationalScalar :
      Set

    rationalScalarIsProjectQ :
      rationalScalar
      ≡
      ℚ

    zeroScalar :
      rationalScalar

    oneScalar :
      rationalScalar

    twoScalar :
      rationalScalar

    tangentBasis :
      List TangentDirection

    primeTransport :
      TangentDirection →
      BasePoint →
      BasePoint

    g :
      BasePoint →
      TangentDirection →
      TangentDirection →
      rationalScalar

    gSymmetric :
      (base : BasePoint) →
      (mu nu : TangentDirection) →
      g base mu nu
      ≡
      g base nu mu

    bilinearSurfaceBoundary :
      List String

record FactorVecFiniteKoszulChristoffelWitness : Setω where
  field
    metric :
      FactorVecSymmetricRationalBilinearMetric

    metricFiniteDifference :
      GL.FactorVec →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    koszulExpression :
      GL.FactorVec →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    christoffelSymbol :
      GL.FactorVec →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    scaledChristoffelSymbol :
      GL.FactorVec →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    koszulChristoffelLaw :
      (base : GL.FactorVec) →
      (lambda mu nu : FactorVecTangentDirection) →
      scaledChristoffelSymbol base lambda mu nu
      ≡
      koszulExpression base lambda mu nu

    torsionFreeChristoffelLaw :
      (base : GL.FactorVec) →
      (lambda mu nu : FactorVecTangentDirection) →
      christoffelSymbol base lambda mu nu
      ≡
      christoffelSymbol base lambda nu mu

    metricCompatibilityLaw :
      (base : GL.FactorVec) →
      (lambda mu nu : FactorVecTangentDirection) →
      metricFiniteDifference base lambda mu nu
      ≡
      zeroℚ

    witnessBoundary :
      List String

record FactorVecConstantDiagonalBasisShapeWitness : Setω where
  field
    metric :
      FactorVecSymmetricRationalBilinearMetric

    diagonalWeight :
      FactorVecTangentDirection →
      ℚ

    metricComponent :
      GL.FactorVec →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    selfComponentLaw :
      (base : GL.FactorVec) →
      (mu : FactorVecTangentDirection) →
      metricComponent base mu mu
      ≡
      diagonalWeight mu

    offDiagonalZeroLaw :
      (base : GL.FactorVec) →
      (mu nu : FactorVecTangentDirection) →
      (mu ≡ nu → ⊥) →
      metricComponent base mu nu
      ≡
      zeroℚ

    basisShapeBoundary :
      List String

record FactorVecFiniteFreeTangentModuleMatrixWitness : Setω where
  field
    coefficientVector :
      Set

    coefficientVectorIsQ15 :
      coefficientVector
      ≡
      FactorVecQCoefficientVector

    scalar :
      Set

    scalarIsQ :
      scalar
      ≡
      ℚ

    zeroVector :
      FactorVecQCoefficientVector

    addVector :
      FactorVecQCoefficientVector →
      FactorVecQCoefficientVector →
      FactorVecQCoefficientVector

    scaleVector :
      ℚ →
      FactorVecQCoefficientVector →
      FactorVecQCoefficientVector

    basisVector :
      FactorVecTangentDirection →
      FactorVecQCoefficientVector

    coordinate :
      FactorVecTangentDirection →
      FactorVecQCoefficientVector →
      ℚ

    diagonalMatrix :
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    diagonalMatrixComponentLaw :
      (base : GL.FactorVec) →
      (mu nu : FactorVecTangentDirection) →
      diagonalMatrix mu nu
      ≡
      factorVecConstantDiagonalReciprocalPrimeMetric base mu nu

    matrixBoundary :
      List String

record FactorVecDiagonalDeterminantProductTarget : Setω where
  field
    matrixWitness :
      FactorVecFiniteFreeTangentModuleMatrixWitness

    determinantProductExpression :
      FactorVecReciprocalPrimeDeterminantProductExpression

    determinantProductExpressionIsCanonical :
      determinantProductExpression
      ≡
      determinantProductOfFifteenReciprocalPrimes

    determinantNonzeroProofPromoted :
      Set

    determinantNonzeroProofStillMissing :
      determinantNonzeroProofPromoted
      ≡
      ⊥

    determinantBoundary :
      List String

data FactorVecMetricSignatureTarget : Set where
  positiveFifteenPrimeLaneSignature :
    FactorVecMetricSignatureTarget
  valuationDependentNonFlatGRSignaturePrimitive :
    FactorVecMetricSignatureTarget

data FactorVecNondegenerateSignatureBlocker : Set where
  missingFiniteFreeTangentModuleOverQ :
    FactorVecNondegenerateSignatureBlocker
  missingMatrixRepresentationForBilinearForm :
    FactorVecNondegenerateSignatureBlocker
  missingDeterminantOrRankNonzeroProof :
    FactorVecNondegenerateSignatureBlocker
  missingRationalReciprocalPositiveNonzeroProofs :
    FactorVecNondegenerateSignatureBlocker
  missingSylvesterInertiaClassifier :
    FactorVecNondegenerateSignatureBlocker
  missingLorentzProjectionOrWickBoundary :
    FactorVecNondegenerateSignatureBlocker

canonicalFactorVecConstantDiagonalNondegenerateSignatureBlockers :
  List FactorVecNondegenerateSignatureBlocker
canonicalFactorVecConstantDiagonalNondegenerateSignatureBlockers =
  missingDeterminantOrRankNonzeroProof
  ∷ missingRationalReciprocalPositiveNonzeroProofs
  ∷ missingSylvesterInertiaClassifier
  ∷ missingLorentzProjectionOrWickBoundary
  ∷ []

data FactorVecMetricGRPrimitive : Set where
  missingConstantDiagonalNondegenerateProof :
    FactorVecMetricGRPrimitive
  missingConstantDiagonalSignatureProof :
    FactorVecMetricGRPrimitive
  missingValuationDependentSiteMetricConstruction :
    FactorVecMetricGRPrimitive
  missingValuationMetricSymmetryProof :
    FactorVecMetricGRPrimitive
  missingValuationMetricNondegenerateProof :
    FactorVecMetricGRPrimitive
  missingValuationMetricSignatureProof :
    FactorVecMetricGRPrimitive
  missingValuationInverseMetricComputation :
    FactorVecMetricGRPrimitive
  missingValuationLeviCivitaChristoffelComputation :
    FactorVecMetricGRPrimitive
  missingValuationRiemannCurvatureComputation :
    FactorVecMetricGRPrimitive
  missingValuationRicciContractionComputation :
    FactorVecMetricGRPrimitive
  missingValuationContractedBianchiComputation :
    FactorVecMetricGRPrimitive
  missingValuationStressEnergyCompatibilityComputation :
    FactorVecMetricGRPrimitive

canonicalFactorVecMetricGRPrimitives :
  List FactorVecMetricGRPrimitive
canonicalFactorVecMetricGRPrimitives =
  missingConstantDiagonalNondegenerateProof
  ∷ missingConstantDiagonalSignatureProof
  ∷ missingValuationDependentSiteMetricConstruction
  ∷ missingValuationMetricSymmetryProof
  ∷ missingValuationMetricNondegenerateProof
  ∷ missingValuationMetricSignatureProof
  ∷ missingValuationInverseMetricComputation
  ∷ missingValuationLeviCivitaChristoffelComputation
  ∷ missingValuationRiemannCurvatureComputation
  ∷ missingValuationRicciContractionComputation
  ∷ missingValuationContractedBianchiComputation
  ∷ missingValuationStressEnergyCompatibilityComputation
  ∷ []

data FactorVecStressEnergyCompatibilityMissingPrimitive : Set where
  missingValuationStressEnergyTensorCandidate :
    FactorVecStressEnergyCompatibilityMissingPrimitive
  missingValuationEinsteinSourceCouplingLaw :
    FactorVecStressEnergyCompatibilityMissingPrimitive
  missingValuationStressEnergyCovariantDivergenceLaw :
    FactorVecStressEnergyCompatibilityMissingPrimitive
  missingValuationMatterReceiptInterface :
    FactorVecStressEnergyCompatibilityMissingPrimitive

canonicalFactorVecStressEnergyCompatibilityMissingPrimitives :
  List FactorVecStressEnergyCompatibilityMissingPrimitive
canonicalFactorVecStressEnergyCompatibilityMissingPrimitives =
  missingValuationStressEnergyTensorCandidate
  ∷ missingValuationEinsteinSourceCouplingLaw
  ∷ missingValuationStressEnergyCovariantDivergenceLaw
  ∷ missingValuationMatterReceiptInterface
  ∷ []

data FactorVecStressEnergyTensorCandidateMissingPrimitive : Set where
  missingValuationStressEnergyTensorComponentFamily :
    FactorVecStressEnergyTensorCandidateMissingPrimitive
  missingValuationStressEnergyTensorSymmetryLaw :
    FactorVecStressEnergyTensorCandidateMissingPrimitive
  missingValuationStressEnergyTensorFiniteSupportLaw :
    FactorVecStressEnergyTensorCandidateMissingPrimitive
  missingValuationStressEnergyTensorCarrierEmbedding :
    FactorVecStressEnergyTensorCandidateMissingPrimitive

canonicalFactorVecStressEnergyTensorCandidateMissingPrimitives :
  List FactorVecStressEnergyTensorCandidateMissingPrimitive
canonicalFactorVecStressEnergyTensorCandidateMissingPrimitives =
  missingValuationStressEnergyTensorComponentFamily
  ∷ missingValuationStressEnergyTensorSymmetryLaw
  ∷ missingValuationStressEnergyTensorFiniteSupportLaw
  ∷ missingValuationStressEnergyTensorCarrierEmbedding
  ∷ []

FactorVecStressEnergyTensorComponentFamily :
  Set
FactorVecStressEnergyTensorComponentFamily =
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ

FactorVecStressEnergyTensorSymmetryLaw :
  FactorVecStressEnergyTensorComponentFamily →
  Set
FactorVecStressEnergyTensorSymmetryLaw tensor =
  (mu nu : FactorVecTangentDirection) →
  tensor mu nu
  ≡
  tensor nu mu

FactorVecStressEnergyTensorFiniteSupportLaw :
  FactorVecStressEnergyTensorComponentFamily →
  Set
FactorVecStressEnergyTensorFiniteSupportLaw tensor =
  (mu nu : FactorVecTangentDirection) →
  tensor mu nu
  ≡
  zeroℚ

FactorVecStressEnergyTensorCarrierEmbeddingLaw :
  FactorVecStressEnergyTensorComponentFamily →
  Set
FactorVecStressEnergyTensorCarrierEmbeddingLaw tensor =
  (mu nu : FactorVecTangentDirection) →
  tensor mu nu
  ≡
  factorVecQCoordinate nu factorVecQZeroVector

factorVecUnitP2LorentzEinsteinTensorComponentFamily :
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecUnitP2LorentzEinsteinTensorComponentFamily _ _ =
  zeroℚ

factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily :
  FactorVecStressEnergyTensorComponentFamily
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily _ _ =
  zeroℚ

factorVecUnitP2LorentzStressEnergyT00Candidate :
  ℚ
factorVecUnitP2LorentzStressEnergyT00Candidate =
  factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily p2 p2

factorVecUnitP2LorentzStressEnergyT00CandidateIsZero :
  factorVecUnitP2LorentzStressEnergyT00Candidate
  ≡
  zeroℚ
factorVecUnitP2LorentzStressEnergyT00CandidateIsZero =
  refl

data FactorVecP2LorentzUnitStressEnergyIndex : Set where
  stressEnergyT0 :
    FactorVecP2LorentzUnitStressEnergyIndex
  stressEnergyX1 :
    FactorVecP2LorentzUnitStressEnergyIndex
  stressEnergyX2 :
    FactorVecP2LorentzUnitStressEnergyIndex
  stressEnergyX3 :
    FactorVecP2LorentzUnitStressEnergyIndex

factorVecP2LorentzUnitStressEnergyIndexToDirection :
  FactorVecP2LorentzUnitStressEnergyIndex →
  FactorVecTangentDirection
factorVecP2LorentzUnitStressEnergyIndexToDirection stressEnergyT0 =
  p2
factorVecP2LorentzUnitStressEnergyIndexToDirection stressEnergyX1 =
  p3
factorVecP2LorentzUnitStressEnergyIndexToDirection stressEnergyX2 =
  p5
factorVecP2LorentzUnitStressEnergyIndexToDirection stressEnergyX3 =
  p7

factorVecP2LorentzUnitStressEnergyFourBasis :
  List FactorVecP2LorentzUnitStressEnergyIndex
factorVecP2LorentzUnitStressEnergyFourBasis =
  stressEnergyT0
  ∷ stressEnergyX1
  ∷ stressEnergyX2
  ∷ stressEnergyX3
  ∷ []

factorVecValuationP2LorentzUnitStressEnergyComponent :
  FactorVecP2LorentzUnitStressEnergyIndex →
  FactorVecP2LorentzUnitStressEnergyIndex →
  ℚ
factorVecValuationP2LorentzUnitStressEnergyComponent _ _ =
  zeroℚ

factorVecValuationP2LorentzUnitStressEnergyComponentIsTangentZero :
  (mu nu : FactorVecP2LorentzUnitStressEnergyIndex) →
  factorVecValuationP2LorentzUnitStressEnergyComponent mu nu
  ≡
  factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    (factorVecP2LorentzUnitStressEnergyIndexToDirection mu)
    (factorVecP2LorentzUnitStressEnergyIndexToDirection nu)
factorVecValuationP2LorentzUnitStressEnergyComponentIsTangentZero _ _ =
  refl

factorVecValuationP2LorentzUnitStressEnergyComponentZero :
  (mu nu : FactorVecP2LorentzUnitStressEnergyIndex) →
  factorVecValuationP2LorentzUnitStressEnergyComponent mu nu
  ≡
  zeroℚ
factorVecValuationP2LorentzUnitStressEnergyComponentZero _ _ =
  refl

record FactorVecValuationP2LorentzUnitStressEnergyComponentFamily : Setω where
  field
    componentIndex :
      Set

    componentIndexIsP2LorentzFour :
      componentIndex
      ≡
      FactorVecP2LorentzUnitStressEnergyIndex

    componentBasis :
      List FactorVecP2LorentzUnitStressEnergyIndex

    componentBasisIsCanonical :
      componentBasis
      ≡
      factorVecP2LorentzUnitStressEnergyFourBasis

    indexToTangentDirection :
      FactorVecP2LorentzUnitStressEnergyIndex →
      FactorVecTangentDirection

    indexToTangentDirectionIsCanonical :
      indexToTangentDirection
      ≡
      factorVecP2LorentzUnitStressEnergyIndexToDirection

    T :
      FactorVecP2LorentzUnitStressEnergyIndex →
      FactorVecP2LorentzUnitStressEnergyIndex →
      ℚ

    TIsComponentFunction :
      T
      ≡
      factorVecValuationP2LorentzUnitStressEnergyComponent

    tangentComponentFamily :
      FactorVecStressEnergyTensorComponentFamily

    tangentComponentFamilyIsSupportedZeroTable :
      tangentComponentFamily
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    T00 :
      ℚ

    T00IsZero :
      T00 ≡ zeroℚ

    T01 :
      ℚ

    T01IsZero :
      T01 ≡ zeroℚ

    T02 :
      ℚ

    T02IsZero :
      T02 ≡ zeroℚ

    T03 :
      ℚ

    T03IsZero :
      T03 ≡ zeroℚ

    T10 :
      ℚ

    T10IsZero :
      T10 ≡ zeroℚ

    T11 :
      ℚ

    T11IsZero :
      T11 ≡ zeroℚ

    T12 :
      ℚ

    T12IsZero :
      T12 ≡ zeroℚ

    T13 :
      ℚ

    T13IsZero :
      T13 ≡ zeroℚ

    T20 :
      ℚ

    T20IsZero :
      T20 ≡ zeroℚ

    T21 :
      ℚ

    T21IsZero :
      T21 ≡ zeroℚ

    T22 :
      ℚ

    T22IsZero :
      T22 ≡ zeroℚ

    T23 :
      ℚ

    T23IsZero :
      T23 ≡ zeroℚ

    T30 :
      ℚ

    T30IsZero :
      T30 ≡ zeroℚ

    T31 :
      ℚ

    T31IsZero :
      T31 ≡ zeroℚ

    T32 :
      ℚ

    T32IsZero :
      T32 ≡ zeroℚ

    T33 :
      ℚ

    T33IsZero :
      T33 ≡ zeroℚ

    componentAgreesWithTangentZero :
      (mu nu : FactorVecP2LorentzUnitStressEnergyIndex) →
      T mu nu
      ≡
      tangentComponentFamily
        (indexToTangentDirection mu)
        (indexToTangentDirection nu)

    allFourComponentsZero :
      (mu nu : FactorVecP2LorentzUnitStressEnergyIndex) →
      T mu nu
      ≡
      zeroℚ

    fullComponentFamilyBoundary :
      List String

factorVecUnitP2LorentzStressEnergyT11Candidate :
  ℚ
factorVecUnitP2LorentzStressEnergyT11Candidate =
  factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily p3 p3

factorVecUnitP2LorentzStressEnergyT11CandidateIsZero :
  factorVecUnitP2LorentzStressEnergyT11Candidate
  ≡
  zeroℚ
factorVecUnitP2LorentzStressEnergyT11CandidateIsZero =
  refl

factorVecUnitP2LorentzStressEnergyT22Candidate :
  ℚ
factorVecUnitP2LorentzStressEnergyT22Candidate =
  factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily p5 p5

factorVecUnitP2LorentzStressEnergyT22CandidateIsZero :
  factorVecUnitP2LorentzStressEnergyT22Candidate
  ≡
  zeroℚ
factorVecUnitP2LorentzStressEnergyT22CandidateIsZero =
  refl

factorVecUnitP2LorentzStressEnergyT33Candidate :
  ℚ
factorVecUnitP2LorentzStressEnergyT33Candidate =
  factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily p7 p7

factorVecUnitP2LorentzStressEnergyT33CandidateIsZero :
  factorVecUnitP2LorentzStressEnergyT33Candidate
  ≡
  zeroℚ
factorVecUnitP2LorentzStressEnergyT33CandidateIsZero =
  refl

factorVecUnitP2LorentzStressEnergyOffDiagonalP2P3Candidate :
  ℚ
factorVecUnitP2LorentzStressEnergyOffDiagonalP2P3Candidate =
  factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily p2 p3

factorVecUnitP2LorentzStressEnergyOffDiagonalP2P3CandidateIsZero :
  factorVecUnitP2LorentzStressEnergyOffDiagonalP2P3Candidate
  ≡
  zeroℚ
factorVecUnitP2LorentzStressEnergyOffDiagonalP2P3CandidateIsZero =
  refl

factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilySymmetry :
  FactorVecStressEnergyTensorSymmetryLaw
    factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilySymmetry _ _ =
  refl

factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyFiniteSupport :
  FactorVecStressEnergyTensorFiniteSupportLaw
    factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyFiniteSupport _ _ =
  refl

factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding :
  FactorVecStressEnergyTensorCarrierEmbeddingLaw
    factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p2 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p3 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p5 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p7 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p11 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p13 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p17 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p19 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p23 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p29 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p31 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p41 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p47 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p59 =
  refl
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding _ p71 =
  refl

canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily :
  FactorVecValuationP2LorentzUnitStressEnergyComponentFamily
canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily =
  record
    { componentIndex =
        FactorVecP2LorentzUnitStressEnergyIndex
    ; componentIndexIsP2LorentzFour =
        refl
    ; componentBasis =
        factorVecP2LorentzUnitStressEnergyFourBasis
    ; componentBasisIsCanonical =
        refl
    ; indexToTangentDirection =
        factorVecP2LorentzUnitStressEnergyIndexToDirection
    ; indexToTangentDirectionIsCanonical =
        refl
    ; T =
        factorVecValuationP2LorentzUnitStressEnergyComponent
    ; TIsComponentFunction =
        refl
    ; tangentComponentFamily =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    ; tangentComponentFamilyIsSupportedZeroTable =
        refl
    ; T00 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyT0 stressEnergyT0
    ; T00IsZero =
        refl
    ; T01 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyT0 stressEnergyX1
    ; T01IsZero =
        refl
    ; T02 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyT0 stressEnergyX2
    ; T02IsZero =
        refl
    ; T03 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyT0 stressEnergyX3
    ; T03IsZero =
        refl
    ; T10 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX1 stressEnergyT0
    ; T10IsZero =
        refl
    ; T11 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX1 stressEnergyX1
    ; T11IsZero =
        refl
    ; T12 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX1 stressEnergyX2
    ; T12IsZero =
        refl
    ; T13 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX1 stressEnergyX3
    ; T13IsZero =
        refl
    ; T20 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX2 stressEnergyT0
    ; T20IsZero =
        refl
    ; T21 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX2 stressEnergyX1
    ; T21IsZero =
        refl
    ; T22 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX2 stressEnergyX2
    ; T22IsZero =
        refl
    ; T23 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX2 stressEnergyX3
    ; T23IsZero =
        refl
    ; T30 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX3 stressEnergyT0
    ; T30IsZero =
        refl
    ; T31 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX3 stressEnergyX1
    ; T31IsZero =
        refl
    ; T32 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX3 stressEnergyX2
    ; T32IsZero =
        refl
    ; T33 =
        factorVecValuationP2LorentzUnitStressEnergyComponent stressEnergyX3 stressEnergyX3
    ; T33IsZero =
        refl
    ; componentAgreesWithTangentZero =
        factorVecValuationP2LorentzUnitStressEnergyComponentIsTangentZero
    ; allFourComponentsZero =
        factorVecValuationP2LorentzUnitStressEnergyComponentZero
    ; fullComponentFamilyBoundary =
        "The p2-time Lorentz stress-energy staging now names all sixteen T00..T33 components over the selected four directions p2,p3,p5,p7"
        ∷ "Each named component is definitionally zero and agrees with the bounded tangent-direction zero-table family"
        ∷ "This is a local flat supported chart component family; it is not an authority-backed matter tensor"
        ∷ []
    }

FactorVecEinsteinSourceCouplingLaw :
  FactorVecStressEnergyTensorComponentFamily →
  Set
FactorVecEinsteinSourceCouplingLaw tensor =
  (mu nu : FactorVecTangentDirection) →
  factorVecUnitP2LorentzEinsteinTensorComponentFamily mu nu
  ≡
  tensor mu nu

factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyEinsteinSourceCoupling :
  FactorVecEinsteinSourceCouplingLaw
    factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyEinsteinSourceCoupling _ _ =
  refl

record FactorVecConstantDiagonalNondegenerateSignaturePrimitiveRequest : Setω where
  field
    candidateMetric :
      FactorVecSymmetricRationalBilinearMetric

    basisShapeWitness :
      FactorVecConstantDiagonalBasisShapeWitness

    finiteFreeMatrixWitness :
      FactorVecFiniteFreeTangentModuleMatrixWitness

    determinantProductTarget :
      FactorVecDiagonalDeterminantProductTarget

    finiteSignatureTarget :
      FactorVecMetricSignatureTarget

    targetIsPositiveFifteenPrimeLaneSignature :
      finiteSignatureTarget
      ≡
      positiveFifteenPrimeLaneSignature

    blockers :
      List FactorVecNondegenerateSignatureBlocker

    blockersAreCanonical :
      blockers
      ≡
      canonicalFactorVecConstantDiagonalNondegenerateSignatureBlockers

    firstMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveIsNondegenerateProof :
      firstMetricPrimitive
      ≡
      missingConstantDiagonalNondegenerateProof

    secondMetricPrimitive :
      FactorVecMetricGRPrimitive

    secondMetricPrimitiveIsSignatureProof :
      secondMetricPrimitive
      ≡
      missingConstantDiagonalSignatureProof

    requestBoundary :
      List String

record FactorVecConstantDiagonalReciprocalPrimeMetricSurface : Setω where
  field
    metric :
      FactorVecSymmetricRationalBilinearMetric

    basisShapeWitness :
      FactorVecConstantDiagonalBasisShapeWitness

    diagonalWeight :
      FactorVecTangentDirection →
      ℚ

    metricComponent :
      GL.FactorVec →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    metricComponentIsCanonical :
      metricComponent
      ≡
      factorVecConstantDiagonalReciprocalPrimeMetric

    constantInBaseBoundary :
      List String

    finiteSignatureTarget :
      FactorVecMetricSignatureTarget

    missingNondegeneratePrimitive :
      FactorVecMetricGRPrimitive

    missingNondegeneratePrimitiveIsRecorded :
      missingNondegeneratePrimitive
      ≡
      missingConstantDiagonalNondegenerateProof

    missingSignaturePrimitive :
      FactorVecMetricGRPrimitive

    missingSignaturePrimitiveIsRecorded :
      missingSignaturePrimitive
      ≡
      missingConstantDiagonalSignatureProof

    nondegenerateSignaturePrimitiveRequest :
      FactorVecConstantDiagonalNondegenerateSignaturePrimitiveRequest

    flatnessCandidateBoundary :
      List String

FactorVecValuationDependentSiteMetricType :
  Set
FactorVecValuationDependentSiteMetricType =
  GL.FactorVec →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ

record FactorVecValuationP2LorentzDiagonalShapeWitness : Setω where
  field
    metricComponent :
      FactorVecValuationDependentSiteMetricType

    metricComponentIsP2LorentzCandidate :
      metricComponent
      ≡
      factorVecValuationDependentP2LorentzMetric

    selectedTimePrime :
      FactorVecCommittedTimePrime

    selectedTimePrimeDirection :
      FactorVecTangentDirection

    selectedTimePrimeDirectionIsP2 :
      selectedTimePrimeDirection
      ≡
      p2

    selfComponentLaw :
      (base : GL.FactorVec) →
      (mu : FactorVecTangentDirection) →
      metricComponent base mu mu
      ≡
      factorVecP2LorentzSignedValuationWeight base mu

    timeComponentLaw :
      (base : GL.FactorVec) →
      metricComponent base p2 p2
      ≡
      (zeroℚ -ℚ factorVecValuationDiagonalWeight base p2)

    spatialSelfComponentLaw :
      (base : GL.FactorVec) →
      (mu : FactorVecTangentDirection) →
      (mu ≡ p2 → ⊥) →
      metricComponent base mu mu
      ≡
      factorVecValuationDiagonalWeight base mu

    offDiagonalZeroLaw :
      (base : GL.FactorVec) →
      (mu nu : FactorVecTangentDirection) →
      (mu ≡ nu → ⊥) →
      metricComponent base mu nu
      ≡
      zeroℚ

    diagonalShapeBoundary :
      List String

record FactorVecValuationAllLaneNonzeroSupportWitness : Setω where
  field
    supportBase :
      GL.FactorVec

    supportBaseIsUnitValuation :
      supportBase
      ≡
      factorVecUnitValuationSupportBase

    allLaneDepthNonzero :
      (mu : FactorVecTangentDirection) →
      FactorVecPositiveExponent (factorVecValuationDepth supportBase mu)

    supportBoundary :
      List String

factorVecP2LorentzSignedValuationWeightVector :
  GL.FactorVec →
  FactorVecQCoefficientVector
factorVecP2LorentzSignedValuationWeightVector base =
  qv15
    (factorVecP2LorentzSignedValuationWeight base p2)
    (factorVecP2LorentzSignedValuationWeight base p3)
    (factorVecP2LorentzSignedValuationWeight base p5)
    (factorVecP2LorentzSignedValuationWeight base p7)
    (factorVecP2LorentzSignedValuationWeight base p11)
    (factorVecP2LorentzSignedValuationWeight base p13)
    (factorVecP2LorentzSignedValuationWeight base p17)
    (factorVecP2LorentzSignedValuationWeight base p19)
    (factorVecP2LorentzSignedValuationWeight base p23)
    (factorVecP2LorentzSignedValuationWeight base p29)
    (factorVecP2LorentzSignedValuationWeight base p31)
    (factorVecP2LorentzSignedValuationWeight base p41)
    (factorVecP2LorentzSignedValuationWeight base p47)
    (factorVecP2LorentzSignedValuationWeight base p59)
    (factorVecP2LorentzSignedValuationWeight base p71)

factorVecP2LorentzSignedValuationWeightVectorCoordinate :
  (base : GL.FactorVec) →
  (mu : FactorVecTangentDirection) →
  factorVecQCoordinate
    mu
    (factorVecP2LorentzSignedValuationWeightVector base)
  ≡
  factorVecP2LorentzSignedValuationWeight base mu
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p2 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p3 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p5 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p7 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p11 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p13 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p17 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p19 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p23 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p29 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p31 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p41 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p47 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p59 =
  refl
factorVecP2LorentzSignedValuationWeightVectorCoordinate _ p71 =
  refl

factorVecP2LorentzSignedValuationWeightVectorTimeCoordinate :
  (base : GL.FactorVec) →
  factorVecQCoordinate
    p2
    (factorVecP2LorentzSignedValuationWeightVector base)
  ≡
  (zeroℚ -ℚ factorVecValuationDiagonalWeight base p2)
factorVecP2LorentzSignedValuationWeightVectorTimeCoordinate base with p2 ≟ p2
... | yes refl =
  refl
... | no neq =
  ⊥-elim (neq refl)

factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate :
  (base : GL.FactorVec) →
  (mu : FactorVecTangentDirection) →
  (mu ≡ p2 → ⊥) →
  factorVecQCoordinate
    mu
    (factorVecP2LorentzSignedValuationWeightVector base)
  ≡
  factorVecValuationDiagonalWeight base mu
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p2 notTime =
  ⊥-elim (notTime refl)
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p3 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p5 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p7 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p11 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p13 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p17 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p19 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p23 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p29 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p31 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p41 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p47 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p59 _ =
  refl
factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate _ p71 _ =
  refl

factorVecUnitValuationDiagonalWeightPositive :
  (mu : FactorVecTangentDirection) →
  R.Positive
    (factorVecValuationDiagonalWeight factorVecUnitValuationSupportBase mu)
factorVecUnitValuationDiagonalWeightPositive p2 =
  _
factorVecUnitValuationDiagonalWeightPositive p3 =
  _
factorVecUnitValuationDiagonalWeightPositive p5 =
  _
factorVecUnitValuationDiagonalWeightPositive p7 =
  _
factorVecUnitValuationDiagonalWeightPositive p11 =
  _
factorVecUnitValuationDiagonalWeightPositive p13 =
  _
factorVecUnitValuationDiagonalWeightPositive p17 =
  _
factorVecUnitValuationDiagonalWeightPositive p19 =
  _
factorVecUnitValuationDiagonalWeightPositive p23 =
  _
factorVecUnitValuationDiagonalWeightPositive p29 =
  _
factorVecUnitValuationDiagonalWeightPositive p31 =
  _
factorVecUnitValuationDiagonalWeightPositive p41 =
  _
factorVecUnitValuationDiagonalWeightPositive p47 =
  _
factorVecUnitValuationDiagonalWeightPositive p59 =
  _
factorVecUnitValuationDiagonalWeightPositive p71 =
  _

factorVecUnitValuationDiagonalWeightNonzero :
  (mu : FactorVecTangentDirection) →
  R.NonZero
    (factorVecValuationDiagonalWeight factorVecUnitValuationSupportBase mu)
factorVecUnitValuationDiagonalWeightNonzero mu =
  Rₚ.pos⇒nonZero
    (factorVecValuationDiagonalWeight factorVecUnitValuationSupportBase mu)
    {{factorVecUnitValuationDiagonalWeightPositive mu}}

factorVecUnitP2LorentzSignedWeightTimeNegative :
  R.Negative
    (factorVecP2LorentzSignedValuationWeight
      factorVecUnitValuationSupportBase
      p2)
factorVecUnitP2LorentzSignedWeightTimeNegative =
  _

factorVecUnitP2LorentzSignedWeightTimeNonzero :
  R.NonZero
    (factorVecP2LorentzSignedValuationWeight
      factorVecUnitValuationSupportBase
      p2)
factorVecUnitP2LorentzSignedWeightTimeNonzero =
  Rₚ.neg⇒nonZero
    (factorVecP2LorentzSignedValuationWeight
      factorVecUnitValuationSupportBase
      p2)
    {{factorVecUnitP2LorentzSignedWeightTimeNegative}}

factorVecUnitP2LorentzSignedWeightSpatialPositive :
  (mu : FactorVecTangentDirection) →
  (mu ≡ p2 → ⊥) →
  R.Positive
    (factorVecP2LorentzSignedValuationWeight
      factorVecUnitValuationSupportBase
      mu)
factorVecUnitP2LorentzSignedWeightSpatialPositive p2 notTime =
  ⊥-elim (notTime refl)
factorVecUnitP2LorentzSignedWeightSpatialPositive p3 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p5 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p7 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p11 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p13 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p17 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p19 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p23 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p29 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p31 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p41 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p47 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p59 _ =
  _
factorVecUnitP2LorentzSignedWeightSpatialPositive p71 _ =
  _

factorVecUnitP2LorentzSignedWeightSpatialNonzero :
  (mu : FactorVecTangentDirection) →
  (mu ≡ p2 → ⊥) →
  R.NonZero
    (factorVecP2LorentzSignedValuationWeight
      factorVecUnitValuationSupportBase
      mu)
factorVecUnitP2LorentzSignedWeightSpatialNonzero mu notTime =
  Rₚ.pos⇒nonZero
    (factorVecP2LorentzSignedValuationWeight
      factorVecUnitValuationSupportBase
      mu)
    {{factorVecUnitP2LorentzSignedWeightSpatialPositive mu notTime}}

factorVecUnitP2LorentzSignedWeightNonzero :
  (mu : FactorVecTangentDirection) →
  R.NonZero
    (factorVecP2LorentzSignedValuationWeight
      factorVecUnitValuationSupportBase
      mu)
factorVecUnitP2LorentzSignedWeightNonzero p2 =
  factorVecUnitP2LorentzSignedWeightTimeNonzero
factorVecUnitP2LorentzSignedWeightNonzero p3 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p3 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p5 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p5 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p7 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p7 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p11 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p11 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p13 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p13 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p17 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p17 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p19 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p19 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p23 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p23 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p29 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p29 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p31 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p31 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p41 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p41 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p47 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p47 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p59 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p59 (λ ())
factorVecUnitP2LorentzSignedWeightNonzero p71 =
  factorVecUnitP2LorentzSignedWeightSpatialNonzero p71 (λ ())

factorVecUnitP2LorentzMetricSelfNonzero :
  (mu : FactorVecTangentDirection) →
  R.NonZero
    (factorVecValuationDependentP2LorentzMetric
      factorVecUnitValuationSupportBase
      mu
      mu)
factorVecUnitP2LorentzMetricSelfNonzero mu with mu ≟ mu
... | yes refl =
  factorVecUnitP2LorentzSignedWeightNonzero mu
... | no neq =
  ⊥-elim (neq refl)

factorVecUnitP2LorentzInertiaLane :
  FactorVecTangentDirection →
  FactorVecP2LorentzInertiaLane
factorVecUnitP2LorentzInertiaLane p2 =
  timeLikeP2Lane
factorVecUnitP2LorentzInertiaLane p3 =
  spatialLikeNonP2Lane p3
factorVecUnitP2LorentzInertiaLane p5 =
  spatialLikeNonP2Lane p5
factorVecUnitP2LorentzInertiaLane p7 =
  spatialLikeNonP2Lane p7
factorVecUnitP2LorentzInertiaLane p11 =
  spatialLikeNonP2Lane p11
factorVecUnitP2LorentzInertiaLane p13 =
  spatialLikeNonP2Lane p13
factorVecUnitP2LorentzInertiaLane p17 =
  spatialLikeNonP2Lane p17
factorVecUnitP2LorentzInertiaLane p19 =
  spatialLikeNonP2Lane p19
factorVecUnitP2LorentzInertiaLane p23 =
  spatialLikeNonP2Lane p23
factorVecUnitP2LorentzInertiaLane p29 =
  spatialLikeNonP2Lane p29
factorVecUnitP2LorentzInertiaLane p31 =
  spatialLikeNonP2Lane p31
factorVecUnitP2LorentzInertiaLane p41 =
  spatialLikeNonP2Lane p41
factorVecUnitP2LorentzInertiaLane p47 =
  spatialLikeNonP2Lane p47
factorVecUnitP2LorentzInertiaLane p59 =
  spatialLikeNonP2Lane p59
factorVecUnitP2LorentzInertiaLane p71 =
  spatialLikeNonP2Lane p71

record FactorVecValuationP2LorentzSignedWeightVectorWitness : Setω where
  field
    supportWitness :
      FactorVecValuationAllLaneNonzeroSupportWitness

    supportBase :
      GL.FactorVec

    supportBaseIsUnitValuation :
      supportBase
      ≡
      factorVecUnitValuationSupportBase

    signedWeightVector :
      FactorVecQCoefficientVector

    signedWeightVectorIsCanonical :
      signedWeightVector
      ≡
      factorVecP2LorentzSignedValuationWeightVector supportBase

    coordinateLaw :
      (mu : FactorVecTangentDirection) →
      factorVecQCoordinate mu signedWeightVector
      ≡
      factorVecP2LorentzSignedValuationWeight supportBase mu

    timeCoordinateLaw :
      factorVecQCoordinate p2 signedWeightVector
      ≡
      (zeroℚ -ℚ factorVecValuationDiagonalWeight supportBase p2)

    spatialCoordinateLaw :
      (mu : FactorVecTangentDirection) →
      (mu ≡ p2 → ⊥) →
      factorVecQCoordinate mu signedWeightVector
      ≡
      factorVecValuationDiagonalWeight supportBase mu

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsNondegenerate :
      firstRemainingMetricPrimitive
      ≡
      missingValuationMetricNondegenerateProof

    signedWeightBoundary :
      List String

record FactorVecValuationP2LorentzRationalNonzeroWeightWitness : Setω where
  field
    signedWeightVectorWitness :
      FactorVecValuationP2LorentzSignedWeightVectorWitness

    diagonalPositive :
      (mu : FactorVecTangentDirection) →
      R.Positive
        (factorVecValuationDiagonalWeight factorVecUnitValuationSupportBase mu)

    diagonalNonzero :
      (mu : FactorVecTangentDirection) →
      R.NonZero
        (factorVecValuationDiagonalWeight factorVecUnitValuationSupportBase mu)

    timeSignedNegative :
      R.Negative
        (factorVecP2LorentzSignedValuationWeight
          factorVecUnitValuationSupportBase
          p2)

    timeSignedNonzero :
      R.NonZero
        (factorVecP2LorentzSignedValuationWeight
          factorVecUnitValuationSupportBase
          p2)

    spatialSignedPositive :
      (mu : FactorVecTangentDirection) →
      (mu ≡ p2 → ⊥) →
      R.Positive
        (factorVecP2LorentzSignedValuationWeight
          factorVecUnitValuationSupportBase
          mu)

    spatialSignedNonzero :
      (mu : FactorVecTangentDirection) →
      (mu ≡ p2 → ⊥) →
      R.NonZero
        (factorVecP2LorentzSignedValuationWeight
          factorVecUnitValuationSupportBase
          mu)

    inertiaLaneClassifier :
      FactorVecTangentDirection →
      FactorVecP2LorentzInertiaLane

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsNondegenerate :
      firstRemainingMetricPrimitive
      ≡
      missingValuationMetricNondegenerateProof

    nonzeroWeightBoundary :
      List String

record FactorVecValuationP2TimePrimeMetricWitness : Setω where
  field
    metricComponent :
      FactorVecValuationDependentSiteMetricType

    metricComponentIsP2LorentzCandidate :
      metricComponent
      ≡
      factorVecValuationDependentP2LorentzMetric

    selectedTimePrime :
      FactorVecCommittedTimePrime

    selectedTimePrimeDirection :
      FactorVecTangentDirection

    selectedTimePrimeDirectionIsP2 :
      selectedTimePrimeDirection
      ≡
      p2

    metricSymmetric :
      (base : GL.FactorVec) →
      (mu nu : FactorVecTangentDirection) →
      metricComponent base mu nu
      ≡
      metricComponent base nu mu

    diagonalShapeWitness :
      FactorVecValuationP2LorentzDiagonalShapeWitness

    signedWeightVectorWitness :
      FactorVecValuationP2LorentzSignedWeightVectorWitness

    rationalNonzeroWeightWitness :
      FactorVecValuationP2LorentzRationalNonzeroWeightWitness

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsNondegenerate :
      firstRemainingMetricPrimitive
      ≡
      missingValuationMetricNondegenerateProof

    timePrimeMetricBoundary :
      List String

record FactorVecValuationP2LorentzRankNondegenerateWitness : Setω where
  field
    rationalNonzeroWeightWitness :
      FactorVecValuationP2LorentzRationalNonzeroWeightWitness

    supportBase :
      GL.FactorVec

    supportBaseIsUnitValuation :
      supportBase
      ≡
      factorVecUnitValuationSupportBase

    metricComponent :
      FactorVecValuationDependentSiteMetricType

    metricComponentIsP2LorentzCandidate :
      metricComponent
      ≡
      factorVecValuationDependentP2LorentzMetric

    selfComponentNonzero :
      (mu : FactorVecTangentDirection) →
      R.NonZero (metricComponent supportBase mu mu)

    offDiagonalZeroLaw :
      (mu nu : FactorVecTangentDirection) →
      (mu ≡ nu → ⊥) →
      metricComponent supportBase mu nu
      ≡
      zeroℚ

    finiteRankCarrier :
      Set

    finiteRankCarrierIsQ15 :
      finiteRankCarrier
      ≡
      FactorVecQCoefficientVector

    nondegenerateMetricPrimitiveDischarged :
      FactorVecMetricGRPrimitive

    nondegenerateMetricPrimitiveDischargedIsValuationNondegenerate :
      nondegenerateMetricPrimitiveDischarged
      ≡
      missingValuationMetricNondegenerateProof

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsSignature :
      firstRemainingMetricPrimitive
      ≡
      missingValuationMetricSignatureProof

    rankBoundary :
      List String

record FactorVecValuationP2LorentzSylvesterInertiaWitness : Setω where
  field
    rankNondegenerateWitness :
      FactorVecValuationP2LorentzRankNondegenerateWitness

    inertiaLaneClassifier :
      FactorVecTangentDirection →
      FactorVecP2LorentzInertiaLane

    inertiaLaneClassifierIsCanonical :
      inertiaLaneClassifier
      ≡
      factorVecUnitP2LorentzInertiaLane

    timeLaneIsTimelikeP2 :
      inertiaLaneClassifier p2
      ≡
      timeLikeP2Lane

    spatialLanesAreNonP2Spatial :
      (mu : FactorVecTangentDirection) →
      (mu ≡ p2 → ⊥) →
      inertiaLaneClassifier mu
      ≡
      spatialLikeNonP2Lane mu

    timeSignedWeightNegative :
      R.Negative
        (factorVecP2LorentzSignedValuationWeight
          factorVecUnitValuationSupportBase
          p2)

    spatialSignedWeightPositive :
      (mu : FactorVecTangentDirection) →
      (mu ≡ p2 → ⊥) →
      R.Positive
        (factorVecP2LorentzSignedValuationWeight
          factorVecUnitValuationSupportBase
          mu)

    signatureMetricPrimitiveDischarged :
      FactorVecMetricGRPrimitive

    signatureMetricPrimitiveDischargedIsValuationSignature :
      signatureMetricPrimitiveDischarged
      ≡
      missingValuationMetricSignatureProof

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsInverseMetric :
      firstRemainingMetricPrimitive
      ≡
      missingValuationInverseMetricComputation

    inertiaBoundary :
      List String

record MetricNondegenerateSignature : Setω where
  field
    constantDiagonalDeterminantTarget :
      FactorVecDiagonalDeterminantProductTarget

    constantDiagonalNondegenerateSignatureRequest :
      FactorVecConstantDiagonalNondegenerateSignaturePrimitiveRequest

    valuationRankNondegenerateWitness :
      FactorVecValuationP2LorentzRankNondegenerateWitness

    valuationSylvesterInertiaWitness :
      FactorVecValuationP2LorentzSylvesterInertiaWitness

    valuationNondegeneratePrimitiveDischarged :
      FactorVecMetricGRPrimitive

    valuationNondegeneratePrimitiveDischargedIsExpected :
      valuationNondegeneratePrimitiveDischarged
      ≡
      missingValuationMetricNondegenerateProof

    valuationSignaturePrimitiveDischarged :
      FactorVecMetricGRPrimitive

    valuationSignaturePrimitiveDischargedIsExpected :
      valuationSignaturePrimitiveDischarged
      ≡
      missingValuationMetricSignatureProof

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsInverseMetric :
      firstRemainingMetricPrimitive
      ≡
      missingValuationInverseMetricComputation

    witnessBoundary :
      List String

factorVecUnitP2LorentzInverseHalf :
  ℚ
factorVecUnitP2LorentzInverseHalf =
  (+ 1) R./ 2

factorVecUnitP2LorentzNegativeInverseHalf :
  ℚ
factorVecUnitP2LorentzNegativeInverseHalf =
  zeroℚ -ℚ factorVecUnitP2LorentzInverseHalf

factorVecUnitP2LorentzInverseMetric :
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecUnitP2LorentzInverseMetric mu nu with mu ≟ nu
... | no _ =
  zeroℚ
... | yes _ with mu ≟ p2
...   | yes _ =
  factorVecUnitP2LorentzNegativeInverseHalf
...   | no _ =
  factorVecUnitP2LorentzInverseHalf

record FactorVecValuationP2LorentzUnitInverseMetricWitness : Setω where
  field
    sylvesterInertiaWitness :
      FactorVecValuationP2LorentzSylvesterInertiaWitness

    unitInverseMetric :
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    unitInverseMetricIsP2LorentzDiagonal :
      unitInverseMetric
      ≡
      factorVecUnitP2LorentzInverseMetric

    inverseMetricPrimitiveDischarged :
      FactorVecMetricGRPrimitive

    inverseMetricPrimitiveDischargedIsValuationInverse :
      inverseMetricPrimitiveDischarged
      ≡
      missingValuationInverseMetricComputation

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsChristoffel :
      firstRemainingMetricPrimitive
      ≡
      missingValuationLeviCivitaChristoffelComputation

    inverseMetricBoundary :
      List String

factorVecUnitP2LorentzChristoffelSymbol :
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecUnitP2LorentzChristoffelSymbol _ _ _ =
  zeroℚ

record FactorVecValuationP2LorentzUnitChristoffelWitness : Setω where
  field
    unitInverseMetricWitness :
      FactorVecValuationP2LorentzUnitInverseMetricWitness

    unitChristoffelSymbol :
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    unitChristoffelSymbolIsZeroTable :
      unitChristoffelSymbol
      ≡
      factorVecUnitP2LorentzChristoffelSymbol

    christoffelPrimitiveDischarged :
      FactorVecMetricGRPrimitive

    christoffelPrimitiveDischargedIsValuationChristoffel :
      christoffelPrimitiveDischarged
      ≡
      missingValuationLeviCivitaChristoffelComputation

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsRiemann :
      firstRemainingMetricPrimitive
      ≡
      missingValuationRiemannCurvatureComputation

    unitChristoffelBoundary :
      List String

record FactorVecValuationP2LorentzUnitInverseChristoffelProgress : Setω where
  field
    unitInverseMetricWitness :
      FactorVecValuationP2LorentzUnitInverseMetricWitness

    unitChristoffelWitness :
      FactorVecValuationP2LorentzUnitChristoffelWitness

    firstMetricPrimitiveAfterUnitInverse :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterUnitInverseIsChristoffel :
      firstMetricPrimitiveAfterUnitInverse
      ≡
      missingValuationLeviCivitaChristoffelComputation

    firstMetricPrimitiveAfterUnitChristoffel :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterUnitChristoffelIsRiemann :
      firstMetricPrimitiveAfterUnitChristoffel
      ≡
      missingValuationRiemannCurvatureComputation

    inverseChristoffelProgressBoundary :
      List String

record FactorVecValuationP2LorentzSignatureInverseHandoffProgress : Setω where
  field
    metricNondegenerateSignatureWitness :
      MetricNondegenerateSignature

    unitInverseChristoffelProgress :
      FactorVecValuationP2LorentzUnitInverseChristoffelProgress

    firstMetricPrimitiveAfterInertia :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterInertiaIsInverseMetric :
      firstMetricPrimitiveAfterInertia
      ≡
      missingValuationInverseMetricComputation

    firstMetricPrimitiveAfterUnitInverse :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterUnitInverseIsChristoffel :
      firstMetricPrimitiveAfterUnitInverse
      ≡
      missingValuationLeviCivitaChristoffelComputation

    signatureInverseHandoffBoundary :
      List String

factorVecUnitP2LorentzRiemannTensor :
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecUnitP2LorentzRiemannTensor _ _ _ _ =
  zeroℚ

factorVecUnitP2LorentzRicciTensor :
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecUnitP2LorentzRicciTensor _ _ =
  zeroℚ

factorVecUnitP2LorentzScalarCurvature :
  ℚ
factorVecUnitP2LorentzScalarCurvature =
  zeroℚ

factorVecUnitP2LorentzEinsteinTensor :
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecUnitP2LorentzEinsteinTensor =
  factorVecUnitP2LorentzEinsteinTensorComponentFamily

factorVecUnitP2LorentzContractedBianchiDivergence :
  FactorVecTangentDirection →
  ℚ
factorVecUnitP2LorentzContractedBianchiDivergence _ =
  zeroℚ

FactorVecStressEnergyCovariantDivergenceLaw :
  FactorVecStressEnergyTensorComponentFamily →
  Set
FactorVecStressEnergyCovariantDivergenceLaw tensor =
  (mu : FactorVecTangentDirection) →
  factorVecUnitP2LorentzContractedBianchiDivergence mu
  ≡
  tensor mu p2

factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility :
  FactorVecStressEnergyCovariantDivergenceLaw
    factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility _ =
  refl

factorVecFormalYMStressEnergyTensorShape :
  String
factorVecFormalYMStressEnergyTensorShape =
  "YM-T-mu-nu=trace(F-mu-alpha F-nu^alpha)-one-quarter g-mu-nu trace(F-alpha-beta F^alpha-beta)"

factorVecContractedBianchiStressEnergyConservationTargetShape :
  String
factorVecContractedBianchiStressEnergyConservationTargetShape =
  "contracted-Bianchi-target=nabla^mu T-mu-nu=0 over the same FactorVec tangent direction family"

factorVecDASHIMatterLagrangianFormula :
  String
factorVecDASHIMatterLagrangianFormula =
  "L_DASHI(fv,A)=1/2 trace(F_A.F_A)+<fv,D_A fv>"

factorVecMetricVariationStressEnergyTensorShape :
  String
factorVecMetricVariationStressEnergyTensorShape =
  "T_mu_nu=-(2/sqrt(-g))*delta(sqrt(-g)*L_DASHI)/delta(g^mu_nu)"

FactorVecStressEnergyIdentityLorentzGaugeInvarianceLaw :
  FactorVecStressEnergyTensorComponentFamily →
  Set
FactorVecStressEnergyIdentityLorentzGaugeInvarianceLaw tensor =
  (mu nu : FactorVecTangentDirection) →
  tensor mu nu
  ≡
  tensor mu nu

factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyIdentityLorentzGaugeInvariant :
  FactorVecStressEnergyIdentityLorentzGaugeInvarianceLaw
    factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyIdentityLorentzGaugeInvariant _ _ =
  refl

record FactorVecValuationP2LorentzUnitRiemannWitness : Setω where
  field
    unitChristoffelWitness :
      FactorVecValuationP2LorentzUnitChristoffelWitness

    unitRiemannTensor :
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    unitRiemannTensorIsZeroTable :
      unitRiemannTensor
      ≡
      factorVecUnitP2LorentzRiemannTensor

    riemannPrimitiveDischarged :
      FactorVecMetricGRPrimitive

    riemannPrimitiveDischargedIsValuationRiemann :
      riemannPrimitiveDischarged
      ≡
      missingValuationRiemannCurvatureComputation

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsRicci :
      firstRemainingMetricPrimitive
      ≡
      missingValuationRicciContractionComputation

    unitRiemannBoundary :
      List String

record FactorVecValuationP2LorentzUnitRicciWitness : Setω where
  field
    unitRiemannWitness :
      FactorVecValuationP2LorentzUnitRiemannWitness

    unitRicciTensor :
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    unitRicciTensorIsZeroTable :
      unitRicciTensor
      ≡
      factorVecUnitP2LorentzRicciTensor

    ricciPrimitiveDischarged :
      FactorVecMetricGRPrimitive

    ricciPrimitiveDischargedIsValuationRicci :
      ricciPrimitiveDischarged
      ≡
      missingValuationRicciContractionComputation

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsContractedBianchi :
      firstRemainingMetricPrimitive
      ≡
      missingValuationContractedBianchiComputation

    unitRicciBoundary :
      List String

record FactorVecValuationP2LorentzUnitScalarCurvatureWitness : Setω where
  field
    unitRicciWitness :
      FactorVecValuationP2LorentzUnitRicciWitness

    unitScalarCurvature :
      ℚ

    unitScalarCurvatureIsZero :
      unitScalarCurvature
      ≡
      factorVecUnitP2LorentzScalarCurvature

    unitScalarCurvatureBoundary :
      List String

record FactorVecValuationP2LorentzUnitEinsteinTensorWitness : Setω where
  field
    unitScalarCurvatureWitness :
      FactorVecValuationP2LorentzUnitScalarCurvatureWitness

    unitEinsteinTensor :
      FactorVecTangentDirection →
      FactorVecTangentDirection →
      ℚ

    unitEinsteinTensorIsZeroTable :
      unitEinsteinTensor
      ≡
      factorVecUnitP2LorentzEinsteinTensor

    unitEinsteinTensorBoundary :
      List String

record FactorVecValuationP2LorentzUnitContractedBianchiWitness : Setω where
  field
    unitRicciWitness :
      FactorVecValuationP2LorentzUnitRicciWitness

    unitContractedBianchiDivergence :
      FactorVecTangentDirection →
      ℚ

    unitContractedBianchiDivergenceIsZeroTable :
      unitContractedBianchiDivergence
      ≡
      factorVecUnitP2LorentzContractedBianchiDivergence

    contractedBianchiPrimitiveDischarged :
      FactorVecMetricGRPrimitive

    contractedBianchiPrimitiveDischargedIsValuationContractedBianchi :
      contractedBianchiPrimitiveDischarged
      ≡
      missingValuationContractedBianchiComputation

    firstRemainingMetricPrimitive :
      FactorVecMetricGRPrimitive

    firstRemainingMetricPrimitiveIsStressEnergy :
      firstRemainingMetricPrimitive
      ≡
      missingValuationStressEnergyCompatibilityComputation

    unitContractedBianchiBoundary :
      List String

record FactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest : Setω where
  field
    stressEnergyCompatibilityPrimitive :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    stressEnergyCompatibilityPrimitiveIsTensorCandidate :
      stressEnergyCompatibilityPrimitive
      ≡
      missingValuationStressEnergyTensorCandidate

    missingTensorCandidatePrimitives :
      List FactorVecStressEnergyTensorCandidateMissingPrimitive

    missingTensorCandidatePrimitivesAreCanonical :
      missingTensorCandidatePrimitives
      ≡
      canonicalFactorVecStressEnergyTensorCandidateMissingPrimitives

    firstMissingTensorCandidatePrimitive :
      FactorVecStressEnergyTensorCandidateMissingPrimitive

    firstMissingTensorCandidatePrimitiveIsComponentFamily :
      firstMissingTensorCandidatePrimitive
      ≡
      missingValuationStressEnergyTensorComponentFamily

    tensorCandidateBoundary :
      List String

record FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress : Setω where
  field
    tensorCandidateRequest :
      FactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest

    tensorComponentFamily :
      FactorVecStressEnergyTensorComponentFamily

    requestFirstMissingPrimitiveIsComponentFamily :
      FactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest.firstMissingTensorCandidatePrimitive
        tensorCandidateRequest
      ≡
      missingValuationStressEnergyTensorComponentFamily

    dischargedTensorCandidatePrimitive :
      FactorVecStressEnergyTensorCandidateMissingPrimitive

    dischargedTensorCandidatePrimitiveIsComponentFamily :
      dischargedTensorCandidatePrimitive
      ≡
      missingValuationStressEnergyTensorComponentFamily

    firstRemainingTensorCandidatePrimitive :
      FactorVecStressEnergyTensorCandidateMissingPrimitive

    firstRemainingTensorCandidatePrimitiveIsSymmetryLaw :
      firstRemainingTensorCandidatePrimitive
      ≡
      missingValuationStressEnergyTensorSymmetryLaw

    componentFamilyProgressBoundary :
      List String

record FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress : Setω where
  field
    componentFamilyProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress

    tensorSymmetryLaw :
      FactorVecStressEnergyTensorSymmetryLaw
        (FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress.tensorComponentFamily
          componentFamilyProgress)

    requestFirstRemainingPrimitiveIsSymmetryLaw :
      FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress.firstRemainingTensorCandidatePrimitive
        componentFamilyProgress
      ≡
      missingValuationStressEnergyTensorSymmetryLaw

    dischargedTensorCandidatePrimitive :
      FactorVecStressEnergyTensorCandidateMissingPrimitive

    dischargedTensorCandidatePrimitiveIsSymmetryLaw :
      dischargedTensorCandidatePrimitive
      ≡
      missingValuationStressEnergyTensorSymmetryLaw

    firstRemainingTensorCandidatePrimitive :
      FactorVecStressEnergyTensorCandidateMissingPrimitive

    firstRemainingTensorCandidatePrimitiveIsFiniteSupportLaw :
      firstRemainingTensorCandidatePrimitive
      ≡
      missingValuationStressEnergyTensorFiniteSupportLaw

    symmetryProgressBoundary :
      List String

record FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress : Setω where
  field
    symmetryProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress

    tensorFiniteSupportLaw :
      FactorVecStressEnergyTensorFiniteSupportLaw
        (FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress.tensorComponentFamily
          (FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress.componentFamilyProgress
            symmetryProgress))

    requestFirstRemainingPrimitiveIsFiniteSupportLaw :
      FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress.firstRemainingTensorCandidatePrimitive
        symmetryProgress
      ≡
      missingValuationStressEnergyTensorFiniteSupportLaw

    dischargedTensorCandidatePrimitive :
      FactorVecStressEnergyTensorCandidateMissingPrimitive

    dischargedTensorCandidatePrimitiveIsFiniteSupportLaw :
      dischargedTensorCandidatePrimitive
      ≡
      missingValuationStressEnergyTensorFiniteSupportLaw

    firstRemainingTensorCandidatePrimitive :
      FactorVecStressEnergyTensorCandidateMissingPrimitive

    firstRemainingTensorCandidatePrimitiveIsCarrierEmbedding :
      firstRemainingTensorCandidatePrimitive
      ≡
      missingValuationStressEnergyTensorCarrierEmbedding

    finiteSupportProgressBoundary :
      List String

record FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress : Setω where
  field
    finiteSupportProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress

    tensorCarrierEmbeddingLaw :
      FactorVecStressEnergyTensorCarrierEmbeddingLaw
        (FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress.tensorComponentFamily
          (FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress.componentFamilyProgress
            (FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress.symmetryProgress
              finiteSupportProgress)))

    requestFirstRemainingPrimitiveIsCarrierEmbedding :
      FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress.firstRemainingTensorCandidatePrimitive
        finiteSupportProgress
      ≡
      missingValuationStressEnergyTensorCarrierEmbedding

    dischargedTensorCandidatePrimitive :
      FactorVecStressEnergyTensorCandidateMissingPrimitive

    dischargedTensorCandidatePrimitiveIsCarrierEmbedding :
      dischargedTensorCandidatePrimitive
      ≡
      missingValuationStressEnergyTensorCarrierEmbedding

    firstRemainingStressEnergyCompatibilityPrimitive :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    firstRemainingStressEnergyCompatibilityPrimitiveIsEinsteinSourceCouplingLaw :
      firstRemainingStressEnergyCompatibilityPrimitive
      ≡
      missingValuationEinsteinSourceCouplingLaw

    carrierEmbeddingProgressBoundary :
      List String

record FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress : Setω where
  field
    carrierEmbeddingProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress

    einsteinSourceCouplingLaw :
      FactorVecEinsteinSourceCouplingLaw
        (FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress.tensorComponentFamily
          (FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress.componentFamilyProgress
            (FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress.symmetryProgress
              (FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress.finiteSupportProgress
                carrierEmbeddingProgress))))

    requestFirstRemainingPrimitiveIsEinsteinSourceCouplingLaw :
      FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress.firstRemainingStressEnergyCompatibilityPrimitive
        carrierEmbeddingProgress
      ≡
      missingValuationEinsteinSourceCouplingLaw

    dischargedStressEnergyCompatibilityPrimitive :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    dischargedStressEnergyCompatibilityPrimitiveIsEinsteinSourceCouplingLaw :
      dischargedStressEnergyCompatibilityPrimitive
      ≡
      missingValuationEinsteinSourceCouplingLaw

    firstRemainingStressEnergyCompatibilityPrimitive :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    firstRemainingStressEnergyCompatibilityPrimitiveIsCovariantDivergenceLaw :
      firstRemainingStressEnergyCompatibilityPrimitive
      ≡
      missingValuationStressEnergyCovariantDivergenceLaw

    exactMissingMatterInterfaceSymbol :
      String

    einsteinSourceCouplingProgressBoundary :
      List String

record FactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress : Setω where
  field
    einsteinSourceCouplingProgress :
      FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress

    stressEnergyCovariantDivergenceLaw :
      FactorVecStressEnergyCovariantDivergenceLaw
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    requestFirstRemainingPrimitiveIsCovariantDivergenceLaw :
      FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress.firstRemainingStressEnergyCompatibilityPrimitive
        einsteinSourceCouplingProgress
      ≡
      missingValuationStressEnergyCovariantDivergenceLaw

    dischargedStressEnergyCompatibilityPrimitive :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    dischargedStressEnergyCompatibilityPrimitiveIsCovariantDivergenceLaw :
      dischargedStressEnergyCompatibilityPrimitive
      ≡
      missingValuationStressEnergyCovariantDivergenceLaw

    firstRemainingStressEnergyCompatibilityPrimitive :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    firstRemainingStressEnergyCompatibilityPrimitiveIsMatterReceiptInterface :
      firstRemainingStressEnergyCompatibilityPrimitive
      ≡
      missingValuationMatterReceiptInterface

    matterStressEnergyInterfaceDiagnostic :
      EEC.W4MatterStressEnergyInterfaceDiagnostic

    matterStressEnergyInterfaceFirstMissing :
      EEC.W4MatterStressEnergyInterfaceMissingField

    matterStressEnergyInterfaceFirstMissingMatchesDiagnostic :
      matterStressEnergyInterfaceFirstMissing
      ≡
      EEC.W4MatterStressEnergyInterfaceDiagnostic.firstMissing
        matterStressEnergyInterfaceDiagnostic

    matterStressEnergyInterfaceFirstMissingIsW4AnchorArtifactReceipt :
      matterStressEnergyInterfaceFirstMissing
      ≡
      EEC.missingW4AnchorArtifactReceiptForMatterStress

    exactMissingMatterInterfaceSymbol :
      String

    covariantDivergenceProgressBoundary :
      List String

record FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest : Setω where
  field
    unitContractedBianchiWitness :
      FactorVecValuationP2LorentzUnitContractedBianchiWitness

    stressEnergyPrimitive :
      FactorVecMetricGRPrimitive

    stressEnergyPrimitiveIsValuationStressEnergyCompatibility :
      stressEnergyPrimitive
      ≡
      missingValuationStressEnergyCompatibilityComputation

    missingStressEnergyCompatibilityPrimitives :
      List FactorVecStressEnergyCompatibilityMissingPrimitive

    missingStressEnergyCompatibilityPrimitivesAreCanonical :
      missingStressEnergyCompatibilityPrimitives
      ≡
      canonicalFactorVecStressEnergyCompatibilityMissingPrimitives

    firstMissingStressEnergyCompatibilityPrimitive :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    firstMissingStressEnergyCompatibilityPrimitiveIsTensorCandidate :
      firstMissingStressEnergyCompatibilityPrimitive
      ≡
      missingValuationStressEnergyTensorCandidate

    tensorCandidateRequest :
      FactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest

    firstMissingTensorCandidatePrimitive :
      FactorVecStressEnergyTensorCandidateMissingPrimitive

    firstMissingTensorCandidatePrimitiveIsComponentFamily :
      firstMissingTensorCandidatePrimitive
      ≡
      missingValuationStressEnergyTensorComponentFamily

    stressEnergyBoundary :
      List String

record FactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt : Setω where
  field
    stressEnergyCompatibilityRequest :
      FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest

    stressEnergyCompatibilityRequestFirstMissing :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    stressEnergyCompatibilityRequestFirstMissingIsTensorCandidate :
      stressEnergyCompatibilityRequestFirstMissing
      ≡
      missingValuationStressEnergyTensorCandidate

    tensorComponentFamilyProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress

    tensorComponentFamily :
      FactorVecStressEnergyTensorComponentFamily

    tensorComponentFamilyIsSupportedZeroTable :
      tensorComponentFamily
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    ymStressEnergyTensorShape :
      String

    ymStressEnergyTensorShapeIsCanonical :
      ymStressEnergyTensorShape
      ≡
      factorVecFormalYMStressEnergyTensorShape

    einsteinSourceCouplingProgress :
      FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress

    contractedBianchiWitness :
      FactorVecValuationP2LorentzUnitContractedBianchiWitness

    contractedBianchiConservationTarget :
      FactorVecTangentDirection →
      ℚ

    contractedBianchiConservationTargetIsSupportedZeroTable :
      contractedBianchiConservationTarget
      ≡
      factorVecUnitP2LorentzContractedBianchiDivergence

    stressEnergyCovariantDivergenceProgress :
      FactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress

    stressEnergyCovariantDivergenceLaw :
      FactorVecStressEnergyCovariantDivergenceLaw
        tensorComponentFamily

    contractedBianchiConservationTargetShape :
      String

    contractedBianchiConservationTargetShapeIsCanonical :
      contractedBianchiConservationTargetShape
      ≡
      factorVecContractedBianchiStressEnergyConservationTargetShape

    firstRemainingStressEnergyCompatibilityPrimitive :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    firstRemainingStressEnergyCompatibilityPrimitiveIsMatterReceiptInterface :
      firstRemainingStressEnergyCompatibilityPrimitive
      ≡
      missingValuationMatterReceiptInterface

    exactMissingMatterInterfaceSymbol :
      String

    compatibilityBoundary :
      List String

record FactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt : Setω where
  field
    internalComponentFamilyProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress

    internalComponentFamily :
      FactorVecStressEnergyTensorComponentFamily

    internalComponentFamilyIsSupportedZeroTable :
      internalComponentFamily
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    originalCompatibilityRequestFirstMissing :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    originalCompatibilityRequestFirstMissingIsTensorCandidate :
      originalCompatibilityRequestFirstMissing
      ≡
      missingValuationStressEnergyTensorCandidate

    boundedLocalProgressFirstRemaining :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    boundedLocalProgressFirstRemainingIsMatterReceiptInterface :
      boundedLocalProgressFirstRemaining
      ≡
      missingValuationMatterReceiptInterface

    w4MatterStressEnergyInterfaceDiagnostic :
      EEC.W4MatterStressEnergyInterfaceDiagnostic

    w4MatterStressEnergyInterfaceFirstMissing :
      EEC.W4MatterStressEnergyInterfaceMissingField

    w4MatterStressEnergyInterfaceFirstMissingIsAnchorArtifactReceipt :
      w4MatterStressEnergyInterfaceFirstMissing
      ≡
      EEC.missingW4AnchorArtifactReceiptForMatterStress

    exactAuthorityBoundarySymbol :
      String

    authorityBoundary :
      List String

record FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt : Setω where
  field
    componentFamilyProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress

    fullTensorCandidate :
      FactorVecStressEnergyTensorComponentFamily

    fullTensorCandidateIsSupportedZeroTable :
      fullTensorCandidate
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    t00Candidate :
      ℚ

    t00CandidateIsSupportedZero :
      t00Candidate
      ≡
      zeroℚ

    symmetryProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress

    finiteSupportProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress

    carrierEmbeddingProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress

    originalCompatibilityFirstMissing :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    originalCompatibilityFirstMissingIsTensorCandidate :
      originalCompatibilityFirstMissing
      ≡
      missingValuationStressEnergyTensorCandidate

    localProgressRemainingBlocker :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    localProgressRemainingBlockerIsMatterReceiptInterface :
      localProgressRemainingBlocker
      ≡
      missingValuationMatterReceiptInterface

    exactMissingMatterInterfaceSymbol :
      String

    stagingBoundary :
      List String

data FactorVecValuationMatterInterfaceReceiptStatus : Set where
  valuationMatterInterfaceHaltedAtExternalW4Receipt :
    FactorVecValuationMatterInterfaceReceiptStatus

record FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt : Setω where
  field
    t00Staging :
      FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt

    fullTensorCandidate :
      FactorVecStressEnergyTensorComponentFamily

    fullTensorCandidateIsSupportedZeroTable :
      fullTensorCandidate
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    t00Candidate :
      ℚ

    t00CandidateIsSupportedZero :
      t00Candidate
      ≡
      zeroℚ

    t11Candidate :
      ℚ

    t11CandidateIsSupportedZero :
      t11Candidate
      ≡
      zeroℚ

    t22Candidate :
      ℚ

    t22CandidateIsSupportedZero :
      t22Candidate
      ≡
      zeroℚ

    t33Candidate :
      ℚ

    t33CandidateIsSupportedZero :
      t33Candidate
      ≡
      zeroℚ

    offDiagonalP2P3Candidate :
      ℚ

    offDiagonalP2P3CandidateIsSupportedZero :
      offDiagonalP2P3Candidate
      ≡
      zeroℚ

    symmetryProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress

    finiteSupportProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress

    carrierEmbeddingProgress :
      FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress

    einsteinSourceCouplingProgress :
      FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress

    covariantDivergenceProgress :
      FactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress

    contractedBianchiWitness :
      FactorVecValuationP2LorentzUnitContractedBianchiWitness

    contractedBianchiConservationTarget :
      FactorVecTangentDirection →
      ℚ

    contractedBianchiConservationTargetIsSupportedZeroTable :
      contractedBianchiConservationTarget
      ≡
      factorVecUnitP2LorentzContractedBianchiDivergence

    covariantDivergenceLaw :
      FactorVecStressEnergyCovariantDivergenceLaw
        fullTensorCandidate

    localProgressRemainingBlocker :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    localProgressRemainingBlockerIsMatterReceiptInterface :
      localProgressRemainingBlocker
      ≡
      missingValuationMatterReceiptInterface

    fullComponentFamilyBoundary :
      List String

record FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt : Setω where
  field
    status :
      FactorVecValuationMatterInterfaceReceiptStatus

    fullComponentFamilyReceipt :
      FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt

    stressEnergyCompatibilityRequest :
      FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest

    originalCompatibilityRequestFirstMissing :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    originalCompatibilityRequestFirstMissingIsTensorCandidate :
      originalCompatibilityRequestFirstMissing
      ≡
      missingValuationStressEnergyTensorCandidate

    localProgressRemainingBlocker :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    localProgressRemainingBlockerIsMatterReceiptInterface :
      localProgressRemainingBlocker
      ≡
      missingValuationMatterReceiptInterface

    w4MatterStressEnergyInterfaceExternalHalt :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt

    w4ExternalHaltFirstBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4ExternalHaltFirstBlockerIsCandidate256 :
      w4ExternalHaltFirstBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    w4ExternalHaltNoSourcedEinsteinPromotion :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt.promotesSourcedEinstein
        w4MatterStressEnergyInterfaceExternalHalt
      ≡
      false

    exactMissingMatterInterfaceSymbol :
      String

    noEinsteinInterfaceReceiptHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    valuationMatterInterfaceBoundary :
      List String

record FactorVecValuationDependentNonFlatSiteMetricSurface : Setω where
  field
    BasePoint :
      Set

    TangentDirection :
      Set

    valuationDepth :
      GL.FactorVec →
      FactorVecTangentDirection →
      GL.Exponent

    valuationDepthIsFactorVecCoordinate :
      valuationDepth
      ≡
      factorVecValuationDepth

    requiredSiteMetricType :
      Set

    requiredSiteMetricTypeIsFactorVecValuationMetric :
      requiredSiteMetricType
      ≡
      FactorVecValuationDependentSiteMetricType

    selectedTimePrime :
      FactorVecCommittedTimePrime

    selectedTimePrimeDirection :
      FactorVecTangentDirection

    selectedTimePrimeDirectionIsP2 :
      selectedTimePrimeDirection
      ≡
      p2

    valuationScale :
      GL.Exponent →
      ℚ

    valuationDiagonalWeight :
      GL.FactorVec →
      FactorVecTangentDirection →
      ℚ

    valuationDependentSiteMetric :
      FactorVecValuationDependentSiteMetricType

    valuationDependentSiteMetricIsP2LorentzCandidate :
      valuationDependentSiteMetric
      ≡
      factorVecValuationDependentP2LorentzMetric

    valuationDependentMetricSymmetric :
      (base : GL.FactorVec) →
      (mu nu : FactorVecTangentDirection) →
      valuationDependentSiteMetric base mu nu
      ≡
      valuationDependentSiteMetric base nu mu

    valuationTimePrimeMetricWitness :
      FactorVecValuationP2TimePrimeMetricWitness

    valuationDiagonalShapeWitness :
      FactorVecValuationP2LorentzDiagonalShapeWitness

    valuationNonzeroSupportWitness :
      FactorVecValuationAllLaneNonzeroSupportWitness

    valuationSignedWeightVectorWitness :
      FactorVecValuationP2LorentzSignedWeightVectorWitness

    valuationRationalNonzeroWeightWitness :
      FactorVecValuationP2LorentzRationalNonzeroWeightWitness

    valuationRankNondegenerateWitness :
      FactorVecValuationP2LorentzRankNondegenerateWitness

    valuationSylvesterInertiaWitness :
      FactorVecValuationP2LorentzSylvesterInertiaWitness

    valuationMetricNondegenerateSignature :
      MetricNondegenerateSignature

    valuationUnitInverseMetricWitness :
      FactorVecValuationP2LorentzUnitInverseMetricWitness

    valuationUnitChristoffelWitness :
      FactorVecValuationP2LorentzUnitChristoffelWitness

    valuationUnitRiemannWitness :
      FactorVecValuationP2LorentzUnitRiemannWitness

    valuationUnitRicciWitness :
      FactorVecValuationP2LorentzUnitRicciWitness

    valuationUnitScalarCurvatureWitness :
      FactorVecValuationP2LorentzUnitScalarCurvatureWitness

    valuationUnitEinsteinTensorWitness :
      FactorVecValuationP2LorentzUnitEinsteinTensorWitness

    valuationUnitContractedBianchiWitness :
      FactorVecValuationP2LorentzUnitContractedBianchiWitness

    valuationUnitStressEnergyCompatibilityRequest :
      FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest

    firstNondegeneratePrimitiveAfterSupport :
      FactorVecMetricGRPrimitive

    firstNondegeneratePrimitiveAfterSupportIsValuationNondegenerate :
      firstNondegeneratePrimitiveAfterSupport
      ≡
      missingValuationMetricNondegenerateProof

    firstMetricPrimitiveAfterInertia :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterInertiaIsInverseMetric :
      firstMetricPrimitiveAfterInertia
      ≡
      missingValuationInverseMetricComputation

    firstMetricPrimitiveAfterUnitInverse :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterUnitInverseIsChristoffel :
      firstMetricPrimitiveAfterUnitInverse
      ≡
      missingValuationLeviCivitaChristoffelComputation

    firstMetricPrimitiveAfterUnitChristoffel :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterUnitChristoffelIsRiemann :
      firstMetricPrimitiveAfterUnitChristoffel
      ≡
      missingValuationRiemannCurvatureComputation

    firstMetricPrimitiveAfterUnitRiemann :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterUnitRiemannIsRicci :
      firstMetricPrimitiveAfterUnitRiemann
      ≡
      missingValuationRicciContractionComputation

    firstMetricPrimitiveAfterUnitRicci :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterUnitRicciIsContractedBianchi :
      firstMetricPrimitiveAfterUnitRicci
      ≡
      missingValuationContractedBianchiComputation

    firstMetricPrimitiveAfterUnitContractedBianchi :
      FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterUnitContractedBianchiIsStressEnergy :
      firstMetricPrimitiveAfterUnitContractedBianchi
      ≡
      missingValuationStressEnergyCompatibilityComputation

    requiredSignatureTarget :
      FactorVecMetricSignatureTarget

    missingPrimitives :
      List FactorVecMetricGRPrimitive

    missingPrimitivesAreCanonical :
      missingPrimitives
      ≡
      canonicalFactorVecMetricGRPrimitives

    nonFlatBoundary :
      List String

record FactorVecRicciBianchiPrimitiveRequest : Setω where
  field
    valuationDependentMetricType :
      Set

    valuationDependentMetricTypeIsCanonical :
      valuationDependentMetricType
      ≡
      FactorVecValuationDependentSiteMetricType

    inverseMetricPrimitive :
      FactorVecMetricGRPrimitive

    christoffelPrimitive :
      FactorVecMetricGRPrimitive

    riemannPrimitive :
      FactorVecMetricGRPrimitive

    ricciPrimitive :
      FactorVecMetricGRPrimitive

    contractedBianchiPrimitive :
      FactorVecMetricGRPrimitive

    stressEnergyPrimitive :
      FactorVecMetricGRPrimitive

    supportedUnitStressEnergyCompatibilityRequest :
      FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest

    primitiveBoundary :
      List String

data FactorVecContractedBianchiRouteMissingGate : Set where
  missingNonDegenerateFactorVecMetricSignature :
    FactorVecContractedBianchiRouteMissingGate
  missingNonFlatFactorVecChristoffelCoefficients :
    FactorVecContractedBianchiRouteMissingGate
  missingFactorVecRiemannAntisymmetry :
    FactorVecContractedBianchiRouteMissingGate
  missingFactorVecRicciContraction :
    FactorVecContractedBianchiRouteMissingGate
  missingFactorVecCovariantDivergence :
    FactorVecContractedBianchiRouteMissingGate
  missingFactorVecBianchiContractionLaw :
    FactorVecContractedBianchiRouteMissingGate
  missingFactorVecStressEnergyCompatibility :
    FactorVecContractedBianchiRouteMissingGate

canonicalFactorVecContractedBianchiRouteMissingGates :
  List FactorVecContractedBianchiRouteMissingGate
canonicalFactorVecContractedBianchiRouteMissingGates =
  missingNonDegenerateFactorVecMetricSignature
  ∷ missingNonFlatFactorVecChristoffelCoefficients
  ∷ missingFactorVecRiemannAntisymmetry
  ∷ missingFactorVecRicciContraction
  ∷ missingFactorVecCovariantDivergence
  ∷ missingFactorVecBianchiContractionLaw
  ∷ missingFactorVecStressEnergyCompatibility
  ∷ []

record FactorVecContractedBianchiRoute : Setω where
  field
    metric :
      FactorVecSymmetricRationalBilinearMetric

    koszulChristoffelWitness :
      FactorVecFiniteKoszulChristoffelWitness

    firstRemainingGate :
      FactorVecContractedBianchiRouteMissingGate

    firstRemainingGateIsNonDegenerateSignature :
      firstRemainingGate
      ≡
      missingNonDegenerateFactorVecMetricSignature

    remainingGates :
      List FactorVecContractedBianchiRouteMissingGate

    remainingGatesAreCanonical :
      remainingGates
      ≡
      canonicalFactorVecContractedBianchiRouteMissingGates

    routeBoundary :
      List String

record FactorVecDiscreteMetricTensorSurface : Setω where
  field
    metric :
      FactorVecSymmetricRationalBilinearMetric

    constantDiagonalReciprocalPrimeFlatnessCandidate :
      FactorVecConstantDiagonalReciprocalPrimeMetricSurface

    valuationDependentNonFlatSiteMetricRequired :
      FactorVecValuationDependentNonFlatSiteMetricSurface

    koszulChristoffelWitness :
      FactorVecFiniteKoszulChristoffelWitness

    ricciBianchiPrimitiveRequest :
      FactorVecRicciBianchiPrimitiveRequest

    contractedBianchiRoute :
      FactorVecContractedBianchiRoute

    surfaceBoundary :
      List String

canonicalFactorVecSymmetricRationalBilinearMetric :
  FactorVecSymmetricRationalBilinearMetric
canonicalFactorVecSymmetricRationalBilinearMetric =
  record
    { BasePoint =
        GL.FactorVec
    ; TangentDirection =
        FactorVecTangentDirection
    ; basePointIsFactorVec =
        refl
    ; tangentDirectionIsSSP =
        refl
    ; rationalScalar =
        ℚ
    ; rationalScalarIsProjectQ =
        refl
    ; zeroScalar =
        zeroℚ
    ; oneScalar =
        oneℚ
    ; twoScalar =
        twoℚ
    ; tangentBasis =
        factorVecTangentBasis
    ; primeTransport =
        factorVecPrimeTransport
    ; g =
        factorVecZeroMetric
    ; gSymmetric =
        factorVecMetricSymmetric
    ; bilinearSurfaceBoundary =
        "BasePoint is Ontology.GodelLattice.FactorVec"
        ∷ "TangentDirection is MonsterOntos.SSP, the finite prime-lane basis"
        ∷ "The scalar field is DASHI.Core.Q.ℚ"
        ∷ "g is the flat zero rational bilinear seed on the finite FactorVec tangent basis"
        ∷ "Symmetry is definitional; non-degeneracy and Lorentz signature are not claimed here"
        ∷ []
    }

canonicalFactorVecConstantDiagonalReciprocalPrimeMetric :
  FactorVecSymmetricRationalBilinearMetric
canonicalFactorVecConstantDiagonalReciprocalPrimeMetric =
  record
    { BasePoint =
        GL.FactorVec
    ; TangentDirection =
        FactorVecTangentDirection
    ; basePointIsFactorVec =
        refl
    ; tangentDirectionIsSSP =
        refl
    ; rationalScalar =
        ℚ
    ; rationalScalarIsProjectQ =
        refl
    ; zeroScalar =
        zeroℚ
    ; oneScalar =
        oneℚ
    ; twoScalar =
        twoℚ
    ; tangentBasis =
        factorVecTangentBasis
    ; primeTransport =
        factorVecPrimeTransport
    ; g =
        factorVecConstantDiagonalReciprocalPrimeMetric
    ; gSymmetric =
        factorVecConstantDiagonalReciprocalPrimeMetricSymmetric
    ; bilinearSurfaceBoundary =
        "BasePoint is Ontology.GodelLattice.FactorVec"
        ∷ "TangentDirection is MonsterOntos.SSP, the finite prime-lane basis"
        ∷ "g is diagonal on equal SSP lanes and zero off diagonal"
        ∷ "The diagonal coefficient on lane p is the rational reciprocal 1/p"
        ∷ "Symmetry is proved by SSP decidable equality; non-degeneracy and signature remain recorded primitives"
        ∷ []
    }

canonicalFactorVecConstantDiagonalBasisShapeWitness :
  FactorVecConstantDiagonalBasisShapeWitness
canonicalFactorVecConstantDiagonalBasisShapeWitness =
  record
    { metric =
        canonicalFactorVecConstantDiagonalReciprocalPrimeMetric
    ; diagonalWeight =
        factorVecReciprocalPrimeWeight
    ; metricComponent =
        factorVecConstantDiagonalReciprocalPrimeMetric
    ; selfComponentLaw =
        factorVecConstantDiagonalSelfComponent
    ; offDiagonalZeroLaw =
        factorVecConstantDiagonalOffDiagonalZero
    ; basisShapeBoundary =
        "The constant candidate is diagonal on the SSP basis"
        ∷ "The self component on lane p is exactly the rational reciprocal 1/p"
        ∷ "Off-diagonal components are zero whenever the two SSP lanes are distinct"
        ∷ "This is only basis-shape data; it is not yet a vector-space non-degeneracy or signature theorem"
        ∷ []
    }

canonicalFactorVecFiniteFreeTangentModuleMatrixWitness :
  FactorVecFiniteFreeTangentModuleMatrixWitness
canonicalFactorVecFiniteFreeTangentModuleMatrixWitness =
  record
    { coefficientVector =
        FactorVecQCoefficientVector
    ; coefficientVectorIsQ15 =
        refl
    ; scalar =
        ℚ
    ; scalarIsQ =
        refl
    ; zeroVector =
        factorVecQZeroVector
    ; addVector =
        factorVecQAdd
    ; scaleVector =
        factorVecQScale
    ; basisVector =
        factorVecQBasisVector
    ; coordinate =
        factorVecQCoordinate
    ; diagonalMatrix =
        factorVecConstantDiagonalReciprocalPrimeMatrix
    ; diagonalMatrixComponentLaw =
        factorVecConstantDiagonalReciprocalPrimeMatrixComponentLaw
    ; matrixBoundary =
        "The tangent carrier is now a concrete fifteen-coordinate vector over DASHI.Core.Q.ℚ"
        ∷ "The finite basis is indexed by the fifteen SSP prime lanes"
        ∷ "The reciprocal-prime metric has an explicit diagonal matrix over that coefficient carrier"
        ∷ "This discharges only the carrier/matrix socket; module laws, determinant nonzero, rank, and inertia are separate proof obligations"
        ∷ []
    }

canonicalFactorVecDiagonalDeterminantProductTarget :
  FactorVecDiagonalDeterminantProductTarget
canonicalFactorVecDiagonalDeterminantProductTarget =
  record
    { matrixWitness =
        canonicalFactorVecFiniteFreeTangentModuleMatrixWitness
    ; determinantProductExpression =
        determinantProductOfFifteenReciprocalPrimes
    ; determinantProductExpressionIsCanonical =
        refl
    ; determinantNonzeroProofPromoted =
        ⊥
    ; determinantNonzeroProofStillMissing =
        refl
    ; determinantBoundary =
        "For the diagonal matrix, the determinant candidate is the product of the fifteen reciprocal-prime diagonal entries"
        ∷ "This target does not prove the product is nonzero in ℚ"
        ∷ "Rank, Sylvester inertia, and Lorentz/Wick projection remain blocked"
        ∷ []
    }

canonicalFactorVecConstantDiagonalNondegenerateSignaturePrimitiveRequest :
  FactorVecConstantDiagonalNondegenerateSignaturePrimitiveRequest
canonicalFactorVecConstantDiagonalNondegenerateSignaturePrimitiveRequest =
  record
    { candidateMetric =
        canonicalFactorVecConstantDiagonalReciprocalPrimeMetric
    ; basisShapeWitness =
        canonicalFactorVecConstantDiagonalBasisShapeWitness
    ; finiteFreeMatrixWitness =
        canonicalFactorVecFiniteFreeTangentModuleMatrixWitness
    ; determinantProductTarget =
        canonicalFactorVecDiagonalDeterminantProductTarget
    ; finiteSignatureTarget =
        positiveFifteenPrimeLaneSignature
    ; targetIsPositiveFifteenPrimeLaneSignature =
        refl
    ; blockers =
        canonicalFactorVecConstantDiagonalNondegenerateSignatureBlockers
    ; blockersAreCanonical =
        refl
    ; firstMetricPrimitive =
        missingConstantDiagonalNondegenerateProof
    ; firstMetricPrimitiveIsNondegenerateProof =
        refl
    ; secondMetricPrimitive =
        missingConstantDiagonalSignatureProof
    ; secondMetricPrimitiveIsSignatureProof =
        refl
    ; requestBoundary =
        "The diagonal SSP basis-shape witness is inhabited"
        ∷ "The finite free fifteen-lane coefficient carrier over DASHI.Core.Q.ℚ is now explicit"
        ∷ "The reciprocal-prime bilinear form is now represented as a diagonal matrix over that carrier"
        ∷ "A determinant product candidate is named, but its nonzero proof and rank theorem are not inhabited"
        ∷ "The rational reciprocal entries 1/p still need positive/nonzero proofs in the selected rational order API"
        ∷ "The positive fifteen-lane inertia classifier is missing and would not by itself imply Lorentz 3+1 signature"
        ∷ "A Lorentz/Wick/projection boundary is required before this candidate can feed a GR promotion route"
        ∷ []
    }

canonicalFactorVecConstantDiagonalReciprocalPrimeMetricSurface :
  FactorVecConstantDiagonalReciprocalPrimeMetricSurface
canonicalFactorVecConstantDiagonalReciprocalPrimeMetricSurface =
  record
    { metric =
        canonicalFactorVecConstantDiagonalReciprocalPrimeMetric
    ; basisShapeWitness =
        canonicalFactorVecConstantDiagonalBasisShapeWitness
    ; diagonalWeight =
        factorVecReciprocalPrimeWeight
    ; metricComponent =
        factorVecConstantDiagonalReciprocalPrimeMetric
    ; metricComponentIsCanonical =
        refl
    ; constantInBaseBoundary =
        "The metric component ignores the FactorVec base point"
        ∷ "Finite differences of this candidate are expected to be flat only after a separate nonzero diagonal/inverse proof"
        ∷ []
    ; finiteSignatureTarget =
        positiveFifteenPrimeLaneSignature
    ; missingNondegeneratePrimitive =
        missingConstantDiagonalNondegenerateProof
    ; missingNondegeneratePrimitiveIsRecorded =
        refl
    ; missingSignaturePrimitive =
        missingConstantDiagonalSignatureProof
    ; missingSignaturePrimitiveIsRecorded =
        refl
    ; nondegenerateSignaturePrimitiveRequest =
        canonicalFactorVecConstantDiagonalNondegenerateSignaturePrimitiveRequest
    ; flatnessCandidateBoundary =
        "This is the constant diagonal reciprocal-prime flatness candidate, not the valuation-dependent non-flat GR metric"
        ∷ "Its finite signature target is the positive fifteen-prime-lane diagonal form, not a continuum Lorentz 3+1 promotion"
        ∷ "The diagonal basis-shape and finite matrix carrier are inhabited, but determinant/rank and finite signature proofs remain named primitives"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzDiagonalShapeWitness :
  FactorVecValuationP2LorentzDiagonalShapeWitness
canonicalFactorVecValuationP2LorentzDiagonalShapeWitness =
  record
    { metricComponent =
        factorVecValuationDependentP2LorentzMetric
    ; metricComponentIsP2LorentzCandidate =
        refl
    ; selectedTimePrime =
        timePrimeP2
    ; selectedTimePrimeDirection =
        factorVecCommittedTimeDirection
    ; selectedTimePrimeDirectionIsP2 =
        refl
    ; selfComponentLaw =
        factorVecValuationP2LorentzSelfComponent
    ; timeComponentLaw =
        factorVecValuationP2LorentzTimeComponent
    ; spatialSelfComponentLaw =
        factorVecValuationP2LorentzSpatialSelfComponent
    ; offDiagonalZeroLaw =
        factorVecValuationP2LorentzOffDiagonalZero
    ; diagonalShapeBoundary =
        "The valuation-dependent candidate is explicitly diagonal on the SSP basis"
        ∷ "The committed p2 time lane has the sign-flipped valuation-weight diagonal component"
        ∷ "Every non-p2 self component keeps the positive valuation-weight orientation at the shape level"
        ∷ "Distinct SSP lanes have zero off-diagonal component"
        ∷ "This is diagonal p2-time shape data only; nonzero valuation depth, nondegeneracy, inertia, inverse metric, and curvature are still separate primitives"
        ∷ []
    }

canonicalFactorVecValuationAllLaneNonzeroSupportWitness :
  FactorVecValuationAllLaneNonzeroSupportWitness
canonicalFactorVecValuationAllLaneNonzeroSupportWitness =
  record
    { supportBase =
        factorVecUnitValuationSupportBase
    ; supportBaseIsUnitValuation =
        refl
    ; allLaneDepthNonzero =
        factorVecUnitValuationDepthNonzero
    ; supportBoundary =
        "A concrete FactorVec base with exponent 1 in every tracked SSP lane is inhabited"
        ∷ "Each valuationDepth(base,p) is therefore a successor exponent, including the committed p2 time lane"
        ∷ "This closes only the local nonzero valuation-support socket for the candidate metric"
        ∷ "It does not prove rational valuation weights nonzero, determinant/rank nondegeneracy, or Lorentzian inertia"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzSignedWeightVectorWitness :
  FactorVecValuationP2LorentzSignedWeightVectorWitness
canonicalFactorVecValuationP2LorentzSignedWeightVectorWitness =
  record
    { supportWitness =
        canonicalFactorVecValuationAllLaneNonzeroSupportWitness
    ; supportBase =
        factorVecUnitValuationSupportBase
    ; supportBaseIsUnitValuation =
        refl
    ; signedWeightVector =
        factorVecP2LorentzSignedValuationWeightVector
          factorVecUnitValuationSupportBase
    ; signedWeightVectorIsCanonical =
        refl
    ; coordinateLaw =
        factorVecP2LorentzSignedValuationWeightVectorCoordinate
          factorVecUnitValuationSupportBase
    ; timeCoordinateLaw =
        factorVecP2LorentzSignedValuationWeightVectorTimeCoordinate
          factorVecUnitValuationSupportBase
    ; spatialCoordinateLaw =
        factorVecP2LorentzSignedValuationWeightVectorSpatialCoordinate
          factorVecUnitValuationSupportBase
    ; firstRemainingMetricPrimitive =
        missingValuationMetricNondegenerateProof
    ; firstRemainingMetricPrimitiveIsNondegenerate =
        refl
    ; signedWeightBoundary =
        "The unit-support p2-time valuation metric now has an explicit fifteen-coordinate signed diagonal weight vector"
        ∷ "The p2 coordinate is definitionally the sign-flipped valuation weight"
        ∷ "Every non-p2 coordinate is definitionally the positive-orientation valuation weight"
        ∷ "This advances the rational-weight packaging socket only; nonzero rational weight proofs, determinant/rank, and Lorentzian inertia remain unpromoted"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzRationalNonzeroWeightWitness :
  FactorVecValuationP2LorentzRationalNonzeroWeightWitness
canonicalFactorVecValuationP2LorentzRationalNonzeroWeightWitness =
  record
    { signedWeightVectorWitness =
        canonicalFactorVecValuationP2LorentzSignedWeightVectorWitness
    ; diagonalPositive =
        factorVecUnitValuationDiagonalWeightPositive
    ; diagonalNonzero =
        factorVecUnitValuationDiagonalWeightNonzero
    ; timeSignedNegative =
        factorVecUnitP2LorentzSignedWeightTimeNegative
    ; timeSignedNonzero =
        factorVecUnitP2LorentzSignedWeightTimeNonzero
    ; spatialSignedPositive =
        factorVecUnitP2LorentzSignedWeightSpatialPositive
    ; spatialSignedNonzero =
        factorVecUnitP2LorentzSignedWeightSpatialNonzero
    ; inertiaLaneClassifier =
        factorVecUnitP2LorentzInertiaLane
    ; firstRemainingMetricPrimitive =
        missingValuationMetricNondegenerateProof
    ; firstRemainingMetricPrimitiveIsNondegenerate =
        refl
    ; nonzeroWeightBoundary =
        "At the unit-support FactorVec base, every unsigned valuation diagonal weight is proved positive and nonzero in Data.Rational"
        ∷ "The p2 signed diagonal weight is proved negative and nonzero"
        ∷ "Every non-p2 signed diagonal weight is proved positive and nonzero"
        ∷ "The finite inertia-lane classifier separates one p2 timelike lane from the remaining fourteen spatiallike lanes"
        ∷ "This does not yet prove determinant/rank nondegeneracy, a Sylvester inertia theorem, inverse metric data, or GR promotion"
        ∷ []
    }

canonicalFactorVecValuationP2TimePrimeMetricWitness :
  FactorVecValuationP2TimePrimeMetricWitness
canonicalFactorVecValuationP2TimePrimeMetricWitness =
  record
    { metricComponent =
        factorVecValuationDependentP2LorentzMetric
    ; metricComponentIsP2LorentzCandidate =
        refl
    ; selectedTimePrime =
        timePrimeP2
    ; selectedTimePrimeDirection =
        factorVecCommittedTimeDirection
    ; selectedTimePrimeDirectionIsP2 =
        refl
    ; metricSymmetric =
        factorVecValuationDependentP2LorentzMetricSymmetric
    ; diagonalShapeWitness =
        canonicalFactorVecValuationP2LorentzDiagonalShapeWitness
    ; signedWeightVectorWitness =
        canonicalFactorVecValuationP2LorentzSignedWeightVectorWitness
    ; rationalNonzeroWeightWitness =
        canonicalFactorVecValuationP2LorentzRationalNonzeroWeightWitness
    ; firstRemainingMetricPrimitive =
        missingValuationMetricNondegenerateProof
    ; firstRemainingMetricPrimitiveIsNondegenerate =
        refl
    ; timePrimeMetricBoundary =
        "The valuation-dependent non-flat site metric is committed to p2 as the time-prime lane"
        ∷ "Symmetry is inhabited for the p2-time valuation metric candidate"
        ∷ "The supported unit valuation base carries canonical signed-weight and rational nonzero-weight witnesses"
        ∷ "This package closes only the TimePrimeMetric lane; rank/nondegeneracy and downstream curvature/stress-energy receipts remain separate"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzRankNondegenerateWitness :
  FactorVecValuationP2LorentzRankNondegenerateWitness
canonicalFactorVecValuationP2LorentzRankNondegenerateWitness =
  record
    { rationalNonzeroWeightWitness =
        canonicalFactorVecValuationP2LorentzRationalNonzeroWeightWitness
    ; supportBase =
        factorVecUnitValuationSupportBase
    ; supportBaseIsUnitValuation =
        refl
    ; metricComponent =
        factorVecValuationDependentP2LorentzMetric
    ; metricComponentIsP2LorentzCandidate =
        refl
    ; selfComponentNonzero =
        factorVecUnitP2LorentzMetricSelfNonzero
    ; offDiagonalZeroLaw =
        factorVecValuationP2LorentzOffDiagonalZero
          factorVecUnitValuationSupportBase
    ; finiteRankCarrier =
        FactorVecQCoefficientVector
    ; finiteRankCarrierIsQ15 =
        refl
    ; nondegenerateMetricPrimitiveDischarged =
        missingValuationMetricNondegenerateProof
    ; nondegenerateMetricPrimitiveDischargedIsValuationNondegenerate =
        refl
    ; firstRemainingMetricPrimitive =
        missingValuationMetricSignatureProof
    ; firstRemainingMetricPrimitiveIsSignature =
        refl
    ; rankBoundary =
        "At the unit-support p2-time base, every diagonal self component of the valuation metric is rationally nonzero"
        ∷ "The metric is diagonal on the fifteen-lane SSP basis, so the finite rank/nondegeneracy socket is now witnessed at this supported base"
        ∷ "This consumes the checked rational nonzero time and spatial weight witnesses rather than adding a new assumption"
        ∷ "The next metric blocker is the full Sylvester/Lorentzian inertia classifier; inverse metric, curvature, Ricci, contracted Bianchi, stress-energy compatibility, and GR promotion remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzSylvesterInertiaWitness :
  FactorVecValuationP2LorentzSylvesterInertiaWitness
canonicalFactorVecValuationP2LorentzSylvesterInertiaWitness =
  record
    { rankNondegenerateWitness =
        canonicalFactorVecValuationP2LorentzRankNondegenerateWitness
    ; inertiaLaneClassifier =
        factorVecUnitP2LorentzInertiaLane
    ; inertiaLaneClassifierIsCanonical =
        refl
    ; timeLaneIsTimelikeP2 =
        refl
    ; spatialLanesAreNonP2Spatial =
        λ
          { p2 notTime →
              ⊥-elim (notTime refl)
          ; p3 _ →
              refl
          ; p5 _ →
              refl
          ; p7 _ →
              refl
          ; p11 _ →
              refl
          ; p13 _ →
              refl
          ; p17 _ →
              refl
          ; p19 _ →
              refl
          ; p23 _ →
              refl
          ; p29 _ →
              refl
          ; p31 _ →
              refl
          ; p41 _ →
              refl
          ; p47 _ →
              refl
          ; p59 _ →
              refl
          ; p71 _ →
              refl
          }
    ; timeSignedWeightNegative =
        factorVecUnitP2LorentzSignedWeightTimeNegative
    ; spatialSignedWeightPositive =
        factorVecUnitP2LorentzSignedWeightSpatialPositive
    ; signatureMetricPrimitiveDischarged =
        missingValuationMetricSignatureProof
    ; signatureMetricPrimitiveDischargedIsValuationSignature =
        refl
    ; firstRemainingMetricPrimitive =
        missingValuationInverseMetricComputation
    ; firstRemainingMetricPrimitiveIsInverseMetric =
        refl
    ; inertiaBoundary =
        "At the unit-support p2-time base, the diagonal sign pattern now carries an explicit finite Sylvester-style inertia witness"
        ∷ "The inertia classifier is canonical: p2 is the unique timelike lane and every non-p2 lane is spatiallike"
        ∷ "This discharges the local valuation-signature primitive socket and advances the next metric blocker to inverse-metric computation"
        ∷ "Christoffel, Riemann, Ricci, contracted Bianchi, stress-energy compatibility, and GR promotion remain open"
        ∷ []
    }

canonicalMetricNondegenerateSignature :
  MetricNondegenerateSignature
canonicalMetricNondegenerateSignature =
  record
    { constantDiagonalDeterminantTarget =
        canonicalFactorVecDiagonalDeterminantProductTarget
    ; constantDiagonalNondegenerateSignatureRequest =
        canonicalFactorVecConstantDiagonalNondegenerateSignaturePrimitiveRequest
    ; valuationRankNondegenerateWitness =
        canonicalFactorVecValuationP2LorentzRankNondegenerateWitness
    ; valuationSylvesterInertiaWitness =
        canonicalFactorVecValuationP2LorentzSylvesterInertiaWitness
    ; valuationNondegeneratePrimitiveDischarged =
        FactorVecValuationP2LorentzRankNondegenerateWitness.nondegenerateMetricPrimitiveDischarged
          canonicalFactorVecValuationP2LorentzRankNondegenerateWitness
    ; valuationNondegeneratePrimitiveDischargedIsExpected =
        refl
    ; valuationSignaturePrimitiveDischarged =
        FactorVecValuationP2LorentzSylvesterInertiaWitness.signatureMetricPrimitiveDischarged
          canonicalFactorVecValuationP2LorentzSylvesterInertiaWitness
    ; valuationSignaturePrimitiveDischargedIsExpected =
        refl
    ; firstRemainingMetricPrimitive =
        FactorVecValuationP2LorentzSylvesterInertiaWitness.firstRemainingMetricPrimitive
          canonicalFactorVecValuationP2LorentzSylvesterInertiaWitness
    ; firstRemainingMetricPrimitiveIsInverseMetric =
        refl
    ; witnessBoundary =
        "MetricNondegenerateSignature bundles determinant target plus valuation rank/nondegeneracy and Lorentzian inertia witnesses"
        ∷ "The valuation nondegenerate primitive is discharged at the unit-support p2-time metric carrier"
        ∷ "The valuation signature primitive is discharged with the canonical one-time/fourteen-spatial inertia split"
        ∷ "The next exact metric primitive after this witness is inverse-metric computation"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitInverseMetricWitness :
  FactorVecValuationP2LorentzUnitInverseMetricWitness
canonicalFactorVecValuationP2LorentzUnitInverseMetricWitness =
  record
    { sylvesterInertiaWitness =
        canonicalFactorVecValuationP2LorentzSylvesterInertiaWitness
    ; unitInverseMetric =
        factorVecUnitP2LorentzInverseMetric
    ; unitInverseMetricIsP2LorentzDiagonal =
        refl
    ; inverseMetricPrimitiveDischarged =
        missingValuationInverseMetricComputation
    ; inverseMetricPrimitiveDischargedIsValuationInverse =
        refl
    ; firstRemainingMetricPrimitive =
        missingValuationLeviCivitaChristoffelComputation
    ; firstRemainingMetricPrimitiveIsChristoffel =
        refl
    ; inverseMetricBoundary =
        "At the unit-support p2-time base, the inverse metric is the diagonal form with -1/2 on p2 and +1/2 on every non-p2 lane"
        ∷ "This consumes the previously witnessed nonzero signed weights and Sylvester lane classifier at that supported base"
        ∷ "This discharges only the local inverse-metric socket; non-flat Christoffel, curvature, Ricci, contracted Bianchi, stress-energy compatibility, and GR promotion remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitChristoffelWitness :
  FactorVecValuationP2LorentzUnitChristoffelWitness
canonicalFactorVecValuationP2LorentzUnitChristoffelWitness =
  record
    { unitInverseMetricWitness =
        canonicalFactorVecValuationP2LorentzUnitInverseMetricWitness
    ; unitChristoffelSymbol =
        factorVecUnitP2LorentzChristoffelSymbol
    ; unitChristoffelSymbolIsZeroTable =
        refl
    ; christoffelPrimitiveDischarged =
        missingValuationLeviCivitaChristoffelComputation
    ; christoffelPrimitiveDischargedIsValuationChristoffel =
        refl
    ; firstRemainingMetricPrimitive =
        missingValuationRiemannCurvatureComputation
    ; firstRemainingMetricPrimitiveIsRiemann =
        refl
    ; unitChristoffelBoundary =
        "At the supported unit p2-time valuation chart, the diagonal inverse metric is constant and the local Christoffel table is the zero rational table"
        ∷ "This discharges only the supported local Christoffel socket; it is not a global non-flat Levi-Civita theorem"
        ∷ "Riemann, Ricci, contracted Bianchi, stress-energy compatibility, and GR promotion remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress :
  FactorVecValuationP2LorentzUnitInverseChristoffelProgress
canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress =
  record
    { unitInverseMetricWitness =
        canonicalFactorVecValuationP2LorentzUnitInverseMetricWitness
    ; unitChristoffelWitness =
        canonicalFactorVecValuationP2LorentzUnitChristoffelWitness
    ; firstMetricPrimitiveAfterUnitInverse =
        FactorVecValuationP2LorentzUnitInverseMetricWitness.firstRemainingMetricPrimitive
          canonicalFactorVecValuationP2LorentzUnitInverseMetricWitness
    ; firstMetricPrimitiveAfterUnitInverseIsChristoffel =
        refl
    ; firstMetricPrimitiveAfterUnitChristoffel =
        FactorVecValuationP2LorentzUnitChristoffelWitness.firstRemainingMetricPrimitive
          canonicalFactorVecValuationP2LorentzUnitChristoffelWitness
    ; firstMetricPrimitiveAfterUnitChristoffelIsRiemann =
        refl
    ; inverseChristoffelProgressBoundary =
        "The supported unit p2-time inverse metric witness is now explicitly paired with the supported unit Christoffel witness"
        ∷ "This progress package threads the exact primitive queue from inverse-metric computation to Christoffel computation, then to Riemann curvature"
        ∷ "No non-flat Levi-Civita promotion is claimed by this bounded progress surface"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzSignatureInverseHandoffProgress :
  FactorVecValuationP2LorentzSignatureInverseHandoffProgress
canonicalFactorVecValuationP2LorentzSignatureInverseHandoffProgress =
  record
    { metricNondegenerateSignatureWitness =
        canonicalMetricNondegenerateSignature
    ; unitInverseChristoffelProgress =
        canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress
    ; firstMetricPrimitiveAfterInertia =
        MetricNondegenerateSignature.firstRemainingMetricPrimitive
          canonicalMetricNondegenerateSignature
    ; firstMetricPrimitiveAfterInertiaIsInverseMetric =
        refl
    ; firstMetricPrimitiveAfterUnitInverse =
        FactorVecValuationP2LorentzUnitInverseChristoffelProgress.firstMetricPrimitiveAfterUnitInverse
          canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress
    ; firstMetricPrimitiveAfterUnitInverseIsChristoffel =
        refl
    ; signatureInverseHandoffBoundary =
        "This handoff pairs the local MetricNondegenerateSignature witness with the supported unit inverse→Christoffel progress package"
        ∷ "It records the exact queue transition expected by downstream GR consumers: inverse-metric first, then Christoffel"
        ∷ "No global non-flat Levi-Civita or curvature promotion is claimed by this local handoff witness"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitRiemannWitness :
  FactorVecValuationP2LorentzUnitRiemannWitness
canonicalFactorVecValuationP2LorentzUnitRiemannWitness =
  record
    { unitChristoffelWitness =
        canonicalFactorVecValuationP2LorentzUnitChristoffelWitness
    ; unitRiemannTensor =
        factorVecUnitP2LorentzRiemannTensor
    ; unitRiemannTensorIsZeroTable =
        refl
    ; riemannPrimitiveDischarged =
        missingValuationRiemannCurvatureComputation
    ; riemannPrimitiveDischargedIsValuationRiemann =
        refl
    ; firstRemainingMetricPrimitive =
        missingValuationRicciContractionComputation
    ; firstRemainingMetricPrimitiveIsRicci =
        refl
    ; unitRiemannBoundary =
        "At the supported unit p2-time valuation chart, the zero Christoffel table yields a zero Riemann tensor table"
        ∷ "This discharges only the supported local Riemann socket; it is not a global non-flat curvature theorem"
        ∷ "Ricci, contracted Bianchi, stress-energy compatibility, and GR promotion remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitRicciWitness :
  FactorVecValuationP2LorentzUnitRicciWitness
canonicalFactorVecValuationP2LorentzUnitRicciWitness =
  record
    { unitRiemannWitness =
        canonicalFactorVecValuationP2LorentzUnitRiemannWitness
    ; unitRicciTensor =
        factorVecUnitP2LorentzRicciTensor
    ; unitRicciTensorIsZeroTable =
        refl
    ; ricciPrimitiveDischarged =
        missingValuationRicciContractionComputation
    ; ricciPrimitiveDischargedIsValuationRicci =
        refl
    ; firstRemainingMetricPrimitive =
        missingValuationContractedBianchiComputation
    ; firstRemainingMetricPrimitiveIsContractedBianchi =
        refl
    ; unitRicciBoundary =
        "At the supported unit p2-time valuation chart, the zero Riemann tensor contracts to the zero Ricci table"
        ∷ "This discharges only the supported local Ricci-contraction socket; it is not a global non-flat Ricci theorem"
        ∷ "Contracted Bianchi, stress-energy compatibility, and GR promotion remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitScalarCurvatureWitness :
  FactorVecValuationP2LorentzUnitScalarCurvatureWitness
canonicalFactorVecValuationP2LorentzUnitScalarCurvatureWitness =
  record
    { unitRicciWitness =
        canonicalFactorVecValuationP2LorentzUnitRicciWitness
    ; unitScalarCurvature =
        factorVecUnitP2LorentzScalarCurvature
    ; unitScalarCurvatureIsZero =
        refl
    ; unitScalarCurvatureBoundary =
        "At the supported unit p2-time valuation chart, the scalar curvature trace is the zero rational scalar"
        ∷ "This discharges only the supported local scalar-curvature socket; it is not a global non-flat scalar-curvature theorem"
        ∷ "Contracted Bianchi, Einstein-source coupling, stress-energy compatibility, and GR promotion remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitEinsteinTensorWitness :
  FactorVecValuationP2LorentzUnitEinsteinTensorWitness
canonicalFactorVecValuationP2LorentzUnitEinsteinTensorWitness =
  record
    { unitScalarCurvatureWitness =
        canonicalFactorVecValuationP2LorentzUnitScalarCurvatureWitness
    ; unitEinsteinTensor =
        factorVecUnitP2LorentzEinsteinTensor
    ; unitEinsteinTensorIsZeroTable =
        refl
    ; unitEinsteinTensorBoundary =
        "At the supported unit p2-time valuation chart, the Einstein tensor table is inhabited as the zero rational table"
        ∷ "This discharges only the supported local Einstein-tensor socket; it is not a global non-flat Einstein tensor law"
        ∷ "Einstein-source coupling, covariant-divergence compatibility, stress-energy compatibility, and GR promotion remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness :
  FactorVecValuationP2LorentzUnitContractedBianchiWitness
canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness =
  record
    { unitRicciWitness =
        canonicalFactorVecValuationP2LorentzUnitRicciWitness
    ; unitContractedBianchiDivergence =
        factorVecUnitP2LorentzContractedBianchiDivergence
    ; unitContractedBianchiDivergenceIsZeroTable =
        refl
    ; contractedBianchiPrimitiveDischarged =
        missingValuationContractedBianchiComputation
    ; contractedBianchiPrimitiveDischargedIsValuationContractedBianchi =
        refl
    ; firstRemainingMetricPrimitive =
        missingValuationStressEnergyCompatibilityComputation
    ; firstRemainingMetricPrimitiveIsStressEnergy =
        refl
    ; unitContractedBianchiBoundary =
        "At the supported unit p2-time valuation chart, the zero Ricci table has zero contracted-Bianchi divergence"
        ∷ "This discharges only the supported local contracted-Bianchi socket; it is not a global non-flat Bianchi theorem"
        ∷ "Stress-energy compatibility and GR promotion remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest :
  FactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest
canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest =
  record
    { stressEnergyCompatibilityPrimitive =
        missingValuationStressEnergyTensorCandidate
    ; stressEnergyCompatibilityPrimitiveIsTensorCandidate =
        refl
    ; missingTensorCandidatePrimitives =
        canonicalFactorVecStressEnergyTensorCandidateMissingPrimitives
    ; missingTensorCandidatePrimitivesAreCanonical =
        refl
    ; firstMissingTensorCandidatePrimitive =
        missingValuationStressEnergyTensorComponentFamily
    ; firstMissingTensorCandidatePrimitiveIsComponentFamily =
        refl
    ; tensorCandidateBoundary =
        "The tensor-candidate blocker is now typed as a missing component-family map on the valuation p2-time metric chart"
        ∷ "Symmetry, finite-support behavior, and carrier-embedding compatibility remain explicit follow-up tensor-candidate sub-primitives"
        ∷ "This is still a blocker surface only; no stress-energy tensor inhabitant is constructed"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress :
  FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress =
  record
    { tensorCandidateRequest =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest
    ; tensorComponentFamily =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    ; requestFirstMissingPrimitiveIsComponentFamily =
        refl
    ; dischargedTensorCandidatePrimitive =
        missingValuationStressEnergyTensorComponentFamily
    ; dischargedTensorCandidatePrimitiveIsComponentFamily =
        refl
    ; firstRemainingTensorCandidatePrimitive =
        missingValuationStressEnergyTensorSymmetryLaw
    ; firstRemainingTensorCandidatePrimitiveIsSymmetryLaw =
        refl
    ; componentFamilyProgressBoundary =
        "At the supported unit p2-time valuation chart, a concrete stress-energy tensor component-family map is now inhabited as the zero rational table over tangent direction pairs"
        ∷ "This discharges only the component-family tensor-candidate sub-primitive; symmetry, finite-support, and carrier-embedding sub-primitives remain open"
        ∷ "No Einstein-source coupling or covariant-divergence compatibility law is inhabited by this bounded step"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress :
  FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress
canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress =
  record
    { componentFamilyProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
    ; tensorSymmetryLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilySymmetry
    ; requestFirstRemainingPrimitiveIsSymmetryLaw =
        refl
    ; dischargedTensorCandidatePrimitive =
        missingValuationStressEnergyTensorSymmetryLaw
    ; dischargedTensorCandidatePrimitiveIsSymmetryLaw =
        refl
    ; firstRemainingTensorCandidatePrimitive =
        missingValuationStressEnergyTensorFiniteSupportLaw
    ; firstRemainingTensorCandidatePrimitiveIsFiniteSupportLaw =
        refl
    ; symmetryProgressBoundary =
        "At the supported unit p2-time valuation chart, the inhabited zero-table stress-energy component family is symmetric on tangent-direction pairs"
        ∷ "This discharges only the symmetry tensor-candidate sub-primitive; finite-support and carrier-embedding sub-primitives remain open"
        ∷ "No Einstein-source coupling or covariant-divergence compatibility law is inhabited by this bounded step"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress :
  FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress
canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress =
  record
    { symmetryProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress
    ; tensorFiniteSupportLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyFiniteSupport
    ; requestFirstRemainingPrimitiveIsFiniteSupportLaw =
        refl
    ; dischargedTensorCandidatePrimitive =
        missingValuationStressEnergyTensorFiniteSupportLaw
    ; dischargedTensorCandidatePrimitiveIsFiniteSupportLaw =
        refl
    ; firstRemainingTensorCandidatePrimitive =
        missingValuationStressEnergyTensorCarrierEmbedding
    ; firstRemainingTensorCandidatePrimitiveIsCarrierEmbedding =
        refl
    ; finiteSupportProgressBoundary =
        "At the supported unit p2-time valuation chart, the inhabited zero-table stress-energy component family has finite support by total vanishing on tangent-direction pairs"
        ∷ "This discharges only the finite-support tensor-candidate sub-primitive; carrier-embedding remains open"
        ∷ "No Einstein-source coupling or covariant-divergence compatibility law is inhabited by this bounded step"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress :
  FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress
canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress =
  record
    { finiteSupportProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress
    ; tensorCarrierEmbeddingLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding
    ; requestFirstRemainingPrimitiveIsCarrierEmbedding =
        refl
    ; dischargedTensorCandidatePrimitive =
        missingValuationStressEnergyTensorCarrierEmbedding
    ; dischargedTensorCandidatePrimitiveIsCarrierEmbedding =
        refl
    ; firstRemainingStressEnergyCompatibilityPrimitive =
        missingValuationEinsteinSourceCouplingLaw
    ; firstRemainingStressEnergyCompatibilityPrimitiveIsEinsteinSourceCouplingLaw =
        refl
    ; carrierEmbeddingProgressBoundary =
        "At the supported unit p2-time valuation chart, the inhabited zero-table stress-energy tensor factors through the finite Q-coefficient carrier coordinates"
        ∷ "This discharges the carrier-embedding tensor-candidate sub-primitive and advances the next stress-energy compatibility primitive to Einstein-source coupling"
        ∷ "Covariant-divergence compatibility and matter receipt interfaces remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress :
  FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress =
  record
    { carrierEmbeddingProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress
    ; einsteinSourceCouplingLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyEinsteinSourceCoupling
    ; requestFirstRemainingPrimitiveIsEinsteinSourceCouplingLaw =
        refl
    ; dischargedStressEnergyCompatibilityPrimitive =
        missingValuationEinsteinSourceCouplingLaw
    ; dischargedStressEnergyCompatibilityPrimitiveIsEinsteinSourceCouplingLaw =
        refl
    ; firstRemainingStressEnergyCompatibilityPrimitive =
        missingValuationStressEnergyCovariantDivergenceLaw
    ; firstRemainingStressEnergyCompatibilityPrimitiveIsCovariantDivergenceLaw =
        refl
    ; exactMissingMatterInterfaceSymbol =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; einsteinSourceCouplingProgressBoundary =
        "At the supported unit p2-time valuation chart, the zero-table Einstein tensor is explicitly coupled to the zero-table stress-energy component family"
        ∷ "This discharges the Einstein-source coupling primitive locally and advances the next stress-energy compatibility primitive to covariant-divergence compatibility"
        ∷ "Exact downstream matter interface symbol remains authority-boundary blocked: DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress :
  FactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress
canonicalFactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress =
  record
    { einsteinSourceCouplingProgress =
        canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
    ; stressEnergyCovariantDivergenceLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility
    ; requestFirstRemainingPrimitiveIsCovariantDivergenceLaw =
        refl
    ; dischargedStressEnergyCompatibilityPrimitive =
        missingValuationStressEnergyCovariantDivergenceLaw
    ; dischargedStressEnergyCompatibilityPrimitiveIsCovariantDivergenceLaw =
        refl
    ; firstRemainingStressEnergyCompatibilityPrimitive =
        missingValuationMatterReceiptInterface
    ; firstRemainingStressEnergyCompatibilityPrimitiveIsMatterReceiptInterface =
        refl
    ; matterStressEnergyInterfaceDiagnostic =
        EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; matterStressEnergyInterfaceFirstMissing =
        EEC.W4MatterStressEnergyInterfaceDiagnostic.firstMissing
          EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; matterStressEnergyInterfaceFirstMissingMatchesDiagnostic =
        refl
    ; matterStressEnergyInterfaceFirstMissingIsW4AnchorArtifactReceipt =
        EEC.W4MatterStressEnergyInterfaceDiagnostic.firstMissingIsW4AnchorArtifactReceipt
          EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; exactMissingMatterInterfaceSymbol =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; covariantDivergenceProgressBoundary =
        "At the supported unit p2-time valuation chart, contracted-Bianchi zero divergence is compatible with the zero-table stress-energy component family"
        ∷ "This discharges the covariant-divergence compatibility primitive locally and advances the next stress-energy compatibility primitive to the matter receipt interface"
        ∷ "Exact downstream matter interface symbol remains authority-boundary blocked: DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
        ∷ "The W4 matter/stress-energy interface diagnostic is now threaded with first missing field fixed to missingW4AnchorArtifactReceiptForMatterStress"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest :
  FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest =
  record
    { unitContractedBianchiWitness =
        canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; stressEnergyPrimitive =
        missingValuationStressEnergyCompatibilityComputation
    ; stressEnergyPrimitiveIsValuationStressEnergyCompatibility =
        refl
    ; missingStressEnergyCompatibilityPrimitives =
        canonicalFactorVecStressEnergyCompatibilityMissingPrimitives
    ; missingStressEnergyCompatibilityPrimitivesAreCanonical =
        refl
    ; firstMissingStressEnergyCompatibilityPrimitive =
        missingValuationStressEnergyTensorCandidate
    ; firstMissingStressEnergyCompatibilityPrimitiveIsTensorCandidate =
        refl
    ; tensorCandidateRequest =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest
    ; firstMissingTensorCandidatePrimitive =
        FactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest.firstMissingTensorCandidatePrimitive
          canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest
    ; firstMissingTensorCandidatePrimitiveIsComponentFamily =
        refl
    ; stressEnergyBoundary =
        "At the supported unit p2-time valuation chart, contracted-Bianchi is locally zero but no stress-energy tensor compatibility law is inhabited"
        ∷ "The next typed blocker is constructing a stress-energy tensor component family over the selected valuation metric carrier"
        ∷ "Einstein-source coupling, covariant-divergence compatibility, and matter receipt interfaces remain open"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt :
  FactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt
canonicalFactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt =
  record
    { stressEnergyCompatibilityRequest =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; stressEnergyCompatibilityRequestFirstMissing =
        FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; stressEnergyCompatibilityRequestFirstMissingIsTensorCandidate =
        refl
    ; tensorComponentFamilyProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
    ; tensorComponentFamily =
        FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress.tensorComponentFamily
          canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
    ; tensorComponentFamilyIsSupportedZeroTable =
        refl
    ; ymStressEnergyTensorShape =
        factorVecFormalYMStressEnergyTensorShape
    ; ymStressEnergyTensorShapeIsCanonical =
        refl
    ; einsteinSourceCouplingProgress =
        canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
    ; contractedBianchiWitness =
        canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; contractedBianchiConservationTarget =
        factorVecUnitP2LorentzContractedBianchiDivergence
    ; contractedBianchiConservationTargetIsSupportedZeroTable =
        refl
    ; stressEnergyCovariantDivergenceProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress
    ; stressEnergyCovariantDivergenceLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility
    ; contractedBianchiConservationTargetShape =
        factorVecContractedBianchiStressEnergyConservationTargetShape
    ; contractedBianchiConservationTargetShapeIsCanonical =
        refl
    ; firstRemainingStressEnergyCompatibilityPrimitive =
        FactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress.firstRemainingStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress
    ; firstRemainingStressEnergyCompatibilityPrimitiveIsMatterReceiptInterface =
        refl
    ; exactMissingMatterInterfaceSymbol =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; compatibilityBoundary =
        "This receipt connects the supported unit p2-time stress-energy component family to the formal Yang-Mills tensor shape string"
        ∷ "The component family is still the bounded zero-table witness over FactorVec tangent directions, not an authority-backed matter tensor"
        ∷ "The contracted-Bianchi target is the supported zero divergence table and the covariant-divergence law is local to that table"
        ∷ "The original stress-energy compatibility request still first-misses at missingValuationStressEnergyTensorCandidate"
        ∷ "After local covariant-divergence progress, the exact remaining blocker is the W4 matter/stress-energy receipt interface"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt :
  FactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt
canonicalFactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt =
  record
    { internalComponentFamilyProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
    ; internalComponentFamily =
        FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress.tensorComponentFamily
          canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
    ; internalComponentFamilyIsSupportedZeroTable =
        refl
    ; originalCompatibilityRequestFirstMissing =
        FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; originalCompatibilityRequestFirstMissingIsTensorCandidate =
        refl
    ; boundedLocalProgressFirstRemaining =
        FactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt.firstRemainingStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt
    ; boundedLocalProgressFirstRemainingIsMatterReceiptInterface =
        refl
    ; w4MatterStressEnergyInterfaceDiagnostic =
        EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; w4MatterStressEnergyInterfaceFirstMissing =
        EEC.W4MatterStressEnergyInterfaceDiagnostic.firstMissing
          EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; w4MatterStressEnergyInterfaceFirstMissingIsAnchorArtifactReceipt =
        EEC.W4MatterStressEnergyInterfaceDiagnostic.firstMissingIsW4AnchorArtifactReceipt
          EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; exactAuthorityBoundarySymbol =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; authorityBoundary =
        "u3 bounded result: the supported unit p2-time flat surface has an internal zero-table stress-energy component-family receipt"
        ∷ "The original compatibility request is intentionally fail-closed and still first-misses at missingValuationStressEnergyTensorCandidate"
        ∷ "The bounded local progress advances through source coupling and covariant divergence only to missingValuationMatterReceiptInterface"
        ∷ "The remaining authority-bound symbol is DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
        ∷ "No W4 authority token or global GR promotion is supplied by this receipt"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt :
  FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt
canonicalFactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt =
  record
    { componentFamilyProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
    ; fullTensorCandidate =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    ; fullTensorCandidateIsSupportedZeroTable =
        refl
    ; t00Candidate =
        factorVecUnitP2LorentzStressEnergyT00Candidate
    ; t00CandidateIsSupportedZero =
        factorVecUnitP2LorentzStressEnergyT00CandidateIsZero
    ; symmetryProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress
    ; finiteSupportProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress
    ; carrierEmbeddingProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress
    ; originalCompatibilityFirstMissing =
        FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; originalCompatibilityFirstMissingIsTensorCandidate =
        refl
    ; localProgressRemainingBlocker =
        FactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt.firstRemainingStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt
    ; localProgressRemainingBlockerIsMatterReceiptInterface =
        refl
    ; exactMissingMatterInterfaceSymbol =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; stagingBoundary =
        "The supported unit p2-time T00 candidate is the p2,p2 component of the local zero-table stress-energy tensor"
        ∷ "The full tensor candidate remains the same bounded zero-table component family over FactorVec tangent directions"
        ∷ "Symmetry, finite support, carrier embedding, Einstein-source coupling, and covariant-divergence compatibility are staged only for this supported local zero table"
        ∷ "The original stress-energy compatibility request remains honestly first-missing at missingValuationStressEnergyTensorCandidate"
        ∷ "No W4MatterStressEnergyInterfaceReceipt, authority token, sourced Einstein law, or global GR promotion is constructed"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt :
  FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt
canonicalFactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt =
  record
    { t00Staging =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt
    ; fullTensorCandidate =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    ; fullTensorCandidateIsSupportedZeroTable =
        refl
    ; t00Candidate =
        factorVecUnitP2LorentzStressEnergyT00Candidate
    ; t00CandidateIsSupportedZero =
        factorVecUnitP2LorentzStressEnergyT00CandidateIsZero
    ; t11Candidate =
        factorVecUnitP2LorentzStressEnergyT11Candidate
    ; t11CandidateIsSupportedZero =
        factorVecUnitP2LorentzStressEnergyT11CandidateIsZero
    ; t22Candidate =
        factorVecUnitP2LorentzStressEnergyT22Candidate
    ; t22CandidateIsSupportedZero =
        factorVecUnitP2LorentzStressEnergyT22CandidateIsZero
    ; t33Candidate =
        factorVecUnitP2LorentzStressEnergyT33Candidate
    ; t33CandidateIsSupportedZero =
        factorVecUnitP2LorentzStressEnergyT33CandidateIsZero
    ; offDiagonalP2P3Candidate =
        factorVecUnitP2LorentzStressEnergyOffDiagonalP2P3Candidate
    ; offDiagonalP2P3CandidateIsSupportedZero =
        factorVecUnitP2LorentzStressEnergyOffDiagonalP2P3CandidateIsZero
    ; symmetryProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress
    ; finiteSupportProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress
    ; carrierEmbeddingProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress
    ; einsteinSourceCouplingProgress =
        canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
    ; covariantDivergenceProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress
    ; contractedBianchiWitness =
        canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; contractedBianchiConservationTarget =
        factorVecUnitP2LorentzContractedBianchiDivergence
    ; contractedBianchiConservationTargetIsSupportedZeroTable =
        refl
    ; covariantDivergenceLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility
    ; localProgressRemainingBlocker =
        FactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress.firstRemainingStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress
    ; localProgressRemainingBlockerIsMatterReceiptInterface =
        refl
    ; fullComponentFamilyBoundary =
        "The supported unit p2-time stress-energy tensor candidate is now recorded as a full component family over all FactorVec tangent-direction pairs"
        ∷ "The displayed T00, T11, T22, T33, and off-diagonal p2,p3 components are projections of the same full zero-table family"
        ∷ "Symmetry, finite support, carrier embedding, Einstein-source coupling, and covariant-divergence compatibility are threaded through the full component family"
        ∷ "The conservation target is the supported contracted-Bianchi zero divergence table for the same tangent-direction family"
        ∷ "This is still bounded local flat staging, not an authority-backed W4 matter tensor or global GR source"
        ∷ []
    }

canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt :
  FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt
canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt =
  record
    { status =
        valuationMatterInterfaceHaltedAtExternalW4Receipt
    ; fullComponentFamilyReceipt =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt
    ; stressEnergyCompatibilityRequest =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; originalCompatibilityRequestFirstMissing =
        FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; originalCompatibilityRequestFirstMissingIsTensorCandidate =
        refl
    ; localProgressRemainingBlocker =
        FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt.localProgressRemainingBlocker
          canonicalFactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt
    ; localProgressRemainingBlockerIsMatterReceiptInterface =
        refl
    ; w4MatterStressEnergyInterfaceExternalHalt =
        W4Stress.canonicalW4MatterStressEnergyInterfaceExternalHalt
    ; w4ExternalHaltFirstBlocker =
        W4Stress.W4MatterStressEnergyInterfaceExternalHalt.firstAuthorityInterfaceBlocker
          W4Stress.canonicalW4MatterStressEnergyInterfaceExternalHalt
    ; w4ExternalHaltFirstBlockerIsCandidate256 =
        refl
    ; w4ExternalHaltNoSourcedEinsteinPromotion =
        W4Stress.w4MatterStressEnergyInterfaceExternalHaltNoSourcedEinsteinPromotion
    ; exactMissingMatterInterfaceSymbol =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; noEinsteinInterfaceReceiptHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; valuationMatterInterfaceBoundary =
        "The valuation stress-energy tensor candidate has advanced from a T00 staging point to the full local component family"
        ∷ "The local source-coupling and conservation checks close only for the supported zero-table family under the flat contracted-Bianchi divergence"
        ∷ "The valuation matter interface is halted exactly at the external W4MatterStressEnergyInterfaceReceipt"
        ∷ "The W4 external halt keeps MatterField, StressEnergyTensor, sourced Einstein law, and GR promotion unconstructed"
        ∷ []
    }

data FactorVecGate4StressEnergyConservationSourceStatus : Set where
  gate4StressEnergyConservationSourceStagedFlatOnly :
    FactorVecGate4StressEnergyConservationSourceStatus

record FactorVecGate4StressEnergyConservationSourceReceipt : Setω where
  field
    status :
      FactorVecGate4StressEnergyConservationSourceStatus

    christoffelWitness :
      FactorVecValuationP2LorentzUnitChristoffelWitness

    christoffelPrimitiveDischarged :
      FactorVecMetricGRPrimitive

    christoffelPrimitiveDischargedIsValuationChristoffel :
      christoffelPrimitiveDischarged
      ≡
      missingValuationLeviCivitaChristoffelComputation

    contractedBianchiWitness :
      FactorVecValuationP2LorentzUnitContractedBianchiWitness

    stressEnergyFullComponentFamilyReceipt :
      FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt

    sourceCouplingProgress :
      FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress

    sourceCouplingLaw :
      FactorVecEinsteinSourceCouplingLaw
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    sourceCouplingPrimitiveDischarged :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    sourceCouplingPrimitiveDischargedIsEinsteinSourceCoupling :
      sourceCouplingPrimitiveDischarged
      ≡
      missingValuationEinsteinSourceCouplingLaw

    covariantDivergenceProgress :
      FactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress

    covariantDivergenceLaw :
      FactorVecStressEnergyCovariantDivergenceLaw
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    covariantDivergencePrimitiveDischarged :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    covariantDivergencePrimitiveDischargedIsCovariantDivergence :
      covariantDivergencePrimitiveDischarged
      ≡
      missingValuationStressEnergyCovariantDivergenceLaw

    valuationMatterInterfaceReceipt :
      FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt

    originalCompatibilityRequestFirstMissing :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    originalCompatibilityRequestFirstMissingIsTensorCandidate :
      originalCompatibilityRequestFirstMissing
      ≡
      missingValuationStressEnergyTensorCandidate

    exactRemainingBlocker :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    exactRemainingBlockerIsMatterReceiptInterface :
      exactRemainingBlocker
      ≡
      missingValuationMatterReceiptInterface

    w4ExternalHaltFirstBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4ExternalHaltFirstBlockerIsCandidate256 :
      w4ExternalHaltFirstBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    noEinsteinInterfaceReceiptHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    noSourcedEinsteinPromotion :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt.promotesSourcedEinstein
        W4Stress.canonicalW4MatterStressEnergyInterfaceExternalHalt
      ≡
      false

    conservationSourceBoundary :
      List String

canonicalFactorVecGate4StressEnergyConservationSourceReceipt :
  FactorVecGate4StressEnergyConservationSourceReceipt
canonicalFactorVecGate4StressEnergyConservationSourceReceipt =
  record
    { status =
        gate4StressEnergyConservationSourceStagedFlatOnly
    ; christoffelWitness =
        canonicalFactorVecValuationP2LorentzUnitChristoffelWitness
    ; christoffelPrimitiveDischarged =
        FactorVecValuationP2LorentzUnitChristoffelWitness.christoffelPrimitiveDischarged
          canonicalFactorVecValuationP2LorentzUnitChristoffelWitness
    ; christoffelPrimitiveDischargedIsValuationChristoffel =
        refl
    ; contractedBianchiWitness =
        canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; stressEnergyFullComponentFamilyReceipt =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt
    ; sourceCouplingProgress =
        canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
    ; sourceCouplingLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyEinsteinSourceCoupling
    ; sourceCouplingPrimitiveDischarged =
        FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress.dischargedStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
    ; sourceCouplingPrimitiveDischargedIsEinsteinSourceCoupling =
        refl
    ; covariantDivergenceProgress =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress
    ; covariantDivergenceLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility
    ; covariantDivergencePrimitiveDischarged =
        FactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress.dischargedStressEnergyCompatibilityPrimitive
          canonicalFactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress
    ; covariantDivergencePrimitiveDischargedIsCovariantDivergence =
        refl
    ; valuationMatterInterfaceReceipt =
        canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt
    ; originalCompatibilityRequestFirstMissing =
        FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt.originalCompatibilityRequestFirstMissing
          canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt
    ; originalCompatibilityRequestFirstMissingIsTensorCandidate =
        refl
    ; exactRemainingBlocker =
        FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt.localProgressRemainingBlocker
          canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt
    ; exactRemainingBlockerIsMatterReceiptInterface =
        refl
    ; w4ExternalHaltFirstBlocker =
        FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt.w4ExternalHaltFirstBlocker
          canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt
    ; w4ExternalHaltFirstBlockerIsCandidate256 =
        refl
    ; noEinsteinInterfaceReceiptHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; noSourcedEinsteinPromotion =
        W4Stress.w4MatterStressEnergyInterfaceExternalHaltNoSourcedEinsteinPromotion
    ; conservationSourceBoundary =
        "Continuation wave 2 records the flat supported Christoffel witness as the Levi-Civita input used by the conservation/source staging"
        ∷ "The full p2-time 4x4 zero-table stress-energy family is threaded through local Einstein-source coupling"
        ∷ "The contracted-Bianchi zero divergence and the zero stress-energy table inhabit the local covariant-divergence/conservation law"
        ∷ "This receipt advances only bounded flat staging; the original global request still first-misses at missingValuationStressEnergyTensorCandidate"
        ∷ "The exact local remaining blocker is missingValuationMatterReceiptInterface, halted at the W4MatterStressEnergyInterfaceReceipt authority boundary"
        ∷ []
    }

data FactorVecDASHIMatterLagrangianCouplingStatus : Set where
  factorVecDASHIMatterLagrangianCouplingRecordedLocalOnly :
    FactorVecDASHIMatterLagrangianCouplingStatus

record FactorVecDASHIMatterLagrangianCouplingReceipt : Setω where
  field
    status :
      FactorVecDASHIMatterLagrangianCouplingStatus

    designReceipt :
      W4Stress.DASHIMatterLagrangianCouplingReceipt

    localInterfaceSurface :
      W4Stress.DASHIMatterLagrangianLocalInterfaceSurface

    localInterfaceOnly :
      W4Stress.DASHIMatterLagrangianLocalInterfaceSurface.localInterfaceOnly
        localInterfaceSurface
      ≡
      true

    localInterfaceConstructsW4MatterField :
      W4Stress.DASHIMatterLagrangianLocalInterfaceSurface.constructsW4MatterField
        localInterfaceSurface
      ≡
      false

    localInterfaceConstructsW4StressEnergyTensor :
      W4Stress.DASHIMatterLagrangianLocalInterfaceSurface.constructsW4StressEnergyTensor
        localInterfaceSurface
      ≡
      false

    lagrangianFormula :
      String

    lagrangianFormulaIsCanonical :
      lagrangianFormula
      ≡
      factorVecDASHIMatterLagrangianFormula

    metricVariationStressEnergyShape :
      String

    metricVariationStressEnergyShapeIsCanonical :
      metricVariationStressEnergyShape
      ≡
      factorVecMetricVariationStressEnergyTensorShape

    localStressEnergyTensorCandidate :
      FactorVecStressEnergyTensorComponentFamily

    localStressEnergyTensorCandidateIsSupportedZeroTable :
      localStressEnergyTensorCandidate
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    tensorCandidatePrimitiveRepresentedLocally :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    tensorCandidatePrimitiveRepresentedLocallyIsTensorCandidate :
      tensorCandidatePrimitiveRepresentedLocally
      ≡
      missingValuationStressEnergyTensorCandidate

    componentFamilyReceipt :
      FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt

    lorentzGaugeInvarianceLaw :
      FactorVecStressEnergyIdentityLorentzGaugeInvarianceLaw
        localStressEnergyTensorCandidate

    sourceCouplingLaw :
      FactorVecEinsteinSourceCouplingLaw localStressEnergyTensorCandidate

    conservationLaw :
      FactorVecStressEnergyCovariantDivergenceLaw
        localStressEnergyTensorCandidate

    sourcedBianchiCompatibilityReceipt :
      FactorVecGate4StressEnergyConservationSourceReceipt

    localCompatibilityRemainingBlocker :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    localCompatibilityRemainingBlockerIsMatterReceiptInterface :
      localCompatibilityRemainingBlocker
      ≡
      missingValuationMatterReceiptInterface

    w4AuthorityFirstBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4AuthorityFirstBlockerIsCandidate256 :
      w4AuthorityFirstBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    noEinsteinInterfaceReceiptHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    localOnlyBoundary :
      List String

canonicalFactorVecDASHIMatterLagrangianCouplingReceipt :
  FactorVecDASHIMatterLagrangianCouplingReceipt
canonicalFactorVecDASHIMatterLagrangianCouplingReceipt =
  record
    { status =
        factorVecDASHIMatterLagrangianCouplingRecordedLocalOnly
    ; designReceipt =
        W4Stress.canonicalDASHIMatterLagrangianCouplingReceipt
    ; localInterfaceSurface =
        W4Stress.DASHIMatterLagrangianCouplingReceipt.localInterfaceSurface
          W4Stress.canonicalDASHIMatterLagrangianCouplingReceipt
    ; localInterfaceOnly =
        W4Stress.DASHIMatterLagrangianCouplingReceipt.localInterfaceOnly
          W4Stress.canonicalDASHIMatterLagrangianCouplingReceipt
    ; localInterfaceConstructsW4MatterField =
        W4Stress.DASHIMatterLagrangianLocalInterfaceSurface.constructsW4MatterFieldIsFalse
          W4Stress.canonicalDASHIMatterLagrangianLocalInterfaceSurface
    ; localInterfaceConstructsW4StressEnergyTensor =
        W4Stress.DASHIMatterLagrangianLocalInterfaceSurface.constructsW4StressEnergyTensorIsFalse
          W4Stress.canonicalDASHIMatterLagrangianLocalInterfaceSurface
    ; lagrangianFormula =
        factorVecDASHIMatterLagrangianFormula
    ; lagrangianFormulaIsCanonical =
        refl
    ; metricVariationStressEnergyShape =
        factorVecMetricVariationStressEnergyTensorShape
    ; metricVariationStressEnergyShapeIsCanonical =
        refl
    ; localStressEnergyTensorCandidate =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    ; localStressEnergyTensorCandidateIsSupportedZeroTable =
        refl
    ; tensorCandidatePrimitiveRepresentedLocally =
        missingValuationStressEnergyTensorCandidate
    ; tensorCandidatePrimitiveRepresentedLocallyIsTensorCandidate =
        refl
    ; componentFamilyReceipt =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt
    ; lorentzGaugeInvarianceLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyIdentityLorentzGaugeInvariant
    ; sourceCouplingLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyEinsteinSourceCoupling
    ; conservationLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility
    ; sourcedBianchiCompatibilityReceipt =
        canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; localCompatibilityRemainingBlocker =
        FactorVecGate4StressEnergyConservationSourceReceipt.exactRemainingBlocker
          canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; localCompatibilityRemainingBlockerIsMatterReceiptInterface =
        refl
    ; w4AuthorityFirstBlocker =
        FactorVecGate4StressEnergyConservationSourceReceipt.w4ExternalHaltFirstBlocker
          canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; w4AuthorityFirstBlockerIsCandidate256 =
        refl
    ; noEinsteinInterfaceReceiptHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; localOnlyBoundary =
        "u3 consumes the typed local DASHIMatterLagrangianLocalInterfaceSurface as a local-only interface"
        ∷ "u3 records L_DASHI as the local design formula for the FactorVec matter/stress-energy surface"
        ∷ "The metric-variation tensor candidate is represented only by the supported unit p2-time zero-table component family"
        ∷ "Identity Lorentz/gauge invariance, source coupling, conservation, and sourced-Bianchi compatibility are inhabited only for that local zero-table family"
        ∷ "The exact remaining local blocker is missingValuationMatterReceiptInterface"
        ∷ "The W4 authority-side first blocker remains missingCandidate256CalibrationReceiptForMatterInterface; no W4/Candidate256 authority is fabricated"
        ∷ []
    }

factorVecDASHIMatterLagrangianCouplingRemainingBlocker :
  FactorVecDASHIMatterLagrangianCouplingReceipt.localCompatibilityRemainingBlocker
    canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
  ≡
  missingValuationMatterReceiptInterface
factorVecDASHIMatterLagrangianCouplingRemainingBlocker =
  refl

factorVecDASHIMatterLagrangianCouplingW4FirstBlocker :
  FactorVecDASHIMatterLagrangianCouplingReceipt.w4AuthorityFirstBlocker
    canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
  ≡
  W4Stress.missingCandidate256CalibrationReceiptForMatterInterface
factorVecDASHIMatterLagrangianCouplingW4FirstBlocker =
  refl

factorVecDASHIMatterLagrangianCouplingLocalInterfaceOnly :
  W4Stress.DASHIMatterLagrangianLocalInterfaceSurface.localInterfaceOnly
    (FactorVecDASHIMatterLagrangianCouplingReceipt.localInterfaceSurface
      canonicalFactorVecDASHIMatterLagrangianCouplingReceipt)
  ≡
  true
factorVecDASHIMatterLagrangianCouplingLocalInterfaceOnly =
  FactorVecDASHIMatterLagrangianCouplingReceipt.localInterfaceOnly
    canonicalFactorVecDASHIMatterLagrangianCouplingReceipt

factorVecValuationMatterInterfaceZeroBase :
  GL.FactorVec
factorVecValuationMatterInterfaceZeroBase =
  GL.v15
    zero zero zero zero zero
    zero zero zero zero zero
    zero zero zero zero zero

data FactorVecValuationMatterInterfaceConstructorAPIFinding : Set where
  factorVecConstructorAvailableViaGLVec15 :
    FactorVecValuationMatterInterfaceConstructorAPIFinding

  ymConnectionCarrierConstructorMissing :
    FactorVecValuationMatterInterfaceConstructorAPIFinding

  selectedFiniteRMetricConstructorMissingForInterface :
    FactorVecValuationMatterInterfaceConstructorAPIFinding

  stressEnergyTensorCarrierConstructorMissing :
    FactorVecValuationMatterInterfaceConstructorAPIFinding

  candidate256W4AuthorityConstructorExternalHalt :
    FactorVecValuationMatterInterfaceConstructorAPIFinding

canonicalFactorVecValuationMatterInterfaceConstructorAPIFindings :
  List FactorVecValuationMatterInterfaceConstructorAPIFinding
canonicalFactorVecValuationMatterInterfaceConstructorAPIFindings =
  factorVecConstructorAvailableViaGLVec15
  ∷ ymConnectionCarrierConstructorMissing
  ∷ selectedFiniteRMetricConstructorMissingForInterface
  ∷ stressEnergyTensorCarrierConstructorMissing
  ∷ candidate256W4AuthorityConstructorExternalHalt
  ∷ []

data FactorVecValuationMatterInterfaceAttemptStatus : Set where
  factorVecValuationMatterInterfaceFailClosedZeroTableOnly :
    FactorVecValuationMatterInterfaceAttemptStatus

record FactorVecValuationMatterReceiptInterfaceFailClosedReceipt : Setω where
  field
    status :
      FactorVecValuationMatterInterfaceAttemptStatus

    dashiMatterLagrangianCouplingReceipt :
      FactorVecDASHIMatterLagrangianCouplingReceipt

    w4ConcreteInterfaceAttempt :
      W4Stress.W4MatterStressEnergyConcreteInterfaceAttemptReceipt

    attemptedConcreteInterfaceShape :
      String

    localFactorVecBase :
      GL.FactorVec

    localFactorVecBaseIsZeroVec15 :
      localFactorVecBase
      ≡
      factorVecValuationMatterInterfaceZeroBase

    constructorAPIFindings :
      List FactorVecValuationMatterInterfaceConstructorAPIFinding

    constructorAPIFindingsAreCanonical :
      constructorAPIFindings
      ≡
      canonicalFactorVecValuationMatterInterfaceConstructorAPIFindings

    localOnlyStressEnergyTerm :
      FactorVecStressEnergyTensorComponentFamily

    localOnlyStressEnergyTermIsSupportedZeroTable :
      localOnlyStressEnergyTerm
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    localOnlyStressEnergyTermFiniteSupport :
      FactorVecStressEnergyTensorFiniteSupportLaw
        localOnlyStressEnergyTerm

    localOnlyStressEnergyTermCarrierEmbedding :
      FactorVecStressEnergyTensorCarrierEmbeddingLaw
        localOnlyStressEnergyTerm

    localOnlyEinsteinSourceCoupling :
      FactorVecEinsteinSourceCouplingLaw
        localOnlyStressEnergyTerm

    localOnlyCovariantDivergence :
      FactorVecStressEnergyCovariantDivergenceLaw
        localOnlyStressEnergyTerm

    matterReceiptInterfaceRemainingBlocker :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    matterReceiptInterfaceRemainingBlockerIsExact :
      matterReceiptInterfaceRemainingBlocker
      ≡
      missingValuationMatterReceiptInterface

    w4AuthorityFirstBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4AuthorityFirstBlockerIsCandidate256 :
      w4AuthorityFirstBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    constructsW4MatterStressEnergyInterfaceReceipt :
      Bool

    constructsW4MatterStressEnergyInterfaceReceiptIsFalse :
      constructsW4MatterStressEnergyInterfaceReceipt ≡ false

    constructsAuthorityBackedStressEnergyTensor :
      Bool

    constructsAuthorityBackedStressEnergyTensorIsFalse :
      constructsAuthorityBackedStressEnergyTensor ≡ false

    promotesSourcedEinstein :
      Bool

    promotesSourcedEinsteinIsFalse :
      promotesSourcedEinstein ≡ false

    noEinsteinInterfaceReceiptHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    failClosedBoundary :
      List String

canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt :
  FactorVecValuationMatterReceiptInterfaceFailClosedReceipt
canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt =
  record
    { status =
        factorVecValuationMatterInterfaceFailClosedZeroTableOnly
    ; dashiMatterLagrangianCouplingReceipt =
        canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
    ; w4ConcreteInterfaceAttempt =
        W4Stress.canonicalW4MatterStressEnergyConcreteInterfaceAttemptReceipt
    ; attemptedConcreteInterfaceShape =
        "FactorVec x YMConnectionCarrier x SelectedFiniteRMetric -> StressEnergyTensorCarrier"
    ; localFactorVecBase =
        factorVecValuationMatterInterfaceZeroBase
    ; localFactorVecBaseIsZeroVec15 =
        refl
    ; constructorAPIFindings =
        canonicalFactorVecValuationMatterInterfaceConstructorAPIFindings
    ; constructorAPIFindingsAreCanonical =
        refl
    ; localOnlyStressEnergyTerm =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    ; localOnlyStressEnergyTermIsSupportedZeroTable =
        refl
    ; localOnlyStressEnergyTermFiniteSupport =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyFiniteSupport
    ; localOnlyStressEnergyTermCarrierEmbedding =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCarrierEmbedding
    ; localOnlyEinsteinSourceCoupling =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyEinsteinSourceCoupling
    ; localOnlyCovariantDivergence =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility
    ; matterReceiptInterfaceRemainingBlocker =
        missingValuationMatterReceiptInterface
    ; matterReceiptInterfaceRemainingBlockerIsExact =
        refl
    ; w4AuthorityFirstBlocker =
        W4Stress.W4MatterStressEnergyConcreteInterfaceAttemptReceipt.firstAuthorityInterfaceBlocker
          W4Stress.canonicalW4MatterStressEnergyConcreteInterfaceAttemptReceipt
    ; w4AuthorityFirstBlockerIsCandidate256 =
        refl
    ; constructsW4MatterStressEnergyInterfaceReceipt =
        false
    ; constructsW4MatterStressEnergyInterfaceReceiptIsFalse =
        refl
    ; constructsAuthorityBackedStressEnergyTensor =
        false
    ; constructsAuthorityBackedStressEnergyTensorIsFalse =
        refl
    ; promotesSourcedEinstein =
        false
    ; promotesSourcedEinsteinIsFalse =
        refl
    ; noEinsteinInterfaceReceiptHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; failClosedBoundary =
        "u3 attempted the concrete matter-interface shape FactorVec x YMConnectionCarrier x SelectedFiniteRMetric -> StressEnergyTensorCarrier"
        ∷ "GL.v15 supplies a local FactorVec base, but the repo-local search did not expose a consumable YMConnectionCarrier constructor for this interface"
        ∷ "The selected finite-r metric tower has GRSelectedFiniteRMetricCarrier, but no exact SelectedFiniteRMetric interface constructor is consumed here"
        ∷ "No authority-backed StressEnergyTensorCarrier constructor is available; only the supported unit p2-time zero-table component family is constructible"
        ∷ "The receipt therefore remains fail-closed at missingValuationMatterReceiptInterface and preserves the W4/Candidate256 external halt"
        ∷ []
    }

factorVecValuationMatterReceiptInterfaceFailClosedStillMissing :
  FactorVecValuationMatterReceiptInterfaceFailClosedReceipt.matterReceiptInterfaceRemainingBlocker
    canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
  ≡
  missingValuationMatterReceiptInterface
factorVecValuationMatterReceiptInterfaceFailClosedStillMissing =
  refl

factorVecValuationMatterReceiptInterfaceFailClosedNoPromotion :
  FactorVecValuationMatterReceiptInterfaceFailClosedReceipt.promotesSourcedEinstein
    canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
  ≡
  false
factorVecValuationMatterReceiptInterfaceFailClosedNoPromotion =
  refl

canonicalFactorVecValuationDependentNonFlatSiteMetricSurface :
  FactorVecValuationDependentNonFlatSiteMetricSurface
canonicalFactorVecValuationDependentNonFlatSiteMetricSurface =
  record
    { BasePoint =
        GL.FactorVec
    ; TangentDirection =
        FactorVecTangentDirection
    ; valuationDepth =
        factorVecValuationDepth
    ; valuationDepthIsFactorVecCoordinate =
        refl
    ; requiredSiteMetricType =
        FactorVecValuationDependentSiteMetricType
    ; requiredSiteMetricTypeIsFactorVecValuationMetric =
        refl
    ; selectedTimePrime =
        timePrimeP2
    ; selectedTimePrimeDirection =
        factorVecCommittedTimeDirection
    ; selectedTimePrimeDirectionIsP2 =
        refl
    ; valuationScale =
        factorVecValuationScale
    ; valuationDiagonalWeight =
        factorVecValuationDiagonalWeight
    ; valuationDependentSiteMetric =
        factorVecValuationDependentP2LorentzMetric
    ; valuationDependentSiteMetricIsP2LorentzCandidate =
        refl
    ; valuationDependentMetricSymmetric =
        factorVecValuationDependentP2LorentzMetricSymmetric
    ; valuationTimePrimeMetricWitness =
        canonicalFactorVecValuationP2TimePrimeMetricWitness
    ; valuationDiagonalShapeWitness =
        canonicalFactorVecValuationP2LorentzDiagonalShapeWitness
    ; valuationNonzeroSupportWitness =
        canonicalFactorVecValuationAllLaneNonzeroSupportWitness
    ; valuationSignedWeightVectorWitness =
        canonicalFactorVecValuationP2LorentzSignedWeightVectorWitness
    ; valuationRationalNonzeroWeightWitness =
        canonicalFactorVecValuationP2LorentzRationalNonzeroWeightWitness
    ; valuationRankNondegenerateWitness =
        canonicalFactorVecValuationP2LorentzRankNondegenerateWitness
    ; valuationSylvesterInertiaWitness =
        canonicalFactorVecValuationP2LorentzSylvesterInertiaWitness
    ; valuationMetricNondegenerateSignature =
        canonicalMetricNondegenerateSignature
    ; valuationUnitInverseMetricWitness =
        canonicalFactorVecValuationP2LorentzUnitInverseMetricWitness
    ; valuationUnitChristoffelWitness =
        canonicalFactorVecValuationP2LorentzUnitChristoffelWitness
    ; valuationUnitRiemannWitness =
        canonicalFactorVecValuationP2LorentzUnitRiemannWitness
    ; valuationUnitRicciWitness =
        canonicalFactorVecValuationP2LorentzUnitRicciWitness
    ; valuationUnitScalarCurvatureWitness =
        canonicalFactorVecValuationP2LorentzUnitScalarCurvatureWitness
    ; valuationUnitEinsteinTensorWitness =
        canonicalFactorVecValuationP2LorentzUnitEinsteinTensorWitness
    ; valuationUnitContractedBianchiWitness =
        canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; valuationUnitStressEnergyCompatibilityRequest =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; firstNondegeneratePrimitiveAfterSupport =
        missingValuationMetricNondegenerateProof
    ; firstNondegeneratePrimitiveAfterSupportIsValuationNondegenerate =
        refl
    ; firstMetricPrimitiveAfterInertia =
        missingValuationInverseMetricComputation
    ; firstMetricPrimitiveAfterInertiaIsInverseMetric =
        refl
    ; firstMetricPrimitiveAfterUnitInverse =
        missingValuationLeviCivitaChristoffelComputation
    ; firstMetricPrimitiveAfterUnitInverseIsChristoffel =
        refl
    ; firstMetricPrimitiveAfterUnitChristoffel =
        missingValuationRiemannCurvatureComputation
    ; firstMetricPrimitiveAfterUnitChristoffelIsRiemann =
        refl
    ; firstMetricPrimitiveAfterUnitRiemann =
        missingValuationRicciContractionComputation
    ; firstMetricPrimitiveAfterUnitRiemannIsRicci =
        refl
    ; firstMetricPrimitiveAfterUnitRicci =
        missingValuationContractedBianchiComputation
    ; firstMetricPrimitiveAfterUnitRicciIsContractedBianchi =
        refl
    ; firstMetricPrimitiveAfterUnitContractedBianchi =
        missingValuationStressEnergyCompatibilityComputation
    ; firstMetricPrimitiveAfterUnitContractedBianchiIsStressEnergy =
        refl
    ; requiredSignatureTarget =
        valuationDependentNonFlatGRSignaturePrimitive
    ; missingPrimitives =
        canonicalFactorVecMetricGRPrimitives
    ; missingPrimitivesAreCanonical =
        refl
    ; nonFlatBoundary =
        "The non-flat candidate now fixes p2 as the time-prime direction"
        ∷ "The site metric is diagonal: valuationDepth(base,p) scaled by 1/p, with the p2 diagonal sign-flipped"
        ∷ "The metric depends on FactorVec valuation coordinates, not only on constant prime reciprocals"
        ∷ "Symmetry is inhabited for the diagonal p2-time candidate"
        ∷ "A concrete all-lane nonzero valuation-support base is inhabited for the p2-time candidate"
        ∷ "The supported base now carries a canonical signed fifteen-coordinate diagonal weight vector"
        ∷ "The unit-support p2-time weights now carry checked rational nonzero witnesses and a one-time/fourteen-spatial finite lane classifier"
        ∷ "The unit-support diagonal rank/nondegeneracy socket is witnessed from those checked nonzero weights"
        ∷ "The unit-support p2-time Sylvester/Lorentzian inertia socket is now witnessed from the checked signed-weight and lane-classifier data"
        ∷ "MetricNondegenerateSignature now packages determinant target, rank/nondegeneracy, and inertia before inverse-metric work"
        ∷ "The unit-support p2-time inverse-metric socket is now witnessed as a diagonal -1/2,+1/2 form"
        ∷ "The supported unit p2-time Christoffel socket is now witnessed by the zero rational table"
        ∷ "The supported unit p2-time Riemann socket is now witnessed by the zero rational table"
        ∷ "The supported unit p2-time Ricci contraction socket is now witnessed by the zero rational table"
        ∷ "The supported unit p2-time scalar-curvature socket is now witnessed by the zero rational scalar"
        ∷ "The supported unit p2-time Einstein-tensor socket is now witnessed by the zero rational table"
        ∷ "The supported unit p2-time contracted-Bianchi socket is now witnessed by the zero divergence table"
        ∷ "Stress-energy compatibility is still primitive"
        ∷ []
    }

canonicalFactorVecFiniteKoszulChristoffelWitness :
  FactorVecFiniteKoszulChristoffelWitness
canonicalFactorVecFiniteKoszulChristoffelWitness =
  record
    { metric =
        canonicalFactorVecSymmetricRationalBilinearMetric
    ; metricFiniteDifference =
        factorVecMetricFiniteDifference
    ; koszulExpression =
        factorVecKoszulExpression
    ; christoffelSymbol =
        factorVecChristoffelSymbol
    ; scaledChristoffelSymbol =
        factorVecScaledChristoffelSymbol
    ; koszulChristoffelLaw =
        factorVecKoszulChristoffelWitness
    ; torsionFreeChristoffelLaw =
        factorVecChristoffelTorsionFree
    ; metricCompatibilityLaw =
        factorVecMetricCompatibilityWitness
    ; witnessBoundary =
        "Metric finite differences are zero on the flat rational seed metric"
        ∷ "The finite Koszul expression is zero on every FactorVec base point and SSP tangent triple"
        ∷ "The Christoffel table is the zero rational table over the finite SSP tangent basis"
        ∷ "The Koszul/Christoffel equality and torsion-free symmetry are inhabited definitionally"
        ∷ "This witness does not provide non-flat Christoffel coefficients or curvature"
        ∷ []
    }

canonicalFactorVecConstantDiagonalFiniteKoszulChristoffelWitness :
  FactorVecFiniteKoszulChristoffelWitness
canonicalFactorVecConstantDiagonalFiniteKoszulChristoffelWitness =
  record
    { metric =
        canonicalFactorVecConstantDiagonalReciprocalPrimeMetric
    ; metricFiniteDifference =
        factorVecMetricFiniteDifference
    ; koszulExpression =
        factorVecKoszulExpression
    ; christoffelSymbol =
        factorVecChristoffelSymbol
    ; scaledChristoffelSymbol =
        factorVecScaledChristoffelSymbol
    ; koszulChristoffelLaw =
        factorVecKoszulChristoffelWitness
    ; torsionFreeChristoffelLaw =
        factorVecChristoffelTorsionFree
    ; metricCompatibilityLaw =
        factorVecMetricCompatibilityWitness
    ; witnessBoundary =
        "The constant diagonal reciprocal-prime metric is base-independent"
        ∷ "The finite-difference/Koszul/Christoffel table remains the zero flat table at this constant-metric rung"
        ∷ "This is a flat constant prerequisite only; it does not provide valuation-dependent curvature"
        ∷ []
    }

canonicalFactorVecRicciBianchiPrimitiveRequest :
  FactorVecRicciBianchiPrimitiveRequest
canonicalFactorVecRicciBianchiPrimitiveRequest =
  record
    { valuationDependentMetricType =
        FactorVecValuationDependentSiteMetricType
    ; valuationDependentMetricTypeIsCanonical =
        refl
    ; inverseMetricPrimitive =
        missingValuationInverseMetricComputation
    ; christoffelPrimitive =
        missingValuationLeviCivitaChristoffelComputation
    ; riemannPrimitive =
        missingValuationRiemannCurvatureComputation
    ; ricciPrimitive =
        missingValuationRicciContractionComputation
    ; contractedBianchiPrimitive =
        missingValuationContractedBianchiComputation
    ; stressEnergyPrimitive =
        missingValuationStressEnergyCompatibilityComputation
    ; supportedUnitStressEnergyCompatibilityRequest =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; primitiveBoundary =
        "Ricci is not computed from the constant reciprocal-prime candidate"
        ∷ "The supported unit p2-time Ricci contraction is witnessed by the local zero table, not by a global non-flat theorem"
        ∷ "The supported unit p2-time contracted-Bianchi computation is witnessed by the local zero divergence table"
        ∷ "Stress-energy compatibility is separately named and cannot be inferred from the flat seed Koszul witness"
        ∷ []
    }

canonicalFactorVecContractedBianchiRoute :
  FactorVecContractedBianchiRoute
canonicalFactorVecContractedBianchiRoute =
  record
    { metric =
        canonicalFactorVecConstantDiagonalReciprocalPrimeMetric
    ; koszulChristoffelWitness =
        canonicalFactorVecConstantDiagonalFiniteKoszulChristoffelWitness
    ; firstRemainingGate =
        missingNonDegenerateFactorVecMetricSignature
    ; firstRemainingGateIsNonDegenerateSignature =
        refl
    ; remainingGates =
        canonicalFactorVecContractedBianchiRouteMissingGates
    ; remainingGatesAreCanonical =
        refl
    ; routeBoundary =
        "The route now starts from a typed symmetric rational g on FactorVec tangent directions"
        ∷ "A finite Koszul/Christoffel witness is available for the flat constant reciprocal-prime candidate"
        ∷ "The diagonal basis-shape laws and finite matrix carrier are inhabited but do not constitute determinant/rank non-degeneracy or signature"
        ∷ "Contracted Bianchi still requires non-degenerate metric/signature data, non-flat Christoffel coefficients, Riemann antisymmetry, Ricci contraction, covariant divergence, contraction law, and stress-energy compatibility"
        ∷ []
    }

canonicalFactorVecDiscreteMetricTensorSurface :
  FactorVecDiscreteMetricTensorSurface
canonicalFactorVecDiscreteMetricTensorSurface =
  record
    { metric =
        canonicalFactorVecConstantDiagonalReciprocalPrimeMetric
    ; constantDiagonalReciprocalPrimeFlatnessCandidate =
        canonicalFactorVecConstantDiagonalReciprocalPrimeMetricSurface
    ; valuationDependentNonFlatSiteMetricRequired =
        canonicalFactorVecValuationDependentNonFlatSiteMetricSurface
    ; koszulChristoffelWitness =
        canonicalFactorVecConstantDiagonalFiniteKoszulChristoffelWitness
    ; ricciBianchiPrimitiveRequest =
        canonicalFactorVecRicciBianchiPrimitiveRequest
    ; contractedBianchiRoute =
        canonicalFactorVecContractedBianchiRoute
    ; surfaceBoundary =
        "This is a theorem-thin discrete metric tensor surface over FactorVec tangent SSP directions"
        ∷ "It separates the constant diagonal reciprocal-prime flatness candidate from the valuation-dependent non-flat site metric required for GR"
        ∷ "It supplies typed symmetric rational g data, finite flat constant Koszul/Christoffel witness data, and an explicit contracted-Bianchi route boundary"
        ∷ "It supplies supported unit p2-time zero-table Riemann/Ricci/scalar-curvature/Einstein and contracted-Bianchi witnesses only"
        ∷ "It does not construct a global non-flat Riemann tensor law, Einstein tensor law, source coupling, stress-energy compatibility, or GR promotion"
        ∷ []
    }

factorVecMetricTensorSurfaceConstantCandidateFirstPrimitive :
  FactorVecConstantDiagonalReciprocalPrimeMetricSurface.missingNondegeneratePrimitive
    canonicalFactorVecConstantDiagonalReciprocalPrimeMetricSurface
  ≡
  missingConstantDiagonalNondegenerateProof
factorVecMetricTensorSurfaceConstantCandidateFirstPrimitive =
  refl

factorVecMetricTensorSurfaceRicciPrimitive :
  FactorVecRicciBianchiPrimitiveRequest.ricciPrimitive
    canonicalFactorVecRicciBianchiPrimitiveRequest
  ≡
  missingValuationRicciContractionComputation
factorVecMetricTensorSurfaceRicciPrimitive =
  refl

factorVecMetricTensorSurfaceSupportedUnitRicciFirstNext :
  FactorVecValuationP2LorentzUnitRicciWitness.firstRemainingMetricPrimitive
    canonicalFactorVecValuationP2LorentzUnitRicciWitness
  ≡
  missingValuationContractedBianchiComputation
factorVecMetricTensorSurfaceSupportedUnitRicciFirstNext =
  refl

factorVecMetricTensorSurfaceSupportedUnitInverseFirstNext :
  FactorVecValuationP2LorentzUnitInverseChristoffelProgress.firstMetricPrimitiveAfterUnitInverse
    canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress
  ≡
  missingValuationLeviCivitaChristoffelComputation
factorVecMetricTensorSurfaceSupportedUnitInverseFirstNext =
  refl

factorVecMetricTensorSurfaceSignatureFirstNext :
  FactorVecValuationP2LorentzSignatureInverseHandoffProgress.firstMetricPrimitiveAfterInertia
    canonicalFactorVecValuationP2LorentzSignatureInverseHandoffProgress
  ≡
  missingValuationInverseMetricComputation
factorVecMetricTensorSurfaceSignatureFirstNext =
  refl

factorVecMetricTensorSurfaceSupportedUnitChristoffelFirstNext :
  FactorVecValuationP2LorentzUnitInverseChristoffelProgress.firstMetricPrimitiveAfterUnitChristoffel
    canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress
  ≡
  missingValuationRiemannCurvatureComputation
factorVecMetricTensorSurfaceSupportedUnitChristoffelFirstNext =
  refl

factorVecMetricTensorSurfaceContractedBianchiPrimitive :
  FactorVecRicciBianchiPrimitiveRequest.contractedBianchiPrimitive
    canonicalFactorVecRicciBianchiPrimitiveRequest
  ≡
  missingValuationContractedBianchiComputation
factorVecMetricTensorSurfaceContractedBianchiPrimitive =
  refl

factorVecMetricTensorSurfaceSupportedUnitContractedBianchiFirstNext :
  FactorVecValuationP2LorentzUnitContractedBianchiWitness.firstRemainingMetricPrimitive
    canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
  ≡
  missingValuationStressEnergyCompatibilityComputation
factorVecMetricTensorSurfaceSupportedUnitContractedBianchiFirstNext =
  refl

factorVecMetricTensorSurfaceStressEnergyPrimitive :
  FactorVecRicciBianchiPrimitiveRequest.stressEnergyPrimitive
    canonicalFactorVecRicciBianchiPrimitiveRequest
  ≡
  missingValuationStressEnergyCompatibilityComputation
factorVecMetricTensorSurfaceStressEnergyPrimitive =
  refl

factorVecMetricTensorSurfaceStressEnergyFirstMissingPrimitive :
  FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingStressEnergyCompatibilityPrimitive
    canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
  ≡
  missingValuationStressEnergyTensorCandidate
factorVecMetricTensorSurfaceStressEnergyFirstMissingPrimitive =
  refl

factorVecMetricTensorSurfaceStressEnergyTensorFirstMissingPrimitive :
  FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingTensorCandidatePrimitive
    canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
  ≡
  missingValuationStressEnergyTensorComponentFamily
factorVecMetricTensorSurfaceStressEnergyTensorFirstMissingPrimitive =
  refl

factorVecMetricTensorSurfaceStressEnergyTensorNextAfterComponentFamily :
  FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress.firstRemainingTensorCandidatePrimitive
    canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
  ≡
  missingValuationStressEnergyTensorSymmetryLaw
factorVecMetricTensorSurfaceStressEnergyTensorNextAfterComponentFamily =
  refl

factorVecMetricTensorSurfaceStressEnergyTensorNextAfterSymmetry :
  FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress.firstRemainingTensorCandidatePrimitive
    canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress
  ≡
  missingValuationStressEnergyTensorFiniteSupportLaw
factorVecMetricTensorSurfaceStressEnergyTensorNextAfterSymmetry =
  refl

factorVecMetricTensorSurfaceStressEnergyTensorNextAfterFiniteSupport :
  FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress.firstRemainingTensorCandidatePrimitive
    canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress
  ≡
  missingValuationStressEnergyTensorCarrierEmbedding
factorVecMetricTensorSurfaceStressEnergyTensorNextAfterFiniteSupport =
  refl

factorVecMetricTensorSurfaceStressEnergyCompatibilityNextAfterCarrierEmbedding :
  FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress.firstRemainingStressEnergyCompatibilityPrimitive
    canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress
  ≡
  missingValuationEinsteinSourceCouplingLaw
factorVecMetricTensorSurfaceStressEnergyCompatibilityNextAfterCarrierEmbedding =
  refl

factorVecMetricTensorSurfaceStressEnergyCompatibilityNextAfterEinsteinSourceCoupling :
  FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress.firstRemainingStressEnergyCompatibilityPrimitive
    canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
  ≡
  missingValuationStressEnergyCovariantDivergenceLaw
factorVecMetricTensorSurfaceStressEnergyCompatibilityNextAfterEinsteinSourceCoupling =
  refl

factorVecMetricTensorSurfaceStressEnergyCompatibilityNextAfterCovariantDivergence :
  FactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress.firstRemainingStressEnergyCompatibilityPrimitive
    canonicalFactorVecValuationP2LorentzUnitStressEnergyCovariantDivergenceProgress
  ≡
  missingValuationMatterReceiptInterface
factorVecMetricTensorSurfaceStressEnergyCompatibilityNextAfterCovariantDivergence =
  refl

factorVecMetricTensorSurfaceYMGRStressEnergyReceiptFirstMissingHonest :
  FactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt.stressEnergyCompatibilityRequestFirstMissing
    canonicalFactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt
  ≡
  missingValuationStressEnergyTensorCandidate
factorVecMetricTensorSurfaceYMGRStressEnergyReceiptFirstMissingHonest =
  refl

factorVecMetricTensorSurfaceYMGRStressEnergyReceiptRemainingBlocker :
  FactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt.firstRemainingStressEnergyCompatibilityPrimitive
    canonicalFactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt
  ≡
  missingValuationMatterReceiptInterface
factorVecMetricTensorSurfaceYMGRStressEnergyReceiptRemainingBlocker =
  refl

factorVecMetricTensorSurfaceStressEnergyAuthorityBoundaryOriginalFirstMissing :
  FactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt.originalCompatibilityRequestFirstMissing
    canonicalFactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt
  ≡
  missingValuationStressEnergyTensorCandidate
factorVecMetricTensorSurfaceStressEnergyAuthorityBoundaryOriginalFirstMissing =
  refl

factorVecMetricTensorSurfaceStressEnergyAuthorityBoundaryLocalRemaining :
  FactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt.boundedLocalProgressFirstRemaining
    canonicalFactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt
  ≡
  missingValuationMatterReceiptInterface
factorVecMetricTensorSurfaceStressEnergyAuthorityBoundaryLocalRemaining =
  refl

factorVecMetricTensorSurfaceStressEnergyAuthorityBoundaryW4FirstMissing :
  FactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt.w4MatterStressEnergyInterfaceFirstMissing
    canonicalFactorVecValuationP2LorentzUnitStressEnergyAuthorityBoundaryReceipt
  ≡
  EEC.missingW4AnchorArtifactReceiptForMatterStress
factorVecMetricTensorSurfaceStressEnergyAuthorityBoundaryW4FirstMissing =
  refl

factorVecMetricTensorSurfaceStressEnergyT00CandidateZero :
  FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt.t00Candidate
    canonicalFactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt
  ≡
  zeroℚ
factorVecMetricTensorSurfaceStressEnergyT00CandidateZero =
  refl

factorVecMetricTensorSurfaceStressEnergyT00StagingOriginalFirstMissing :
  FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt.originalCompatibilityFirstMissing
    canonicalFactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt
  ≡
  missingValuationStressEnergyTensorCandidate
factorVecMetricTensorSurfaceStressEnergyT00StagingOriginalFirstMissing =
  refl

factorVecMetricTensorSurfaceStressEnergyT00StagingLocalRemaining :
  FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt.localProgressRemainingBlocker
    canonicalFactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt
  ≡
  missingValuationMatterReceiptInterface
factorVecMetricTensorSurfaceStressEnergyT00StagingLocalRemaining =
  refl

factorVecMetricTensorSurfaceStressEnergyFullFourByFourT33Zero :
  FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T33
    canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
  ≡
  zeroℚ
factorVecMetricTensorSurfaceStressEnergyFullFourByFourT33Zero =
  refl

factorVecMetricTensorSurfaceStressEnergyFullFourByFourAllZero :
  (mu nu : FactorVecP2LorentzUnitStressEnergyIndex) →
  FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T
    canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    mu
    nu
  ≡
  zeroℚ
factorVecMetricTensorSurfaceStressEnergyFullFourByFourAllZero =
  FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.allFourComponentsZero
    canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily

factorVecMetricTensorSurfaceStressEnergyFullFamilyLocalRemaining :
  FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt.localProgressRemainingBlocker
    canonicalFactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt
  ≡
  missingValuationMatterReceiptInterface
factorVecMetricTensorSurfaceStressEnergyFullFamilyLocalRemaining =
  refl

factorVecMetricTensorSurfaceValuationMatterInterfaceHardHalt :
  FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt.w4ExternalHaltFirstBlocker
    canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt
  ≡
  W4Stress.missingCandidate256CalibrationReceiptForMatterInterface
factorVecMetricTensorSurfaceValuationMatterInterfaceHardHalt =
  refl

factorVecMetricSurfaceFirstContractedBianchiGate :
  FactorVecContractedBianchiRoute.firstRemainingGate
    canonicalFactorVecContractedBianchiRoute
  ≡
  missingNonDegenerateFactorVecMetricSignature
factorVecMetricSurfaceFirstContractedBianchiGate =
  refl

factorVecMetricTensorSurfaceKoszulLaw :
  (base : GL.FactorVec) →
  (lambda mu nu : FactorVecTangentDirection) →
  factorVecScaledChristoffelSymbol base lambda mu nu
  ≡
  factorVecKoszulExpression base lambda mu nu
factorVecMetricTensorSurfaceKoszulLaw =
  factorVecKoszulChristoffelWitness

data FactorVecGate4DASHIMatterStressEnergyFinalStatus : Set where
  factorVecGate4DASHIMatterStressEnergyFinalNonPromoting :
    FactorVecGate4DASHIMatterStressEnergyFinalStatus

record FactorVecGate4DASHIMatterStressEnergyFinalReceipt : Setω where
  field
    status :
      FactorVecGate4DASHIMatterStressEnergyFinalStatus

    dashiMatterLagrangianCouplingReceipt :
      FactorVecDASHIMatterLagrangianCouplingReceipt

    valuationMatterReceiptInterfaceFailClosedReceipt :
      FactorVecValuationMatterReceiptInterfaceFailClosedReceipt

    w4HardHaltReceipt :
      W4Stress.W4MatterStressEnergyGate4HardHaltReceipt

    fullValuationStressEnergyTensorCandidate :
      FactorVecStressEnergyTensorComponentFamily

    fullValuationStressEnergyTensorCandidateIsSupportedZeroTable :
      fullValuationStressEnergyTensorCandidate
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    fullValuationStressEnergyTensorCandidateAllZero :
      FactorVecStressEnergyTensorFiniteSupportLaw
        fullValuationStressEnergyTensorCandidate

    lorentzGaugeInvarianceLaw :
      FactorVecStressEnergyIdentityLorentzGaugeInvarianceLaw
        fullValuationStressEnergyTensorCandidate

    conservationLaw :
      FactorVecStressEnergyCovariantDivergenceLaw
        fullValuationStressEnergyTensorCandidate

    contractedBianchiSourceCompatibilityReceipt :
      FactorVecGate4StressEnergyConservationSourceReceipt

    matterReceiptInterfaceRemainingBlocker :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    matterReceiptInterfaceRemainingBlockerIsExact :
      matterReceiptInterfaceRemainingBlocker
      ≡
      missingValuationMatterReceiptInterface

    w4AuthorityFirstBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4AuthorityFirstBlockerIsCandidate256 :
      w4AuthorityFirstBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    noEinsteinInterfaceReceiptHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    finalNonPromotionBoundary :
      List String

canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt :
  FactorVecGate4DASHIMatterStressEnergyFinalReceipt
canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt =
  record
    { status =
        factorVecGate4DASHIMatterStressEnergyFinalNonPromoting
    ; dashiMatterLagrangianCouplingReceipt =
        canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
    ; valuationMatterReceiptInterfaceFailClosedReceipt =
        canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
    ; w4HardHaltReceipt =
        W4Stress.canonicalW4MatterStressEnergyGate4HardHaltReceipt
    ; fullValuationStressEnergyTensorCandidate =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    ; fullValuationStressEnergyTensorCandidateIsSupportedZeroTable =
        refl
    ; fullValuationStressEnergyTensorCandidateAllZero =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyFiniteSupport
    ; lorentzGaugeInvarianceLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyIdentityLorentzGaugeInvariant
    ; conservationLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility
    ; contractedBianchiSourceCompatibilityReceipt =
        canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; matterReceiptInterfaceRemainingBlocker =
        FactorVecGate4StressEnergyConservationSourceReceipt.exactRemainingBlocker
          canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; matterReceiptInterfaceRemainingBlockerIsExact =
        refl
    ; w4AuthorityFirstBlocker =
        W4Stress.W4MatterStressEnergyGate4HardHaltReceipt.firstAuthorityInterfaceBlocker
          W4Stress.canonicalW4MatterStressEnergyGate4HardHaltReceipt
    ; w4AuthorityFirstBlockerIsCandidate256 =
        refl
    ; noEinsteinInterfaceReceiptHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; finalNonPromotionBoundary =
        "Gate 4 final local receipt: L_DASHI is recorded, and the full valuation T_mu_nu candidate is the supported unit p2-time zero-table family"
        ∷ "The concrete interface attempt is fail-closed: FactorVec is locally inhabited, but YMConnectionCarrier, SelectedFiniteRMetric interface wiring, and authority-backed StressEnergyTensorCarrier are not"
        ∷ "The local zero-table candidate has inhabited identity Lorentz/gauge invariance, conservation, and contracted-Bianchi source compatibility witnesses"
        ∷ "Those witnesses are bounded flat staging only; the remaining local blocker is missingValuationMatterReceiptInterface"
        ∷ "The W4 hard halt first blocker is missingCandidate256CalibrationReceiptForMatterInterface, so no W4 MatterField, authority-backed StressEnergyTensor, sourced Einstein law, or GR promotion is constructed"
        ∷ []
    }

factorVecGate4DASHIMatterStressEnergyFinalRemainingBlocker :
  FactorVecGate4DASHIMatterStressEnergyFinalReceipt.matterReceiptInterfaceRemainingBlocker
    canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
  ≡
  missingValuationMatterReceiptInterface
factorVecGate4DASHIMatterStressEnergyFinalRemainingBlocker =
  refl

factorVecGate4DASHIMatterStressEnergyFinalW4FirstBlocker :
  FactorVecGate4DASHIMatterStressEnergyFinalReceipt.w4AuthorityFirstBlocker
    canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
  ≡
  W4Stress.missingCandidate256CalibrationReceiptForMatterInterface
factorVecGate4DASHIMatterStressEnergyFinalW4FirstBlocker =
  refl

------------------------------------------------------------------------
-- Current-wave u3 consumable constructor surface.
--
-- The requested constructor
--   FactorVec x YMConnectionCarrier x SelectedFiniteRMetric ->
--   StressEnergyTensorCarrier
-- is not available as an authority-backed interface in this file.  What is
-- locally consumable is the bounded supported-unit p2-time zero-table tensor
-- family, with the DASHI matter Lagrangian formula, source coupling, Lorentz
-- identity invariance, and covariant-divergence law already threaded above.

data FactorVecGate4ConsumableStressEnergyConstructorStatus : Set where
  factorVecGate4ConsumableStressEnergyConstructorFailClosed :
    FactorVecGate4ConsumableStressEnergyConstructorStatus

record FactorVecGate4ConsumableStressEnergyConstructorReceipt : Setω where
  field
    status :
      FactorVecGate4ConsumableStressEnergyConstructorStatus

    dashiMatterLagrangianCouplingReceipt :
      FactorVecDASHIMatterLagrangianCouplingReceipt

    valuationMatterInterfaceAttempt :
      FactorVecValuationMatterReceiptInterfaceFailClosedReceipt

    requestedConstructorShape :
      String

    localFactorVecBase :
      GL.FactorVec

    localFactorVecBaseIsZeroVec15 :
      localFactorVecBase
      ≡
      factorVecValuationMatterInterfaceZeroBase

    localStressEnergyConstructor :
      GL.FactorVec →
      FactorVecStressEnergyTensorComponentFamily

    localStressEnergyAtZeroBase :
      localStressEnergyConstructor localFactorVecBase
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    localStressEnergyFiniteSupport :
      FactorVecStressEnergyTensorFiniteSupportLaw
        (localStressEnergyConstructor localFactorVecBase)

    localStressEnergyLorentzGaugeInvariant :
      FactorVecStressEnergyIdentityLorentzGaugeInvarianceLaw
        (localStressEnergyConstructor localFactorVecBase)

    localStressEnergyEinsteinSourceCoupling :
      FactorVecEinsteinSourceCouplingLaw
        (localStressEnergyConstructor localFactorVecBase)

    localStressEnergyCovariantDivergence :
      FactorVecStressEnergyCovariantDivergenceLaw
        (localStressEnergyConstructor localFactorVecBase)

    remainingMatterInterfaceBlocker :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    remainingMatterInterfaceBlockerIsExact :
      remainingMatterInterfaceBlocker
      ≡
      missingValuationMatterReceiptInterface

    w4AuthorityFirstBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4AuthorityFirstBlockerIsCandidate256 :
      w4AuthorityFirstBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    constructsYMConnectionCarrier :
      Bool

    constructsYMConnectionCarrierIsFalse :
      constructsYMConnectionCarrier
      ≡
      false

    constructsSelectedFiniteRMetricInterface :
      Bool

    constructsSelectedFiniteRMetricInterfaceIsFalse :
      constructsSelectedFiniteRMetricInterface
      ≡
      false

    constructsAuthorityBackedStressEnergyTensorCarrier :
      Bool

    constructsAuthorityBackedStressEnergyTensorCarrierIsFalse :
      constructsAuthorityBackedStressEnergyTensorCarrier
      ≡
      false

    promotesSourcedEinstein :
      Bool

    promotesSourcedEinsteinIsFalse :
      promotesSourcedEinstein
      ≡
      false

    noEinsteinInterfaceReceiptHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    constructorBoundary :
      List String

canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt :
  FactorVecGate4ConsumableStressEnergyConstructorReceipt
canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt =
  record
    { status =
        factorVecGate4ConsumableStressEnergyConstructorFailClosed
    ; dashiMatterLagrangianCouplingReceipt =
        canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
    ; valuationMatterInterfaceAttempt =
        canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
    ; requestedConstructorShape =
        "FactorVec -> YMConnectionCarrier -> SelectedFiniteRMetric -> StressEnergyTensorCarrier"
    ; localFactorVecBase =
        factorVecValuationMatterInterfaceZeroBase
    ; localFactorVecBaseIsZeroVec15 =
        refl
    ; localStressEnergyConstructor =
        λ _ → factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    ; localStressEnergyAtZeroBase =
        refl
    ; localStressEnergyFiniteSupport =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyFiniteSupport
    ; localStressEnergyLorentzGaugeInvariant =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyIdentityLorentzGaugeInvariant
    ; localStressEnergyEinsteinSourceCoupling =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyEinsteinSourceCoupling
    ; localStressEnergyCovariantDivergence =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility
    ; remainingMatterInterfaceBlocker =
        FactorVecValuationMatterReceiptInterfaceFailClosedReceipt.matterReceiptInterfaceRemainingBlocker
          canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
    ; remainingMatterInterfaceBlockerIsExact =
        FactorVecValuationMatterReceiptInterfaceFailClosedReceipt.matterReceiptInterfaceRemainingBlockerIsExact
          canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
    ; w4AuthorityFirstBlocker =
        FactorVecValuationMatterReceiptInterfaceFailClosedReceipt.w4AuthorityFirstBlocker
          canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
    ; w4AuthorityFirstBlockerIsCandidate256 =
        FactorVecValuationMatterReceiptInterfaceFailClosedReceipt.w4AuthorityFirstBlockerIsCandidate256
          canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
    ; constructsYMConnectionCarrier =
        false
    ; constructsYMConnectionCarrierIsFalse =
        refl
    ; constructsSelectedFiniteRMetricInterface =
        false
    ; constructsSelectedFiniteRMetricInterfaceIsFalse =
        refl
    ; constructsAuthorityBackedStressEnergyTensorCarrier =
        false
    ; constructsAuthorityBackedStressEnergyTensorCarrierIsFalse =
        refl
    ; promotesSourcedEinstein =
        false
    ; promotesSourcedEinsteinIsFalse =
        refl
    ; noEinsteinInterfaceReceiptHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; constructorBoundary =
        "u3 current-wave constructor surface exposes a consumable local FactorVec -> stress-energy zero-table map"
        ∷ "The requested YMConnectionCarrier and SelectedFiniteRMetric arguments remain interface-shape names, not constructors consumed by this FactorVec surface"
        ∷ "The only inhabited tensor term is the supported unit p2-time zero-table component family with finite support, identity Lorentz/gauge invariance, source coupling, and covariant divergence"
        ∷ "The exact local blocker remains missingValuationMatterReceiptInterface; the W4 authority blocker remains missingCandidate256CalibrationReceiptForMatterInterface"
        ∷ "No W4MatterStressEnergyInterfaceReceipt, authority-backed StressEnergyTensorCarrier, or sourced Einstein equation is constructed"
        ∷ []
    }

factorVecGate4ConsumableStressEnergyConstructorRemainingBlocker :
  FactorVecGate4ConsumableStressEnergyConstructorReceipt.remainingMatterInterfaceBlocker
    canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt
  ≡
  missingValuationMatterReceiptInterface
factorVecGate4ConsumableStressEnergyConstructorRemainingBlocker =
  refl

factorVecGate4ConsumableStressEnergyConstructorNoPromotion :
  FactorVecGate4ConsumableStressEnergyConstructorReceipt.promotesSourcedEinstein
    canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt
  ≡
  false
factorVecGate4ConsumableStressEnergyConstructorNoPromotion =
  refl

------------------------------------------------------------------------
-- Lower6 u3 full stress-energy component receipt.
--
-- This records the current tranche's requested component surface using the
-- strongest local data available here: the supported p2-time zero-table
-- component family, its full 4 x 4 named entries, identity Lorentz/gauge
-- invariance, flat covariant-divergence witness, and the retained W4 halt.

data FactorVecLower6FullStressEnergyComponentStatus : Set where
  factorVecLower6FullStressEnergyComponentsRecordedFailClosed :
    FactorVecLower6FullStressEnergyComponentStatus

record FactorVecLower6FullStressEnergyComponentReceipt : Setω where
  field
    status :
      FactorVecLower6FullStressEnergyComponentStatus

    previousConsumableConstructor :
      FactorVecGate4ConsumableStressEnergyConstructorReceipt

    fullComponentFamily :
      FactorVecValuationP2LorentzUnitStressEnergyComponentFamily

    tensorCandidate :
      FactorVecStressEnergyTensorComponentFamily

    tensorCandidateIsSupportedZeroTable :
      tensorCandidate
      ≡
      factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily

    t00 :
      ℚ

    t00IsZero :
      t00
      ≡
      zeroℚ

    t01 :
      ℚ

    t01IsZero :
      t01
      ≡
      zeroℚ

    t02 :
      ℚ

    t02IsZero :
      t02
      ≡
      zeroℚ

    t03 :
      ℚ

    t03IsZero :
      t03
      ≡
      zeroℚ

    t11 :
      ℚ

    t11IsZero :
      t11
      ≡
      zeroℚ

    t12 :
      ℚ

    t12IsZero :
      t12
      ≡
      zeroℚ

    t13 :
      ℚ

    t13IsZero :
      t13
      ≡
      zeroℚ

    t22 :
      ℚ

    t22IsZero :
      t22
      ≡
      zeroℚ

    t23 :
      ℚ

    t23IsZero :
      t23
      ≡
      zeroℚ

    t33 :
      ℚ

    t33IsZero :
      t33
      ≡
      zeroℚ

    symmetryLaw :
      FactorVecStressEnergyTensorSymmetryLaw tensorCandidate

    finiteSupportLaw :
      FactorVecStressEnergyTensorFiniteSupportLaw tensorCandidate

    lorentzGaugeInvarianceLaw :
      FactorVecStressEnergyIdentityLorentzGaugeInvarianceLaw tensorCandidate

    covariantDivergenceLaw :
      FactorVecStressEnergyCovariantDivergenceLaw tensorCandidate

    contractedBianchiSourceCompatibilityReceipt :
      FactorVecGate4StressEnergyConservationSourceReceipt

    localProgressRemainingBlocker :
      FactorVecStressEnergyCompatibilityMissingPrimitive

    localProgressRemainingBlockerIsMatterReceiptInterface :
      localProgressRemainingBlocker
      ≡
      missingValuationMatterReceiptInterface

    w4AuthorityFirstBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4AuthorityFirstBlockerIsCandidate256 :
      w4AuthorityFirstBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    constructsAuthorityBackedStressEnergyTensorCarrier :
      Bool

    constructsAuthorityBackedStressEnergyTensorCarrierIsFalse :
      constructsAuthorityBackedStressEnergyTensorCarrier
      ≡
      false

    promotesSourcedEinstein :
      Bool

    promotesSourcedEinsteinIsFalse :
      promotesSourcedEinstein
      ≡
      false

    noEinsteinInterfaceReceiptHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    fullStressEnergyBoundary :
      List String

canonicalFactorVecLower6FullStressEnergyComponentReceipt :
  FactorVecLower6FullStressEnergyComponentReceipt
canonicalFactorVecLower6FullStressEnergyComponentReceipt =
  record
    { status =
        factorVecLower6FullStressEnergyComponentsRecordedFailClosed
    ; previousConsumableConstructor =
        canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt
    ; fullComponentFamily =
        canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; tensorCandidate =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
    ; tensorCandidateIsSupportedZeroTable =
        refl
    ; t00 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T00
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t00IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T00IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t01 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T01
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t01IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T01IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t02 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T02
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t02IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T02IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t03 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T03
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t03IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T03IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t11 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T11
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t11IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T11IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t12 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T12
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t12IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T12IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t13 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T13
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t13IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T13IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t22 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T22
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t22IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T22IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t23 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T23
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t23IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T23IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t33 =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T33
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; t33IsZero =
        FactorVecValuationP2LorentzUnitStressEnergyComponentFamily.T33IsZero
          canonicalFactorVecValuationP2LorentzUnitStressEnergyComponentFamily
    ; symmetryLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilySymmetry
    ; finiteSupportLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyFiniteSupport
    ; lorentzGaugeInvarianceLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyIdentityLorentzGaugeInvariant
    ; covariantDivergenceLaw =
        factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamilyCovariantDivergenceCompatibility
    ; contractedBianchiSourceCompatibilityReceipt =
        canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; localProgressRemainingBlocker =
        missingValuationMatterReceiptInterface
    ; localProgressRemainingBlockerIsMatterReceiptInterface =
        refl
    ; w4AuthorityFirstBlocker =
        W4Stress.missingCandidate256CalibrationReceiptForMatterInterface
    ; w4AuthorityFirstBlockerIsCandidate256 =
        refl
    ; constructsAuthorityBackedStressEnergyTensorCarrier =
        false
    ; constructsAuthorityBackedStressEnergyTensorCarrierIsFalse =
        refl
    ; promotesSourcedEinstein =
        false
    ; promotesSourcedEinsteinIsFalse =
        refl
    ; noEinsteinInterfaceReceiptHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; fullStressEnergyBoundary =
        "lower6 u3 records all ten independent p2-time Lorentz stress-energy components T00,T01,T02,T03,T11,T12,T13,T22,T23,T33"
        ∷ "The local component values are inherited from the existing full 4x4 supported zero-table family and are definitionally zero"
        ∷ "Identity Lorentz/gauge invariance, flat covariant divergence, and contracted-Bianchi source compatibility are threaded from existing local witnesses"
        ∷ "This is not a physical stress-energy promotion: missingValuationMatterReceiptInterface and W4 Candidate256 authority remain retained blockers"
        ∷ []
    }

factorVecLower6FullStressEnergyT33Zero :
  FactorVecLower6FullStressEnergyComponentReceipt.t33
    canonicalFactorVecLower6FullStressEnergyComponentReceipt
  ≡
  zeroℚ
factorVecLower6FullStressEnergyT33Zero =
  refl

factorVecLower6FullStressEnergyNoSourcedEinsteinPromotion :
  FactorVecLower6FullStressEnergyComponentReceipt.promotesSourcedEinstein
    canonicalFactorVecLower6FullStressEnergyComponentReceipt
  ≡
  false
factorVecLower6FullStressEnergyNoSourcedEinsteinPromotion =
  refl

factorVecLower6LocalYMGRStressEnergyZeroTableAgreement :
  (mu nu : FactorVecTangentDirection) →
  FactorVecLower6FullStressEnergyComponentReceipt.tensorCandidate
    canonicalFactorVecLower6FullStressEnergyComponentReceipt
    mu
    nu
  ≡
  factorVecUnitP2LorentzEinsteinTensorComponentFamily mu nu
factorVecLower6LocalYMGRStressEnergyZeroTableAgreement _ _ =
  refl

factorVecLower6NoAuthorityBackedStressEnergyUniquenessPromotion :
  FactorVecLower6FullStressEnergyComponentReceipt.constructsAuthorityBackedStressEnergyTensorCarrier
    canonicalFactorVecLower6FullStressEnergyComponentReceipt
  ≡
  false
factorVecLower6NoAuthorityBackedStressEnergyUniquenessPromotion =
  refl

------------------------------------------------------------------------
-- Gate 4 sourced Einstein equation target, zero-table only.
--
-- The rational kappa records the requested 8*pi approximation using
-- pi ~= 355/113, hence kappa ~= 2840/113.  The only inhabited law here is
-- the bounded zero-table target; W4 authority-backed stress-energy remains
-- blocked by the matter receipt interface surfaces above.

factorVecGate4PiApprox355Over113 :
  ℚ
factorVecGate4PiApprox355Over113 =
  (+ 355) R./ 113

factorVecGate4KappaEightPiApprox :
  ℚ
factorVecGate4KappaEightPiApprox =
  (+ 2840) R./ 113

factorVecGate4KappaEightPiApproxIs2840Over113 :
  factorVecGate4KappaEightPiApprox
  ≡
  (+ 2840) R./ 113
factorVecGate4KappaEightPiApproxIs2840Over113 =
  refl

factorVecGate4TwoTimesEinsteinTensorComponentFamily :
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecGate4TwoTimesEinsteinTensorComponentFamily _ _ =
  zeroℚ

factorVecGate4KappaScaledStressEnergyComponentFamily :
  FactorVecStressEnergyTensorComponentFamily →
  FactorVecTangentDirection →
  FactorVecTangentDirection →
  ℚ
factorVecGate4KappaScaledStressEnergyComponentFamily tensor mu nu =
  factorVecGate4KappaEightPiApprox *ℚ tensor mu nu

FactorVecGate4SourcedEinsteinEquationTargetLaw :
  FactorVecStressEnergyTensorComponentFamily →
  Set
FactorVecGate4SourcedEinsteinEquationTargetLaw tensor =
  (mu nu : FactorVecTangentDirection) →
  factorVecGate4TwoTimesEinsteinTensorComponentFamily mu nu
  ≡
  factorVecGate4KappaScaledStressEnergyComponentFamily tensor mu nu

factorVecGate4SourcedEinsteinZeroTableEquationTarget :
  FactorVecGate4SourcedEinsteinEquationTargetLaw
    factorVecUnitP2LorentzStressEnergyTensorZeroComponentFamily
factorVecGate4SourcedEinsteinZeroTableEquationTarget _ _ =
  sym (Rₚ.*-zeroʳ factorVecGate4KappaEightPiApprox)
