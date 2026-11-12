module DASHI.Physics.YangMills.BalabanLiteralSevenGeneratorScalarAtomCertificatesExact where

-- The seven actual B4 generators fix every source-native scalar ATOM:
-- hatMomentumSquared for each momentum role, colorCasimir, gaugeParameter.
-- They do not automatically fix any axis-labelled sine or cosine atom,
-- nor the unspecified full Wilson/ghost/Haar regularIntegrand tree.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopHyperoctahedralGeneratorCertificateExact as Cert
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact as Joint

scalarHatAllSeven :
  ∀ role →
  Cert.SevenGeneratorInvariantExpression
    (Eval.atom (Eval.hatMomentumSquared role))
scalarHatAllSeven role = record
  { Cert.flip0Exact = refl
  ; Cert.flip1Exact = refl
  ; Cert.flip2Exact = refl
  ; Cert.flip3Exact = refl
  ; Cert.swap01Exact = refl
  ; Cert.swap12Exact = refl
  ; Cert.swap23Exact = refl
  }

colorCasimirAllSeven :
  Cert.SevenGeneratorInvariantExpression (Eval.atom Eval.colorCasimir)
colorCasimirAllSeven = record
  { Cert.flip0Exact = refl
  ; Cert.flip1Exact = refl
  ; Cert.flip2Exact = refl
  ; Cert.flip3Exact = refl
  ; Cert.swap01Exact = refl
  ; Cert.swap12Exact = refl
  ; Cert.swap23Exact = refl
  }

gaugeParameterAllSeven :
  Cert.SevenGeneratorInvariantExpression (Eval.atom Eval.gaugeParameter)
gaugeParameterAllSeven = record
  { Cert.flip0Exact = refl
  ; Cert.flip1Exact = refl
  ; Cert.flip2Exact = refl
  ; Cert.flip3Exact = refl
  ; Cert.swap01Exact = refl
  ; Cert.swap12Exact = refl
  ; Cert.swap23Exact = refl
  }

-- Actual original syntax action is homomorphic for multiplication.
-- This allows assembling exactly the scalar fragments proved invariant,
-- without assuming the whole physical source is a scalar fragment.
sevenMultiply :
  ∀ {a b} →
  Cert.SevenGeneratorInvariantExpression a →
  Cert.SevenGeneratorInvariantExpression b →
  Cert.SevenGeneratorInvariantExpression (Eval.multiply a b)
sevenMultiply left right = record
  { Cert.flip0Exact = cong₂ Eval.multiply
      (Cert.flip0Exact left) (Cert.flip0Exact right)
  ; Cert.flip1Exact = cong₂ Eval.multiply
      (Cert.flip1Exact left) (Cert.flip1Exact right)
  ; Cert.flip2Exact = cong₂ Eval.multiply
      (Cert.flip2Exact left) (Cert.flip2Exact right)
  ; Cert.flip3Exact = cong₂ Eval.multiply
      (Cert.flip3Exact left) (Cert.flip3Exact right)
  ; Cert.swap01Exact = cong₂ Eval.multiply
      (Cert.swap01Exact left) (Cert.swap01Exact right)
  ; Cert.swap12Exact = cong₂ Eval.multiply
      (Cert.swap12Exact left) (Cert.swap12Exact right)
  ; Cert.swap23Exact = cong₂ Eval.multiply
      (Cert.swap23Exact left) (Cert.swap23Exact right)
  }

sevenAdd :
  ∀ {a b} →
  Cert.SevenGeneratorInvariantExpression a →
  Cert.SevenGeneratorInvariantExpression b →
  Cert.SevenGeneratorInvariantExpression (Eval.add a b)
sevenAdd left right = record
  { Cert.flip0Exact = cong₂ Eval.add
      (Cert.flip0Exact left) (Cert.flip0Exact right)
  ; Cert.flip1Exact = cong₂ Eval.add
      (Cert.flip1Exact left) (Cert.flip1Exact right)
  ; Cert.flip2Exact = cong₂ Eval.add
      (Cert.flip2Exact left) (Cert.flip2Exact right)
  ; Cert.flip3Exact = cong₂ Eval.add
      (Cert.flip3Exact left) (Cert.flip3Exact right)
  ; Cert.swap01Exact = cong₂ Eval.add
      (Cert.swap01Exact left) (Cert.swap01Exact right)
  ; Cert.swap12Exact = cong₂ Eval.add
      (Cert.swap12Exact left) (Cert.swap12Exact right)
  ; Cert.swap23Exact = cong₂ Eval.add
      (Cert.swap23Exact left) (Cert.swap23Exact right)
  }
