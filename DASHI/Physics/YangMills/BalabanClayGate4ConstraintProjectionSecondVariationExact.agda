module DASHI.Physics.YangMills.BalabanClayGate4ConstraintProjectionSecondVariationExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact mixed second variation of Q* (Q Q*)^{-1} Q.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- For R=A^{-1},
--
--   D R[h] = -R D A[h] R,
--
--   D²R[h,k]
--     = R DA[h] R DA[k] R
--       + R DA[k] R DA[h] R
--       - R D²A[h,k] R.
--
-- The mixed derivative of Q* R Q is the nine-term noncommutative Leibniz
-- expansion. These formulas fix exact channel ownership before norm estimates.
------------------------------------------------------------------------

record NoncommutativeOperatorAlgebra (Operator : Set) : Set₁ where
  field
    zero one : Operator
    add compose : Operator → Operator → Operator
    negate : Operator → Operator

open NoncommutativeOperatorAlgebra public

record MixedSecondJet (Operator : Set) : Set where
  constructor mixedSecondJet
  field
    value firstVariation secondVariation mixedVariation : Operator

open MixedSecondJet public

inverseFirstFormula :
  ∀ {Operator} → NoncommutativeOperatorAlgebra Operator →
  Operator → Operator → Operator
inverseFirstFormula algebra inverseValue derivative =
  negate algebra
    (compose algebra inverseValue
      (compose algebra derivative inverseValue))

inverseMixedFormula :
  ∀ {Operator} → NoncommutativeOperatorAlgebra Operator →
  Operator → Operator → Operator → Operator → Operator
inverseMixedFormula algebra inverseValue firstDerivative secondDerivative
    mixedDerivative =
  add algebra
    (compose algebra inverseValue
      (compose algebra firstDerivative
        (compose algebra inverseValue
          (compose algebra secondDerivative inverseValue))))
    (add algebra
      (compose algebra inverseValue
        (compose algebra secondDerivative
          (compose algebra inverseValue
            (compose algebra firstDerivative inverseValue))))
      (negate algebra
        (compose algebra inverseValue
          (compose algebra mixedDerivative inverseValue))))

inverseJet :
  ∀ {Operator} → NoncommutativeOperatorAlgebra Operator →
  Operator → MixedSecondJet Operator → MixedSecondJet Operator
inverseJet algebra inverseValue input = mixedSecondJet
  inverseValue
  (inverseFirstFormula algebra inverseValue (firstVariation input))
  (inverseFirstFormula algebra inverseValue (secondVariation input))
  (inverseMixedFormula algebra inverseValue
    (firstVariation input) (secondVariation input) (mixedVariation input))

inverseJetFirstExact :
  ∀ {Operator}
    (algebra : NoncommutativeOperatorAlgebra Operator)
    inverseValue input →
  firstVariation (inverseJet algebra inverseValue input)
  ≡ inverseFirstFormula algebra inverseValue (firstVariation input)
inverseJetFirstExact algebra inverseValue input = refl

inverseJetMixedExact :
  ∀ {Operator}
    (algebra : NoncommutativeOperatorAlgebra Operator)
    inverseValue input →
  mixedVariation (inverseJet algebra inverseValue input)
  ≡ inverseMixedFormula algebra inverseValue
      (firstVariation input) (secondVariation input) (mixedVariation input)
inverseJetMixedExact algebra inverseValue input = refl

tripleMixedFormula :
  ∀ {Operator} → NoncommutativeOperatorAlgebra Operator →
  MixedSecondJet Operator → MixedSecondJet Operator →
  MixedSecondJet Operator → Operator
tripleMixedFormula algebra left middle right =
  add algebra
    (compose algebra (mixedVariation left)
      (compose algebra (value middle) (value right)))
    (add algebra
      (compose algebra (firstVariation left)
        (compose algebra (secondVariation middle) (value right)))
      (add algebra
        (compose algebra (firstVariation left)
          (compose algebra (value middle) (secondVariation right)))
        (add algebra
          (compose algebra (secondVariation left)
            (compose algebra (firstVariation middle) (value right)))
          (add algebra
            (compose algebra (value left)
              (compose algebra (mixedVariation middle) (value right)))
            (add algebra
              (compose algebra (value left)
                (compose algebra (firstVariation middle)
                  (secondVariation right)))
              (add algebra
                (compose algebra (secondVariation left)
                  (compose algebra (value middle) (firstVariation right)))
                (add algebra
                  (compose algebra (value left)
                    (compose algebra (secondVariation middle)
                      (firstVariation right)))
                  (compose algebra (value left)
                    (compose algebra (value middle)
                      (mixedVariation right))))))))))

record ConstraintProjectionSecondVariationData (Operator : Set) : Set₁ where
  field
    algebra : NoncommutativeOperatorAlgebra Operator

    qStar q normal : MixedSecondJet Operator
    inverseNormalValue : Operator

    normalInverse : MixedSecondJet Operator
    normalInverseMeaning :
      normalInverse ≡ inverseJet algebra inverseNormalValue normal

    projectionValue projectionMixed : Operator

    projectionValueMeaning :
      projectionValue
      ≡ compose algebra (value qStar)
          (compose algebra inverseNormalValue (value q))

    projectionMixedMeaning :
      projectionMixed
      ≡ tripleMixedFormula algebra qStar normalInverse q

open ConstraintProjectionSecondVariationData public

constraintProjectionMixedNineTermFormula :
  ∀ {Operator}
    (dataSet : ConstraintProjectionSecondVariationData Operator) →
  projectionMixed dataSet
  ≡ tripleMixedFormula (algebra dataSet)
      (qStar dataSet) (normalInverse dataSet) (q dataSet)
constraintProjectionMixedNineTermFormula = projectionMixedMeaning

constraintInverseMixedFormula :
  ∀ {Operator}
    (dataSet : ConstraintProjectionSecondVariationData Operator) →
  mixedVariation (normalInverse dataSet)
  ≡ inverseMixedFormula (algebra dataSet)
      (inverseNormalValue dataSet)
      (firstVariation (normal dataSet))
      (secondVariation (normal dataSet))
      (mixedVariation (normal dataSet))
constraintInverseMixedFormula dataSet
  rewrite normalInverseMeaning dataSet = refl

constraintInverseDerivativeFormulaLevel : ProofLevel
constraintInverseDerivativeFormulaLevel = machineChecked

constraintProjectionNineTermSecondVariationLevel : ProofLevel
constraintProjectionNineTermSecondVariationLevel = machineChecked

physicalAveragingJetIdentificationInputsLevel : ProofLevel
physicalAveragingJetIdentificationInputsLevel = conditional

physicalConstraintNormalInverseInputsLevel : ProofLevel
physicalConstraintNormalInverseInputsLevel = conditional
