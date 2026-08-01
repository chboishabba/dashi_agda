module DASHI.Physics.YangMills.BalabanClayGate4IdentityDefectOperatorNormExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- From ||T-I|| to ||T||.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- The outer dexp and logarithm dexp^-1 stages need bounds for the full
-- operators, while the SU(2) chart analysis naturally gives bounds for their
-- defects from the identity.  The triangle inequality yields
--
--   ||T|| <= 1 + ||T-I|| <= 1 + delta.
------------------------------------------------------------------------

record IdentityDefectNormAlgebra
    (Operator Bound : Set) : Set₁ where
  field
    identityOperator : Operator
    addOperator : Operator → Operator → Operator
    operatorNorm : Operator → Bound

    one : Bound
    addBound : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (addBound left right) (addBound lower upper)

    identityNorm : operatorNorm identityOperator ≡ one

    normTriangle : ∀ left right →
      LessEqual
        (operatorNorm (addOperator left right))
        (addBound (operatorNorm left) (operatorNorm right))

open IdentityDefectNormAlgebra public

record OperatorFromIdentityDefect
    (Operator Bound : Set) : Set₁ where
  field
    algebra : IdentityDefectNormAlgebra Operator Bound

    operator defect : Operator
    defectBound : Bound

    operatorMeaning :
      operator ≡ addOperator algebra (identityOperator algebra) defect

    defectEstimate :
      LessEqual algebra (operatorNorm algebra defect) defectBound

open OperatorFromIdentityDefect public

operatorNormBelowOnePlusDefect :
  ∀ {Operator Bound}
    (dataSet : OperatorFromIdentityDefect Operator Bound) →
  LessEqual (algebra dataSet)
    (operatorNorm (algebra dataSet) (operator dataSet))
    (addBound (algebra dataSet)
      (one (algebra dataSet)) (defectBound dataSet))
operatorNormBelowOnePlusDefect dataSet =
  subst
    (λ selected →
      LessEqual (algebra dataSet)
        (operatorNorm (algebra dataSet) selected)
        (addBound (algebra dataSet)
          (one (algebra dataSet)) (defectBound dataSet)))
    (sym (operatorMeaning dataSet))
    (transitive (algebra dataSet)
      (normTriangle (algebra dataSet)
        (identityOperator (algebra dataSet)) (defect dataSet))
      (addMonotone (algebra dataSet)
        (subst
          (λ lower → LessEqual (algebra dataSet) lower
            (one (algebra dataSet)))
          (sym (identityNorm (algebra dataSet)))
          (reflexive (algebra dataSet) (one (algebra dataSet))))
        (defectEstimate dataSet)))

identityDefectToFullOperatorNormLevel : ProofLevel
identityDefectToFullOperatorNormLevel = machineChecked

physicalIdentityOperatorNormConventionInputsLevel : ProofLevel
physicalIdentityOperatorNormConventionInputsLevel = conditional
