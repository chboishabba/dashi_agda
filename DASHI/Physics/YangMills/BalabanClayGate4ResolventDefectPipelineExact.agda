module DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectPipelineExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Resolvent defect from one exact identity and three norm factors.
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
-- For A invertible and A+E invertible, the second resolvent identity gives
--
--   (A+E)^-1 - A^-1 = -(A+E)^-1 E A^-1.
--
-- The module derives the corresponding operator-norm estimate from
-- submultiplicativity.  Gauge and constraint channels can therefore share one
-- resolvent defect whose physical inputs are only the two inverse bounds, the
-- perturbation bound and the exact operator identification.
------------------------------------------------------------------------

record ResolventNormAlgebra
    (Operator Bound : Set) : Set₁ where
  field
    compose : Operator → Operator → Operator
    negate : Operator → Operator
    subtract : Operator → Operator → Operator
    operatorNorm : Operator → Bound

    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (multiply left right) (multiply lower upper)

    normNegate : ∀ operator →
      operatorNorm (negate operator) ≡ operatorNorm operator

    normSubmultiplicative : ∀ outer inner →
      LessEqual
        (operatorNorm (compose outer inner))
        (multiply (operatorNorm outer) (operatorNorm inner))

open ResolventNormAlgebra public

record ResolventIdentityData
    (Operator Bound : Set) : Set₁ where
  field
    algebra : ResolventNormAlgebra Operator Bound

    referenceInverse perturbedInverse perturbation difference : Operator

    differenceMeaning :
      difference ≡ subtract algebra perturbedInverse referenceInverse

    secondResolventIdentity :
      difference
      ≡ negate algebra
          (compose algebra perturbedInverse
            (compose algebra perturbation referenceInverse))

    perturbedInverseBound perturbationBound referenceInverseBound
      differenceBudget : Bound

    perturbedInverseEstimate :
      LessEqual algebra
        (operatorNorm algebra perturbedInverse)
        perturbedInverseBound

    perturbationEstimate :
      LessEqual algebra
        (operatorNorm algebra perturbation)
        perturbationBound

    referenceInverseEstimate :
      LessEqual algebra
        (operatorNorm algebra referenceInverse)
        referenceInverseBound

    differenceBudgetMeaning :
      differenceBudget
      ≡ multiply algebra perturbedInverseBound
          (multiply algebra perturbationBound referenceInverseBound)

open ResolventIdentityData public

threeFactorNormBound :
  ∀ {Operator Bound}
    (algebra : ResolventNormAlgebra Operator Bound)
    outer middle inner outerBound middleBound innerBound →
  LessEqual algebra (operatorNorm algebra outer) outerBound →
  LessEqual algebra (operatorNorm algebra middle) middleBound →
  LessEqual algebra (operatorNorm algebra inner) innerBound →
  LessEqual algebra
    (operatorNorm algebra
      (compose algebra outer (compose algebra middle inner)))
    (multiply algebra outerBound
      (multiply algebra middleBound innerBound))
threeFactorNormBound algebra outer middle inner
    outerBound middleBound innerBound
    outerEstimate middleEstimate innerEstimate =
  transitive algebra
    (normSubmultiplicative algebra outer
      (compose algebra middle inner))
    (multiplyMonotone algebra
      outerEstimate
      (transitive algebra
        (normSubmultiplicative algebra middle inner)
        (multiplyMonotone algebra middleEstimate innerEstimate)))

resolventDifferenceNormBelowBudget :
  ∀ {Operator Bound}
    (dataSet : ResolventIdentityData Operator Bound) →
  LessEqual (algebra dataSet)
    (operatorNorm (algebra dataSet) (difference dataSet))
    (differenceBudget dataSet)
resolventDifferenceNormBelowBudget dataSet =
  subst
    (λ upper →
      LessEqual (algebra dataSet)
        (operatorNorm (algebra dataSet) (difference dataSet)) upper)
    (sym (differenceBudgetMeaning dataSet))
    (subst
      (λ selectedDifference →
        LessEqual (algebra dataSet)
          (operatorNorm (algebra dataSet) selectedDifference)
          (multiply (algebra dataSet)
            (perturbedInverseBound dataSet)
            (multiply (algebra dataSet)
              (perturbationBound dataSet)
              (referenceInverseBound dataSet))))
      (sym (secondResolventIdentity dataSet))
      (subst
        (λ lower →
          LessEqual (algebra dataSet) lower
            (multiply (algebra dataSet)
              (perturbedInverseBound dataSet)
              (multiply (algebra dataSet)
                (perturbationBound dataSet)
                (referenceInverseBound dataSet))))
        (sym
          (normNegate (algebra dataSet)
            (compose (algebra dataSet)
              (perturbedInverse dataSet)
              (compose (algebra dataSet)
                (perturbation dataSet)
                (referenceInverse dataSet)))))
        (threeFactorNormBound (algebra dataSet)
          (perturbedInverse dataSet)
          (perturbation dataSet)
          (referenceInverse dataSet)
          (perturbedInverseBound dataSet)
          (perturbationBound dataSet)
          (referenceInverseBound dataSet)
          (perturbedInverseEstimate dataSet)
          (perturbationEstimate dataSet)
          (referenceInverseEstimate dataSet))))

record RelativeResolventBudget (Bound : Set) : Set₁ where
  field
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    relativeFactor referenceInverseBound perturbedInverseBound
      perturbationBound resolventBudget : Bound

    relativeFactorMeaning :
      relativeFactor ≡ multiply referenceInverseBound perturbationBound

    perturbedInverseBoundMeaning : Set

    resolventBudgetMeaning :
      resolventBudget
      ≡ multiply perturbedInverseBound
          (multiply perturbationBound referenceInverseBound)

    relativeFactorStrictlyBelowOne : Set

open RelativeResolventBudget public

resolventSecondIdentityLevel : ProofLevel
resolventSecondIdentityLevel = standardImported

resolventThreeFactorNormLevel : ProofLevel
resolventThreeFactorNormLevel = machineChecked

resolventDifferenceBudgetAssemblyLevel : ProofLevel
resolventDifferenceBudgetAssemblyLevel = machineChecked

physicalPerturbedInverseNormInputsLevel : ProofLevel
physicalPerturbedInverseNormInputsLevel = conditional

physicalResolventOperatorIdentificationInputsLevel : ProofLevel
physicalResolventOperatorIdentificationInputsLevel = conditional
