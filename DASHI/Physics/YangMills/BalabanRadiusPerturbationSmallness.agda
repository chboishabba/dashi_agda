module DASHI.Physics.YangMills.BalabanRadiusPerturbationSmallness where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The five background Hessian perturbations are each controlled by the common
-- small-field radius. Their sum is compared directly with the coercivity margin.
------------------------------------------------------------------------

record RadiusPerturbationData (Bound : Set) : Set₁ where
  field
    radius curvatureCoefficient transportCoefficient chartCoefficient
      gaugeCoefficient constraintCoefficient : Bound
    curvatureUpper transportUpper chartUpper gaugeUpper constraintUpper
      perturbationUpper c0 cH : Bound

    add multiply : Bound → Bound → Bound
    LessEqual StrictlyBelow : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (add left right) (add left′ right′)

    curvatureRadiusBound :
      LessEqual (multiply curvatureCoefficient radius) curvatureUpper
    transportRadiusBound :
      LessEqual (multiply transportCoefficient radius) transportUpper
    chartRadiusBound : LessEqual (multiply chartCoefficient radius) chartUpper
    gaugeRadiusBound : LessEqual (multiply gaugeCoefficient radius) gaugeUpper
    constraintRadiusBound :
      LessEqual (multiply constraintCoefficient radius) constraintUpper

    perturbationUpperDefinition :
      perturbationUpper ≡
      add curvatureUpper
        (add transportUpper (add chartUpper (add gaugeUpper constraintUpper)))

    coefficientSumRadiusBelowMargin :
      LessEqual
        (add (multiply curvatureCoefficient radius)
          (add (multiply transportCoefficient radius)
            (add (multiply chartCoefficient radius)
              (add (multiply gaugeCoefficient radius)
                (multiply constraintCoefficient radius)))))
        (add cH perturbationUpper)

    coercivityBudget : LessEqual (add cH perturbationUpper) c0
    strictPerturbation : StrictlyBelow perturbationUpper c0

open RadiusPerturbationData public

componentRadiusSumBound :
  ∀ {Bound : Set} →
  (dataSet : RadiusPerturbationData Bound) →
  LessEqual dataSet
    (add dataSet (multiply dataSet (curvatureCoefficient dataSet) (radius dataSet))
      (add dataSet (multiply dataSet (transportCoefficient dataSet) (radius dataSet))
        (add dataSet (multiply dataSet (chartCoefficient dataSet) (radius dataSet))
          (add dataSet (multiply dataSet (gaugeCoefficient dataSet) (radius dataSet))
            (multiply dataSet (constraintCoefficient dataSet) (radius dataSet))))))
    (perturbationUpper dataSet)
componentRadiusSumBound dataSet rewrite perturbationUpperDefinition dataSet =
  addMonotone dataSet
    (curvatureRadiusBound dataSet)
    (addMonotone dataSet
      (transportRadiusBound dataSet)
      (addMonotone dataSet
        (chartRadiusBound dataSet)
        (addMonotone dataSet
          (gaugeRadiusBound dataSet)
          (constraintRadiusBound dataSet))))

fullCoercivityBudget :
  ∀ {Bound : Set} →
  (dataSet : RadiusPerturbationData Bound) →
  LessEqual dataSet (add dataSet (cH dataSet) (perturbationUpper dataSet)) (c0 dataSet)
fullCoercivityBudget dataSet = coercivityBudget dataSet

radiusPerturbationAssemblyLevel : ProofLevel
radiusPerturbationAssemblyLevel = machineChecked

radiusPerturbationCoefficientInputsLevel : ProofLevel
radiusPerturbationCoefficientInputsLevel = conditional
