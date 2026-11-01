module DASHI.Physics.YangMills.BalabanSmallFieldNonlinearConstants where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Quantitative small-field producer for the seven B5 constants.
--
-- The dependence on the common chart radius is explicit.  The analytic work is
-- reduced to base coefficient estimates for the actual Wilson/BCH operators.
------------------------------------------------------------------------

record SmallFieldNonlinearCoefficientData (Bound : Set) : Set₁ where
  field
    radius : Bound
    add multiply square : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    bchCoefficient commutatorCoefficient transportCoefficient
      backgroundDerivativeCoefficient gaugeCoefficient constraintCoefficient
      chartCoefficient : Bound

    bchUpper commutatorUpper transportUpper backgroundDerivativeUpper
      gaugeUpper constraintUpper chartUpper : Bound

    bchRadiusBound :
      LessEqual (multiply bchCoefficient (square radius radius)) bchUpper
    commutatorRadiusBound :
      LessEqual (multiply commutatorCoefficient radius) commutatorUpper
    transportRadiusBound :
      LessEqual (multiply transportCoefficient radius) transportUpper
    backgroundDerivativeRadiusBound :
      LessEqual (multiply backgroundDerivativeCoefficient radius)
        backgroundDerivativeUpper
    gaugeRadiusBound :
      LessEqual (multiply gaugeCoefficient radius) gaugeUpper
    constraintRadiusBound :
      LessEqual (multiply constraintCoefficient radius) constraintUpper
    chartRadiusBound :
      LessEqual (multiply chartCoefficient radius) chartUpper

open SmallFieldNonlinearCoefficientData public

nonlinearUpper :
  ∀ {Bound : Set} → SmallFieldNonlinearCoefficientData Bound → Bound
nonlinearUpper dataSet =
  add dataSet (bchUpper dataSet)
    (add dataSet (commutatorUpper dataSet)
      (add dataSet (transportUpper dataSet)
        (add dataSet (backgroundDerivativeUpper dataSet)
          (add dataSet (gaugeUpper dataSet)
            (add dataSet (constraintUpper dataSet) (chartUpper dataSet))))))

record SevenComponentBoundsProduced {Bound : Set}
    (dataSet : SmallFieldNonlinearCoefficientData Bound) : Set₁ where
  field
    bchBound :
      LessEqual dataSet
        (multiply dataSet (bchCoefficient dataSet)
          (square dataSet (radius dataSet) (radius dataSet)))
        (bchUpper dataSet)
    commutatorBound :
      LessEqual dataSet
        (multiply dataSet (commutatorCoefficient dataSet) (radius dataSet))
        (commutatorUpper dataSet)
    transportBound :
      LessEqual dataSet
        (multiply dataSet (transportCoefficient dataSet) (radius dataSet))
        (transportUpper dataSet)
    backgroundDerivativeBound :
      LessEqual dataSet
        (multiply dataSet (backgroundDerivativeCoefficient dataSet)
          (radius dataSet))
        (backgroundDerivativeUpper dataSet)
    gaugeBound :
      LessEqual dataSet
        (multiply dataSet (gaugeCoefficient dataSet) (radius dataSet))
        (gaugeUpper dataSet)
    constraintBound :
      LessEqual dataSet
        (multiply dataSet (constraintCoefficient dataSet) (radius dataSet))
        (constraintUpper dataSet)
    chartBound :
      LessEqual dataSet
        (multiply dataSet (chartCoefficient dataSet) (radius dataSet))
        (chartUpper dataSet)

produceSevenComponentBounds :
  ∀ {Bound : Set} →
  (dataSet : SmallFieldNonlinearCoefficientData Bound) →
  SevenComponentBoundsProduced dataSet
produceSevenComponentBounds dataSet = record
  { bchBound = bchRadiusBound dataSet
  ; commutatorBound = commutatorRadiusBound dataSet
  ; transportBound = transportRadiusBound dataSet
  ; backgroundDerivativeBound = backgroundDerivativeRadiusBound dataSet
  ; gaugeBound = gaugeRadiusBound dataSet
  ; constraintBound = constraintRadiusBound dataSet
  ; chartBound = chartRadiusBound dataSet
  }

smallFieldNonlinearConstantsAssemblyLevel : ProofLevel
smallFieldNonlinearConstantsAssemblyLevel = machineChecked

smallFieldCoefficientInputsLevel : ProofLevel
smallFieldCoefficientInputsLevel = conditional
