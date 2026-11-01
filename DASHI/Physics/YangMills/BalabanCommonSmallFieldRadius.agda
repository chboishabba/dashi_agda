module DASHI.Physics.YangMills.BalabanCommonSmallFieldRadius where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One radius must simultaneously satisfy chart, coercivity, Neumann,
-- nonlinear-contraction and displacement-at-zero budgets.
------------------------------------------------------------------------

record CommonSmallFieldRadiusData (Bound : Set) : Set₁ where
  field
    radius chartRadius coercivityRadius neumannRadius nonlinearRadius
      displacementRadius : Bound
    LessEqual : Bound → Bound → Set

    radiusWithinChart : LessEqual radius chartRadius
    radiusWithinCoercivity : LessEqual radius coercivityRadius
    radiusWithinNeumann : LessEqual radius neumannRadius
    radiusWithinNonlinear : LessEqual radius nonlinearRadius
    radiusWithinDisplacement : LessEqual radius displacementRadius

    ChartValid CoercivityValid NeumannValid NonlinearValid DisplacementValid : Set
    chartValid : ChartValid
    coercivityValid : CoercivityValid
    neumannValid : NeumannValid
    nonlinearValid : NonlinearValid
    displacementValid : DisplacementValid

open CommonSmallFieldRadiusData public

record CommonSmallFieldRadiusCertificate {Bound : Set}
    (dataSet : CommonSmallFieldRadiusData Bound) : Set₁ where
  field
    chartBudget : LessEqual dataSet (radius dataSet) (chartRadius dataSet)
    coercivityBudget : LessEqual dataSet (radius dataSet) (coercivityRadius dataSet)
    neumannBudget : LessEqual dataSet (radius dataSet) (neumannRadius dataSet)
    nonlinearBudget : LessEqual dataSet (radius dataSet) (nonlinearRadius dataSet)
    displacementBudget : LessEqual dataSet (radius dataSet) (displacementRadius dataSet)
    chartValidity : ChartValid dataSet
    coercivityValidity : CoercivityValid dataSet
    neumannValidity : NeumannValid dataSet
    nonlinearValidity : NonlinearValid dataSet
    displacementValidity : DisplacementValid dataSet

assembleCommonSmallFieldRadius :
  ∀ {Bound : Set} →
  (dataSet : CommonSmallFieldRadiusData Bound) →
  CommonSmallFieldRadiusCertificate dataSet
assembleCommonSmallFieldRadius dataSet = record
  { chartBudget = radiusWithinChart dataSet
  ; coercivityBudget = radiusWithinCoercivity dataSet
  ; neumannBudget = radiusWithinNeumann dataSet
  ; nonlinearBudget = radiusWithinNonlinear dataSet
  ; displacementBudget = radiusWithinDisplacement dataSet
  ; chartValidity = chartValid dataSet
  ; coercivityValidity = coercivityValid dataSet
  ; neumannValidity = neumannValid dataSet
  ; nonlinearValidity = nonlinearValid dataSet
  ; displacementValidity = displacementValid dataSet
  }

commonSmallFieldRadiusAssemblyLevel : ProofLevel
commonSmallFieldRadiusAssemblyLevel = machineChecked

commonSmallFieldRadiusExistenceLevel : ProofLevel
commonSmallFieldRadiusExistenceLevel = conditional
