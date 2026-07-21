module DASHI.Physics.YangMills.BalabanConcreteHodgeHessianCoercivity where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPatchRegimeHodgeUniformity using
  (PatchRegime; bulk; boundary; scaleInterface; corner; nestedRestriction)

------------------------------------------------------------------------
-- Concrete completion layer for uniform reference Hodge coercivity and the
-- small-background Hessian perturbation argument.
--
-- Unlike the earlier bridge, GaugeFixedTangent below is one structured
-- constrained lattice tangent space.  The four zero-mode-removal statements
-- are projections from that structure, rather than unrelated predicates.
------------------------------------------------------------------------

record ConcreteHodgeHessianData
    (Index State Bound Radius : Set) : Set₁ where
  field
    regime : Index → PatchRegime

    referenceEnergy : Index → State → Bound
    referenceHessian hessian : Index → State → State
    inner : State → State → Bound
    normSq : Index → State → Bound
    scale add : Bound → Bound → Bound

    LessEqual StrictLess : Bound → Bound → Set
    Positive : Bound → Set
    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (add left right) (add left′ right′)
    addRightCancel : ∀ {left right common} →
      LessEqual (add left common) (add right common) → LessEqual left right

    GaugeOrthogonal : Index → State → Set
    BlockAverageZero : Index → State → Set
    ResidualGaugeOrthogonal : Index → State → Set
    BoundaryCompatibility : Index → State → Set

  record GaugeFixedTangent (index : Index) (state : State) : Set where
    field
      gaugeOrthogonal : GaugeOrthogonal index state
      blockAverageZero : BlockAverageZero index state
      residualGaugeOrthogonal : ResidualGaugeOrthogonal index state
      boundaryCompatible : BoundaryCompatibility index state

  field
    cBulk cBoundary cInterface cCorner cNested cCommon cH c0 : Bound
    cBulkPositive : Positive cBulk
    cBoundaryPositive : Positive cBoundary
    cInterfacePositive : Positive cInterface
    cCornerPositive : Positive cCorner
    cNestedPositive : Positive cNested
    cCommonPositive : Positive cCommon
    cHPositive : Positive cH

    commonBelowBulkScaled : ∀ index state →
      LessEqual (scale cCommon (normSq index state))
        (scale cBulk (normSq index state))
    commonBelowBoundaryScaled : ∀ index state →
      LessEqual (scale cCommon (normSq index state))
        (scale cBoundary (normSq index state))
    commonBelowInterfaceScaled : ∀ index state →
      LessEqual (scale cCommon (normSq index state))
        (scale cInterface (normSq index state))
    commonBelowCornerScaled : ∀ index state →
      LessEqual (scale cCommon (normSq index state))
        (scale cCorner (normSq index state))
    commonBelowNestedScaled : ∀ index state →
      LessEqual (scale cCommon (normSq index state))
        (scale cNested (normSq index state))

    commonBelowBulk : LessEqual cCommon cBulk
    commonBelowBoundary : LessEqual cCommon cBoundary
    commonBelowInterface : LessEqual cCommon cInterface
    commonBelowCorner : LessEqual cCommon cCorner
    commonBelowNested : LessEqual cCommon cNested

    bulkHodgePoincare : ∀ index state →
      regime index ≡ bulk → GaugeFixedTangent index state →
      LessEqual (scale cBulk (normSq index state))
        (referenceEnergy index state)
    boundaryHodgePoincare : ∀ index state →
      regime index ≡ boundary → GaugeFixedTangent index state →
      LessEqual (scale cBoundary (normSq index state))
        (referenceEnergy index state)
    interfaceHodgePoincare : ∀ index state →
      regime index ≡ scaleInterface → GaugeFixedTangent index state →
      LessEqual (scale cInterface (normSq index state))
        (referenceEnergy index state)
    cornerHodgePoincare : ∀ index state →
      regime index ≡ corner → GaugeFixedTangent index state →
      LessEqual (scale cCorner (normSq index state))
        (referenceEnergy index state)
    nestedHodgePoincare : ∀ index state →
      regime index ≡ nestedRestriction → GaugeFixedTangent index state →
      LessEqual (scale cNested (normSq index state))
        (referenceEnergy index state)

    regimeComplete : ∀ index →
      (regime index ≡ bulk) ⊎
      (regime index ≡ boundary) ⊎
      (regime index ≡ scaleInterface) ⊎
      (regime index ≡ corner) ⊎
      (regime index ≡ nestedRestriction)

    referenceEnergyHessianIdentity : ∀ index state →
      referenceEnergy index state ≡ inner state (referenceHessian index state)

    curvaturePart transportPart chartPart gaugePart constraintPart
      perturbationEnergy : Index → State → Bound
    δCurvature δTransport δChart δGauge δConstraint : Radius → Bound
    RadiusLessEqual : Radius → Radius → Set

    curvatureBound : ∀ radius index state →
      LessEqual (curvaturePart index state)
        (scale (δCurvature radius) (normSq index state))
    transportBound : ∀ radius index state →
      LessEqual (transportPart index state)
        (scale (δTransport radius) (normSq index state))
    chartBound : ∀ radius index state →
      LessEqual (chartPart index state)
        (scale (δChart radius) (normSq index state))
    gaugeBound : ∀ radius index state →
      LessEqual (gaugePart index state)
        (scale (δGauge radius) (normSq index state))
    constraintBound : ∀ radius index state →
      LessEqual (constraintPart index state)
        (scale (δConstraint radius) (normSq index state))

    perturbationDecomposes : ∀ index state →
      LessEqual (perturbationEnergy index state)
        (add (curvaturePart index state)
          (add (transportPart index state)
            (add (chartPart index state)
              (add (gaugePart index state) (constraintPart index state)))))

    δCurvatureIsMonotone : ∀ {small large} → RadiusLessEqual small large →
      LessEqual (δCurvature small) (δCurvature large)
    δTransportIsMonotone : ∀ {small large} → RadiusLessEqual small large →
      LessEqual (δTransport small) (δTransport large)
    δChartIsMonotone : ∀ {small large} → RadiusLessEqual small large →
      LessEqual (δChart small) (δChart large)
    δGaugeIsMonotone : ∀ {small large} → RadiusLessEqual small large →
      LessEqual (δGauge small) (δGauge large)
    δConstraintIsMonotone : ∀ {small large} → RadiusLessEqual small large →
      LessEqual (δConstraint small) (δConstraint large)

    δTotal : Radius → Bound
    δTotalIdentity : ∀ radius →
      δTotal radius ≡
        add (δCurvature radius)
          (add (δTransport radius)
            (add (δChart radius)
              (add (δGauge radius) (δConstraint radius))))

    componentBoundsCombine : ∀ radius index state →
      LessEqual
        (add (curvaturePart index state)
          (add (transportPart index state)
            (add (chartPart index state)
              (add (gaugePart index state) (constraintPart index state))))
        (scale (δTotal radius) (normSq index state))

    perturbationFitsMargin : ∀ radius state index →
      LessEqual
        (add (scale cH (normSq index state))
          (scale (δTotal radius) (normSq index state)))
        (scale c0 (normSq index state))

    perturbationStrictlyBelowGap : ∀ radius → StrictLess (δTotal radius) c0

    referenceGapIsCommon : c0 ≡ cCommon

    referenceBelowFullPlusPerturbation : ∀ index state →
      GaugeFixedTangent index state →
      LessEqual (inner state (referenceHessian index state))
        (add (inner state (hessian index state))
          (perturbationEnergy index state))

open ConcreteHodgeHessianData public
open ConcreteHodgeHessianData.GaugeFixedTangent public

bulkGaugeFixedHodgePoincare :
  ∀ {Index State Bound Radius} →
  (dataSet : ConcreteHodgeHessianData Index State Bound Radius) →
  ∀ index state → regime dataSet index ≡ bulk →
  GaugeFixedTangent dataSet index state →
  LessEqual dataSet
    (scale dataSet (cBulk dataSet) (normSq dataSet index state))
    (referenceEnergy dataSet index state)
bulkGaugeFixedHodgePoincare = bulkHodgePoincare

boundaryGaugeFixedHodgePoincare = boundaryHodgePoincare
scaleInterfaceGaugeFixedHodgePoincare = interfaceHodgePoincare
cornerGaugeFixedHodgePoincare = cornerHodgePoincare
nestedRestrictionGaugeFixedHodgePoincare = nestedHodgePoincare

commonHodgeConstantPositive = cCommonPositive

-- Exact zero-mode removal is structural: every witness is a projection from
-- the single constrained tangent-space inhabitant.
gaugeZeroModesRemoved :
  ∀ {Index State Bound Radius}
    {dataSet : ConcreteHodgeHessianData Index State Bound Radius}
    {index state} →
  GaugeFixedTangent dataSet index state → GaugeOrthogonal dataSet index state
gaugeZeroModesRemoved = gaugeOrthogonal

blockAverageModesRemoved :
  ∀ {Index State Bound Radius}
    {dataSet : ConcreteHodgeHessianData Index State Bound Radius}
    {index state} →
  GaugeFixedTangent dataSet index state → BlockAverageZero dataSet index state
blockAverageModesRemoved = blockAverageZero

residualGaugeModesRemoved :
  ∀ {Index State Bound Radius}
    {dataSet : ConcreteHodgeHessianData Index State Bound Radius}
    {index state} →
  GaugeFixedTangent dataSet index state →
  ResidualGaugeOrthogonal dataSet index state
residualGaugeModesRemoved = residualGaugeOrthogonal

boundaryDegeneraciesRemoved :
  ∀ {Index State Bound Radius}
    {dataSet : ConcreteHodgeHessianData Index State Bound Radius}
    {index state} →
  GaugeFixedTangent dataSet index state → BoundaryCompatibility dataSet index state
boundaryDegeneraciesRemoved = boundaryCompatible

referenceEnergyIsReferenceHessian = referenceEnergyHessianIdentity

curvatureHessianPerturbationBound = curvatureBound
transportHessianPerturbationBound = transportBound
chartHessianPerturbationBound = chartBound
gaugeFixingHessianPerturbationBound = gaugeBound
blockConstraintHessianPerturbationBound = constraintBound
fullHessianDifferenceDecomposes = perturbationDecomposes
δCurvatureMonotone = δCurvatureIsMonotone
δTransportMonotone = δTransportIsMonotone
δChartMonotone = δChartIsMonotone
δGaugeMonotone = δGaugeIsMonotone
δConstraintMonotone = δConstraintIsMonotone
perturbationFitsCoercivityMargin = perturbationFitsMargin
perturbationStrictlyBelowReferenceGap = perturbationStrictlyBelowGap

uniformReferenceHodgeCoercive :
  ∀ {Index State Bound Radius} →
  (dataSet : ConcreteHodgeHessianData Index State Bound Radius) →
  ∀ index state → GaugeFixedTangent dataSet index state →
  LessEqual dataSet
    (scale dataSet (cCommon dataSet) (normSq dataSet index state))
    (referenceEnergy dataSet index state)
uniformReferenceHodgeCoercive dataSet index state tangent
  with regimeComplete dataSet index
... | inj₁ p = transitive dataSet
  (commonBelowBulkScaled dataSet index state)
  (bulkHodgePoincare dataSet index state p tangent)
... | inj₂ (inj₁ p) = transitive dataSet
  (commonBelowBoundaryScaled dataSet index state)
  (boundaryHodgePoincare dataSet index state p tangent)
... | inj₂ (inj₂ (inj₁ p)) = transitive dataSet
  (commonBelowInterfaceScaled dataSet index state)
  (interfaceHodgePoincare dataSet index state p tangent)
... | inj₂ (inj₂ (inj₂ (inj₁ p))) = transitive dataSet
  (commonBelowCornerScaled dataSet index state)
  (cornerHodgePoincare dataSet index state p tangent)
... | inj₂ (inj₂ (inj₂ (inj₂ p))) = transitive dataSet
  (commonBelowNestedScaled dataSet index state)
  (nestedHodgePoincare dataSet index state p tangent)

perturbationEnergyBound :
  ∀ {Index State Bound Radius} →
  (dataSet : ConcreteHodgeHessianData Index State Bound Radius) →
  ∀ radius index state →
  LessEqual dataSet (perturbationEnergy dataSet index state)
    (scale dataSet (δTotal dataSet radius) (normSq dataSet index state))
perturbationEnergyBound dataSet radius index state =
  transitive dataSet
    (perturbationDecomposes dataSet index state)
    (componentBoundsCombine dataSet radius index state)

uniformConstrainedHessianCoercive :
  ∀ {Index State Bound Radius} →
  (dataSet : ConcreteHodgeHessianData Index State Bound Radius) →
  ∀ radius index state → GaugeFixedTangent dataSet index state →
  LessEqual dataSet
    (scale dataSet (cH dataSet) (normSq dataSet index state))
    (inner dataSet state (hessian dataSet index state))
uniformConstrainedHessianCoercive dataSet radius index state tangent =
  addRightCancel dataSet
    (transitive dataSet
      (perturbationFitsMargin dataSet radius state index)
      (transitive dataSet referenceStep
        (transitive dataSet
          (referenceBelowFullPlusPerturbation dataSet index state tangent)
          (addMonotone dataSet
            (reflexive dataSet (inner dataSet state (hessian dataSet index state)))
            (perturbationEnergyBound dataSet radius index state)))))
  where
  referenceStep :
    LessEqual dataSet
      (scale dataSet (c0 dataSet) (normSq dataSet index state))
      (inner dataSet state (referenceHessian dataSet index state))
  referenceStep rewrite referenceGapIsCommon dataSet |
    referenceEnergyHessianIdentity dataSet index state =
    uniformReferenceHodgeCoercive dataSet index state tangent

concreteHodgeHessianAssemblyLevel : ProofLevel
concreteHodgeHessianAssemblyLevel = machineChecked

concreteRegimeAndPerturbationInputsLevel : ProofLevel
concreteRegimeAndPerturbationInputsLevel = conditional
