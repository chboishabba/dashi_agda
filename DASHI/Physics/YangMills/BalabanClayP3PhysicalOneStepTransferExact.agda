module DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Rational using (ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanClayP4DyadicCoercivityBudgetExact
  using (coercivityLoss; DyadicCoercivityRecurrence)

Not : Set → Set
Not proposition = proposition → ⊥

------------------------------------------------------------------------
-- P3A: exact finite-volume one-step transformation.
------------------------------------------------------------------------

record ExactOneStepIntegral
    (FineField CoarseField Measure Weight EffectiveAction Scalar : Set) : Set₁ where
  field
    blockMap : FineField → CoarseField
    fineMeasure : Measure
    boltzmannWeight : FineField → Weight
    constrainedIntegral : Measure → (FineField → Weight) → CoarseField → Scalar
    nextEffectiveAction : CoarseField → EffectiveAction
    exponentialOfNegativeAction : EffectiveAction → Scalar

    smallFieldContribution largeFieldContribution : CoarseField → Scalar
    vacuumNormalization : Scalar
    addScalar multiplyScalar : Scalar → Scalar → Scalar

    smallLargePartitionExact : ∀ coarse →
      constrainedIntegral fineMeasure boltzmannWeight coarse
      ≡ addScalar
          (smallFieldContribution coarse)
          (largeFieldContribution coarse)

    effectiveActionDefinesIntegral : ∀ coarse →
      exponentialOfNegativeAction (nextEffectiveAction coarse)
      ≡ multiplyScalar vacuumNormalization
          (constrainedIntegral fineMeasure boltzmannWeight coarse)

open ExactOneStepIntegral public

------------------------------------------------------------------------
-- P3B: nonlinear minimizing-background coordinates with their exact Jacobian.
------------------------------------------------------------------------

record ExactNonlinearFluctuationCoordinates
    (FineField CoarseField Background Fluctuation Jacobian : Set) : Set₁ where
  field
    SmallField : FineField → Set
    coarseOf : FineField → CoarseField
    backgroundOf : CoarseField → Background
    reconstruct : Background → Fluctuation → FineField
    fluctuationOf : FineField → Fluctuation
    jacobianOf : Background → Fluctuation → Jacobian
    coordinateJacobian : FineField → Jacobian
    FluctuationConstraint : CoarseField → Fluctuation → Set

    reconstructs : ∀ fineField → SmallField fineField →
      reconstruct (backgroundOf (coarseOf fineField)) (fluctuationOf fineField) ≡ fineField

    fluctuationSatisfiesConstraint : ∀ fineField → SmallField fineField →
      FluctuationConstraint (coarseOf fineField) (fluctuationOf fineField)

    backgroundUnique : ∀ fineField → SmallField fineField →
      ∀ background fluctuation →
      reconstruct background fluctuation ≡ fineField →
      background ≡ backgroundOf (coarseOf fineField)

    fluctuationUnique : ∀ fineField → SmallField fineField →
      ∀ background fluctuation →
      reconstruct background fluctuation ≡ fineField →
      fluctuation ≡ fluctuationOf fineField

    jacobianExact : ∀ fineField → SmallField fineField →
      jacobianOf
        (backgroundOf (coarseOf fineField)) (fluctuationOf fineField)
      ≡ coordinateJacobian fineField

open ExactNonlinearFluctuationCoordinates public

------------------------------------------------------------------------
-- P3C: exact constrained Schur-complement surface.
------------------------------------------------------------------------

record ExactSchurComplement
    (Coarse Fluctuation Bound : Set) : Set₁ where
  field
    coarseHessian : Coarse → Coarse
    mixedHessian : Coarse → Fluctuation
    fluctuationHessian fluctuationGreen : Fluctuation → Fluctuation
    schurHessian : Coarse → Coarse

    coarseInner : Coarse → Coarse → Bound
    fluctuationInner : Fluctuation → Fluctuation → Bound
    subtract : Bound → Bound → Bound

    fluctuationInverseLeft : ∀ fluctuation →
      fluctuationGreen (fluctuationHessian fluctuation) ≡ fluctuation
    fluctuationInverseRight : ∀ fluctuation →
      fluctuationHessian (fluctuationGreen fluctuation) ≡ fluctuation

    schurEnergyExact : ∀ coarse →
      coarseInner coarse (schurHessian coarse)
      ≡ subtract
          (coarseInner coarse (coarseHessian coarse))
          (fluctuationInner
            (mixedHessian coarse)
            (fluctuationGreen (mixedHessian coarse)))

    FluctuationCoercive : Set
    fluctuationCoercive : FluctuationCoercive

    GaugeCovariant : (Coarse → Coarse) → Set
    schurGaugeCovariant : GaugeCovariant schurHessian

    KernelExactlyPrescribedGaugeModes : Set
    kernelExactlyPrescribedGaugeModes : KernelExactlyPrescribedGaugeModes

    NextScaleNormalizationMatches : Set
    nextScaleNormalizationMatches : NextScaleNormalizationMatches

open ExactSchurComplement public

------------------------------------------------------------------------
-- P3E: the five one-step Hessian losses in one common norm.
------------------------------------------------------------------------

record OneStepHessianComponents (Scale State : Set) : Set₁ where
  field
    normSq : State → ℚ
    totalPenalty : Scale → State → ℚ
    backgroundPenalty jacobianPenalty determinantPenalty bchPenalty
      localizationPenalty : Scale → State → ℚ

    backgroundUpper jacobianUpper determinantUpper bchUpper
      localizationUpper : Scale → ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper

    totalBelowComponents : ∀ scale state →
      totalPenalty scale state ≤
      backgroundPenalty scale state
      + (jacobianPenalty scale state
      + (determinantPenalty scale state
      + (bchPenalty scale state + localizationPenalty scale state)))

    backgroundSubstitutionEstimate : ∀ scale state →
      backgroundPenalty scale state
      ≤ backgroundUpper scale * normSq state
    jacobianContributionBound : ∀ scale state →
      jacobianPenalty scale state
      ≤ jacobianUpper scale * normSq state
    determinantContributionBound : ∀ scale state →
      determinantPenalty scale state
      ≤ determinantUpper scale * normSq state
    bchTaylorRemainderEstimate : ∀ scale state →
      bchPenalty scale state
      ≤ bchUpper scale * normSq state
    localizationEstimate : ∀ scale state →
      localizationPenalty scale state
      ≤ localizationUpper scale * normSq state

    combineUpper : ∀ scale radius →
      backgroundUpper scale * radius
      + (jacobianUpper scale * radius
      + (determinantUpper scale * radius
      + (bchUpper scale * radius + localizationUpper scale * radius)))
      ≡ (backgroundUpper scale
        + (jacobianUpper scale
        + (determinantUpper scale
        + (bchUpper scale + localizationUpper scale)))) * radius

open OneStepHessianComponents public

record DeterminantDomainHypotheses (Scale State : Set) : Set₁ where
  field
    admissibleBackground : Scale → State → Set
    smallFieldBackground : Scale → State → Set
    uniformCoercive : Scale → Set

open DeterminantDomainHypotheses public

record DeterminantProofChain (Scale State : Set) : Set₁ where
  field
    domainHypotheses : DeterminantDomainHypotheses Scale State
    referenceFluctuationHessianPositive : ∀ (scale : Scale) (state : State) →
      admissibleBackground domainHypotheses scale state → Set
    physicalFluctuationHessianPositiveOnSmallField : ∀ (scale : Scale) (state : State) →
      smallFieldBackground domainHypotheses scale state → Set
    relativeHessianOperatorNormBelowOne : ∀ (scale : Scale) (state : State) → Set
    traceLogSeriesConverges : ∀ (scale : Scale) (state : State) → Set
    logDetBoundFromTraceNorm : ∀ (scale : Scale) (state : State) → ℚ

open DeterminantProofChain public

oneStepTotalUpper :
  ∀ {Scale State} → OneStepHessianComponents Scale State → Scale → ℚ
oneStepTotalUpper dataSet scale =
  backgroundUpper dataSet scale
  + (jacobianUpper dataSet scale
  + (determinantUpper dataSet scale
  + (bchUpper dataSet scale + localizationUpper dataSet scale)))

oneStepPerturbationBound :
  ∀ {Scale State}
    (dataSet : OneStepHessianComponents Scale State)
    scale state →
  totalPenalty dataSet scale state
  ≤ oneStepTotalUpper dataSet scale * normSq dataSet state
oneStepPerturbationBound dataSet scale state =
  subst
    (λ right → totalPenalty dataSet scale state ≤ right)
    (combineUpper dataSet scale (normSq dataSet state))
    (transitive dataSet
      (totalBelowComponents dataSet scale state)
      (addMonotone dataSet
        (backgroundSubstitutionEstimate dataSet scale state)
        (addMonotone dataSet
          (jacobianContributionBound dataSet scale state)
          (addMonotone dataSet
            (determinantContributionBound dataSet scale state)
            (addMonotone dataSet
              (bchTaylorRemainderEstimate dataSet scale state)
              (localizationEstimate dataSet scale state))))))

------------------------------------------------------------------------
-- P3D: physical coercivity transfer at one scale.
------------------------------------------------------------------------

record OneStepPhysicalCoercivityData (Scale State : Set) : Set₁ where
  field
    components : OneStepHessianComponents Scale State
    currentEnergy nextEnergy : Scale → State → ℚ
    currentCoercivity nextCoercivity : Scale → ℚ

    addRightCancel : ∀ {left right common} →
      left + common ≤ right + common → left ≤ right

    currentCoercive : ∀ scale state →
      currentCoercivity scale * normSq components state
      ≤ currentEnergy scale state

    currentBelowNextPlusPenalty : ∀ scale state →
      currentEnergy scale state
      ≤ nextEnergy scale state + totalPenalty components scale state

    nextBudgetPlusLossBelowCurrent : ∀ scale state →
      nextCoercivity scale * normSq components state
      + oneStepTotalUpper components scale * normSq components state
      ≤ currentCoercivity scale * normSq components state

open OneStepPhysicalCoercivityData public

oneStepPhysicalCoercivityTransfer :
  ∀ {Scale State}
    (dataSet : OneStepPhysicalCoercivityData Scale State)
    scale state →
  nextCoercivity dataSet scale * normSq (components dataSet) state
  ≤ nextEnergy dataSet scale state
oneStepPhysicalCoercivityTransfer dataSet scale state =
  addRightCancel dataSet
    (transitive (components dataSet)
      (nextBudgetPlusLossBelowCurrent dataSet scale state)
      (transitive (components dataSet)
        (currentCoercive dataSet scale state)
        (transitive (components dataSet)
          (currentBelowNextPlusPenalty dataSet scale state)
          (addMonotone (components dataSet)
            (reflexive (components dataSet) (nextEnergy dataSet scale state))
            (oneStepPerturbationBound
              (components dataSet) scale state)))))

------------------------------------------------------------------------
-- P3F: exact Ward-identity preservation and exclusion of a mass counterterm.
------------------------------------------------------------------------

record OneStepWardIdentity
    (GaugeTransform Field EffectiveAction LocalTerm : Set) : Set₁ where
  field
    transformField : GaugeTransform → Field → Field
    effectiveAction : Field → EffectiveAction
    transformAction : GaugeTransform → EffectiveAction → EffectiveAction
    localize : EffectiveAction → LocalTerm
    GaugeInvariantLocalTerm : LocalTerm → Set
    GaugeBosonMassTerm : LocalTerm → Set

    fluctuationIntegralGaugeInvariant : ∀ gauge gaugeField →
      effectiveAction (transformField gauge gaugeField)
      ≡ transformAction gauge (effectiveAction gaugeField)

    localizationPreservesWardIdentity : ∀ gauge gaugeField →
      localize (effectiveAction (transformField gauge gaugeField))
      ≡ localize (transformAction gauge (effectiveAction gaugeField))

    localizedEffectiveActionGaugeInvariant : ∀ gaugeField →
      GaugeInvariantLocalTerm (localize (effectiveAction gaugeField))

    gaugeInvariantTermCannotBeMass : ∀ term →
      GaugeInvariantLocalTerm term → Not (GaugeBosonMassTerm term)

open OneStepWardIdentity public

noGeneratedGaugeBosonMass :
  ∀ {GaugeTransform Field EffectiveAction LocalTerm}
    (dataSet : OneStepWardIdentity
      GaugeTransform Field EffectiveAction LocalTerm)
    gaugeField →
  Not (GaugeBosonMassTerm dataSet
    (localize dataSet (effectiveAction dataSet gaugeField)))
noGeneratedGaugeBosonMass dataSet gaugeField =
  gaugeInvariantTermCannotBeMass dataSet
    (localize dataSet (effectiveAction dataSet gaugeField))
    (localizedEffectiveActionGaugeInvariant dataSet gaugeField)

------------------------------------------------------------------------
-- P3G: exact running-coupling recursion with a controlled remainder.
------------------------------------------------------------------------

record RunningCouplingRecursion (Scale Bound : Set) : Set₁ where
  field
    inverseCouplingSq : Scale → Bound
    betaLogBlocking remainder : Scale → Bound
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    Absolute : Bound → Bound
    remainderUpper : Scale → Bound
    nextScale : Scale → Scale

    recursionExact : ∀ scale →
      inverseCouplingSq (nextScale scale)
      ≡ add (inverseCouplingSq scale)
          (add (betaLogBlocking scale) (remainder scale))

    remainderControlled : ∀ scale →
      LessEqual (Absolute (remainder scale)) (remainderUpper scale)

open RunningCouplingRecursion public

------------------------------------------------------------------------
-- Scale family adapter into the exact dyadic all-scale theorem.
------------------------------------------------------------------------

record PhysicalOneStepCoercivityFamily : Set₁ where
  field
    coercivityAt : Nat → ℚ
    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper
    addRightCancel : ∀ {left right common} →
      left + common ≤ right + common → left ≤ right

    initialCoercivity :
      DASHI.Physics.YangMills.BalabanClayP4DyadicCoercivityBudgetExact.oneThirtySecond
      ≤ coercivityAt zero

    physicalOneStepLoss : ∀ scale →
      coercivityAt scale
      ≤ coercivityAt (suc scale) + coercivityLoss scale

open PhysicalOneStepCoercivityFamily public

toDyadicCoercivityRecurrence :
  PhysicalOneStepCoercivityFamily → DyadicCoercivityRecurrence
toDyadicCoercivityRecurrence family = record
  { coercivityAt = coercivityAt family
  ; reflexive = reflexive family
  ; transitive = transitive family
  ; addMonotone = addMonotone family
  ; addRightCancel = addRightCancel family
  ; initialCoercivity = initialCoercivity family
  ; oneStepLossBound = physicalOneStepLoss family
  }

p3FiveComponentAssemblyLevel : ProofLevel
p3FiveComponentAssemblyLevel = machineChecked

p3OneStepCoercivityAssemblyLevel : ProofLevel
p3OneStepCoercivityAssemblyLevel = machineChecked

p3WardNoMassConsequenceLevel : ProofLevel
p3WardNoMassConsequenceLevel = machineChecked

p3ExactIntegralAndCoordinateProducerLevel : ProofLevel
p3ExactIntegralAndCoordinateProducerLevel = conditional

p3SchurComplementProducerLevel : ProofLevel
p3SchurComplementProducerLevel = conditional

p3FivePhysicalComponentEstimateProducerLevel : ProofLevel
p3FivePhysicalComponentEstimateProducerLevel = conditional

p3WardIdentityAndNoMassProducerLevel : ProofLevel
p3WardIdentityAndNoMassProducerLevel = conditional

p3RunningCouplingProducerLevel : ProofLevel
p3RunningCouplingProducerLevel = conditional
