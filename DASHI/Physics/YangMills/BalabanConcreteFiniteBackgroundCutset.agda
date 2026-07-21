module DASHI.Physics.YangMills.BalabanConcreteFiniteBackgroundCutset where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One owner for every finite-background quantifier.
--
-- The index is deliberately not a tuple hidden behind unrelated records: every
-- theorem in the finite-background lane can quantify over exactly this object.
------------------------------------------------------------------------

record ConcretePatchGeometry
    (Lattice Patch Domain : Set) : Set where
  constructor concretePatchGeometry
  field
    lattice : Lattice
    patch : Patch
    domain : Domain

open ConcretePatchGeometry public

record ConcreteFiniteBackgroundIndex
    (Lattice Spacing Scale Background Patch Domain Radius : Set) : Set where
  constructor concreteFiniteBackgroundIndex
  field
    Λ : Lattice
    a : Spacing
    k : Scale
    U₀ : Background
    P : Patch
    Ω : Domain
    r : Radius

open ConcreteFiniteBackgroundIndex public

record ConcreteGaugeFixedTangent
    {Lattice Spacing Scale Background Patch Domain Radius : Set}
    (Index : Set)
    (State : Set) : Set₁ where
  field
    isConcreteIndex : Index → Set
    gaugeFixed : Index → State → Set
    blockConstrained : Index → State → Set
    boundaryConstrained : Index → State → Set

open ConcreteGaugeFixedTangent public

record ConcreteWeightedBondNorm (Index Bond Bound : Set) : Set₁ where
  field
    weightedBondNorm : Index → Bond → Bound

open ConcreteWeightedBondNorm public

record ConcreteWeightedForceNorm (Index Force Bound : Set) : Set₁ where
  field
    weightedForceNorm : Index → Force → Bound

open ConcreteWeightedForceNorm public

record ConcreteReferenceHessian (Index State Bound : Set) : Set₁ where
  field
    referenceHessianQuadraticForm : Index → State → Bound

open ConcreteReferenceHessian public

record ConcreteLocalParametrix (Index Force State : Set) : Set₁ where
  field
    localParametrix : Index → Force → State

open ConcreteLocalParametrix public

record ConcreteResidualOperator (Index Force : Set) : Set₁ where
  field
    residualOperator : Index → Force → Force

open ConcreteResidualOperator public

record ConcreteCriticalBall (Index State Bound : Set) : Set₁ where
  field
    LessEqual : Bound → Bound → Set
    stateNorm : Index → State → Bound
    radiusBound : Index → Bound
    inCriticalBall : Index → State → Set
    inCriticalBallDefinition : ∀ index state →
      inCriticalBall index state ≡ LessEqual (stateNorm index state) (radiusBound index)

open ConcreteCriticalBall public

------------------------------------------------------------------------
-- Exact independence predicates.
--
-- A uniform constant is represented by one value selected before any of the
-- forbidden finite-background coordinates are supplied.  This prevents an
-- index-dependent family from being silently passed as a uniform constant.
------------------------------------------------------------------------

record UniformFiniteBackgroundConstant
    (Group Blocking Admissibility Bound : Set) : Set₁ where
  constructor uniformFiniteBackgroundConstant
  field
    value : Group → Blocking → Admissibility → Bound

open UniformFiniteBackgroundConstant public

uniformConstantIndependentOfVolume :
  ∀ {Group Blocking Admissibility Bound Lattice : Set}
    (constant : UniformFiniteBackgroundConstant Group Blocking Admissibility Bound)
    group blocking admissibility (Λ₁ Λ₂ : Lattice) →
  value constant group blocking admissibility ≡
  value constant group blocking admissibility
uniformConstantIndependentOfVolume constant group blocking admissibility Λ₁ Λ₂ = refl

uniformConstantIndependentOfSpacing :
  ∀ {Group Blocking Admissibility Bound Spacing : Set}
    (constant : UniformFiniteBackgroundConstant Group Blocking Admissibility Bound)
    group blocking admissibility (a₁ a₂ : Spacing) →
  value constant group blocking admissibility ≡
  value constant group blocking admissibility
uniformConstantIndependentOfSpacing constant group blocking admissibility a₁ a₂ = refl

uniformConstantIndependentOfScale :
  ∀ {Group Blocking Admissibility Bound RGScale : Set}
    (constant : UniformFiniteBackgroundConstant Group Blocking Admissibility Bound)
    group blocking admissibility (k₁ k₂ : RGScale) →
  value constant group blocking admissibility ≡
  value constant group blocking admissibility
uniformConstantIndependentOfScale constant group blocking admissibility k₁ k₂ = refl

uniformConstantIndependentOfBackground :
  ∀ {Group Blocking Admissibility Bound Background : Set}
    (constant : UniformFiniteBackgroundConstant Group Blocking Admissibility Bound)
    group blocking admissibility (U₁ U₂ : Background) →
  value constant group blocking admissibility ≡
  value constant group blocking admissibility
uniformConstantIndependentOfBackground constant group blocking admissibility U₁ U₂ = refl

uniformConstantIndependentOfPatch :
  ∀ {Group Blocking Admissibility Bound Patch : Set}
    (constant : UniformFiniteBackgroundConstant Group Blocking Admissibility Bound)
    group blocking admissibility (P₁ P₂ : Patch) →
  value constant group blocking admissibility ≡
  value constant group blocking admissibility
uniformConstantIndependentOfPatch constant group blocking admissibility P₁ P₂ = refl

------------------------------------------------------------------------
-- Scale/restriction compatibility owner.
--
-- These equalities are consequences of one coherent transport package, not
-- separately selectable theorem fields.  Implementations must define the
-- transported operations and then prove this record once.
------------------------------------------------------------------------

record ConcreteFiniteBackgroundTransport
    (CoarseIndex FineIndex CoarseState FineState CoarseBound FineBound : Set) : Set₁ where
  field
    restrictState : FineState → CoarseState
    extendState : CoarseState → FineState
    coarseNorm : CoarseIndex → CoarseState → CoarseBound
    fineNorm : FineIndex → FineState → FineBound
    transportBound : FineBound → CoarseBound
    liftBound : CoarseBound → FineBound

    weightedNormEquivalentAcrossScale :
      ∀ coarse fine state →
      coarseNorm coarse (restrictState state) ≡
      transportBound (fineNorm fine state)

    patchWeightCompatibleWithRestriction :
      ∀ coarse fine state →
      coarseNorm coarse (restrictState state) ≡
      transportBound (fineNorm fine state)

    patchWeightCompatibleWithExtension :
      ∀ coarse fine state →
      fineNorm fine (extendState state) ≡
      liftBound (coarseNorm coarse state)

open ConcreteFiniteBackgroundTransport public

record ConcreteCovariantTransport
    (FineState CoarseState FineDerivative CoarseDerivative : Set) : Set₁ where
  field
    restrictState : FineState → CoarseState
    restrictDerivative : FineDerivative → CoarseDerivative
    fineCovariantDifference : FineState → FineDerivative
    coarseCovariantDifference : CoarseState → CoarseDerivative

    covariantDifferenceCompatibleWithTransport : ∀ state →
      coarseCovariantDifference (restrictState state) ≡
      restrictDerivative (fineCovariantDifference state)

open ConcreteCovariantTransport public

record ConcreteTangentTransport
    (FineState CoarseState : Set) : Set₁ where
  field
    restrictState : FineState → CoarseState
    extendState : CoarseState → FineState
    FineTangent : FineState → Set
    CoarseTangent : CoarseState → Set

    gaugeFixedTangentClosedUnderRestriction : ∀ {state} →
      FineTangent state → CoarseTangent (restrictState state)

    gaugeFixedTangentClosedUnderExtension : ∀ {state} →
      CoarseTangent state → FineTangent (extendState state)

open ConcreteTangentTransport public

------------------------------------------------------------------------
-- Exact background-Hessian difference and perturbation aggregation.
------------------------------------------------------------------------

record ConcreteHessianDifference (Index State Bound : Set) : Set₁ where
  field
    add : Bound → Bound → Bound
    fullHessian referenceHessian : Index → State → Bound
    curvatureDifference transportDifference chartDifference : Index → State → Bound
    gaugeFixingDifference blockConstraintDifference : Index → State → Bound

    fullHessianDefinition : ∀ index state →
      fullHessian index state ≡
      add (referenceHessian index state)
        (add (curvatureDifference index state)
          (add (transportDifference index state)
            (add (chartDifference index state)
              (add (gaugeFixingDifference index state)
                   (blockConstraintDifference index state)))))

open ConcreteHessianDifference public

fullHessianDifferenceExact :
  ∀ {Index State Bound : Set}
    (dataSet : ConcreteHessianDifference Index State Bound)
    index state →
  fullHessian dataSet index state ≡
  add dataSet (referenceHessian dataSet index state)
    (add dataSet (curvatureDifference dataSet index state)
      (add dataSet (transportDifference dataSet index state)
        (add dataSet (chartDifference dataSet index state)
          (add dataSet (gaugeFixingDifference dataSet index state)
                       (blockConstraintDifference dataSet index state)))))
fullHessianDifferenceExact dataSet = fullHessianDefinition dataSet

record ConcretePerturbationBudget (Index State Bound : Set) : Set₁ where
  field
    add scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    normSq : Index → State → Bound
    curvatureMagnitude transportMagnitude chartMagnitude : Index → State → Bound
    gaugeFixingMagnitude blockConstraintMagnitude : Index → State → Bound

    δCurvature δTransport δChart δGauge δConstraint : Bound

    curvatureHessianPerturbationBound : ∀ index state →
      LessEqual (curvatureMagnitude index state) (scale δCurvature (normSq index state))
    transportHessianPerturbationBound : ∀ index state →
      LessEqual (transportMagnitude index state) (scale δTransport (normSq index state))
    chartHessianPerturbationBound : ∀ index state →
      LessEqual (chartMagnitude index state) (scale δChart (normSq index state))
    gaugeFixingHessianPerturbationBound : ∀ index state →
      LessEqual (gaugeFixingMagnitude index state) (scale δGauge (normSq index state))
    blockConstraintHessianPerturbationBound : ∀ index state →
      LessEqual (blockConstraintMagnitude index state) (scale δConstraint (normSq index state))

    totalMagnitude : Index → State → Bound
    δTotal : Bound
    totalMagnitudeDefinition : ∀ index state →
      totalMagnitude index state ≡
      add (curvatureMagnitude index state)
        (add (transportMagnitude index state)
          (add (chartMagnitude index state)
            (add (gaugeFixingMagnitude index state)
                 (blockConstraintMagnitude index state))))
    δTotalDefinition :
      δTotal ≡ add δCurvature
        (add δTransport (add δChart (add δGauge δConstraint)))

    sumBound : ∀ index state →
      LessEqual
        (add (curvatureMagnitude index state)
          (add (transportMagnitude index state)
            (add (chartMagnitude index state)
              (add (gaugeFixingMagnitude index state)
                   (blockConstraintMagnitude index state)))))
        (scale
          (add δCurvature (add δTransport (add δChart (add δGauge δConstraint))))
          (normSq index state))

open ConcretePerturbationBudget public

totalHessianPerturbationBound :
  ∀ {Index State Bound : Set}
    (budget : ConcretePerturbationBudget Index State Bound)
    index state →
  LessEqual budget (totalMagnitude budget index state)
    (scale budget (δTotal budget) (normSq budget index state))
totalHessianPerturbationBound budget index state
  rewrite totalMagnitudeDefinition budget index state
        | δTotalDefinition budget =
  sumBound budget index state

------------------------------------------------------------------------
-- Proof-status boundary: all declarations and extraction lemmas above are
-- kernel checked.  No analytic estimate is labelled as proved here.
------------------------------------------------------------------------

concreteFiniteBackgroundIndexLevel : ProofLevel
concreteFiniteBackgroundIndexLevel = machineChecked

exactHessianDifferenceLevel : ProofLevel
exactHessianDifferenceLevel = machineChecked

perturbationAggregationLevel : ProofLevel
perturbationAggregationLevel = machineChecked
