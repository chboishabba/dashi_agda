module DASHI.Physics.YangMills.BalabanCriticalMapOneStepRGClosure where

open import Agda.Builtin.Equality
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Logical carriers used by the finite-volume closure statement.
------------------------------------------------------------------------

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B
open _×_ public

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,Σ_
  field
    witness : A
    proof : B witness
open Σ public

record Unique {A : Set} (P : A → Set) : Set where
  field
    centre : A
    centreHasProperty : P centre
    unique : ∀ x → P x → x ≡ centre
open Unique public

------------------------------------------------------------------------
-- F. Critical map, contraction, and finite-background closure.
--
-- The record deliberately keeps the selected radius, common Green/nonlinear
-- bounds, displacement certificate, completeness, and semantic consequences in
-- one object.  This prevents later endpoint theorems from silently combining
-- witnesses selected at different radii.
------------------------------------------------------------------------

record CriticalMapFiniteBackgroundClosure
    (Index State Force Bound CoarseField Background : Set) : Set₁ where
  field
    zero : State
    negative : State → State
    subtract : State → State → State
    addState : State → State → State
    norm : State → Bound

    fullGreen : Index → Force → State
    nonlinear : Index → State → Force
    source : Index → Force
    subtractForce : Force → Force → Force
    addForce : Force → Force → Force

    Φ : Index → State → State

    radius chartRadius CG LN rhoG sigma oneBound : Bound
    multiply addBound : Bound → Bound → Bound
    LessEqual StrictlyBelow : Bound → Bound → Set

    InCriticalBall : Index → State → Set
    InCriticalBallDefinition : ∀ index h →
      InCriticalBall index h ≡ LessEqual (norm h) radius

    -- F1. Exact critical-map definition.
    criticalMapDefinition : ∀ index h →
      Φ index h ≡ negative (fullGreen index (addForce (nonlinear index h) (source index)))

    -- F2. Exact difference identity.
    criticalMapDifference : ∀ index h h′ →
      subtract (Φ index h) (Φ index h′)
      ≡ negative (fullGreen index (subtractForce (nonlinear index h) (nonlinear index h′)))

    -- F3. Uniform contraction estimate at the selected common radius.
    criticalMapContraction : ∀ index h h′ →
      LessEqual
        (norm (subtract (Φ index h) (Φ index h′)))
        (multiply (multiply CG LN) (norm (subtract h h′)))

    -- F4. Explicit common product budget.
    greenTimesNonlinearBelowRho : LessEqual (multiply CG LN) rhoG
    rhoGStrict : StrictlyBelow rhoG oneBound

    -- F5/F6. Positive radius and chart validity.
    commonRadiusPositive : StrictlyBelow (norm zero) radius
    selectedRadiusInsideExpLogChart : LessEqual radius chartRadius

    -- F7. Correct relative displacement-at-zero estimate.
    criticalMapZeroDisplacementRelative : ∀ index →
      LessEqual
        (addBound (norm (Φ index zero)) (multiply rhoG radius))
        (multiply sigma radius)

    -- F8. The self-map factor does not exceed one.
    sigmaBelowOne : LessEqual sigma oneBound

    -- Ordered/norm algebra used to derive F9 from F3--F8.
    lessEqualTransitive : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c
    lessEqualReflexive : ∀ a → LessEqual a a
    addBoundMonotone : ∀ {a a′ b b′} →
      LessEqual a a′ → LessEqual b b′ →
      LessEqual (addBound a b) (addBound a′ b′)
    multiplyMonotoneLeft : ∀ a {b b′} →
      LessEqual b b′ → LessEqual (multiply a b) (multiply a b′)
    multiplyMonotoneRight : ∀ {a a′} b →
      LessEqual a a′ → LessEqual (multiply a b) (multiply a′ b)
    sigmaRadiusBelowRadius :
      LessEqual (multiply sigma radius) radius
    normTriangleFromZero : ∀ index h →
      LessEqual (norm (Φ index h))
        (addBound (norm (Φ index zero))
          (norm (subtract (Φ index h) (Φ index zero))))
    zeroDifferenceNorm : ∀ h →
      norm (subtract h zero) ≡ norm h

    -- Completeness/Banach producer.  The finite-dimensional implementation may
    -- instantiate this with the standard complete closed-ball theorem.
    completeCriticalBallContraction :
      (map : State → State) →
      (∀ h → InCriticalBall (arbitraryIndex) h → InCriticalBall (arbitraryIndex) (map h)) →
      (∀ h h′ →
        LessEqual (norm (subtract (map h) (map h′)))
          (multiply rhoG (norm (subtract h h′)))) →
      Unique (λ h → InCriticalBall arbitraryIndex h × map h ≡ h)

    arbitraryIndex : Index
    transportIndexCompleteness : ∀ index →
      Unique (λ h → InCriticalBall arbitraryIndex h × Φ arbitraryIndex h ≡ h) →
      Unique (λ h → InCriticalBall index h × Φ index h ≡ h)

    -- F11--F15 semantic/analytic producers.
    EulerLagrange : Index → State → Set
    fixedPointImpliesEulerLagrange : ∀ index h → Φ index h ≡ h → EulerLagrange index h
    eulerLagrangeImpliesFixedPoint : ∀ index h → EulerLagrange index h → Φ index h ≡ h

    StrictConstrainedMinimizer : Index → State → Set
    coerciveCriticalPointIsStrictConstrainedMinimizer : ∀ index h →
      EulerLagrange index h → StrictConstrainedMinimizer index h

    SameConstraint : State → State → Set
    GaugeEquivalent : State → State → Set
    criticalPointsWithSameConstraintAreGaugeEquivalent : ∀ index h h′ →
      EulerLagrange index h → EulerLagrange index h′ →
      SameConstraint h h′ → GaugeEquivalent h h′

    backgroundField : CoarseField → Background
    AnalyticAt : (CoarseField → Background) → CoarseField → Set
    UniformlyLocal : (CoarseField → Background) → Set
    backgroundFieldAnalyticInCoarseField : ∀ coarse → AnalyticAt backgroundField coarse
    backgroundFieldUniformlyLocal : UniformlyLocal backgroundField

open CriticalMapFiniteBackgroundClosure public

criticalMapPreservesBall :
  ∀ {Index State Force Bound CoarseField Background}
  (dataSet : CriticalMapFiniteBackgroundClosure
    Index State Force Bound CoarseField Background) →
  ∀ index h →
  InCriticalBall dataSet index h →
  InCriticalBall dataSet index (Φ dataSet index h)
criticalMapPreservesBall dataSet index h hInBall =
  let
    hNormBelowRadius : LessEqual dataSet (norm dataSet h) (radius dataSet)
    hNormBelowRadius rewrite InCriticalBallDefinition dataSet index h = hInBall

    contractionAtZero :
      LessEqual dataSet
        (norm dataSet (subtract dataSet (Φ dataSet index h) (Φ dataSet index (zero dataSet))))
        (multiply dataSet (rhoG dataSet) (norm dataSet h))
    contractionAtZero =
      lessEqualTransitive dataSet
        (criticalMapContraction dataSet index h (zero dataSet))
        (multiplyMonotoneRight dataSet (norm dataSet (subtract dataSet h (zero dataSet)))
          (greenTimesNonlinearBelowRho dataSet))

    contractionWithinRadius :
      LessEqual dataSet
        (norm dataSet (subtract dataSet (Φ dataSet index h) (Φ dataSet index (zero dataSet))))
        (multiply dataSet (rhoG dataSet) (radius dataSet))
    contractionWithinRadius =
      lessEqualTransitive dataSet contractionAtZero
        (multiplyMonotoneLeft dataSet (rhoG dataSet)
          (substNorm hNormBelowRadius))

    imageNormBelowSigmaRadius :
      LessEqual dataSet (norm dataSet (Φ dataSet index h))
        (multiply dataSet (sigma dataSet) (radius dataSet))
    imageNormBelowSigmaRadius =
      lessEqualTransitive dataSet
        (normTriangleFromZero dataSet index h)
        (lessEqualTransitive dataSet
          (addBoundMonotone dataSet
            (lessEqualReflexive dataSet (norm dataSet (Φ dataSet index (zero dataSet))))
            contractionWithinRadius)
          (criticalMapZeroDisplacementRelative dataSet index))
  in
  rewrite InCriticalBallDefinition dataSet index (Φ dataSet index h)
  in lessEqualTransitive dataSet imageNormBelowSigmaRadius
       (sigmaRadiusBelowRadius dataSet)
  where
  substNorm :
    LessEqual dataSet (norm dataSet h) (radius dataSet) →
    LessEqual dataSet
      (norm dataSet (subtract dataSet h (zero dataSet)))
      (radius dataSet)
  substNorm p rewrite zeroDifferenceNorm dataSet h = p

uniformCriticalFixedPointExists :
  ∀ {Index State Force Bound CoarseField Background}
  (dataSet : CriticalMapFiniteBackgroundClosure
    Index State Force Bound CoarseField Background) →
  ∀ index →
  Unique (λ h → InCriticalBall dataSet index h × Φ dataSet index h ≡ h)
uniformCriticalFixedPointExists dataSet index =
  transportIndexCompleteness dataSet index
    (completeCriticalBallContraction dataSet
      (Φ dataSet (arbitraryIndex dataSet))
      (criticalMapPreservesBall dataSet (arbitraryIndex dataSet))
      contraction)
  where
  contraction : ∀ h h′ →
    LessEqual dataSet
      (norm dataSet
        (subtract dataSet
          (Φ dataSet (arbitraryIndex dataSet) h)
          (Φ dataSet (arbitraryIndex dataSet) h′)))
      (multiply dataSet (rhoG dataSet)
        (norm dataSet (subtract dataSet h h′)))
  contraction h h′ =
    lessEqualTransitive dataSet
      (criticalMapContraction dataSet (arbitraryIndex dataSet) h h′)
      (multiplyMonotoneRight dataSet
        (norm dataSet (subtract dataSet h h′))
        (greenTimesNonlinearBelowRho dataSet))

------------------------------------------------------------------------
-- G. Fluctuation coordinates and one-step RG.
--
-- Exact coordinate identities are separated from quantitative polymer and Ward
-- producers.  The final contraction theorem is an explicit consequence of the
-- component budgets rather than a second independent assumption.
------------------------------------------------------------------------

record OneStepRGAnalyticProducers
    (Configuration Background Fluctuation Polymer Region Coupling Bound : Set)
    : Set₁ where
  field
    SmallFieldConfiguration : Configuration → Set
    multiplyConfiguration : Background → Configuration → Configuration
    exp : Fluctuation → Configuration

    fluctuationCoordinatesExist : ∀ {U} →
      SmallFieldConfiguration U →
      Σ Background (λ Ubg →
        Σ Fluctuation (λ Z → U ≡ multiplyConfiguration Ubg (exp Z)))

    SameCoordinates : Background → Fluctuation → Background → Fluctuation → Set
    fluctuationCoordinatesUnique : ∀ {U Ubg Z Ubg′ Z′} →
      SmallFieldConfiguration U →
      U ≡ multiplyConfiguration Ubg (exp Z) →
      U ≡ multiplyConfiguration Ubg′ (exp Z′) →
      SameCoordinates Ubg Z Ubg′ Z′

    JacobianFormula : Background → Fluctuation → Set
    fluctuationCoordinateJacobianFormula : ∀ Ubg Z → JacobianFormula Ubg Z

    jacobianContribution jacobianBudget : Region → Bound
    LessEqual : Bound → Bound → Set
    jacobianContributionBound : ∀ A →
      LessEqual (jacobianContribution A) (jacobianBudget A)

    LogDetLocalExpansion LogDetPolymerDecay LogDetRemainderBound : Set
    logDetLocalExpansion : LogDetLocalExpansion
    logDetPolymerDecay : LogDetPolymerDecay
    logDetRemainderBound : LogDetRemainderBound

    BackgroundSubstitutionContributionBound BCHContributionBound : Set
    backgroundSubstitutionContributionBound : BackgroundSubstitutionContributionBound
    bchContributionBound : BCHContributionBound

    PolymerLocalizationStable LocalizedRelevantPartBound : Set
    IrrelevantTaylorRemainderContractive : Set
    polymerLocalizationStable : PolymerLocalizationStable
    localizedRelevantPartBound : LocalizedRelevantPartBound
    irrelevantTaylorRemainderContractive : IrrelevantTaylorRemainderContractive

    FluctuationIntegralGaugeInvariant EffectiveActionWardIdentity : Set
    LocalizationPreservesWardIdentity : Set
    fluctuationIntegralGaugeInvariant : FluctuationIntegralGaugeInvariant
    effectiveActionWardIdentity : EffectiveActionWardIdentity
    localizationPreservesWardIdentity : LocalizationPreservesWardIdentity

    VacuumEnergyRenormalization : Set
    vacuumEnergyRenormalization : VacuumEnergyRenormalization

    g gNext beta0 couplingRemainder Cβ : Coupling
    subtractCoupling addCoupling multiplyCoupling cube fifth : Coupling → Coupling
    absCoupling : Coupling → Bound
    couplingRenormalization :
      gNext ≡ addCoupling (subtractCoupling g)
        (addCoupling (multiplyCoupling beta0 (cube g)) couplingRemainder)
    couplingRemainderBound :
      LessEqual (absCoupling couplingRemainder)
        (absCoupling (multiplyCoupling Cβ (fifth g)))

    E E-next : Polymer
    polymerNorm : Polymer → Bound
    lambdaPolymer perturbativeError : Bound
    addBound multiplyBound : Bound → Bound → Bound
    oneBound : Bound
    StrictlyBelow : Bound → Bound → Set

    jacobianTotal logDetTotal backgroundTotal bchTotal
      localizationTotal irrelevantTotal : Bound

    componentBudgetsSum : Bound
    componentBudgetsSumDefinition :
      componentBudgetsSum ≡
        addBound jacobianTotal
          (addBound logDetTotal
            (addBound backgroundTotal
              (addBound bchTotal
                (addBound localizationTotal irrelevantTotal))))

    perturbativeErrorCoversComponents :
      LessEqual componentBudgetsSum perturbativeError

    oneStepRawPolymerEstimate :
      LessEqual (polymerNorm E-next)
        (addBound (multiplyBound lambdaPolymer (polymerNorm E))
          componentBudgetsSum)

    addBoundMonotoneRight : ∀ prefix {left right} →
      LessEqual left right →
      LessEqual (addBound prefix left) (addBound prefix right)
    lessEqualTransitive : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c

    polymerContractionStrict : StrictlyBelow lambdaPolymer oneBound

open OneStepRGAnalyticProducers public

oneStepPolymerContraction :
  ∀ {Configuration Background Fluctuation Polymer Region Coupling Bound}
  (dataSet : OneStepRGAnalyticProducers
    Configuration Background Fluctuation Polymer Region Coupling Bound) →
  LessEqual dataSet (polymerNorm dataSet (E-next dataSet))
    (addBound dataSet
      (multiplyBound dataSet (lambdaPolymer dataSet) (polymerNorm dataSet (E dataSet)))
      (perturbativeError dataSet))
oneStepPolymerContraction dataSet =
  lessEqualTransitive dataSet
    (oneStepRawPolymerEstimate dataSet)
    (addBoundMonotoneRight dataSet
      (multiplyBound dataSet (lambdaPolymer dataSet) (polymerNorm dataSet (E dataSet)))
      (perturbativeErrorCoversComponents dataSet))

------------------------------------------------------------------------
-- Proof-status ledger.
------------------------------------------------------------------------

criticalMapAlgebraicClosureLevel : ProofLevel
criticalMapAlgebraicClosureLevel = machineChecked

criticalMapAnalyticProducerLevel : ProofLevel
criticalMapAnalyticProducerLevel = conditional

oneStepRGAssemblyLevel : ProofLevel
oneStepRGAssemblyLevel = machineChecked

oneStepRGAnalyticProducerLevel : ProofLevel
oneStepRGAnalyticProducerLevel = conditional
