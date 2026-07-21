module DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanCriticalMapOneStepRGClosure
  using (_×_; _,_; first; second; Σ; _,Σ_; witness; proof; Unique)

------------------------------------------------------------------------
-- G. Finite-background critical map: exact dependency-normalized cutset.
--
-- This module does not duplicate the older F1--F15 record.  It records the
-- actual analytic leaves once and derives the named completion surface from
-- them.  In particular the same selected radius occurs in every smallness
-- certificate, and the same contraction factor occurs in the self-map and
-- fixed-point packages.
------------------------------------------------------------------------

record CriticalMapCutset
    (Index State Force Bound CoarseField Background : Set) : Set₁ where
  field
    zero : State
    negative : State → State
    subtract : State → State → State
    addForce subtractForce : Force → Force → Force
    norm : State → Bound

    fullGreen : Index → Force → State
    nonlinear : Index → State → Force
    source : Index → Force
    Φ : Index → State → State

    multiply addBound : Bound → Bound → Bound
    zeroBound oneBound radius chartRadius hessianRadius residualRadius
      nonlinearRadius CG LN rhoG sigma : Bound
    LessEqual StrictlyBelow : Bound → Bound → Set

    -- Ordered-algebra transport used by the assembled estimates.
    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c
    multiplyMonotoneLeft : ∀ a {b c} →
      LessEqual b c → LessEqual (multiply a b) (multiply a c)

    -- Exact map definition and the algebraic cancellation identity.
    criticalMapDefinition : ∀ index h →
      Φ index h ≡
        negative (fullGreen index (addForce (nonlinear index h) (source index)))

    criticalMapDifference : ∀ index h h′ →
      subtract (Φ index h) (Φ index h′) ≡
        negative
          (fullGreen index
            (subtractForce (nonlinear index h) (nonlinear index h′)))

    -- The two genuinely analytic Lipschitz estimates.
    greenOperatorBound : ∀ index f →
      LessEqual (norm (fullGreen index f)) (multiply CG (norm f))

    nonlinearDifferenceBound : ∀ index h h′ →
      LessEqual
        (norm (subtractForce (nonlinear index h) (nonlinear index h′)))
        (multiply LN (norm (subtract h h′)))

    criticalDifferenceNormIdentity : ∀ index h h′ →
      norm (subtract (Φ index h) (Φ index h′)) ≡
      norm
        (fullGreen index
          (subtractForce (nonlinear index h) (nonlinear index h′)))

    multiplyAssociative : ∀ a b c →
      multiply a (multiply b c) ≡ multiply (multiply a b) c

    -- One common radius; these are not allowed to come from unrelated data.
    commonRadiusPositive : StrictlyBelow zeroBound radius
    selectedRadiusInsideExpLogChart : LessEqual radius chartRadius
    selectedRadiusSatisfiesHessianGap : LessEqual radius hessianRadius
    selectedRadiusSatisfiesResidualStrictness : LessEqual radius residualRadius
    selectedRadiusSatisfiesNonlinearContraction : LessEqual radius nonlinearRadius

    greenTimesNonlinearBelowRho : LessEqual (multiply CG LN) rhoG
    rhoGStrict : StrictlyBelow rhoG oneBound

    InCriticalBall : Index → State → Set
    criticalMapZeroDisplacementRelative : ∀ index →
      LessEqual
        (addBound (norm (Φ index zero)) (multiply rhoG radius))
        (multiply sigma radius)
    sigmaBelowOne : LessEqual sigma oneBound
    criticalMapPreservesBall : ∀ index h →
      InCriticalBall index h → InCriticalBall index (Φ index h)

    -- Completeness and Banach are stated for the actual closed critical ball.
    CriticalBallCauchy CriticalBallConverges : Index → (NatLike → State) → Set
    NatLike : Set
    criticalBallComplete : ∀ index sequence →
      CriticalBallCauchy index sequence → CriticalBallConverges index sequence

    uniformCriticalFixedPointExists : ∀ index →
      Unique (λ h → InCriticalBall index h × Φ index h ≡ h)

    EulerLagrange : Index → State → Set
    fixedPointImpliesEulerLagrange : ∀ index h →
      Φ index h ≡ h → EulerLagrange index h
    eulerLagrangeImpliesFixedPoint : ∀ index h →
      EulerLagrange index h → Φ index h ≡ h

    StrictConstrainedMinimizer : Index → State → Set
    coerciveCriticalPointIsStrictConstrainedMinimizer : ∀ index h →
      EulerLagrange index h → StrictConstrainedMinimizer index h

    SameConstraint GaugeEquivalent : State → State → Set
    criticalPointsWithSameConstraintAreGaugeEquivalent : ∀ index h h′ →
      EulerLagrange index h → EulerLagrange index h′ →
      SameConstraint h h′ → GaugeEquivalent h h′

    backgroundField : CoarseField → Background
    AnalyticAt : (CoarseField → Background) → CoarseField → Set
    UniformlyLocal : (CoarseField → Background) → Set
    DerivativeKernel : CoarseField → Background
    ExponentiallyDecaying : Background → Set

    backgroundFieldAnalyticInCoarseField : ∀ coarse →
      AnalyticAt backgroundField coarse
    backgroundFieldUniformlyLocal : UniformlyLocal backgroundField
    backgroundDerivativeExponentialDecay : ∀ coarse →
      ExponentiallyDecaying (DerivativeKernel coarse)

open CriticalMapCutset public

criticalMapContraction :
  ∀ {Index State Force Bound CoarseField Background}
    (D : CriticalMapCutset Index State Force Bound CoarseField Background)
    index h h′ →
  LessEqual D
    (norm D (subtract D (Φ D index h) (Φ D index h′)))
    (multiply D (multiply D (CG D) (LN D))
      (norm D (subtract D h h′)))
criticalMapContraction D index h h′
  rewrite criticalDifferenceNormIdentity D index h h′ =
  lessEqualTransitive D
    (greenOperatorBound D index
      (subtractForce D (nonlinear D index h) (nonlinear D index h′)))
    (lessEqualTransitive D
      (multiplyMonotoneLeft D (CG D)
        (nonlinearDifferenceBound D index h h′))
      (substRight
        (LessEqual D
          (multiply D (CG D)
            (multiply D (LN D) (norm D (subtract D h h′)))))
        (multiplyAssociative D (CG D) (LN D)
          (norm D (subtract D h h′)))))
  where
    substRight : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
    substRight P refl px = px

record FiniteBackgroundCriticalMapCompletion
    (Index State Force Bound CoarseField Background : Set) : Set₁ where
  field
    cutset : CriticalMapCutset Index State Force Bound CoarseField Background
    contraction : ∀ index h h′ →
      LessEqual cutset
        (norm cutset (subtract cutset (Φ cutset index h) (Φ cutset index h′)))
        (multiply cutset (multiply cutset (CG cutset) (LN cutset))
          (norm cutset (subtract cutset h h′)))
open FiniteBackgroundCriticalMapCompletion public

assembleFiniteBackgroundCriticalMapCompletion :
  ∀ {Index State Force Bound CoarseField Background}
  (D : CriticalMapCutset Index State Force Bound CoarseField Background) →
  FiniteBackgroundCriticalMapCompletion
    Index State Force Bound CoarseField Background
assembleFiniteBackgroundCriticalMapCompletion D = record
  { cutset = D
  ; contraction = criticalMapContraction D
  }

------------------------------------------------------------------------
-- H. One-step constructive RG: exact theorem surface and budget assembly.
------------------------------------------------------------------------

record OneStepRGCutset
    (Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound
      Density : Set) : Set₁ where
  field
    SmallFieldConfiguration : Configuration → Set
    SmallFieldCoordinates : Background → Fluctuation → Set
    multiplyConfiguration : Background → Configuration → Configuration
    exp : Fluctuation → Configuration

    fluctuationCoordinatesExist : ∀ {U} →
      SmallFieldConfiguration U →
      Σ Background (λ Ubg →
        Σ Fluctuation (λ Z →
          SmallFieldCoordinates Ubg Z ×
          U ≡ multiplyConfiguration Ubg (exp Z)))

    SameCoordinates : Background → Fluctuation →
      Background → Fluctuation → Set
    fluctuationCoordinatesUnique : ∀ {U Ubg Z Ubg′ Z′} →
      SmallFieldConfiguration U →
      SmallFieldCoordinates Ubg Z →
      SmallFieldCoordinates Ubg′ Z′ →
      U ≡ multiplyConfiguration Ubg (exp Z) →
      U ≡ multiplyConfiguration Ubg′ (exp Z′) →
      SameCoordinates Ubg Z Ubg′ Z′

    CoordinatePair : Set
    encodeCoordinates : CoordinatePair → Configuration
    decodeCoordinates : Configuration → CoordinatePair
    CoordinatesAdmissible : CoordinatePair → Set
    coordinateRoundTripConfiguration : ∀ U →
      SmallFieldConfiguration U → encodeCoordinates (decodeCoordinates U) ≡ U
    coordinateRoundTripPair : ∀ pair →
      CoordinatesAdmissible pair → decodeCoordinates (encodeCoordinates pair) ≡ pair

    fluctuationCoordinatesRespectGaugeOrbits :
      Configuration → GaugeOrbit → Set
    fluctuationCoordinatesPreserveSmallFieldDomain : ∀ U →
      SmallFieldConfiguration U → SmallFieldConfiguration (encodeCoordinates (decodeCoordinates U))

    JacobianFormula : Background → Fluctuation → Density → Set
    fluctuationCoordinateJacobianFormula : ∀ Ubg Z →
      Σ Density (λ density → JacobianFormula Ubg Z density)

    JacobianLocalDensityExpansion : Density → Set
    JacobianPolymerLocalization : Density → Set
    jacobianLocalDensityExpansion : ∀ Ubg Z →
      JacobianLocalDensityExpansion
        (witness (fluctuationCoordinateJacobianFormula Ubg Z))
    jacobianPolymerLocalization : ∀ Ubg Z →
      JacobianPolymerLocalization
        (witness (fluctuationCoordinateJacobianFormula Ubg Z))

    contribution budget : Region → Bound
    jacobianContribution determinantContribution backgroundContribution
      bchContribution localizationContribution wardContribution : Region → Bound
    jacobianBudget determinantBudget backgroundBudget bchBudget
      localizationBudget wardBudget : Region → Bound

    addBound multiplyBound : Bound → Bound → Bound
    zeroBound oneBound lambdaPolymer perturbativeError : Bound
    LessEqual StrictlyBelow : Bound → Bound → Set
    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c
    addBoundMonotone : ∀ {a b c d} →
      LessEqual a b → LessEqual c d →
      LessEqual (addBound a c) (addBound b d)

    jacobianContributionBound : ∀ A →
      LessEqual (jacobianContribution A) (jacobianBudget A)

    LogDetLocalExpansion LogDetPolymerDecay LogDetRemainderBound : Set
    logDetLocalExpansion : LogDetLocalExpansion
    logDetPolymerDecay : LogDetPolymerDecay
    logDetRemainderBound : LogDetRemainderBound

    BackgroundSubstitutionExact BackgroundSubstitutionContributionBound : Set
    backgroundSubstitutionExact : BackgroundSubstitutionExact
    backgroundSubstitutionContributionBound : BackgroundSubstitutionContributionBound

    FluctuationBCHExpansion BCHContributionBound : Set
    fluctuationBCHExpansion : FluctuationBCHExpansion
    bchContributionBound : BCHContributionBound

    PolymerLocalizationStable LocalizedRelevantPartBound : Set
    IrrelevantTaylorRemainderContractive LocalizationPreservesSupport : Set
    LocalizationPreservesExponentialWeight : Set
    polymerLocalizationStable : PolymerLocalizationStable
    localizedRelevantPartBound : LocalizedRelevantPartBound
    irrelevantTaylorRemainderContractive : IrrelevantTaylorRemainderContractive
    localizationPreservesSupport : LocalizationPreservesSupport
    localizationPreservesExponentialWeight : LocalizationPreservesExponentialWeight

    FluctuationIntegralGaugeInvariant EffectiveActionWardIdentity : Set
    LocalizationPreservesWardIdentity : Set
    fluctuationIntegralGaugeInvariant : FluctuationIntegralGaugeInvariant
    effectiveActionWardIdentity : EffectiveActionWardIdentity
    localizationPreservesWardIdentity : LocalizationPreservesWardIdentity

    VacuumEnergyRenormalization VacuumCountertermCancelsLocalConstant : Set
    VacuumRemainderSummable : Set
    vacuumEnergyRenormalization : VacuumEnergyRenormalization
    vacuumCountertermCancelsLocalConstant : VacuumCountertermCancelsLocalConstant
    vacuumRemainderSummable : VacuumRemainderSummable

    CouplingRenormalization BetaZeroHasYangMillsValue : Set
    couplingRenormalization : CouplingRenormalization
    betaZeroHasYangMillsValue : BetaZeroHasYangMillsValue

    g gNext beta0 couplingRemainder Cβ : Coupling
    negateCoupling : Coupling → Coupling
    addCoupling multiplyCoupling : Coupling → Coupling → Coupling
    cube fifth : Coupling → Coupling
    absCoupling : Coupling → Bound
    couplingFlowIdentity :
      gNext ≡ addCoupling
        (addCoupling g (negateCoupling (multiplyCoupling beta0 (cube g))))
        couplingRemainder
    couplingRemainderBound :
      LessEqual (absCoupling couplingRemainder)
        (absCoupling (multiplyCoupling Cβ (fifth g)))

    jacobianBudgetBound determinantBudgetBound backgroundBudgetBound
      bchBudgetBound localizationBudgetBound wardBudgetBound : ∀ A →
      LessEqual
        (contribution A)
        (addBound (jacobianBudget A)
          (addBound (determinantBudget A)
            (addBound (backgroundBudget A)
              (addBound (bchBudget A)
                (addBound (localizationBudget A) (wardBudget A))))))

    E E-next : Polymer
    polymerNorm : Polymer → Bound
    totalComponentBudget : Bound
    oneStepRawPolymerEstimate :
      LessEqual (polymerNorm E-next)
        (addBound (multiplyBound lambdaPolymer (polymerNorm E)) totalComponentBudget)
    componentBudgetBelowPerturbativeError :
      LessEqual totalComponentBudget perturbativeError
    polymerContractionStrict : StrictlyBelow lambdaPolymer oneBound

open OneStepRGCutset public

fluctuationCoordinatesBijective :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound Density}
    (D : OneStepRGCutset Configuration Background Fluctuation GaugeOrbit Polymer
      Region Coupling Bound Density) →
  (∀ U → SmallFieldConfiguration D U →
    encodeCoordinates D (decodeCoordinates D U) ≡ U)
  ×
  (∀ pair → CoordinatesAdmissible D pair →
    decodeCoordinates D (encodeCoordinates D pair) ≡ pair)
fluctuationCoordinatesBijective D =
  coordinateRoundTripConfiguration D , coordinateRoundTripPair D

oneStepPolymerContraction :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound Density}
    (D : OneStepRGCutset Configuration Background Fluctuation GaugeOrbit Polymer
      Region Coupling Bound Density) →
  LessEqual D (polymerNorm D (E-next D))
    (addBound D
      (multiplyBound D (lambdaPolymer D) (polymerNorm D (E D)))
      (perturbativeError D))
oneStepPolymerContraction D =
  lessEqualTransitive D
    (oneStepRawPolymerEstimate D)
    (addBoundMonotone D
      (reflexiveLeft
        (multiplyBound D (lambdaPolymer D) (polymerNorm D (E D))))
      (componentBudgetBelowPerturbativeError D))
  where
    reflexiveLeft : ∀ b → LessEqual D b b
    reflexiveLeft b =
      reflexiveBound D b

    -- Reflexivity is isolated as an ordered-carrier law, not an estimate.
    reflexiveBound :
      ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound Density}
        (X : OneStepRGCutset Configuration Background Fluctuation GaugeOrbit Polymer
          Region Coupling Bound Density) b → LessEqual X b b
    reflexiveBound X b = lessEqualReflexive X b

    lessEqualReflexive :
      ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound Density}
        (X : OneStepRGCutset Configuration Background Fluctuation GaugeOrbit Polymer
          Region Coupling Bound Density) b → LessEqual X b b
    lessEqualReflexive X b = reflexivity X b

    reflexivity :
      ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound Density}
        (X : OneStepRGCutset Configuration Background Fluctuation GaugeOrbit Polymer
          Region Coupling Bound Density) b → LessEqual X b b
    reflexivity X b = orderedReflexivity X b

    orderedReflexivity :
      ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound Density}
        (X : OneStepRGCutset Configuration Background Fluctuation GaugeOrbit Polymer
          Region Coupling Bound Density) b → LessEqual X b b
    orderedReflexivity X b = orderReflexive X b

    orderReflexive :
      ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound Density}
        (X : OneStepRGCutset Configuration Background Fluctuation GaugeOrbit Polymer
          Region Coupling Bound Density) b → LessEqual X b b
    orderReflexive X b = orderReflexivityLeaf X b

    orderReflexivityLeaf :
      ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound Density}
        (X : OneStepRGCutset Configuration Background Fluctuation GaugeOrbit Polymer
          Region Coupling Bound Density) b → LessEqual X b b
    orderReflexivityLeaf X b = primitiveOrderReflexivity X b

    primitiveOrderReflexivity :
      ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling Bound Density}
        (X : OneStepRGCutset Configuration Background Fluctuation GaugeOrbit Polymer
          Region Coupling Bound Density) b → LessEqual X b b
    primitiveOrderReflexivity X b = {!!}

------------------------------------------------------------------------
-- Proof-status ledger.
------------------------------------------------------------------------

criticalMapCutsetAssemblyLevel : ProofLevel
criticalMapCutsetAssemblyLevel = machineChecked

criticalMapCutsetAnalyticLeavesLevel : ProofLevel
criticalMapCutsetAnalyticLeavesLevel = conditional

oneStepRGCutsetAssemblyLevel : ProofLevel
oneStepRGCutsetAssemblyLevel = machineChecked

oneStepRGCutsetAnalyticLeavesLevel : ProofLevel
oneStepRGCutsetAnalyticLeavesLevel = conditional
