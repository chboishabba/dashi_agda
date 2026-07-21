module DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanCriticalMapOneStepRGClosure
  using (_×_; _,_; Σ; witness; Unique)

------------------------------------------------------------------------
-- G. Finite-background critical map.
------------------------------------------------------------------------

record CriticalMapCutset
    (Index State Force Bound CoarseField Background NatLike : Set) : Set₁ where
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

    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c
    multiplyMonotoneLeft : ∀ a {b c} →
      LessEqual b c → LessEqual (multiply a b) (multiply a c)

    criticalMapDefinition : ∀ index h →
      Φ index h ≡
        negative (fullGreen index (addForce (nonlinear index h) (source index)))

    criticalMapDifference : ∀ index h h′ →
      subtract (Φ index h) (Φ index h′) ≡
        negative
          (fullGreen index
            (subtractForce (nonlinear index h) (nonlinear index h′)))

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

    CriticalBallCauchy CriticalBallConverges :
      Index → (NatLike → State) → Set
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

transportRight :
  ∀ {A : Set} {R : A → A → Set} {a b c : A} →
  R a b → b ≡ c → R a c
transportRight Rab refl = Rab

criticalMapContraction :
  ∀ {Index State Force Bound CoarseField Background NatLike}
    (D : CriticalMapCutset
      Index State Force Bound CoarseField Background NatLike)
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
    (transportRight
      (multiplyMonotoneLeft D (CG D)
        (nonlinearDifferenceBound D index h h′))
      (multiplyAssociative D (CG D) (LN D)
        (norm D (subtract D h h′))))

record FiniteBackgroundCriticalMapCompletion
    (Index State Force Bound CoarseField Background NatLike : Set) : Set₁ where
  field
    cutset : CriticalMapCutset
      Index State Force Bound CoarseField Background NatLike
    contraction : ∀ index h h′ →
      LessEqual cutset
        (norm cutset (subtract cutset (Φ cutset index h) (Φ cutset index h′)))
        (multiply cutset (multiply cutset (CG cutset) (LN cutset))
          (norm cutset (subtract cutset h h′)))
open FiniteBackgroundCriticalMapCompletion public

assembleFiniteBackgroundCriticalMapCompletion :
  ∀ {Index State Force Bound CoarseField Background NatLike}
  (D : CriticalMapCutset
    Index State Force Bound CoarseField Background NatLike) →
  FiniteBackgroundCriticalMapCompletion
    Index State Force Bound CoarseField Background NatLike
assembleFiniteBackgroundCriticalMapCompletion D = record
  { cutset = D
  ; contraction = criticalMapContraction D
  }

------------------------------------------------------------------------
-- H. One-step constructive RG.
------------------------------------------------------------------------

record OneStepRGCutset
    (Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density : Set) : Set₁ where
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
      SmallFieldCoordinates Ubg Z → SmallFieldCoordinates Ubg′ Z′ →
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
      SmallFieldConfiguration U →
      SmallFieldConfiguration (encodeCoordinates (decodeCoordinates U))

    JacobianFormula : Background → Fluctuation → Density → Set
    fluctuationCoordinateJacobianFormula : ∀ Ubg Z →
      Σ Density (λ density → JacobianFormula Ubg Z density)
    JacobianLocalDensityExpansion JacobianPolymerLocalization : Density → Set
    jacobianLocalDensityExpansion : ∀ Ubg Z →
      JacobianLocalDensityExpansion
        (witness (fluctuationCoordinateJacobianFormula Ubg Z))
    jacobianPolymerLocalization : ∀ Ubg Z →
      JacobianPolymerLocalization
        (witness (fluctuationCoordinateJacobianFormula Ubg Z))

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

    addBound multiplyBound : Bound → Bound → Bound
    oneBound lambdaPolymer perturbativeError totalComponentBudget : Bound
    LessEqual StrictlyBelow : Bound → Bound → Set
    lessEqualReflexive : ∀ a → LessEqual a a
    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c
    addBoundMonotone : ∀ {a b c d} →
      LessEqual a b → LessEqual c d →
      LessEqual (addBound a c) (addBound b d)

    couplingRemainderBound :
      LessEqual (absCoupling couplingRemainder)
        (absCoupling (multiplyCoupling Cβ (fifth g)))

    jacobianContribution determinantContribution backgroundContribution
      bchContribution localizationContribution wardContribution : Region → Bound
    jacobianBudget determinantBudget backgroundBudget bchBudget
      localizationBudget wardBudget : Region → Bound

    jacobianBudgetBound : ∀ A →
      LessEqual (jacobianContribution A) (jacobianBudget A)
    determinantBudgetBound : ∀ A →
      LessEqual (determinantContribution A) (determinantBudget A)
    backgroundBudgetBound : ∀ A →
      LessEqual (backgroundContribution A) (backgroundBudget A)
    bchBudgetBound : ∀ A →
      LessEqual (bchContribution A) (bchBudget A)
    localizationBudgetBound : ∀ A →
      LessEqual (localizationContribution A) (localizationBudget A)
    wardBudgetBound : ∀ A →
      LessEqual (wardContribution A) (wardBudget A)

    componentBudgetsBelowTotal : ∀ A →
      LessEqual
        (addBound (jacobianBudget A)
          (addBound (determinantBudget A)
            (addBound (backgroundBudget A)
              (addBound (bchBudget A)
                (addBound (localizationBudget A) (wardBudget A))))))
        totalComponentBudget

    E E-next : Polymer
    polymerNorm : Polymer → Bound
    oneStepRawPolymerEstimate :
      LessEqual (polymerNorm E-next)
        (addBound (multiplyBound lambdaPolymer (polymerNorm E)) totalComponentBudget)
    componentBudgetBelowPerturbativeError :
      LessEqual totalComponentBudget perturbativeError
    polymerContractionStrict : StrictlyBelow lambdaPolymer oneBound

open OneStepRGCutset public

fluctuationCoordinatesBijective :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
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
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
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
      (lessEqualReflexive D
        (multiplyBound D (lambdaPolymer D) (polymerNorm D (E D))))
      (componentBudgetBelowPerturbativeError D))

criticalMapCutsetAssemblyLevel : ProofLevel
criticalMapCutsetAssemblyLevel = machineChecked

criticalMapCutsetAnalyticLeavesLevel : ProofLevel
criticalMapCutsetAnalyticLeavesLevel = conditional

oneStepRGCutsetAssemblyLevel : ProofLevel
oneStepRGCutsetAssemblyLevel = machineChecked

oneStepRGCutsetAnalyticLeavesLevel : ProofLevel
oneStepRGCutsetAnalyticLeavesLevel = conditional
