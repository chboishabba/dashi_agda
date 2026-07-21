module DASHI.Physics.YangMills.BalabanCriticalMapOneStepRGClosure where

open import Agda.Builtin.Equality
open import DASHI.Physics.YangMills.CompactLieProofLevel

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
-- Every field below is tied to the same selected radius and the same common
-- Green/nonlinear constants.  In particular, the displacement certificate can
-- no longer be imported from a different smallness radius.
------------------------------------------------------------------------

record CriticalMapFiniteBackgroundClosure
    (Index State Force Bound CoarseField Background : Set) : Set₁ where
  field
    zero : State
    negative : State → State
    subtract : State → State → State
    norm : State → Bound

    fullGreen : Index → Force → State
    nonlinear : Index → State → Force
    source : Index → Force
    subtractForce addForce : Force → Force → Force
    Φ : Index → State → State

    radius chartRadius CG LN rhoG sigma oneBound zeroBound : Bound
    multiply addBound : Bound → Bound → Bound
    LessEqual StrictlyBelow : Bound → Bound → Set

    InCriticalBall : Index → State → Set

    -- F1--F3.
    criticalMapDefinition : ∀ index h →
      Φ index h ≡
        negative (fullGreen index (addForce (nonlinear index h) (source index)))

    criticalMapDifference : ∀ index h h′ →
      subtract (Φ index h) (Φ index h′) ≡
        negative
          (fullGreen index
            (subtractForce (nonlinear index h) (nonlinear index h′)))

    criticalMapContraction : ∀ index h h′ →
      LessEqual
        (norm (subtract (Φ index h) (Φ index h′)))
        (multiply (multiply CG LN) (norm (subtract h h′)))

    -- F4--F8.
    greenTimesNonlinearBelowRho : LessEqual (multiply CG LN) rhoG
    rhoGStrict : StrictlyBelow rhoG oneBound
    commonRadiusPositive : StrictlyBelow zeroBound radius
    selectedRadiusInsideExpLogChart : LessEqual radius chartRadius

    criticalMapZeroDisplacementRelative : ∀ index →
      LessEqual
        (addBound (norm (Φ index zero)) (multiply rhoG radius))
        (multiply sigma radius)

    sigmaBelowOne : LessEqual sigma oneBound

    -- F9/F10.  The implementation instance must discharge closed-ball
    -- preservation and completeness for the actual finite-dimensional or Banach
    -- carrier, rather than assuming completeness of the ambient syntax.
    criticalMapPreservesBall : ∀ index h →
      InCriticalBall index h → InCriticalBall index (Φ index h)

    uniformCriticalFixedPointExists : ∀ index →
      Unique (λ h → InCriticalBall index h × Φ index h ≡ h)

    -- F11.
    EulerLagrange : Index → State → Set
    fixedPointImpliesEulerLagrange : ∀ index h →
      Φ index h ≡ h → EulerLagrange index h
    eulerLagrangeImpliesFixedPoint : ∀ index h →
      EulerLagrange index h → Φ index h ≡ h

    -- F12/F13.
    StrictConstrainedMinimizer : Index → State → Set
    coerciveCriticalPointIsStrictConstrainedMinimizer : ∀ index h →
      EulerLagrange index h → StrictConstrainedMinimizer index h

    SameConstraint GaugeEquivalent : State → State → Set
    criticalPointsWithSameConstraintAreGaugeEquivalent : ∀ index h h′ →
      EulerLagrange index h →
      EulerLagrange index h′ →
      SameConstraint h h′ →
      GaugeEquivalent h h′

    -- F14/F15.
    backgroundField : CoarseField → Background
    AnalyticAt : (CoarseField → Background) → CoarseField → Set
    UniformlyLocal : (CoarseField → Background) → Set
    backgroundFieldAnalyticInCoarseField : ∀ coarse →
      AnalyticAt backgroundField coarse
    backgroundFieldUniformlyLocal : UniformlyLocal backgroundField

open CriticalMapFiniteBackgroundClosure public

-- The repaired finite-volume endpoint exports all F-obligations through one
-- witness, so downstream code cannot mix radii or constants.
record UnconditionalFiniteVolumeBackgroundFieldTheorem
    (Index State Force Bound CoarseField Background : Set) : Set₁ where
  field
    closure : CriticalMapFiniteBackgroundClosure
      Index State Force Bound CoarseField Background
open UnconditionalFiniteVolumeBackgroundFieldTheorem public

------------------------------------------------------------------------
-- G. Fluctuation coordinates and one-step RG.
------------------------------------------------------------------------

record OneStepRGAnalyticProducers
    (Configuration Background Fluctuation Polymer Region Coupling Bound : Set)
    : Set₁ where
  field
    SmallFieldConfiguration : Configuration → Set
    multiplyConfiguration : Background → Configuration → Configuration
    exp : Fluctuation → Configuration

    -- G1/G2.
    fluctuationCoordinatesExist : ∀ {U} →
      SmallFieldConfiguration U →
      Σ Background (λ Ubg →
        Σ Fluctuation (λ Z → U ≡ multiplyConfiguration Ubg (exp Z)))

    SameCoordinates : Background → Fluctuation →
      Background → Fluctuation → Set
    fluctuationCoordinatesUnique : ∀ {U Ubg Z Ubg′ Z′} →
      SmallFieldConfiguration U →
      U ≡ multiplyConfiguration Ubg (exp Z) →
      U ≡ multiplyConfiguration Ubg′ (exp Z′) →
      SameCoordinates Ubg Z Ubg′ Z′

    -- G3/G4.
    JacobianFormula : Background → Fluctuation → Set
    fluctuationCoordinateJacobianFormula : ∀ Ubg Z →
      JacobianFormula Ubg Z

    jacobianContribution jacobianBudget : Region → Bound
    LessEqual : Bound → Bound → Set
    jacobianContributionBound : ∀ A →
      LessEqual (jacobianContribution A) (jacobianBudget A)

    -- G5--G12.
    LogDetLocalExpansion LogDetPolymerDecay LogDetRemainderBound : Set
    logDetLocalExpansion : LogDetLocalExpansion
    logDetPolymerDecay : LogDetPolymerDecay
    logDetRemainderBound : LogDetRemainderBound

    BackgroundSubstitutionContributionBound BCHContributionBound : Set
    backgroundSubstitutionContributionBound :
      BackgroundSubstitutionContributionBound
    bchContributionBound : BCHContributionBound

    PolymerLocalizationStable LocalizedRelevantPartBound : Set
    IrrelevantTaylorRemainderContractive : Set
    polymerLocalizationStable : PolymerLocalizationStable
    localizedRelevantPartBound : LocalizedRelevantPartBound
    irrelevantTaylorRemainderContractive :
      IrrelevantTaylorRemainderContractive

    -- G13--G16.
    FluctuationIntegralGaugeInvariant EffectiveActionWardIdentity : Set
    LocalizationPreservesWardIdentity VacuumEnergyRenormalization : Set
    fluctuationIntegralGaugeInvariant : FluctuationIntegralGaugeInvariant
    effectiveActionWardIdentity : EffectiveActionWardIdentity
    localizationPreservesWardIdentity : LocalizationPreservesWardIdentity
    vacuumEnergyRenormalization : VacuumEnergyRenormalization

    -- G17/G18.
    g gNext beta0 couplingRemainder Cβ : Coupling
    negateCoupling : Coupling → Coupling
    addCoupling multiplyCoupling : Coupling → Coupling → Coupling
    cube fifth : Coupling → Coupling
    absCoupling : Coupling → Bound

    couplingRenormalization :
      gNext ≡
        addCoupling
          (addCoupling g
            (negateCoupling (multiplyCoupling beta0 (cube g))))
          couplingRemainder

    couplingRemainderBound :
      LessEqual (absCoupling couplingRemainder)
        (absCoupling (multiplyCoupling Cβ (fifth g)))

    -- G19 component estimate and strict factor.
    E E-next : Polymer
    polymerNorm : Polymer → Bound
    lambdaPolymer perturbativeError componentBudget oneBound : Bound
    addBound multiplyBound : Bound → Bound → Bound
    StrictlyBelow : Bound → Bound → Set

    oneStepRawPolymerEstimate :
      LessEqual (polymerNorm E-next)
        (addBound
          (multiplyBound lambdaPolymer (polymerNorm E))
          componentBudget)

    componentBudgetBelowPerturbativeError :
      LessEqual componentBudget perturbativeError

    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c

    addBoundMonotoneRight : ∀ prefix {left right} →
      LessEqual left right →
      LessEqual (addBound prefix left) (addBound prefix right)

    polymerContractionStrict : StrictlyBelow lambdaPolymer oneBound

open OneStepRGAnalyticProducers public

oneStepPolymerContraction :
  ∀ {Configuration Background Fluctuation Polymer Region Coupling Bound}
  (dataSet : OneStepRGAnalyticProducers
    Configuration Background Fluctuation Polymer Region Coupling Bound) →
  LessEqual dataSet
    (polymerNorm dataSet (E-next dataSet))
    (addBound dataSet
      (multiplyBound dataSet
        (lambdaPolymer dataSet)
        (polymerNorm dataSet (E dataSet)))
      (perturbativeError dataSet))
oneStepPolymerContraction dataSet =
  lessEqualTransitive dataSet
    (oneStepRawPolymerEstimate dataSet)
    (addBoundMonotoneRight dataSet
      (multiplyBound dataSet
        (lambdaPolymer dataSet)
        (polymerNorm dataSet (E dataSet)))
      (componentBudgetBelowPerturbativeError dataSet))

record OneStepRGClosure
    (Configuration Background Fluctuation Polymer Region Coupling Bound : Set)
    : Set₁ where
  field
    producers : OneStepRGAnalyticProducers
      Configuration Background Fluctuation Polymer Region Coupling Bound
    contraction :
      LessEqual producers
        (polymerNorm producers (E-next producers))
        (addBound producers
          (multiplyBound producers
            (lambdaPolymer producers)
            (polymerNorm producers (E producers)))
          (perturbativeError producers))
open OneStepRGClosure public

assembleOneStepRGClosure :
  ∀ {Configuration Background Fluctuation Polymer Region Coupling Bound} →
  (producers : OneStepRGAnalyticProducers
    Configuration Background Fluctuation Polymer Region Coupling Bound) →
  OneStepRGClosure
    Configuration Background Fluctuation Polymer Region Coupling Bound
assembleOneStepRGClosure producers = record
  { producers = producers
  ; contraction = oneStepPolymerContraction producers
  }

------------------------------------------------------------------------
-- Proof-status ledger.
------------------------------------------------------------------------

criticalMapFiniteBackgroundPackagingLevel : ProofLevel
criticalMapFiniteBackgroundPackagingLevel = machineChecked

criticalMapFiniteBackgroundAnalyticInputsLevel : ProofLevel
criticalMapFiniteBackgroundAnalyticInputsLevel = conditional

oneStepRGAssemblyLevel : ProofLevel
oneStepRGAssemblyLevel = machineChecked

oneStepRGAnalyticInputsLevel : ProofLevel
oneStepRGAnalyticInputsLevel = conditional
