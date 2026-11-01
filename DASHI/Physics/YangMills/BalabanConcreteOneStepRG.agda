module DASHI.Physics.YangMills.BalabanConcreteOneStepRG where

------------------------------------------------------------------------
-- Concrete one-step RG assembly from the explicit polymer budget theorem.
--
-- The compatibility surface at the top retains the original finite one-step
-- assembly.  The second half names the analytic R1--R7 obligations and proves
-- the quantitative R8 contraction from the five component estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOneStepPolymerEstimate as Polymer
import DASHI.Physics.YangMills.BalabanOneStepRGClosure as RG

record OneStepRGStructure
    (Field EffectiveAction : Set) : Set₁ where
  field
    backgroundField : Field → Field
    fluctuationCoordinate : Field → Field → Field
    effectiveAction : Field → EffectiveAction

    FluctuationParametrizationValid : Set
    JacobianControlled : Set
    DeterminantControlled : Set
    BCHRemainderControlled : Set
    WardIdentityPreserved : Set
    EffectiveActionLocalized : Set
    VacuumEnergyRenormalized : Set
    CouplingRenormalized : Set

    fluctuationParametrizationValid : FluctuationParametrizationValid
    jacobianControlled : JacobianControlled
    determinantControlled : DeterminantControlled
    bchRemainderControlled : BCHRemainderControlled
    wardIdentityPreserved : WardIdentityPreserved
    effectiveActionLocalized : EffectiveActionLocalized
    vacuumEnergyRenormalized : VacuumEnergyRenormalized
    couplingRenormalized : CouplingRenormalized

open OneStepRGStructure public

toOneStepRGInputs :
  ∀ {Field EffectiveAction PolymerCarrier Bound : Set} →
  OneStepRGStructure Field EffectiveAction →
  Polymer.OneStepPolymerEstimateData Field PolymerCarrier Bound →
  RG.OneStepRGInputs Field EffectiveAction PolymerCarrier Bound
toOneStepRGInputs structure estimate = record
  { backgroundField = backgroundField structure
  ; fluctuationCoordinate = fluctuationCoordinate structure
  ; effectiveAction = effectiveAction structure
  ; irrelevantRemainder = Polymer.outputPolymer estimate
  ; polymerNorm = Polymer.polymerNorm estimate
  ; outputBound = Polymer.oneStepPolymerBudget estimate
  ; FluctuationParametrizationValid = FluctuationParametrizationValid structure
  ; JacobianControlled = JacobianControlled structure
  ; DeterminantControlled = DeterminantControlled structure
  ; BCHRemainderControlled = BCHRemainderControlled structure
  ; WardIdentityPreserved = WardIdentityPreserved structure
  ; EffectiveActionLocalized = EffectiveActionLocalized structure
  ; VacuumEnergyRenormalized = VacuumEnergyRenormalized structure
  ; CouplingRenormalized = CouplingRenormalized structure
  ; fluctuationParametrizationValid = fluctuationParametrizationValid structure
  ; jacobianControlled = jacobianControlled structure
  ; determinantControlled = determinantControlled structure
  ; bchRemainderControlled = bchRemainderControlled structure
  ; wardIdentityPreserved = wardIdentityPreserved structure
  ; effectiveActionLocalized = effectiveActionLocalized structure
  ; vacuumEnergyRenormalized = vacuumEnergyRenormalized structure
  ; couplingRenormalized = couplingRenormalized structure
  ; LessEqual = Polymer.LessEqual (Polymer.order estimate)
  ; irrelevantRemainderBound = Polymer.oneStepPolymerEstimate estimate
  }

concreteOneStepRGCertificate :
  ∀ {Field EffectiveAction PolymerCarrier Bound : Set} →
  OneStepRGStructure Field EffectiveAction →
  Polymer.OneStepPolymerEstimateData Field PolymerCarrier Bound →
  RG.OneStepRGCertificate Field EffectiveAction PolymerCarrier Bound
concreteOneStepRGCertificate structure estimate =
  RG.assembleOneStepRG (toOneStepRGInputs structure estimate)

------------------------------------------------------------------------
-- R1: unique fluctuation coordinates, including their Jacobian.
------------------------------------------------------------------------

record FluctuationCoordinateWitness
    (Background Fluctuation Jacobian : Set) : Set₁ where
  field
    background : Background
    fluctuation : Fluctuation
    coordinateJacobian : Jacobian

open FluctuationCoordinateWitness public

record FluctuationCoordinatesBijective
    (Field Background Fluctuation Jacobian : Set)
    (SmallFieldDomain : Field → Set)
    (reconstruct : Background → Fluctuation → Field)
    (jacobianOf : Background → Fluctuation → Jacobian) : Set₁ where
  field
    coordinates : ∀ field → SmallFieldDomain field →
      FluctuationCoordinateWitness Background Fluctuation Jacobian

    reconstructs : ∀ field small →
      reconstruct
        (background (coordinates field small))
        (fluctuation (coordinates field small))
      ≡ field

    jacobianCorrect : ∀ field small →
      jacobianOf
        (background (coordinates field small))
        (fluctuation (coordinates field small))
      ≡ coordinateJacobian (coordinates field small)

    backgroundUnique : ∀ field small background′ fluctuation′ →
      reconstruct background′ fluctuation′ ≡ field →
      background′ ≡ background (coordinates field small)

    fluctuationUnique : ∀ field small background′ fluctuation′ →
      reconstruct background′ fluctuation′ ≡ field →
      fluctuation′ ≡ fluctuation (coordinates field small)

open FluctuationCoordinatesBijective public

------------------------------------------------------------------------
-- R2--R7 and the exact quantitative R8 target.
------------------------------------------------------------------------

record ConcreteOneStepAnalyticData
    (Field Background Fluctuation Jacobian PolymerCarrier Bound
     GaugeTransform : Set) : Set₁ where
  field
    SmallFieldDomain : Field → Set
    reconstruct : Background → Fluctuation → Field
    jacobianOf : Background → Fluctuation → Jacobian

    fluctuationCoordinatesBijective :
      FluctuationCoordinatesBijective
        Field Background Fluctuation Jacobian
        SmallFieldDomain reconstruct jacobianOf

    order : Polymer.OrderedAdditiveBudget Bound
    polymerNorm : PolymerCarrier → Bound
    E : Nat → PolymerCarrier

    backgroundContribution : Nat → Bound
    jacobianContribution : Nat → Bound
    determinantContribution : Nat → Bound
    bchContribution : Nat → Bound
    localizationContribution : Nat → Bound

    backgroundBudget : Nat → Bound
    jacobianBudget : Nat → Bound
    determinantBudget : Nat → Bound
    bchBudget : Nat → Bound
    localizationBudget : Nat → Bound

    -- R2: Jacobian polymer estimate.
    jacobianContributionBound : ∀ k →
      Polymer.LessEqual order
        (jacobianContribution k) (jacobianBudget k)

    -- R3: determinant/local covariance expansion, polymer decay and tail.
    LogDetLocalExpansion : Set
    LogDetPolymerDecay : Set
    LogDetRemainderBound : Set
    logDetLocalExpansion : LogDetLocalExpansion
    logDetPolymerDecay : LogDetPolymerDecay
    logDetRemainderBound : LogDetRemainderBound
    determinantContributionBound : ∀ k →
      Polymer.LessEqual order
        (determinantContribution k) (determinantBudget k)

    -- R4: nonlinear minimizing-background substitution.
    backgroundSubstitutionEstimate : ∀ k →
      Polymer.LessEqual order
        (backgroundContribution k) (backgroundBudget k)

    -- R5: compact-Lie BCH/Taylor remainder in the RG norm.
    bchTaylorRemainderEstimate : ∀ k →
      Polymer.LessEqual order
        (bchContribution k) (bchBudget k)

    -- R6: localization of the nonlocal contribution.
    PolymerLocalizationStable : Set
    LocalizedRelevantPartBound : Set
    IrrelevantTaylorRemainderContractive : Set
    polymerLocalizationStable : PolymerLocalizationStable
    localizedRelevantPartBound : LocalizedRelevantPartBound
    irrelevantTaylorRemainderContractive :
      IrrelevantTaylorRemainderContractive
    localizationEstimate : ∀ k →
      Polymer.LessEqual order
        (localizationContribution k) (localizationBudget k)

    -- R7: Ward identities survive integration and localization.
    FluctuationIntegralGaugeInvariant : Set
    EffectiveActionWardIdentity : Set
    LocalizationPreservesWardIdentity : Set
    fluctuationIntegralGaugeInvariant :
      FluctuationIntegralGaugeInvariant
    effectiveActionWardIdentity : EffectiveActionWardIdentity
    localizationPreservesWardIdentity :
      LocalizationPreservesWardIdentity

    -- Exact decomposition into the five one-step contributions.
    outputBelowComponents : ∀ k →
      Polymer.LessEqual order
        (polymerNorm (E (suc k)))
        (Polymer.componentTotal order
          (backgroundContribution k)
          (jacobianContribution k)
          (determinantContribution k)
          (bchContribution k)
          (localizationContribution k))

    multiplyBound : Bound → Bound → Bound
    contractionFactor : Bound
    perturbativeError : Nat → Bound

    -- This is the quantitative C_G g_k^p budget domination.  In particular,
    -- the right side is not an opaque outputBound.
    componentBudgetsGiveContraction : ∀ k →
      Polymer.LessEqual order
        (Polymer.componentTotal order
          (backgroundBudget k)
          (jacobianBudget k)
          (determinantBudget k)
          (bchBudget k)
          (localizationBudget k))
        (Polymer.add order
          (multiplyBound contractionFactor (polymerNorm (E k)))
          (perturbativeError k))

open ConcreteOneStepAnalyticData public

componentEstimates :
  ∀ {F B Z J P R G} →
  (dataSet : ConcreteOneStepAnalyticData F B Z J P R G) →
  ∀ k →
  Polymer.LessEqual (order dataSet)
    (Polymer.componentTotal (order dataSet)
      (backgroundContribution dataSet k)
      (jacobianContribution dataSet k)
      (determinantContribution dataSet k)
      (bchContribution dataSet k)
      (localizationContribution dataSet k))
    (Polymer.componentTotal (order dataSet)
      (backgroundBudget dataSet k)
      (jacobianBudget dataSet k)
      (determinantBudget dataSet k)
      (bchBudget dataSet k)
      (localizationBudget dataSet k))
componentEstimates dataSet k =
  Polymer.componentsBelowBudget (order dataSet)
    (backgroundSubstitutionEstimate dataSet k)
    (jacobianContributionBound dataSet k)
    (determinantContributionBound dataSet k)
    (bchTaylorRemainderEstimate dataSet k)
    (localizationEstimate dataSet k)

-- R8: ||E_{k+1}|| <= contractionFactor * ||E_k|| + perturbativeError k.
oneStepPolymerContraction :
  ∀ {F B Z J P R G} →
  (dataSet : ConcreteOneStepAnalyticData F B Z J P R G) →
  ∀ k →
  Polymer.LessEqual (order dataSet)
    (polymerNorm dataSet (E dataSet (suc k)))
    (Polymer.add (order dataSet)
      (multiplyBound dataSet
        (contractionFactor dataSet)
        (polymerNorm dataSet (E dataSet k)))
      (perturbativeError dataSet k))
oneStepPolymerContraction dataSet k =
  Polymer.transitive (order dataSet)
    (outputBelowComponents dataSet k)
    (Polymer.transitive (order dataSet)
      (componentEstimates dataSet k)
      (componentBudgetsGiveContraction dataSet k))

record ConcreteOneStepRGCertificate
    (Field Background Fluctuation Jacobian PolymerCarrier Bound
     GaugeTransform : Set) : Set₁ where
  field
    analyticData : ConcreteOneStepAnalyticData
      Field Background Fluctuation Jacobian PolymerCarrier Bound
      GaugeTransform

  coordinatesValid :
    FluctuationCoordinatesBijective
      Field Background Fluctuation Jacobian
      (SmallFieldDomain analyticData)
      (reconstruct analyticData)
      (jacobianOf analyticData)
  coordinatesValid = fluctuationCoordinatesBijective analyticData

  contractionAtEveryScale : ∀ k →
    Polymer.LessEqual (order analyticData)
      (polymerNorm analyticData (E analyticData (suc k)))
      (Polymer.add (order analyticData)
        (multiplyBound analyticData
          (contractionFactor analyticData)
          (polymerNorm analyticData (E analyticData k)))
        (perturbativeError analyticData k))
  contractionAtEveryScale = oneStepPolymerContraction analyticData

open ConcreteOneStepRGCertificate public

assembleConcreteOneStepRG :
  ∀ {F B Z J P R G} →
  ConcreteOneStepAnalyticData F B Z J P R G →
  ConcreteOneStepRGCertificate F B Z J P R G
assembleConcreteOneStepRG analyticData = record { analyticData = analyticData }

concreteOneStepRGAssemblyLevel : ProofLevel
concreteOneStepRGAssemblyLevel = machineChecked

concreteOneStepRGAnalyticStructureLevel : ProofLevel
concreteOneStepRGAnalyticStructureLevel = conditional
