module DASHI.Physics.YangMills.BalabanClayT5LpUniformIntegrabilityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS

------------------------------------------------------------------------
-- Generic L^p and de la Vallee Poussin uniform-integrability route.
--
-- Tapas Kumar Chandra,
-- "de La Vallee Poussin's theorem, uniform integrability, tightness and moments",
-- Statistics & Probability Letters 107 (2015), 136--141.
-- DOI: 10.1016/j.spl.2015.08.011.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- The physical route is deliberately:
--
--   marked exponential moments
--     -> selected polynomial moments of each factor
--     -> Holder/Young L^(1+delta) bound for the reflected product
--     -> direct L^p-bounded (p>1) uniform integrability
--     -> weak-limit expectation convergence and OS-Gram continuity.
--
-- A general de la Vallee Poussin authority remains available with G(t)=t^p,
-- but it does not replace the product estimate: it consumes the product moment
-- after the Holder/Young bridge has been proved.
------------------------------------------------------------------------

record UniformLpMoment
    (Measure Observable Scalar Exponent : Set)
    (operations : Gram.PhysicalOSOperations Measure Observable Scalar)
    (measureSequence : Nat → Measure)
    (absoluteObservable : Observable → Observable)
    (powerObservable : Exponent → Observable → Observable)
    (LessEqual : Scalar → Scalar → Set)
    (exponent : Exponent)
    (observable : Observable) : Set₁ where
  field
    bound : Scalar
    uniformBound : ∀ cutoff →
      LessEqual
        (Gram.expectation operations (measureSequence cutoff)
          (powerObservable exponent (absoluteObservable observable)))
        bound

open UniformLpMoment public

record ExponentialToPolynomialMomentAuthority
    (Measure Observable Scalar Exponent : Set)
    (operations : Gram.PhysicalOSOperations Measure Observable Scalar)
    (measureSequence : Nat → Measure)
    (absoluteObservable : Observable → Observable)
    (powerObservable : Exponent → Observable → Observable)
    (LessEqual : Scalar → Scalar → Set)
    (Admissible : Observable → Set) : Set₁ where
  field
    exponentialMomentBound : Observable → Set
    selectedMoment : (exponent : Exponent) → (observable : Observable) →
      UniformLpMoment Measure Observable Scalar Exponent
        operations measureSequence absoluteObservable powerObservable LessEqual
        exponent observable
    exponentialImpliesSelectedMoment :
      (exponent : Exponent) → (observable : Observable) →
      Admissible observable → exponentialMomentBound observable → Set

open ExponentialToPolynomialMomentAuthority public

record ReflectedProductHolderAuthority
    (Measure Observable Scalar Exponent : Set)
    (operations : Gram.PhysicalOSOperations Measure Observable Scalar)
    (measureSequence : Nat → Measure)
    (absoluteObservable : Observable → Observable)
    (powerObservable : Exponent → Observable → Observable)
    (LessEqual : Scalar → Scalar → Set) : Set₁ where
  field
    p doubleP : Exponent
    pGreaterThanOne : Set
    doublePIsTwiceP : Set

    reflectedProductMoment : ∀ left right →
      UniformLpMoment Measure Observable Scalar Exponent
        operations measureSequence absoluteObservable powerObservable LessEqual
        doubleP left →
      UniformLpMoment Measure Observable Scalar Exponent
        operations measureSequence absoluteObservable powerObservable LessEqual
        doubleP right →
      UniformLpMoment Measure Observable Scalar Exponent
        operations measureSequence absoluteObservable powerObservable LessEqual
        p
        (Gram.multiplyObservable operations
          (Gram.reflectObservable operations left) right)

    holderOrYoungProof : (left right : Observable) → Set

open ReflectedProductHolderAuthority public

record LpUniformIntegrabilityAuthority
    (Measure Observable Scalar Exponent : Set)
    (operations : Gram.PhysicalOSOperations Measure Observable Scalar)
    (measureSequence : Nat → Measure)
    (absoluteObservable : Observable → Observable)
    (powerObservable : Exponent → Observable → Observable)
    (LessEqual : Scalar → Scalar → Set)
    (UniformlyIntegrable : (Nat → Observable) → Set) : Set₁ where
  field
    GreaterThanOne : Exponent → Set
    lpBoundedImpliesUniformlyIntegrable : ∀ exponent observable →
      GreaterThanOne exponent →
      UniformLpMoment Measure Observable Scalar Exponent
        operations measureSequence absoluteObservable powerObservable LessEqual
        exponent observable →
      UniformlyIntegrable (λ _ → observable)
    holderChebyshevTailModulus :
      (exponent : Exponent) → (observable : Observable) → Set

open LpUniformIntegrabilityAuthority public

record DeLaValleePoussinAuthority
    (Measure Observable Scalar : Set)
    (operations : Gram.PhysicalOSOperations Measure Observable Scalar)
    (measureSequence : Nat → Measure)
    (absoluteObservable : Observable → Observable)
    (UniformlyIntegrable : (Nat → Observable) → Set) : Set₁ where
  field
    YoungFunction : Set
    applyYoung : YoungFunction → Observable → Observable
    increasing : YoungFunction → Set
    convex : YoungFunction → Set
    superlinear : YoungFunction → Set
    uniformlyBoundedYoungMoment : YoungFunction → Observable → Set
    criterion : ∀ young observable →
      increasing young → convex young → superlinear young →
      uniformlyBoundedYoungMoment young observable →
      UniformlyIntegrable (λ _ → observable)

open DeLaValleePoussinAuthority public

record PowerYoungFunctionRoute
    (Measure Observable Scalar Exponent : Set)
    (operations : Gram.PhysicalOSOperations Measure Observable Scalar)
    (measureSequence : Nat → Measure)
    (absoluteObservable : Observable → Observable)
    (powerObservable : Exponent → Observable → Observable)
    (LessEqual : Scalar → Scalar → Set)
    (UniformlyIntegrable : (Nat → Observable) → Set)
    (deLaValleePoussin :
      DeLaValleePoussinAuthority
        Measure Observable Scalar operations measureSequence
        absoluteObservable UniformlyIntegrable) : Set₁ where
  field
    exponent : Exponent
    exponentGreaterThanOne : Set
    powerYoungFunction : YoungFunction deLaValleePoussin
    powerYoungFunctionIncreasing : increasing deLaValleePoussin powerYoungFunction
    powerYoungFunctionConvex : convex deLaValleePoussin powerYoungFunction
    powerYoungFunctionSuperlinear : superlinear deLaValleePoussin powerYoungFunction
    lpMomentSuppliesYoungMoment : ∀ observable →
      UniformLpMoment Measure Observable Scalar Exponent
        operations measureSequence absoluteObservable powerObservable LessEqual
        exponent observable →
      uniformlyBoundedYoungMoment deLaValleePoussin powerYoungFunction observable

open PowerYoungFunctionRoute public

powerMomentImpliesUniformIntegrability :
  ∀ {Measure Observable Scalar Exponent operations measureSequence
      absoluteObservable powerObservable LessEqual UniformlyIntegrable
      deLaValleePoussin}
    (route : PowerYoungFunctionRoute
      Measure Observable Scalar Exponent operations measureSequence
      absoluteObservable powerObservable LessEqual UniformlyIntegrable
      deLaValleePoussin)
    observable →
  UniformLpMoment Measure Observable Scalar Exponent
    operations measureSequence absoluteObservable powerObservable LessEqual
    (exponent route) observable →
  UniformlyIntegrable (λ _ → observable)
powerMomentImpliesUniformIntegrability
  {deLaValleePoussin = deLaValleePoussin} route observable moment =
  criterion deLaValleePoussin
    (powerYoungFunction route)
    observable
    (powerYoungFunctionIncreasing route)
    (powerYoungFunctionConvex route)
    (powerYoungFunctionSuperlinear route)
    (lpMomentSuppliesYoungMoment route observable moment)

------------------------------------------------------------------------
-- Adapter to the already-existing DASHI thermodynamic and OS-Gram lanes.
------------------------------------------------------------------------

record PhysicalLpUniformIntegrabilityRoute
    {Measure Observable Scalar : Set}
    (operations : Gram.PhysicalOSOperations Measure Observable Scalar)
    (measureSequence : Nat → Measure)
    (RenormalizedObservable : Observable → Set)
    (moments : Thermo.ExponentialMomentProducer
      operations measureSequence RenormalizedObservable) : Set₁ where
  field
    Exponent : Set
    LessEqual : Scalar → Scalar → Set
    absoluteObservable : Observable → Observable
    powerObservable : Exponent → Observable → Observable

    polynomialMoments :
      ExponentialToPolynomialMomentAuthority
        Measure Observable Scalar Exponent operations measureSequence
        absoluteObservable powerObservable LessEqual RenormalizedObservable

    holder :
      ReflectedProductHolderAuthority
        Measure Observable Scalar Exponent operations measureSequence
        absoluteObservable powerObservable LessEqual

    UniformlyIntegrable : (Nat → Observable) → Set
    lpAuthority :
      LpUniformIntegrabilityAuthority
        Measure Observable Scalar Exponent operations measureSequence
        absoluteObservable powerObservable LessEqual UniformlyIntegrable

    factorMomentFromMarkedExponential : ∀ observable →
      RenormalizedObservable observable →
      UniformLpMoment Measure Observable Scalar Exponent
        operations measureSequence absoluteObservable powerObservable LessEqual
        (doubleP holder) observable

    pRecognizedGreaterThanOne : GreaterThanOne lpAuthority (p holder)

    deLaValleePoussin :
      DeLaValleePoussinAuthority
        Measure Observable Scalar operations measureSequence
        absoluteObservable UniformlyIntegrable

    powerYoungRoute :
      PowerYoungFunctionRoute
        Measure Observable Scalar Exponent operations measureSequence
        absoluteObservable powerObservable LessEqual UniformlyIntegrable
        deLaValleePoussin

    directLpAndPowerYoungRoutesAgree :
      (left right : Observable) → Set

    witnessFromLpRoute : ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      Thermo.UniformIntegrabilityWitness Observable Scalar
        (λ cutoff → Gram.multiplyObservable operations
          (Gram.reflectObservable operations left) right)

open PhysicalLpUniformIntegrabilityRoute public

reflectedProductMomentFromFactorMoments :
  ∀ {Measure Observable Scalar operations measureSequence RenormalizedObservable moments}
    (route : PhysicalLpUniformIntegrabilityRoute
      operations measureSequence RenormalizedObservable moments)
    left right →
  RenormalizedObservable left → RenormalizedObservable right →
  UniformLpMoment Measure Observable Scalar (Exponent route)
    operations measureSequence
    (absoluteObservable route) (powerObservable route) (LessEqual route)
    (p (holder route))
    (Gram.multiplyObservable operations
      (Gram.reflectObservable operations left) right)
reflectedProductMomentFromFactorMoments route left right leftAdmissible rightAdmissible =
  reflectedProductMoment (holder route) left right
    (factorMomentFromMarkedExponential route left leftAdmissible)
    (factorMomentFromMarkedExponential route right rightAdmissible)

reflectedProductUniformlyIntegrableFromLp :
  ∀ {Measure Observable Scalar operations measureSequence RenormalizedObservable moments}
    (route : PhysicalLpUniformIntegrabilityRoute
      operations measureSequence RenormalizedObservable moments)
    left right →
  RenormalizedObservable left → RenormalizedObservable right →
  UniformlyIntegrable route
    (λ _ → Gram.multiplyObservable operations
      (Gram.reflectObservable operations left) right)
reflectedProductUniformlyIntegrableFromLp route left right leftAdmissible rightAdmissible =
  lpBoundedImpliesUniformlyIntegrable (lpAuthority route)
    (p (holder route))
    (Gram.multiplyObservable operations (Gram.reflectObservable operations left) right)
    (pRecognizedGreaterThanOne route)
    (reflectedProductMomentFromFactorMoments route left right
      leftAdmissible rightAdmissible)

record LpExpectationProducerUpgrade
    {Measure Observable Scalar : Set}
    (producer : Thermo.PhysicalExpectationProducerData Measure Observable Scalar) : Set₁ where
  field
    lpRoute :
      PhysicalLpUniformIntegrabilityRoute
        (Thermo.operations (Thermo.thermodynamic producer))
        (Thermo.diagonalMeasure producer)
        (Thermo.RenormalizedObservable (Thermo.thermodynamic producer))
        (Thermo.moments producer)

    uiPredicatesAgree : ∀ sequence →
      UniformlyIntegrable lpRoute sequence →
      Thermo.UniformlyIntegrable producer sequence

    reflectedProductWitnessIsLpDerived :
      (left right : Observable) → Set

open LpExpectationProducerUpgrade public

lpRoutePhysicalMeasureConvergenceData :
  ∀ {Measure Observable Scalar}
    {producer : Thermo.PhysicalExpectationProducerData Measure Observable Scalar} →
  LpExpectationProducerUpgrade producer →
  Gram.PhysicalMeasureConvergenceData Measure Observable Scalar
lpRoutePhysicalMeasureConvergenceData {producer = producer} upgrade =
  Thermo.physicalMeasureConvergenceDataFromProducer producer

record LpRouteOSGramAdapter
    {Measure Observable Scalar : Set}
    {producer : Thermo.PhysicalExpectationProducerData Measure Observable Scalar}
    (upgrade : LpExpectationProducerUpgrade producer) : Set₁ where
  field
    gramData : Gram.PhysicalMeasureToOSGramData Measure Observable Scalar
    convergenceDataIsLpRoute :
      Gram.convergenceData gramData
      ≡ lpRoutePhysicalMeasureConvergenceData upgrade

open LpRouteOSGramAdapter public

lpUniformIntegrabilityFeedsOSGram :
  ∀ {Measure Observable Scalar producer upgrade}
    (adapter : LpRouteOSGramAdapter
      {Measure} {Observable} {Scalar} {producer} upgrade) →
  OS.OSGramLimitData Measure
    (Gram.TestFamily (gramData adapter)) Scalar
lpUniformIntegrabilityFeedsOSGram adapter =
  Gram.physicalMeasureTopologyControlsOSGram (gramData adapter)

lpHolderReductionLevel : ProofLevel
lpHolderReductionLevel = machineChecked

powerYoungFunctionReductionLevel : ProofLevel
powerYoungFunctionReductionLevel = machineChecked

lpToPhysicalMeasureAdapterLevel : ProofLevel
lpToPhysicalMeasureAdapterLevel = machineChecked

lpToOSGramAdapterLevel : ProofLevel
lpToOSGramAdapterLevel = machineChecked

physicalSelectedMomentInputsLevel : ProofLevel
physicalSelectedMomentInputsLevel = conditional

physicalHolderAndUniformIntegrabilityInputsLevel : ProofLevel
physicalHolderAndUniformIntegrabilityInputsLevel = conditional
