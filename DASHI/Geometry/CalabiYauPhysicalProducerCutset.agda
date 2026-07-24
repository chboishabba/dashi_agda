module DASHI.Geometry.CalabiYauPhysicalProducerCutset where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

import DASHI.Geometry.CalabiYau as CY
import DASHI.Geometry.CalabiYau369CompactFibreBridge as Bridge

record ConcreteCompactCalabiYau : Set₁ where
  field
    Point Coordinate RealScalar : Set
    Tangent : Point → Set
    IntegralCohomology2 TopForm : Set
    ExtendedPoint TotalPoint : Set
    authority :
      CY.CalabiYauAuthority
        Point Coordinate RealScalar Tangent IntegralCohomology2 TopForm
    dimensionBridge :
      Bridge.CalabiYau369Bridge
        Point Coordinate RealScalar Tangent IntegralCohomology2 TopForm
        ExtendedPoint TotalPoint
    definingEquationReceipt chartReceipt compactnessReceipt : String
    hodgeNumberReceipt intersectionReceipt chernClassReceipt : String
    discreteSymmetryReceipt : String

open ConcreteCompactCalabiYau public

record RicciFlatMetricAuthority (model : ConcreteCompactCalabiYau) : Set₁ where
  field
    Metric : Set
    metric : Metric
    kahlerClassReceipt ricciFlatReceipt uniquenessReceipt : String
    exactClosedFormAvailable : Bool

open RicciFlatMetricAuthority public

record ModuliStabilizationAuthority (model : ConcreteCompactCalabiYau) : Set₁ where
  field
    Modulus FluxData Potential : Set
    selectedModuli : List Modulus
    fluxData : FluxData
    potential : Potential
    stableMinimumReceipt : String

open ModuliStabilizationAuthority public

record DimensionalReductionAuthority (model : ConcreteCompactCalabiYau) : Set₁ where
  field
    InternalMode EffectiveField EffectiveAction : Set
    modeBasis : List InternalMode
    reduceMode : InternalMode → EffectiveField
    effectiveAction : EffectiveAction
    normalisationReceipt fibreIntegrationReceipt : String

open DimensionalReductionAuthority public

record EffectiveSpectrumAuthority (model : ConcreteCompactCalabiYau) : Set₁ where
  field
    State Mass Coupling : Set
    states : List State
    massOf : State → Mass
    couplingOf : State → State → State → Coupling
    spectrumReceipt symmetryBreakingReceipt : String

open EffectiveSpectrumAuthority public

record PhysicalCouplingAuthority
    (model : ConcreteCompactCalabiYau)
    (spectrum : EffectiveSpectrumAuthority model) : Set₁ where
  field
    CouplingValue : Set
    fibreOverlap :
      State spectrum → State spectrum → State spectrum → CouplingValue
    fibreIntegralReceipt normalisationReceipt physicalUnitReceipt : String

open PhysicalCouplingAuthority public

record AnomalyCancellationAuthority (model : ConcreteCompactCalabiYau) : Set₁ where
  field
    GaugeBundle AnomalyClass : Set
    gaugeBundle : GaugeBundle
    anomalyClass : AnomalyClass
    cancellationReceipt : String

open AnomalyCancellationAuthority public

record ObservationalPredictionAuthority (model : ConcreteCompactCalabiYau) : Set₁ where
  field
    Prediction Observable : Set
    candidatePredictions : List Prediction
    observableProjection : Prediction → Observable
    empiricalBridgeReceipt : String

open ObservationalPredictionAuthority public

record PhysicalCompactificationChain : Set₁ where
  field
    model : ConcreteCompactCalabiYau
    ricciFlat : RicciFlatMetricAuthority model
    stabilization : ModuliStabilizationAuthority model
    reduction : DimensionalReductionAuthority model
    spectrum : EffectiveSpectrumAuthority model
    couplings : PhysicalCouplingAuthority model spectrum
    anomalyCancellation : AnomalyCancellationAuthority model
    predictionAuthority : ObservationalPredictionAuthority model
    chainReceipt : String

open PhysicalCompactificationChain public

record CalabiYauPhysicalBoundary : Set where
  constructor calabiYauPhysicalBoundary
  field
    dimensionIdentitySuppliesPhysicalModel : Bool
    dimensionIdentitySuppliesPhysicalModelIsFalse :
      dimensionIdentitySuppliesPhysicalModel ≡ false
    structuralBridgeSuppliesObservationalPrediction : Bool
    structuralBridgeSuppliesObservationalPredictionIsFalse :
      structuralBridgeSuppliesObservationalPrediction ≡ false

canonicalCalabiYauPhysicalBoundary : CalabiYauPhysicalBoundary
canonicalCalabiYauPhysicalBoundary =
  calabiYauPhysicalBoundary false refl false refl
