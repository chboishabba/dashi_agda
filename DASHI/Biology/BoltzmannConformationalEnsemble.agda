module DASHI.Biology.BoltzmannConformationalEnsemble where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using
  ( Float
  ; primFloatPlus
  ; primFloatTimes
  ; primFloatDiv
  ; primFloatNegate
  ; primFloatExp
  ; primFloatLog
  ; primFloatLess
  )
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Biology.ConcreteProteinMolecularMechanics

------------------------------------------------------------------------
-- Finite conformational ensembles.
--
-- A literal finite list replaces the continuum integral.  This is executable
-- and useful for finite sampling, but convergence to a continuum or equilibrium
-- ensemble remains a separate theorem/evidence obligation.

record ThermodynamicParameters : Set where
  constructor thermodynamicParameters
  field
    inverseTemperature : Float
    boltzmannConstant : Float
    temperature : Float

open ThermodynamicParameters public

record WeightedConformation : Set where
  constructor weightedConformation
  field
    conformation : ProteinConfiguration
    quadratureWeight : Float

open WeightedConformation public

boltzmannFactor :
  ThermodynamicParameters →
  ProteinConfiguration →
  Float
boltzmannFactor p c =
  primFloatExp
    (primFloatNegate
      (inverseTemperature p *f concreteTotalPotential c))

weightedBoltzmannFactor :
  ThermodynamicParameters →
  WeightedConformation →
  Float
weightedBoltzmannFactor p w =
  quadratureWeight w *f boltzmannFactor p (conformation w)

finitePartitionFunction :
  ThermodynamicParameters →
  List WeightedConformation →
  Float
finitePartitionFunction p ensemble =
  sumBy (weightedBoltzmannFactor p) ensemble

finiteProbability :
  ThermodynamicParameters →
  List WeightedConformation →
  WeightedConformation →
  Float
finiteProbability p ensemble w =
  weightedBoltzmannFactor p w /f
  finitePartitionFunction p ensemble

mapWeightedProbability :
  ThermodynamicParameters →
  List WeightedConformation →
  List WeightedConformation →
  List Float
mapWeightedProbability p all [] = []
mapWeightedProbability p all (w ∷ ws) =
  finiteProbability p all w ∷ mapWeightedProbability p all ws

finiteProbabilities :
  ThermodynamicParameters →
  List WeightedConformation →
  List Float
finiteProbabilities p ensemble =
  mapWeightedProbability p ensemble ensemble

finiteHelmholtzFreeEnergy :
  ThermodynamicParameters →
  List WeightedConformation →
  Float
finiteHelmholtzFreeEnergy p ensemble =
  primFloatNegate
    (boltzmannConstant p *f temperature p *f
     primFloatLog (finitePartitionFunction p ensemble))

partitionFunctionDefinition :
  (p : ThermodynamicParameters) →
  (ensemble : List WeightedConformation) →
  finitePartitionFunction p ensemble ≡
  sumBy (weightedBoltzmannFactor p) ensemble
partitionFunctionDefinition p ensemble = refl

probabilityDefinition :
  (p : ThermodynamicParameters) →
  (ensemble : List WeightedConformation) →
  (w : WeightedConformation) →
  finiteProbability p ensemble w ≡
  weightedBoltzmannFactor p w /f finitePartitionFunction p ensemble
probabilityDefinition p ensemble w = refl

freeEnergyDefinition :
  (p : ThermodynamicParameters) →
  (ensemble : List WeightedConformation) →
  finiteHelmholtzFreeEnergy p ensemble ≡
  primFloatNegate
    (boltzmannConstant p *f temperature p *f
     primFloatLog (finitePartitionFunction p ensemble))
freeEnergyDefinition p ensemble = refl

------------------------------------------------------------------------
-- Finite expectations.

record Observable : Set where
  constructor observable
  field
    evaluate : ProteinConfiguration → Float

open Observable public

weightedObservableTerm :
  ThermodynamicParameters →
  List WeightedConformation →
  Observable →
  WeightedConformation →
  Float
weightedObservableTerm p ensemble observable w =
  finiteProbability p ensemble w *f
  evaluate observable (conformation w)

finiteExpectation :
  ThermodynamicParameters →
  List WeightedConformation →
  Observable →
  Float
finiteExpectation p ensemble observable =
  sumBy (weightedObservableTerm p ensemble observable) ensemble

potentialEnergyObservable : Observable
potentialEnergyObservable = observable concreteTotalPotential

meanPotentialEnergy :
  ThermodynamicParameters →
  List WeightedConformation →
  Float
meanPotentialEnergy p ensemble =
  finiteExpectation p ensemble potentialEnergyObservable

------------------------------------------------------------------------
-- Sampling and numerical validity boundaries.

record FiniteEnsembleValidationBoundary : Set where
  field
    nonemptyEnsemble : Bool
    positiveQuadratureWeights : Bool
    positiveTemperature : Bool
    positiveBoltzmannConstant : Bool
    positivePartitionFunction : Bool
    finiteEnergyValues : Bool
    finiteExponentialValues : Bool
    normalizedWithinTolerance : Bool
    normalizationTolerance : Float
    effectiveSampleSize : Float
    independentSampleCount : Nat
    samplingConverged : Bool
    metastableBasinsCovered : Bool
    continuumQuadratureErrorBound : Float
    floatingPointErrorBound : Float

open FiniteEnsembleValidationBoundary public

record EnsembleConvergenceCertificate : Set where
  field
    sampleCount : Nat
    energyMeanErrorBound : Float
    observableErrorBound : Float
    partitionFunctionRelativeErrorBound : Float
    freeEnergyAbsoluteErrorBound : Float
    autocorrelationControlled : Bool
    burnInRemoved : Bool
    convergenceAcrossIndependentChains : Bool

open EnsembleConvergenceCertificate public

------------------------------------------------------------------------
-- Explicit separation between finite sampled Z and the continuum integral.

record ContinuumPartitionBridge : Set₁ where
  field
    ContinuumConfiguration : Set
    continuumEnergy : ContinuumConfiguration → Float
    continuumPartitionValue : Float
    finiteApproximation : List WeightedConformation
    finiteApproximatesContinuum : Bool
    absoluteApproximationError : Float
    relativeApproximationError : Float

open ContinuumPartitionBridge public
