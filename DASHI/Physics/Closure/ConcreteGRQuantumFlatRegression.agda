module DASHI.Physics.Closure.ConcreteGRQuantumFlatRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

import Base369 as B369
import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Geometry.ValuationConformalMetricCandidate as ValuationMetric
import DASHI.Physics.Closure.FiniteQuantumGRFlatModel as Quantum
import DASHI.Physics.Closure.QuantumGRActionCompatibilityBoundary as Boundary
import DASHI.Physics.Closure.SymbolicEinsteinHilbertModel as EH
import DASHI.Physics.Closure.TypedStressEnergyMassBridge as Source

------------------------------------------------------------------------
-- Compact proposition-level regression surface for the concrete model tranche.

flatTimeSignatureRegression :
  Flat.signature13 Flat.timeAxis ≡ Flat.timelikeSign
flatTimeSignatureRegression = Flat.timeIsTimelike

flatSpatialSignatureRegression :
  Flat.signature13 Flat.zAxis ≡ Flat.spacelikeSign
flatSpatialSignatureRegression = Flat.zIsSpacelike

flatTimeUniquenessRegression :
  (a : Flat.Axis4) →
  Flat.signature13 a ≡ Flat.timelikeSign →
  a ≡ Flat.timeAxis
flatTimeUniquenessRegression = Flat.timelikeDirectionIsUnique

flatMetricNondegeneracyRegression :
  (a : Flat.Axis4) →
  Flat.NonZeroMetricEntry (Flat.flatMetricEntry a a)
flatMetricNondegeneracyRegression = Flat.diagonalEntryNonzero

valuationMetricUnderdeterminationRegression :
  ValuationMetric.ValuationMetricUnderdeterminationReceipt
valuationMetricUnderdeterminationRegression =
  ValuationMetric.valuationMetricUnderdeterminationReceipt

flatConnectionTorsionRegression :
  Flat.TorsionFree Flat.flatConnection
flatConnectionTorsionRegression = Flat.flatConnectionTorsionFree

flatConnectionCompatibilityRegression :
  Flat.MetricCompatibleWithFlatMetric Flat.flatConnection
flatConnectionCompatibilityRegression = Flat.flatConnectionMetricCompatible

symbolicRicciVariationRegression :
  EH.varyInvariant EH.ricciScalarDensity ≡ EH.EinsteinTensorTerm
symbolicRicciVariationRegression = EH.ricciVariationIsEinstein

symbolicBoundaryVariationRegression :
  EH.varyInvariant EH.boundaryDivergence ≡ EH.zeroBulkBoundaryTerm
symbolicBoundaryVariationRegression = EH.boundaryVariationHasNoBulkTerm

flatEinsteinVacuumRegression :
  (a b : Flat.Axis4) → EH.flatEinsteinTensor a b ≡ B369.tri-mid
flatEinsteinVacuumRegression = EH.flatEinsteinIsZero

zeroStressSymmetryRegression :
  Source.SymmetricTensor Source.zeroTensor
zeroStressSymmetryRegression = Source.zeroTensorSymmetric

zeroDefectStressRegression :
  Source.ZeroTensor
    (Source.stressFromDefectRequiresCoupling
      Source.zeroDefectEnergy
      Source.zeroVacuumDefectCoupling)
zeroDefectStressRegression = Source.zeroVacuumCoupledStressIsZero

zeroMassRegression :
  Source.activeAmount
    (Source.activeMassFromDefectRequiresWitness
      Source.zeroDefectEnergy
      Source.zeroMassIdentificationWitness)
  ≡ zero
zeroMassRegression = refl

quantumCompositionRegression :
  Quantum.historyAmplitude
    (Quantum.composeHistory Quantum.vacuumHistory Quantum.vacuumHistory)
  ≡ B369.triXor
      (Quantum.historyAmplitude Quantum.vacuumHistory)
      (Quantum.historyAmplitude Quantum.vacuumHistory)
quantumCompositionRegression =
  Quantum.amplitudeRespectsComposition
    Quantum.vacuumHistory
    Quantum.vacuumHistory

jointFlatInterfaceRegression : Quantum.FlatQuantumGRInterfaceReceipt
jointFlatInterfaceRegression = Quantum.flatQuantumGRInterfaceReceipt

unificationStillBlockedRegression :
  Boundary.quantumGRUnificationProved
    Boundary.canonicalUnificationPromotionBoundary
  ≡ false
unificationStillBlockedRegression = Boundary.canonicalQuantumGRUnificationBlocked

theoryOfEverythingStillBlockedRegression :
  Boundary.theoryOfEverythingPromotionPermitted
    Boundary.canonicalUnificationPromotionBoundary
  ≡ false
theoryOfEverythingStillBlockedRegression = Boundary.canonicalTheoryOfEverythingBlocked
