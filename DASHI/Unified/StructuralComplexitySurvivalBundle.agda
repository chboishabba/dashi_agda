module DASHI.Unified.StructuralComplexitySurvivalBundle where

open import DASHI.Foundations.SpectralCountingComplexity public
open import DASHI.Foundations.FiniteSpectralCountingInstance public
open import DASHI.Foundations.DivergenceComparisonPackage public
open import DASHI.Foundations.FiniteDiracDivergenceInstance public
open import DASHI.Physics.NavierStokes.DissipationNullComputationalCarrier public
open import DASHI.Algebra.Quantum.BraKet public
open import DASHI.Algebra.Quantum.TernaryCircuit public
open import DASHI.Algebra.Quantum.QutritAmplitude public
open import DASHI.Algebra.Quantum.QutritUnitaryBridge public
open import DASHI.Promotion.FiniteTernaryQuantumCircuitAdapter public

------------------------------------------------------------------------
-- Shared boundary: contraction, dissipation, or compression in one typed
-- defect does not by itself collapse spectral, computational, or operational
-- complexity measured by a different carrier.

data ComplexityCarrierKind : Set where
  spectralCapacity : ComplexityCarrierKind
  harmonicComputation : ComplexityCarrierKind
  divergenceOperationalMeaning : ComplexityCarrierKind
  finiteQutritPermutation : ComplexityCarrierKind
  amplitudeQutrit : ComplexityCarrierKind

record TypedComplexitySeparation : Set₁ where
  field
    Carrier : ComplexityCarrierKind → Set
    compressedCarrier : ComplexityCarrierKind
    survivingCarrier : ComplexityCarrierKind
    compressionPredicate : Carrier compressedCarrier → Set
    survivalPredicate : Carrier survivingCarrier → Set
    witnessCompressed : Carrier compressedCarrier
    witnessSurviving : Carrier survivingCarrier
    compressionHolds : compressionPredicate witnessCompressed
    survivalHolds : survivalPredicate witnessSurviving

open TypedComplexitySeparation public
