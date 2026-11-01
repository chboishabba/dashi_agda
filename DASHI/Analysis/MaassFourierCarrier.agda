module DASHI.Analysis.MaassFourierCarrier where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- The analytic owner for a weight-zero Maaß Fourier--Bessel candidate.
-- No connection to the normal-form operator in MaassRestorationShift is
-- intended or used here.

postulate
  Real    : Set
  Complex : Set

record ΓMaass : Set where
  field
    modularGroup          : String
    weight                : Nat
    characterDescription  : String
    laplaceConvention     : String
    parityDescription     : String
    spectralParameter     : Real
    fourierTruncation     : Nat
    sampleCount           : Nat
    horocycleHeight       : Real
    coefficientNormalisation : String
    automorphyGenerators  : String
    tailBoundDescription  : String

open ΓMaass public

record SpectralSeed (Γ : ΓMaass) : Set where
  field
    spectralParameterSeed : Real
    paritySeed            : String
    normalisationSeed     : String

record TruncatedFourierState (Γ : ΓMaass) : Set where
  field
    seed         : SpectralSeed Γ
    coefficients : Nat → Complex
    basisReading : String

record HorocycleSampleVector (Γ : ΓMaass) : Set where
  field
    samples       : Nat → Complex
    sampleReading : String

record RecoveredCoefficientVector (Γ : ΓMaass) : Set where
  field
    recovered       : Nat → Complex
    recoveryReading : String

record AutomorphyComparison (Γ : ΓMaass) : Set where
  field
    generatorReading : String
    comparisonReading : String

-- These maps name the mathematical operations.  Implementations must later
-- supply a concrete complex/interval carrier and Bessel-K evaluation.
postulate
  fourierExpand        : ∀ {Γ} → SpectralSeed Γ → TruncatedFourierState Γ
  horocycleSample      : ∀ {Γ} → TruncatedFourierState Γ → HorocycleSampleVector Γ
  rootsOfUnityRecover  : ∀ {Γ} → HorocycleSampleVector Γ → RecoveredCoefficientVector Γ
  pullbackByGenerator  : ∀ {Γ} → TruncatedFourierState Γ → AutomorphyComparison Γ

