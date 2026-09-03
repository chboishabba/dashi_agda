module DASHI.Physics.QuantumVacuum.ZeroPointModeHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PURPOSE
--
-- Formalise zero-point energy without flattening field, boundary, mode,
-- Hamiltonian, state, and renormalisation coordinates into one scalar.
--
-- The exact finite spine is:
--
--   field/boundary base
--     -> admissible mode fibre
--     -> oscillator spectrum
--     -> ground-state receipt
--     -> zero-point assignment
--     -> finite vacuum aggregate
--
-- The QFT/renormalised observable is deliberately a later fibre.  In
-- particular, the raw finite or formal mode sum is not identified here with
-- a cosmological constant or with extractable work.
------------------------------------------------------------------------

record ScalarSpectrum : Set₁ where
  field
    Scalar : Set
    zero one half hbar : Scalar
    _+_ _*_ : Scalar → Scalar → Scalar
    _≤_ _<_ : Scalar → Scalar → Set
    fromNat : Nat → Scalar

    addZeroRight : (x : Scalar) → x + zero ≡ x
    mulZeroLeft  : (x : Scalar) → zero * x ≡ zero
    halfPositive : zero < half

open ScalarSpectrum public

record FieldBoundaryBase (S : ScalarSpectrum) : Set₁ where
  field
    Field : Set
    Boundary : Set
    Mode : Set

    field : Field
    boundary : Boundary

    admissible : Mode → Set
    frequency : Mode → Scalar S
    positiveFrequency : (k : Mode) → admissible k → zero S < frequency k

    baseReading : String

open FieldBoundaryBase public

------------------------------------------------------------------------
-- Each admissible mode carries its own oscillator fibre.
------------------------------------------------------------------------

record OscillatorModeFibre
    {S : ScalarSpectrum}
    (B : FieldBoundaryBase S)
    (k : Mode B)
    (ak : admissible B k) : Set₁ where
  field
    Occupation : Set
    groundOccupation : Occupation
    occupationNumber : Occupation → Nat

    Energy : Occupation → Scalar S

    spectrumLaw :
      (n : Occupation) →
      Energy n ≡
        (hbar S * frequency B k) *
        (fromNat S (occupationNumber n) + half S)

    groundOccupationIsZero :
      occupationNumber groundOccupation ≡ 0

open OscillatorModeFibre public

zeroPointEnergy :
  {S : ScalarSpectrum}
  {B : FieldBoundaryBase S}
  {k : Mode B}
  {ak : admissible B k} →
  OscillatorModeFibre B k ak →
  Scalar S
zeroPointEnergy {S} {B} {k} F =
  (hbar S * frequency B k) * half S

record ZeroPointFormulaReceipt
    {S : ScalarSpectrum}
    {B : FieldBoundaryBase S}
    {k : Mode B}
    {ak : admissible B k}
    (F : OscillatorModeFibre B k ak) : Set where
  field
    groundEnergyIsZeroPoint :
      Energy F (groundOccupation F) ≡ zeroPointEnergy F

open ZeroPointFormulaReceipt public

------------------------------------------------------------------------
-- Ground state is a spectral minimum, not merely occupation label zero.
------------------------------------------------------------------------

record GroundStateReceipt
    {S : ScalarSpectrum}
    {B : FieldBoundaryBase S}
    {k : Mode B}
    {ak : admissible B k}
    (F : OscillatorModeFibre B k ak) : Set where
  field
    groundMinimal :
      (n : Occupation F) →
      _≤_ S (Energy F (groundOccupation F)) (Energy F n)

open GroundStateReceipt public

record ExcitationEnergyModel
    {S : ScalarSpectrum}
    {B : FieldBoundaryBase S}
    {k : Mode B}
    {ak : admissible B k}
    (F : OscillatorModeFibre B k ak) : Set₁ where
  field
    ExcitationEnergy : Occupation F → Scalar S

    groundExcitationIsZero :
      ExcitationEnergy (groundOccupation F) ≡ zero S

    excitationSpectrumLaw :
      (n : Occupation F) →
      ExcitationEnergy n ≡
        fromNat S (occupationNumber F n) *
        (hbar S * frequency B k)

open ExcitationEnergyModel public

------------------------------------------------------------------------
-- Structural no-free-descent theorem.
--
-- Positive work from the isolated same-Hamiltonian ground state would require
-- a final state of strictly lower energy.  Ground minimality excludes exactly
-- that.  This theorem does not forbid work obtained after changing boundary,
-- Hamiltonian, coupling, external drive, or reservoir: those are different
-- hypervoxels and require separate accounting.
------------------------------------------------------------------------

record StrictOrderIrreflexiveAgainstLE (S : ScalarSpectrum) : Set₁ where
  field
    leAndLtImpossible :
      {x y : Scalar S} →
      _≤_ S x y →
      _<_ S y x →
      ⊥

open StrictOrderIrreflexiveAgainstLE public

record PositiveWorkFromGroundAlone
    {S : ScalarSpectrum}
    {B : FieldBoundaryBase S}
    {k : Mode B}
    {ak : admissible B k}
    (F : OscillatorModeFibre B k ak) : Set where
  field
    finalState : Occupation F
    finalStrictlyBelowGround :
      _<_ S
        (Energy F finalState)
        (Energy F (groundOccupation F))

open PositiveWorkFromGroundAlone public

groundStateBlocksPositiveWorkFromGroundAlone :
  {S : ScalarSpectrum} →
  (order : StrictOrderIrreflexiveAgainstLE S) →
  {B : FieldBoundaryBase S} →
  {k : Mode B} →
  {ak : admissible B k} →
  (F : OscillatorModeFibre B k ak) →
  GroundStateReceipt F →
  ¬ PositiveWorkFromGroundAlone F
groundStateBlocksPositiveWorkFromGroundAlone {S} order F ground claim =
  leAndLtImpossible order
    (groundMinimal ground (finalState claim))
    (finalStrictlyBelowGround claim)

------------------------------------------------------------------------
-- Finite vacuum hyperfabric.
------------------------------------------------------------------------

record ModePoint
    {S : ScalarSpectrum}
    (B : FieldBoundaryBase S) : Set₁ where
  field
    mode : Mode B
    admission : admissible B mode

open ModePoint public

record VacuumModeHypervoxel
    {S : ScalarSpectrum}
    (B : FieldBoundaryBase S) : Set₁ where
  field
    point : ModePoint B
    oscillator : OscillatorModeFibre B (mode point) (admission point)
    zeroPointReceipt : ZeroPointFormulaReceipt oscillator
    groundReceipt : GroundStateReceipt oscillator

open VacuumModeHypervoxel public

record FiniteVacuumHyperfabric (S : ScalarSpectrum) : Set₁ where
  field
    base : FieldBoundaryBase S
    Hypervoxel : Set
    realise : Hypervoxel → VacuumModeHypervoxel base
    finiteModes : List Hypervoxel

    aggregate : List Hypervoxel → Scalar S

    aggregateEmpty :
      aggregate [] ≡ zero S

    aggregateStep :
      (v : Hypervoxel) (vs : List Hypervoxel) →
      aggregate (v ∷ vs) ≡
        zeroPointEnergy (oscillator (realise v)) + aggregate vs

    fabricReading : String

open FiniteVacuumHyperfabric public

finiteVacuumEnergy :
  {S : ScalarSpectrum} →
  FiniteVacuumHyperfabric S →
  Scalar S
finiteVacuumEnergy H = aggregate H (finiteModes H)

------------------------------------------------------------------------
-- Boundary-dependent mode fabrics and non-factorability.
------------------------------------------------------------------------

record SameFieldDifferentBoundaryWitness
    {S : ScalarSpectrum}
    (left right : FiniteVacuumHyperfabric S) : Set₁ where
  field
    sameFieldType : Field (base left) ≡ Field (base right)
    sameFieldPoint :
      subst (λ F → F) sameFieldType (field (base left)) ≡ field (base right)

    boundariesDiffer :
      Boundary (base left) → Boundary (base right) → Set

    boundaryDifferenceHeld :
      boundariesDiffer (boundary (base left)) (boundary (base right))

    vacuumEnergiesDiffer : Set

open SameFieldDifferentBoundaryWitness public

-- The explicit witness type prevents vacuum energy from being represented as
-- a function of field identity alone.  Boundary/mode data are retained in the
-- hypervoxel rather than quotiented away.

record VacuumEnergyDoesNotFactorThroughFieldIdentity
    {S : ScalarSpectrum} : Set₁ where
  field
    left right : FiniteVacuumHyperfabric S
    witness : SameFieldDifferentBoundaryWitness left right

open VacuumEnergyDoesNotFactorThroughFieldIdentity public

------------------------------------------------------------------------
-- Renormalisation is a distinct fibre.
------------------------------------------------------------------------

record VacuumRenormalisationFibre
    {S : ScalarSpectrum}
    (H : FiniteVacuumHyperfabric S) : Set₁ where
  field
    RawVacuumExpression : Set
    Regulator : Set
    Scheme : Set
    Reference : Set
    Observable : Set

    rawExpression : RawVacuumExpression

    renormalise :
      RawVacuumExpression →
      Regulator →
      Scheme →
      Reference →
      Observable

    renormalisationReading : String

open VacuumRenormalisationFibre public

record CosmologicalCouplingBoundary : Set₁ where
  field
    RenormalisedVacuumObservable : Set
    StressEnergySemantics : Set
    GravityModel : Set
    CosmologicalObservable : Set

    coupleToGravity :
      RenormalisedVacuumObservable →
      StressEnergySemantics →
      GravityModel →
      CosmologicalObservable

    couplingReading : String

open CosmologicalCouplingBoundary public

------------------------------------------------------------------------
-- Explicit non-promotion flags for downstream consumers.
------------------------------------------------------------------------

rawModeSumIsRenormalisedPrediction : Bool
rawModeSumIsRenormalisedPrediction = false

zeroPointEnergyIsExtractableWorkByDefinition : Bool
zeroPointEnergyIsExtractableWorkByDefinition = false

rawModeSumIsCosmologicalConstantByDefinition : Bool
rawModeSumIsCosmologicalConstantByDefinition = false

rawModeSumIsRenormalisedPredictionIsFalse :
  rawModeSumIsRenormalisedPrediction ≡ false
rawModeSumIsRenormalisedPredictionIsFalse = refl

zeroPointEnergyIsExtractableWorkByDefinitionIsFalse :
  zeroPointEnergyIsExtractableWorkByDefinition ≡ false
zeroPointEnergyIsExtractableWorkByDefinitionIsFalse = refl

rawModeSumIsCosmologicalConstantByDefinitionIsFalse :
  rawModeSumIsCosmologicalConstantByDefinition ≡ false
rawModeSumIsCosmologicalConstantByDefinitionIsFalse = refl
