module DASHI.Physics.BianchiLovelockCompletion where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.FiniteToContinuumGeometry as FCG

------------------------------------------------------------------------
-- Typed Bianchi/Lovelock completion over the continuum bridge.

record EinsteinTensorData (G : FCG.ContinuumGeometry) : Set₁ where
  open FCG.ContinuumGeometry G
  field
    zeroScalar : Scalar
    EinsteinTensor : Tensor2
    StressEnergy   : Tensor2
    divergence    : Tensor2 → Scalar
    symmetric     : Tensor2 → Set
    secondOrder   : Tensor2 → Set
    natural       : Tensor2 → Set

record BianchiLovelockClosure
  (G : FCG.ContinuumGeometry)
  (E : EinsteinTensorData G) : Set₁ where
  open FCG.ContinuumGeometry G
  open EinsteinTensorData E

  field
    contractedBianchi : divergence EinsteinTensor ≡ zeroScalar
    einsteinSymmetric : symmetric EinsteinTensor
    einsteinSecondOrder : secondOrder EinsteinTensor
    einsteinNatural : natural EinsteinTensor

    fieldEquation : EinsteinTensor ≡ StressEnergy

    -- Lovelock uniqueness is stated extensionally: every natural, symmetric,
    -- divergence-free, second-order candidate equals the Einstein tensor.
    lovelockUnique :
      ∀ X →
      symmetric X →
      secondOrder X →
      natural X →
      divergence X ≡ zeroScalar →
      X ≡ EinsteinTensor

record EinsteinContinuumClosure : Set₁ where
  field
    lorentzContinuum : FCG.ContinuumLorentzClosure
    tensors : EinsteinTensorData
      (FCG.ContinuumLorentzClosure.geometry lorentzContinuum)
    laws : BianchiLovelockClosure
      (FCG.ContinuumLorentzClosure.geometry lorentzContinuum)
      tensors

open EinsteinContinuumClosure public
