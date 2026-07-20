module DASHI.Physics.MultiscaleWaveCorrespondenceRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec using ([]; _∷_)

open import DASHI.Geometry.SSP369Ultrametric
open import DASHI.Geometry.SSP369KernelStability
open import DASHI.Physics.MultiscaleWaveCorrespondence

------------------------------------------------------------------------
-- Compact import and reduction surface.

canonicalAddress : Address 3
canonicalAddress = digit3 ∷ digit6 ∷ digit9 ∷ []

identityKernelPreservesCanonicalDistance :
  distance
    (apply identityPrefixKernel canonicalAddress)
    (apply identityPrefixKernel canonicalAddress)
  ≡ distance canonicalAddress canonicalAddress
identityKernelPreservesCanonicalDistance = refl

exactCoreRecorded :
  exactMultiscaleCoreAvailable currentMultiscaleWaveStatus ≡ true
exactCoreRecorded = refl

residualReconstructionRecorded :
  exactResidualReconstructionAvailable currentMultiscaleWaveStatus ≡ true
residualReconstructionRecorded = refl

continuumDerivationRemainsOpen :
  continuumPDEDerived currentMultiscaleWaveStatus ≡ false
continuumDerivationRemainsOpen = refl

shannonOptimalityRemainsOpen :
  shannonOptimalityProved currentMultiscaleWaveStatus ≡ false
shannonOptimalityRemainsOpen = refl

physicalLawSelectionRemainsOpen :
  physicalLawSelectionProved currentMultiscaleWaveStatus ≡ false
physicalLawSelectionRemainsOpen = refl
