module DASHI.Physics.YangMills.BalabanPath4FourDimensionalTensorizationRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (_*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate using
  (coercivityConstant)
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate
open import DASHI.Physics.YangMills.BalabanFourDimensionalLDLTensorization

------------------------------------------------------------------------
-- Concrete four-axis regression for the committed generated P4 certificate.
------------------------------------------------------------------------

Path4TensorBlock : Set
Path4TensorBlock = FourAxisTensorBlock Path4Coordinates

path4FourDimensionalPoincare : ∀ block →
  oneSixteenth * tensorizedNormSq path4LDLCertificate block
  ≤ tensorizedEdgeEnergy path4LDLCertificate block
path4FourDimensionalPoincare =
  fourAxisTensorBlockPoincare path4LDLCertificate

path4CertificateConstantMatches :
  coercivityConstant path4LDLCertificate ≡ oneSixteenth
path4CertificateConstantMatches = refl

path4FourDimensionalTensorizationLevel : ProofLevel
path4FourDimensionalTensorizationLevel = machineChecked
