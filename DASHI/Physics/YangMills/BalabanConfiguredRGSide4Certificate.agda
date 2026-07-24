module DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using
  (ℚ; 0ℚ; _*_; _≤_; _<_; Positive)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate

------------------------------------------------------------------------
-- The currently configured physical RG lane uses one fixed blocking side.
--
-- This is the finite alternative requested by C1.6: no finite collection of
-- tested sides is presented as an arbitrary-L theorem.  The configured side is
-- definitionally four, and the selected certificate is the checked rational
-- LDL^T certificate already consumed by the physical tensorization lane.
------------------------------------------------------------------------

configuredRGBlockSide : Nat
configuredRGBlockSide = side4

configuredRGBlockSideIsFour : configuredRGBlockSide ≡ side4
configuredRGBlockSideIsFour = refl

ConfiguredPhysicalBlock : Set
ConfiguredPhysicalBlock = PhysicalBlockL configuredRGBlockSide

configuredPhysicalBlockIsSideFour :
  ConfiguredPhysicalBlock ≡ PhysicalBlockL side4
configuredPhysicalBlockIsSideFour = refl

ConfiguredRationalBondField : Set
ConfiguredRationalBondField = BondField configuredRGBlockSide ℚ

configuredRationalBondFieldIsSideFour :
  ConfiguredRationalBondField ≡ BondField side4 ℚ
configuredRationalBondFieldIsSideFour = refl

configuredPathCertificate : RationalLDLCertificate Path4Coordinates
configuredPathCertificate = path4LDLCertificate

configuredPathCoercivityConstant : ℚ
configuredPathCoercivityConstant = coercivityConstant configuredPathCertificate

configuredPathCoercivityConstantIsOneSixteenth :
  configuredPathCoercivityConstant ≡ oneSixteenth
configuredPathCoercivityConstantIsOneSixteenth = refl

configuredPathCoercivityConstantPositive :
  0ℚ < configuredPathCoercivityConstant
configuredPathCoercivityConstantPositive =
  let
    instance
      oneSixteenthPositive : Positive oneSixteenth
      oneSixteenthPositive = ℚP.normalize-pos 1 16
  in
  ℚP.positive⁻¹ configuredPathCoercivityConstant

configuredRGPathPoincare : ∀ coordinate →
  configuredPathCoercivityConstant * path4NormSq coordinate
  ≤ path4Energy coordinate
configuredRGPathPoincare = path4Poincare

configuredRGSideSelectionLevel : ProofLevel
configuredRGSideSelectionLevel = machineChecked

configuredRGSideCertificateLevel : ProofLevel
configuredRGSideCertificateLevel = machineChecked

configuredRGCoercivityConstantPositiveLevel : ProofLevel
configuredRGCoercivityConstantPositiveLevel = machineChecked

arbitraryRGSideClaimLevel : ProofLevel
arbitraryRGSideClaimLevel = conditional
