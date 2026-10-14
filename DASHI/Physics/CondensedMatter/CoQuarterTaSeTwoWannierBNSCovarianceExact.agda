module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoWannierBNSCovarianceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBNS194268SameObjectExact as BNS
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoWannierSpectralProducerExact as Wannier

------------------------------------------------------------------------
-- SAME-BASIS MATERIAL MSG COVARIANCE AUDIT
--
-- scripts/co_tase2_wannier_bns_covariance_audit.py consumes a literal
-- Wannier90 H(R), the already-owned 24-operation BNS authority, and sewing
-- matrices supplied in that SAME Wannier basis.  It checks unitarity, exact
-- authority/parity coverage and unitary/antiunitary Hamiltonian covariance.
--
-- This is the correct bridge between our literal magnetic-space-group table
-- and a future material Hamiltonian.  The earlier four-band sewing fixture is
-- not silently reused as the representation of an arbitrary Wannier basis.
------------------------------------------------------------------------

record MaterialBasisCovarianceContract : Set where
  constructor material-basis-covariance-contract
  field
    literalWannierHamiltonianRequired : Bool
    literalBNSAuthorityRequired : Bool
    sameBasisSewingMatricesRequired : Bool
    allTwentyFourOperationsRequired : Bool
    antiunitaryParityChecked : Bool
    sewingUnitarityChecked : Bool
    unitaryCovarianceChecked : Bool
    antiunitaryConjugationChecked : Bool
    transformedMomentumSuppliedExplicitly : Bool
    toyFourBandRepresentationNotReusedImplicitly : Bool

open MaterialBasisCovarianceContract public

canonicalMaterialBasisCovarianceContract : MaterialBasisCovarianceContract
canonicalMaterialBasisCovarianceContract =
  material-basis-covariance-contract
    true true true true true true true true true true

record MaterialBasisCovarianceStatus : Set where
  constructor material-basis-covariance-status
  field
    executableAuditImplemented : Bool
    syntheticCoverageSelfTestImplemented : Bool
    literalMaterialSewingArtifactPresent : Bool
    literalMaterialCovarianceReceiptExecuted : Bool

canonicalMaterialBasisCovarianceStatus : MaterialBasisCovarianceStatus
canonicalMaterialBasisCovarianceStatus =
  material-basis-covariance-status true true false false

existingBNSStatus : BNS.OperationSameObjectStatus
existingBNSStatus = BNS.canonicalOperationSameObjectStatus

existingWannierStatus : Wannier.WannierProducerStatus
existingWannierStatus = Wannier.canonicalWannierProducerStatus

record MaterialBasisPromotionBoundary : Set where
  constructor material-basis-promotion-boundary
  field
    abstractBNSActionImpliesWannierBasisAction : Bool
    sameOperationNamesImplySameRepresentation : Bool
    syntheticGammaSelfTestImpliesMaterialCovariance : Bool
    futurePassingMaterialReceiptRequiresSameObjectProvenance : Bool

canonicalMaterialBasisPromotionBoundary : MaterialBasisPromotionBoundary
canonicalMaterialBasisPromotionBoundary =
  material-basis-promotion-boundary false false false true
