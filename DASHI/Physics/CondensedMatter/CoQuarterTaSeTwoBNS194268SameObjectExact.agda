module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBNS194268SameObjectExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LITERAL MAGNETIC-GROUP IDENTIFICATION SURFACE
--
-- Material source:
--   Mandujano et al., Phys. Rev. B 110, 144420 (2024),
--   DOI 10.1103/PhysRevB.110.144420.
--   Reported magnetic space group: P6_3'/m'm'c, BNS 194.268.
--
-- Independent operation authority acquired 2026-10-12:
--   MAGNDATA entry 0.118, BNS P6_3'/m'm'c (#194.268), standard setting.
--   The repository stores all 24 listed magnetic operations in
--   data/co_tase2/bns_194_268_magndata_operations.json.
--
-- Executable audit receipt:
--   outputs/co_tase2/bns_194_268_operation_audit.json
--   authority SHA256
--   32377c575e20bb24b243ee3a4b4b97f2c195058d4886798a18496b1d95d2085c
--   records exact set equality of all 24 (spatial triplet, antiunitary parity)
--   pairs against the Gemmi P63/mmc + staggered-Co-moment construction:
--   12 unitary + 12 antiunitary; no missing or extra operations.
--
-- This closes the external operation-table SAME-OBJECT acquisition/audit leaf.
-- It does NOT turn the Python audit into an Agda proof of matrix/sewing laws;
-- those remain separately typed below.
------------------------------------------------------------------------

record MagneticGroupIdentity : Set where
  constructor magnetic-group-identity
  field
    bnsNumber : String
    bnsSymbol : String
    magneticHallSymbol : String
    parentNuclearNumber : Nat
    materialSourceDOI : String
    independentAuthority : String
    independentAuthorityPresent : Bool

open MagneticGroupIdentity public

coQuarterTaSeTwoBNS : MagneticGroupIdentity
coQuarterTaSeTwoBNS = magnetic-group-identity
  "194.268"
  "P6_3'/m'm'c"
  "-P 6c' 2c"
  194
  "10.1103/PhysRevB.110.144420"
  "MAGNDATA entry 0.118"
  true

record OperationSameObjectStatus : Set where
  constructor operation-same-object-status
  field
    metadataIdentityFixed : Bool
    parentP63mmcOperationsConstructed : Bool
    staggeredMomentAntiunitaryTagsConstructed : Bool
    nonsymmorphicBlochPhaseImplementedNumerically : Bool
    independentLiteralMagneticOperationTableStored : Bool
    independentTableHas24Operations : Bool
    independentTableHas12AntiunitaryOperations : Bool
    externalExactOperationSetAuditPassed : Bool
    fullMagneticGroupOperationSameObjectClosed : Bool
    operationEqualityKernelProved : Bool

canonicalOperationSameObjectStatus : OperationSameObjectStatus
canonicalOperationSameObjectStatus =
  operation-same-object-status
    true true true true
    true true true true true
    false

record OperationAuditReceipt : Set where
  constructor operation-audit-receipt
  field
    authoritySHA256 : String
    authorityOperationCount : Nat
    modeledOperationCount : Nat
    unitaryCount : Nat
    antiunitaryCount : Nat
    missingOperationCount : Nat
    extraOperationCount : Nat
    exactSetMatch : Bool

canonicalOperationAuditReceipt : OperationAuditReceipt
canonicalOperationAuditReceipt = operation-audit-receipt
  "32377c575e20bb24b243ee3a4b4b97f2c195058d4886798a18496b1d95d2085c"
  24 24 12 12 0 0 true

-- Promotion rule after acquisition: the metadata label is still not the proof.
-- What pays the external same-object leaf is the independent literal table plus
-- the exact operation-set audit.  Matrix/sewing/cocycle kernel promotion is a
-- distinct obligation and cannot be inferred from this receipt.
record BNSPromotionBoundary : Set where
  constructor bns-promotion-boundary
  field
    matchingBNSNumberAloneImpliesOperationEquality : Bool
    matchingSymbolAloneImpliesBlochRepresentationEquality : Bool
    independentOperationTableStillRequired : Bool
    externalOperationAuditPaysKernelBlochProof : Bool

canonicalBNSPromotionBoundary : BNSPromotionBoundary
canonicalBNSPromotionBoundary =
  bns-promotion-boundary false false false false
