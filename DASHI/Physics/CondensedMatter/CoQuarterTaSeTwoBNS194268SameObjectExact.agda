module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBNS194268SameObjectExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LITERAL MAGNETIC-GROUP IDENTIFICATION SURFACE
--
-- Measured/material source:
--   Mandujano et al., Phys. Rev. B 110, 144420 (2024),
--   DOI 10.1103/PhysRevB.110.144420.
--   Reported magnetic space group: P6_3'/m'm'c, BNS 194.268.
--
-- Independent notation authority:
--   magnetic Hall-symbol tables identify BNS 194.268 with Hall symbol
--   -P 6c' 2c.
--
-- This module deliberately distinguishes metadata identity from an
-- operation-by-operation magCIF equality proof.  The latter remains false
-- until a literal independently acquired magnetic operation table is stored
-- and compared in-repository.
------------------------------------------------------------------------

record MagneticGroupIdentity : Set where
  constructor magnetic-group-identity
  field
    bnsNumber : String
    bnsSymbol : String
    magneticHallSymbol : String
    parentNuclearNumber : Nat
    materialSourceDOI : String
    independentAuthorityPresent : Bool

open MagneticGroupIdentity public

coQuarterTaSeTwoBNS : MagneticGroupIdentity
coQuarterTaSeTwoBNS = magnetic-group-identity
  "194.268"
  "P6_3'/m'm'c"
  "-P 6c' 2c"
  194
  "10.1103/PhysRevB.110.144420"
  true

record OperationSameObjectStatus : Set where
  constructor operation-same-object-status
  field
    metadataIdentityFixed : Bool
    parentP63mmcOperationsConstructed : Bool
    staggeredMomentAntiunitaryTagsConstructed : Bool
    nonsymmorphicBlochPhaseImplementedNumerically : Bool
    independentLiteralMagCIFStored : Bool
    operationByOperationEqualityProved : Bool
    fullMagneticGroupSameObjectClosed : Bool

canonicalOperationSameObjectStatus : OperationSameObjectStatus
canonicalOperationSameObjectStatus =
  operation-same-object-status
    true true true true false false false

-- Promotion rule: metadata agreement is insufficient for the final same-object
-- claim.  This prevents the BNS label itself from silently paying the literal
-- operation equality debt.
record BNSPromotionBoundary : Set where
  constructor bns-promotion-boundary
  field
    matchingBNSNumberImpliesOperationEquality : Bool
    matchingSymbolImpliesBlochRepresentationEquality : Bool
    independentOperationTableStillRequired : Bool

canonicalBNSPromotionBoundary : BNSPromotionBoundary
canonicalBNSPromotionBoundary =
  bns-promotion-boundary false false true
