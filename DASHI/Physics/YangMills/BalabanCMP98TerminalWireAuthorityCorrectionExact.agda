{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98TerminalWireAuthorityCorrectionExact where

------------------------------------------------------------------------
-- TERMINAL WIRE AUTHORITY CORRECTION
--
-- `YMThermodynamicOSWightmanOperatorBoundaryReceipt` is a fail-closed boundary
-- ledger.  Its own canonical data simultaneously records six open theorem
-- bridges and seven explicit non-claims.  Later Bool fields named
-- `...Constructed` are status metadata; they are not inhabitants of those
-- theorem bridges.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.YMThermodynamicOSWightmanOperatorBoundaryReceipt as Wire

canonicalWireStillListsAllOpenBridges :
  Wire.openBridges Wire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ Wire.canonicalYMThermodynamicOpenBridges
canonicalWireStillListsAllOpenBridges = refl

canonicalWireStillListsAllExplicitNonClaims :
  Wire.explicitNonClaims Wire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ Wire.canonicalYMThermodynamicExplicitNonClaims
canonicalWireStillListsAllExplicitNonClaims = refl

canonicalWireOpenBridgeCountIsSix :
  Wire.openBridgeCount Wire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ 6
canonicalWireOpenBridgeCountIsSix = refl

canonicalWireConstructedMetadataCanStillBeTrue :
  Wire.thermodynamicLimitConstructed
    Wire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
canonicalWireConstructedMetadataCanStillBeTrue = refl

record TerminalWireAuthorityReading : Set where
  field
    openBridgesRemainCanonical :
      Wire.openBridges Wire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
      ≡ Wire.canonicalYMThermodynamicOpenBridges

    explicitNonClaimsRemainCanonical :
      Wire.explicitNonClaims Wire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
      ≡ Wire.canonicalYMThermodynamicExplicitNonClaims

    openBridgeCountRemainsSix :
      Wire.openBridgeCount Wire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
      ≡ 6

open TerminalWireAuthorityReading public

canonicalTerminalWireAuthorityReading : TerminalWireAuthorityReading
canonicalTerminalWireAuthorityReading = record
  { openBridgesRemainCanonical = canonicalWireStillListsAllOpenBridges
  ; explicitNonClaimsRemainCanonical = canonicalWireStillListsAllExplicitNonClaims
  ; openBridgeCountRemainsSix = canonicalWireOpenBridgeCountIsSix
  }

cmp98TerminalWireOpenBridgeAuthorityLevel : ProofLevel
cmp98TerminalWireOpenBridgeAuthorityLevel = machineChecked

-- A theorem-bearing successor may supersede this boundary only by providing
-- explicit inhabitants/transport for these mathematical stages.  Setting a
-- Boolean status field to true does not itself do so.
literalTerminalWireTheoremSuccessorLevel : ProofLevel
literalTerminalWireTheoremSuccessorLevel = conditional
