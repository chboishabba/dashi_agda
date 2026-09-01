module DASHI.Combinatorics.ProofFabricLocalCompatibilityExact where

open import DASHI.Core.Prelude
open import Data.List using (List; []; _∷_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Combinatorics.ProofFabricCompilerExact as Fabric

------------------------------------------------------------------------
-- PROOF FABRIC LOCAL COMPATIBILITY
--
-- The physical code has a local typing discipline: only the three tiles that
-- decode to trits are admitted.  The reserved 11 tile is structurally rejected.
-- Logical validity still belongs to the source proof system / ProofTritCodec.
------------------------------------------------------------------------

data LocallyWellTypedTile : Fabric.ProofWeaveTile → Set where
  tile00Typed : LocallyWellTypedTile Fabric.tile00
  tile01Typed : LocallyWellTypedTile Fabric.tile01
  tile10Typed : LocallyWellTypedTile Fabric.tile10

reservedTileCannotType : LocallyWellTypedTile Fabric.tile11 → ⊥
reservedTileCannotType ()

compiledTritTileIsTyped : (t : Trit) → LocallyWellTypedTile (Fabric.tritToTile t)
compiledTritTileIsTyped neg = tile00Typed
compiledTritTileIsTyped zer = tile01Typed
compiledTritTileIsTyped pos = tile10Typed

------------------------------------------------------------------------
-- Whole-stream local compatibility is proof-relevant and mirrors the list
-- structure of the material code.
------------------------------------------------------------------------

data LocallyCompatibleFabric : List Fabric.ProofWeaveTile → Set where
  emptyCompatible : LocallyCompatibleFabric []
  consCompatible :
    ∀ {tile tiles} →
    LocallyWellTypedTile tile →
    LocallyCompatibleFabric tiles →
    LocallyCompatibleFabric (tile ∷ tiles)

compiledTritStreamLocallyCompatible :
  (stream : List Trit) →
  LocallyCompatibleFabric (Fabric.compileTritStream stream)
compiledTritStreamLocallyCompatible [] = emptyCompatible
compiledTritStreamLocallyCompatible (t ∷ ts) =
  consCompatible
    (compiledTritTileIsTyped t)
    (compiledTritStreamLocallyCompatible ts)

compiledProofFabricLocallyCompatible :
  {Proof : Set} →
  (codec : Fabric.ProofTritCodec Proof) →
  (proof : Proof) →
  LocallyCompatibleFabric
    (Fabric.weaveTiles (Fabric.compileProofToFabric codec proof))
compiledProofFabricLocallyCompatible codec proof =
  compiledTritStreamLocallyCompatible (Fabric.serializeProof codec proof)

------------------------------------------------------------------------
-- A physical reader can reject malformed local structure before invoking the
-- source proof parser.  This is syntactic/material certification, not proof
-- validity by itself.
------------------------------------------------------------------------

data LocalFabricStatus : Set where
  locallyAdmitted locallyMalformed : LocalFabricStatus

classifyTile : Fabric.ProofWeaveTile → LocalFabricStatus
classifyTile Fabric.tile00 = locallyAdmitted
classifyTile Fabric.tile01 = locallyAdmitted
classifyTile Fabric.tile10 = locallyAdmitted
classifyTile Fabric.tile11 = locallyMalformed

reservedTileClassifiesMalformed : classifyTile Fabric.tile11 ≡ locallyMalformed
reservedTileClassifiesMalformed = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data LocallyTypedFabricCreatesProof : Set where
data MalformedTileRefutesSourceTheorem : Set where
data PhysicalCompatibilityEqualsLogicalDerivability : Set where
data EveryCulturalPatternIsAvailableProofCode : Set where

localTypingDoesNotCreateProof : LocallyTypedFabricCreatesProof → ⊥
localTypingDoesNotCreateProof ()

malformedTileDoesNotRefuteSourceTheorem : MalformedTileRefutesSourceTheorem → ⊥
malformedTileDoesNotRefuteSourceTheorem ()

physicalCompatibilityIsNotLogicalDerivability :
  PhysicalCompatibilityEqualsLogicalDerivability → ⊥
physicalCompatibilityIsNotLogicalDerivability ()

culturalPatternAvailabilityIsNotAutomatic :
  EveryCulturalPatternIsAvailableProofCode → ⊥
culturalPatternAvailabilityIsNotAutomatic ()

record ProofFabricLocalCompatibilityBoundary : Set where
  constructor proof-fabric-local-compatibility-boundary
  field
    threeValidTilesLocallyTyped : Bool
    reservedTileRejected : Bool
    everyCompiledTritStreamTyped : Bool
    everyCompiledProofFabricTyped : Bool
    localTypingCreatesLogicalProof : Bool
    physicalCompatibilityEqualsDerivability : Bool

canonicalProofFabricLocalCompatibilityBoundary :
  ProofFabricLocalCompatibilityBoundary
canonicalProofFabricLocalCompatibilityBoundary =
  proof-fabric-local-compatibility-boundary
    true true true true false false
