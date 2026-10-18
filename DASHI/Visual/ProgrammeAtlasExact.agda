module DASHI.Visual.ProgrammeAtlasExact where

open import DASHI.Core.Prelude

record ProgrammeRegion : Set where
  constructor programmeRegion
  field
    programmeName : String
    regionX : Nat
    regionY : Nat

open ProgrammeRegion public

record ProgrammeAtlasBoundary : Set where
  constructor programmeAtlasBoundary
  field
    programmeRegionMayMoveWhenUnrelatedProgrammeChanges : Bool
    programmeRegionMayMoveWhenUnrelatedProgrammeChangesIsFalse :
      programmeRegionMayMoveWhenUnrelatedProgrammeChanges ≡ false

    localSemanticLayoutMayEvolveInsideRegion : Bool
    localSemanticLayoutMayEvolveInsideRegionIsTrue :
      localSemanticLayoutMayEvolveInsideRegion ≡ true

    atlasPositionDefinesSemanticIdentity : Bool
    atlasPositionDefinesSemanticIdentityIsFalse :
      atlasPositionDefinesSemanticIdentity ≡ false

    dormantNodePositionMayBeForgotten : Bool
    dormantNodePositionMayBeForgottenIsFalse :
      dormantNodePositionMayBeForgotten ≡ false

    returningNodeMayReuseArchivedPosition : Bool
    returningNodeMayReuseArchivedPositionIsTrue :
      returningNodeMayReuseArchivedPosition ≡ true

canonicalProgrammeAtlasBoundary : ProgrammeAtlasBoundary
canonicalProgrammeAtlasBoundary =
  programmeAtlasBoundary
    false refl
    true refl
    false refl
    false refl
    true refl
