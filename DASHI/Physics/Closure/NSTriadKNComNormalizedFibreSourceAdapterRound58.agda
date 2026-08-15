module DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceAdapterRound58 where

------------------------------------------------------------------------
-- Round 58/60 B integration surface.
--
-- Round60 moves the canonical source record into the lightweight
-- NSTriadKNComNormalizedFibreSourceRound60Exact module.  This adapter now does
-- only the expensive legacy transport.  Consequently focused checks of the
-- physical same/adjacent inequalities no longer have to elaborate the complete
-- Round47/42 envelope graph.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as LightHat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as LightGram
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceRound60Exact as Source
import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Legacy
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support

legacySkeleton :
  (source : Source.PhysicalNormalizedOddPQSource) →
  Legacy.PhysicalOddPQSupportSkeleton
legacySkeleton source = record
  { physicalPairProduct = LightGram.pairProduct (Source.realization source)
  ; shellDistance = Source.shellDistance source
  ; supportActive = LightHat.supportActive (Source.support source)
  ; pairProductNonnegative =
      LightGram.pairProductNonnegative (Source.realization source)
  ; inactiveSupportAnnihilatesPairProduct =
      Source.inactiveSupportAnnihilatesPairProduct source
  }

legacyHat :
  (source : Source.PhysicalNormalizedOddPQSource) →
  Legacy.PhysicalOddPQHatIdentification (legacySkeleton source)
legacyHat source = record
  { commonHatSupport = LightHat.commonHatSupport (Source.support source)
  ; leftActiveInCommonHat =
      LightHat.leftActiveInCommonHat (Source.support source)
  ; rightActiveInCommonHat =
      LightHat.rightActiveInCommonHat (Source.support source)
  }

legacyBounds :
  (source : Source.PhysicalNormalizedOddPQSource) →
  Legacy.SameAdjacentPhysicalComBounds
    (legacySkeleton source)
    (legacyHat source)
legacyBounds source = record
  { sameShellDistance = Source.sameShellDistance source
  ; forwardAdjacentDistance = Source.forwardAdjacentDistance source
  ; backwardAdjacentDistance = Source.reverseAdjacentDistance source
  ; physicalComSameShellActiveBound =
      λ q active →
        LightGram.sameShellBound (Source.bounds source) q active
  ; physicalComAdjacentShellActiveBound =
      λ q active →
        LightGram.forwardAdjacentBound (Source.bounds source) q active
  ; physicalComReverseAdjacentShellActiveBound =
      λ q active →
        LightGram.reverseAdjacentBound (Source.bounds source) q active
  }

legacyEnvelope :
  (source : Source.PhysicalNormalizedOddPQSource) →
  Support.PhysicalComSupportOverlapEnvelope
legacyEnvelope source =
  Legacy.physicalComEnvelopeFromSameAdjacent
    (legacyHat source)
    (legacyBounds source)

-- Transport is complete, but the three physical normalized-fibre estimates
-- remain an explicit uninhabited frontier in the lightweight source.
physicalNormalizedFibreBoundsConstructed : Bool
physicalNormalizedFibreBoundsConstructed = false

physicalNormalizedFibreBoundsConstructedIsFalse :
  physicalNormalizedFibreBoundsConstructed ≡ false
physicalNormalizedFibreBoundsConstructedIsFalse = refl
