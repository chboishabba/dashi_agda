module DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceAdapterRound58 where

------------------------------------------------------------------------
-- Round 58 B integration surface.
--
-- The lightweight B leaf and the legacy B consumer previously described the
-- same physical object with two records.  This adapter gives that object one
-- source package: the normalized Gram realization, its common hat, the shell
-- distance, and the off-support annihilation law.  The three target estimates
-- remain explicit fields of `bounds`; this file proves only the transport.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as LightHat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as LightGram
import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Legacy
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support

record PhysicalNormalizedOddPQSource : Set₁ where
  field
    support : LightHat.PhysicalOddPQCommonHatIdentification
    realization :
      LightGram.PhysicalNormalizedOddPQGramRealization support
    bounds :
      LightGram.SameAdjacentNormalizedFibreMassBounds realization

    shellDistance : Nat → Nat → Nat
    sameShellDistance : ∀ q → shellDistance q q ≡ zero
    forwardAdjacentDistance : ∀ q →
      shellDistance q (suc q) ≡ suc zero
    reverseAdjacentDistance : ∀ q →
      shellDistance (suc q) q ≡ suc zero

    inactiveSupportAnnihilatesPairProduct : ∀ q r →
      LightHat.supportActive support q r ≡ false →
      LightGram.pairProduct realization q r ≡ 0ℚ


open PhysicalNormalizedOddPQSource public

activeRelationIsLiteralOutputFibre :
  (source : PhysicalNormalizedOddPQSource) →
  ∀ q r →
  LightHat.supportActive (support source) q r
  ≡ LightHat.literalOddPQOutputFibreActive (support source) q r
activeRelationIsLiteralOutputFibre source q r = refl

legacySkeleton :
  (source : PhysicalNormalizedOddPQSource) →
  Legacy.PhysicalOddPQSupportSkeleton
legacySkeleton source = record
  { physicalPairProduct = LightGram.pairProduct (realization source)
  ; shellDistance = shellDistance source
  ; supportActive = LightHat.supportActive (support source)
  ; pairProductNonnegative =
      LightGram.pairProductNonnegative (realization source)
  ; inactiveSupportAnnihilatesPairProduct =
      inactiveSupportAnnihilatesPairProduct source
  }

legacyHat :
  (source : PhysicalNormalizedOddPQSource) →
  Legacy.PhysicalOddPQHatIdentification (legacySkeleton source)
legacyHat source = record
  { commonHatSupport = LightHat.commonHatSupport (support source)
  ; leftActiveInCommonHat =
      LightHat.leftActiveInCommonHat (support source)
  ; rightActiveInCommonHat =
      LightHat.rightActiveInCommonHat (support source)
  }

legacyBounds :
  (source : PhysicalNormalizedOddPQSource) →
  Legacy.SameAdjacentPhysicalComBounds
    (legacySkeleton source)
    (legacyHat source)
legacyBounds source = record
  { sameShellDistance = sameShellDistance source
  ; forwardAdjacentDistance = forwardAdjacentDistance source
  ; backwardAdjacentDistance = reverseAdjacentDistance source
  ; physicalComSameShellActiveBound =
      λ q active →
        LightGram.sameShellBound (bounds source) q active
  ; physicalComAdjacentShellActiveBound =
      λ q active →
        LightGram.forwardAdjacentBound (bounds source) q active
  ; physicalComReverseAdjacentShellActiveBound =
      λ q active →
        LightGram.reverseAdjacentBound (bounds source) q active
  }

legacyEnvelope :
  (source : PhysicalNormalizedOddPQSource) →
  Support.PhysicalComSupportOverlapEnvelope
legacyEnvelope source =
  Legacy.physicalComEnvelopeFromSameAdjacent
    (legacyHat source)
    (legacyBounds source)

-- Transport is complete, but the three physical normalized-fibre estimates
-- remain an explicit uninhabited frontier.
physicalNormalizedFibreBoundsConstructed : Bool
physicalNormalizedFibreBoundsConstructed = false

physicalNormalizedFibreBoundsConstructedIsFalse :
  physicalNormalizedFibreBoundsConstructed ≡ false
physicalNormalizedFibreBoundsConstructedIsFalse = refl

-- This is an integration theorem, not the missing fibre estimate: if a source
-- record is supplied, the old envelope consumer receives the same object and
-- the same three rational inequalities.
