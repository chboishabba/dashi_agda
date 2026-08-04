module DASHI.Reasoning.ParallaxHolonomyBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import Base369 as Base
import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Geometry.TwistedCycleOrientationCover as Twisted

------------------------------------------------------------------------
-- Exact bridge: the existing +3 mod 6 transport preserves triadic phase and
-- flips the two-sheet orientation sign.  The semantic reading of the sheets
-- remains an additional labelled bridge, not a theorem of topology.
------------------------------------------------------------------------

polarityToSign : Mobius.OrientationPolarity → Twisted.OrientationSign
polarityToSign Mobius.positive = Twisted.plus
polarityToSign Mobius.negative = Twisted.minus

polarityFlipRealisesSignFlip :
  ∀ polarity →
  polarityToSign (Mobius.flipOrientationPolarity polarity) ≡
  Twisted.flipSign (polarityToSign polarity)
polarityFlipRealisesSignFlip Mobius.positive = refl
polarityFlipRealisesSignFlip Mobius.negative = refl

hexOrientationSign : Base.HexTruth → Twisted.OrientationSign
hexOrientationSign value =
  polarityToSign (Mobius.hexOrientationPolarity value)

mobiusTransportFlipsOrientationSign :
  ∀ value →
  hexOrientationSign (Mobius.mobiusTransport value) ≡
  Twisted.flipSign (hexOrientationSign value)
mobiusTransportFlipsOrientationSign Base.hex-0 = refl
mobiusTransportFlipsOrientationSign Base.hex-1 = refl
mobiusTransportFlipsOrientationSign Base.hex-2 = refl
mobiusTransportFlipsOrientationSign Base.hex-3 = refl
mobiusTransportFlipsOrientationSign Base.hex-4 = refl
mobiusTransportFlipsOrientationSign Base.hex-5 = refl

mobiusTransportPreservesPhase :
  ∀ value →
  Mobius.hexTriadicPhase (Mobius.mobiusTransport value) ≡
  Mobius.hexTriadicPhase value
mobiusTransportPreservesPhase =
  Mobius.mobiusTransport-preservesTriadicPhase

mobiusTransportDoubleTraversalReturns :
  ∀ value →
  Mobius.mobiusTransport (Mobius.mobiusTransport value) ≡ value
mobiusTransportDoubleTraversalReturns =
  Mobius.mobiusTransport-squares-to-identity

record SemanticSheetLabelling (Claim : Set) : Set₁ where
  field
    positiveLabel negativeLabel : Claim
    label : Twisted.OrientationSign → Claim
    positiveSheetLabelled : label Twisted.plus ≡ positiveLabel
    negativeSheetLabelled : label Twisted.minus ≡ negativeLabel
    labelsAreLogicalNegationsClaimed : Bool
    empiricalTrajectoryWitnessRequired : Bool

record ParallaxHolonomySystem (Claim : Set) : Set₁ where
  field
    localPhase : Base.TriTruth
    orientation : Twisted.OrientationSign
    transport : Twisted.OrientationSign → Twisted.OrientationSign
    transportIsFlip :
      ∀ sign → transport sign ≡ Twisted.flipSign sign
    semanticLabelling : SemanticSheetLabelling Claim
    traversedDistinguishedLoop : Bool
    semanticReversalPromoted : Bool

record ParallaxHolonomyAuthorityBoundary : Set where
  field
    base369OrientationFlipProved : Bool
    base369PhasePreservationProved : Bool
    finiteTwistedCoverAvailable : Bool
    topologyAloneProvesPropositionNegation : Bool
    topologyAloneProvesHistoricalReversal : Bool
    bridgeNote : String

canonicalParallaxHolonomyAuthorityBoundary :
  ParallaxHolonomyAuthorityBoundary
canonicalParallaxHolonomyAuthorityBoundary = record
  { base369OrientationFlipProved = true
  ; base369PhasePreservationProved = true
  ; finiteTwistedCoverAvailable = true
  ; topologyAloneProvesPropositionNegation = false
  ; topologyAloneProvesHistoricalReversal = false
  ; bridgeNote =
      "Base369 realises the finite sheet flip exactly; parallax semantics additionally require a claim labelling and a witnessed contextual loop."
  }
