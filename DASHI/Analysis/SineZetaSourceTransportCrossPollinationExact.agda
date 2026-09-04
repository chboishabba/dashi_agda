module DASHI.Analysis.SineZetaSourceTransportCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Analysis.SineZeroClassificationSourceAuthorityExact as Sine
import DASHI.Analysis.ZetaMinusThreeSourceAuthorityExact as Zeta

------------------------------------------------------------------------
-- SINE / ZETA SOURCE-TRANSPORT CROSS-POLLINATION
--
-- These two applications have the same provenance geometry:
--
--   bounded external theorem
--        + same-object/function/normalisation weld
--        -> local theorem target.
--
-- Their source instances are deliberately NOT reusable across one another.
------------------------------------------------------------------------

sineSourceClaim : Transport.SourceBackedClaim
sineSourceClaim = record
  { Transport.SourceClaim = Sine.zerosAreIntegerMultiplesOfPi Sine.nistDLMFSineZeroAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName = Sine.sourceName Sine.nistDLMFSineZeroAuthority
  ; Transport.sourceLocator = Sine.sourceLocator Sine.nistDLMFSineZeroAuthority
  ; Transport.reading = "DLMF sine-zero classification as bounded external theorem authority."
  }

zetaSourceClaim : Transport.SourceBackedClaim
zetaSourceClaim = record
  { Transport.SourceClaim = Zeta.zetaMinusThreeEqualsMinusB4OverFour Zeta.nistDLMFZetaMinusThreeAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName = Zeta.sourceName Zeta.nistDLMFZetaMinusThreeAuthority
  ; Transport.sourceLocator = Zeta.sourceLocator Zeta.nistDLMFZetaMinusThreeAuthority
  ; Transport.reading = "DLMF zeta(-3) Bernoulli relation as bounded external theorem authority."
  }

record SineLocalTarget : Set₁ where
  field
    LocalSineZeroClassification : Set
    sameConstructedSineAndPi : Set
    sourceSemanticsTransport :
      Sine.zerosAreIntegerMultiplesOfPi Sine.nistDLMFSineZeroAuthority →
      sameConstructedSineAndPi →
      LocalSineZeroClassification
    reading : String

open SineLocalTarget public

asSineTransportTarget :
  SineLocalTarget →
  Transport.LocalTheoremTarget sineSourceClaim
asSineTransportTarget T = record
  { Transport.LocalClaim = LocalSineZeroClassification T
  ; Transport.sameMathematicalObject = sameConstructedSineAndPi T
  ; Transport.sourceSemanticsToLocal = sourceSemanticsTransport T
  ; Transport.reading = reading T
  }

record ZetaLocalTarget : Set₁ where
  field
    LocalZetaMinusThreeTheorem : Set
    sameAnalyticContinuationAndNormalisation : Set
    sourceSemanticsTransport :
      Zeta.zetaMinusThreeEqualsMinusB4OverFour Zeta.nistDLMFZetaMinusThreeAuthority →
      sameAnalyticContinuationAndNormalisation →
      LocalZetaMinusThreeTheorem
    reading : String

open ZetaLocalTarget public

asZetaTransportTarget :
  ZetaLocalTarget →
  Transport.LocalTheoremTarget zetaSourceClaim
asZetaTransportTarget T = record
  { Transport.LocalClaim = LocalZetaMinusThreeTheorem T
  ; Transport.sameMathematicalObject = sameAnalyticContinuationAndNormalisation T
  ; Transport.sourceSemanticsToLocal = sourceSemanticsTransport T
  ; Transport.reading = reading T
  }

data SineSourceReceiptAutomaticallyProvesZetaTheorem : Set where

data ZetaSourceReceiptAutomaticallyClassifiesSineZeros : Set where

noSineToZetaInstanceLeak :
  SineSourceReceiptAutomaticallyProvesZetaTheorem → ⊥
noSineToZetaInstanceLeak ()

noZetaToSineInstanceLeak :
  ZetaSourceReceiptAutomaticallyClassifiesSineZeros → ⊥
noZetaToSineInstanceLeak ()

record CrossPollinationStatus : Set where
  field
    commonTransportShapeOwned : Bool
    sineApplicationNeedsOwnWeld : Bool
    zetaApplicationNeedsOwnWeld : Bool
    sidewaysReceiptReuseForbidden : Bool

    commonTransportShapeOwnedIsTrue : commonTransportShapeOwned ≡ true
    sineApplicationNeedsOwnWeldIsTrue : sineApplicationNeedsOwnWeld ≡ true
    zetaApplicationNeedsOwnWeldIsTrue : zetaApplicationNeedsOwnWeld ≡ true
    sidewaysReceiptReuseForbiddenIsTrue : sidewaysReceiptReuseForbidden ≡ true

open CrossPollinationStatus public

canonicalCrossPollinationStatus : CrossPollinationStatus
canonicalCrossPollinationStatus = record
  { commonTransportShapeOwned = true
  ; sineApplicationNeedsOwnWeld = true
  ; zetaApplicationNeedsOwnWeld = true
  ; sidewaysReceiptReuseForbidden = true
  ; commonTransportShapeOwnedIsTrue = refl
  ; sineApplicationNeedsOwnWeldIsTrue = refl
  ; zetaApplicationNeedsOwnWeldIsTrue = refl
  ; sidewaysReceiptReuseForbiddenIsTrue = refl
  }
