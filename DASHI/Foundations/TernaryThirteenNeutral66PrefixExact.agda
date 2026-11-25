module DASHI.Foundations.TernaryThirteenNeutral66PrefixExact where

-- Original signed 369 word / pants / cylinder, NOT radix expansion of
-- the integer 66. Source-written, no fresh kernel acceptance.
open import DASHI.Core.Prelude
open import Data.Vec using () renaming (_∷_ to _vcons_)
import DASHI.Foundations.TernaryThirteenFibreSplitExact as W
import DASHI.Foundations.TernaryThirteenFibrePunctureExact as Z
import DASHI.Foundations.TernaryThirteenOriginalPantsFrontierBridgeExact as B
import DASHI.Foundations.TernaryThirteenFibreObserverNonDescentExact as N
import DASHI.Topology.TernaryCylinderPantsGeometryExact as J
import DASHI.Topology.TernaryPantsFrontierExact as P
import DASHI.Geometry.SSP369Ultrametric as U

prefix66 : W.TritWord 2
prefix66 = W.neutral , (W.neutral , tt)

embed66 : (n : Nat) → W.TritWord n → W.TritWord (2 + n)
embed66 n suffix = W.joinTrit 2 n prefix66 suffix

reopen66 : (n : Nat) → W.TritWord (2 + n) → W.TritWord n
reopen66 n word = proj₂ (W.splitTrit 2 n word)

prefixOf : (n : Nat) → W.TritWord (2 + n) → W.TritWord 2
prefixOf n word = proj₁ (W.splitTrit 2 n word)

prefix66Exact : (n : Nat) (suffix : W.TritWord n) →
  prefixOf n (embed66 n suffix) ≡ prefix66
prefix66Exact n suffix = cong proj₁
  (W.splitTritAfterJoin 2 n prefix66 suffix)

reopen66AfterEmbed : (n : Nat) (suffix : W.TritWord n) →
  reopen66 n (embed66 n suffix) ≡ suffix
reopen66AfterEmbed n suffix = cong proj₂
  (W.splitTritAfterJoin 2 n prefix66 suffix)

embed66AfterReopen : (n : Nat) (word : W.TritWord (2 + n)) →
  prefixOf n word ≡ prefix66 →
  embed66 n (reopen66 n word) ≡ word
embed66AfterReopen n word eq =
  trans
    (cong (λ p → W.joinTrit 2 n p (reopen66 n word)) (sym eq))
    (W.joinTritAfterSplit 2 n word)

pants66 : (suffix : W.TritWord 11) →
  B.wordToPants 13 (embed66 11 suffix) ≡
  J.slot6 vcons (J.slot6 vcons B.wordToPants 11 suffix)
pants66 suffix = refl

cylinder66 : (suffix : W.TritWord 11) →
  B.wordToCylinder 13 (embed66 11 suffix) ≡
  U.digit6 vcons (U.digit6 vcons B.wordToCylinder 11 suffix)
cylinder66 suffix = refl

-- Both source coordinates retained. Neutral prefix does not imply
-- global origin or a neutral last coordinate.
neutralSuffix positiveSuffix : W.TritWord 11
neutralSuffix = Z.zeroTritWord 11
positiveSuffix = W.positive , Z.zeroTritWord 10

neutralWord : W.TritWord 13
neutralWord = embed66 11 neutralSuffix

nonzeroWord : W.TritWord 13
nonzeroWord = embed66 11 positiveSuffix

neutralWordIsOrigin : neutralWord ≡ Z.zeroTritWord 13
neutralWordIsOrigin = refl

nonzeroWordNotOrigin : ¬ (nonzeroWord ≡ Z.zeroTritWord 13)
nonzeroWordNotOrigin ()

samePrefix : prefixOf 11 neutralWord ≡ prefixOf 11 nonzeroWord
samePrefix = refl

-- Use the existing 12+1 witness pair: both lie in this prefix, yet
-- even the 12-prefix does not determine the last coordinate.
neutralExtensionIn66 : prefixOf 11 N.neutralExtension ≡ prefix66
neutralExtensionIn66 = refl

positiveExtensionIn66 : prefixOf 11 N.positiveExtension ≡ prefix66
positiveExtensionIn66 = refl

-- The source modular/Tate -> actual word map is NOT asserted here.
-- It needs a source-selected observer and preservation/reopening proof.
