module DASHI.Biology.DASHIYijingRelationalOperatorsExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.DASHIYijingTernaryDivinationExact as Yijing

------------------------------------------------------------------------
-- Received four-valued casting surface.
--
-- 6 = old/changing yin
-- 7 = young/stable yang
-- 8 = young/stable yin
-- 9 = old/changing yang

data ClassicalLineValue : Set where
  oldYinSix : ClassicalLineValue
  youngYangSeven : ClassicalLineValue
  youngYinEight : ClassicalLineValue
  oldYangNine : ClassicalLineValue

primaryTrit : ClassicalLineValue → Triadic.KernelTrit
primaryTrit oldYinSix = Triadic.negativeTrit
primaryTrit youngYangSeven = Triadic.positiveTrit
primaryTrit youngYinEight = Triadic.negativeTrit
primaryTrit oldYangNine = Triadic.positiveTrit

isMovingLine : ClassicalLineValue → Bool
isMovingLine oldYinSix = true
isMovingLine youngYangSeven = false
isMovingLine youngYinEight = false
isMovingLine oldYangNine = true

resultingTrit : ClassicalLineValue → Triadic.KernelTrit
resultingTrit oldYinSix = Triadic.positiveTrit
resultingTrit youngYangSeven = Triadic.positiveTrit
resultingTrit youngYinEight = Triadic.negativeTrit
resultingTrit oldYangNine = Triadic.negativeTrit

mapPrimary :
  ∀ {n : Nat} → Vec ClassicalLineValue n → Vec Triadic.KernelTrit n
mapPrimary vnil = vnil
mapPrimary (x vcons xs) = primaryTrit x vcons mapPrimary xs

mapMoving :
  ∀ {n : Nat} → Vec ClassicalLineValue n → Vec Bool n
mapMoving vnil = vnil
mapMoving (x vcons xs) = isMovingLine x vcons mapMoving xs

mapResulting :
  ∀ {n : Nat} → Vec ClassicalLineValue n → Vec Triadic.KernelTrit n
mapResulting vnil = vnil
mapResulting (x vcons xs) = resultingTrit x vcons mapResulting xs

record CastTransformation : Set where
  constructor castTransformation
  field
    classicalValues : Vec ClassicalLineValue 6
    initialHexagram : Yijing.TernaryHexagram
    movingMask : Vec Bool 6
    resultingHexagram : Yijing.TernaryHexagram

open CastTransformation public

compileCast : Vec ClassicalLineValue 6 → CastTransformation
compileCast values =
  castTransformation
    values
    (mapPrimary values)
    (mapMoving values)
    (mapResulting values)

canonicalClassicalCast : Vec ClassicalLineValue 6
canonicalClassicalCast =
  oldYinSix vcons
  youngYangSeven vcons
  youngYinEight vcons
  oldYangNine vcons
  youngYangSeven vcons
  youngYinEight vcons
  vnil

canonicalCastInitial : Yijing.TernaryHexagram
canonicalCastInitial =
  Triadic.negativeTrit vcons
  Triadic.positiveTrit vcons
  Triadic.negativeTrit vcons
  Triadic.positiveTrit vcons
  Triadic.positiveTrit vcons
  Triadic.negativeTrit vcons
  vnil

canonicalCastMask : Vec Bool 6
canonicalCastMask =
  true vcons false vcons false vcons true vcons false vcons false vcons vnil

canonicalCastResulting : Yijing.TernaryHexagram
canonicalCastResulting =
  Triadic.positiveTrit vcons
  Triadic.positiveTrit vcons
  Triadic.negativeTrit vcons
  Triadic.negativeTrit vcons
  Triadic.positiveTrit vcons
  Triadic.negativeTrit vcons
  vnil

canonicalCastCompilesExactly :
  compileCast canonicalClassicalCast
  ≡ castTransformation
      canonicalClassicalCast
      canonicalCastInitial
      canonicalCastMask
      canonicalCastResulting
canonicalCastCompilesExactly = refl

------------------------------------------------------------------------
-- Lower and upper trigrams.

lowerTrigram : Yijing.TernaryHexagram → Yijing.TernaryTrigram
lowerTrigram
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) =
  a vcons b vcons c vcons vnil

upperTrigram : Yijing.TernaryHexagram → Yijing.TernaryTrigram
upperTrigram
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) =
  d vcons e vcons f vcons vnil

composeTrigrams :
  Yijing.TernaryTrigram → Yijing.TernaryTrigram → Yijing.TernaryHexagram
composeTrigrams
  (a vcons b vcons c vcons vnil)
  (d vcons e vcons f vcons vnil) =
  a vcons b vcons c vcons d vcons e vcons f vcons vnil

splitThenCompose :
  (x : Yijing.TernaryHexagram) →
  composeTrigrams (lowerTrigram x) (upperTrigram x) ≡ x
splitThenCompose
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = refl

------------------------------------------------------------------------
-- Classical eight-trigram image observation.  Any zero-containing trigram is
-- a DASHI ternary extension rather than one of the received binary images.

data TrigramImage : Set where
  heavenImage : TrigramImage
  earthImage : TrigramImage
  thunderImage : TrigramImage
  windWoodImage : TrigramImage
  waterImage : TrigramImage
  fireImage : TrigramImage
  mountainImage : TrigramImage
  lakeMarshImage : TrigramImage

data TrigramImageObservation : Set where
  receivedImage : TrigramImage → TrigramImageObservation
  ternaryBeyondReceivedEight : TrigramImageObservation

observeTrigramImage : Yijing.TernaryTrigram → TrigramImageObservation
observeTrigramImage
  (Triadic.positiveTrit vcons Triadic.positiveTrit vcons Triadic.positiveTrit vcons vnil) =
  receivedImage heavenImage
observeTrigramImage
  (Triadic.negativeTrit vcons Triadic.negativeTrit vcons Triadic.negativeTrit vcons vnil) =
  receivedImage earthImage
observeTrigramImage
  (Triadic.positiveTrit vcons Triadic.negativeTrit vcons Triadic.negativeTrit vcons vnil) =
  receivedImage thunderImage
observeTrigramImage
  (Triadic.negativeTrit vcons Triadic.positiveTrit vcons Triadic.positiveTrit vcons vnil) =
  receivedImage windWoodImage
observeTrigramImage
  (Triadic.negativeTrit vcons Triadic.positiveTrit vcons Triadic.negativeTrit vcons vnil) =
  receivedImage waterImage
observeTrigramImage
  (Triadic.positiveTrit vcons Triadic.negativeTrit vcons Triadic.positiveTrit vcons vnil) =
  receivedImage fireImage
observeTrigramImage
  (Triadic.negativeTrit vcons Triadic.negativeTrit vcons Triadic.positiveTrit vcons vnil) =
  receivedImage mountainImage
observeTrigramImage
  (Triadic.positiveTrit vcons Triadic.positiveTrit vcons Triadic.negativeTrit vcons vnil) =
  receivedImage lakeMarshImage
observeTrigramImage trigram = ternaryBeyondReceivedEight

canonicalTernaryTrigramExtendsReceivedEight :
  observeTrigramImage Yijing.canonicalTernaryTrigram
  ≡ ternaryBeyondReceivedEight
canonicalTernaryTrigramExtendsReceivedEight = refl

------------------------------------------------------------------------
-- Position, stage, centrality, correctness, and correspondence.

data LinePosition : Set where
  lineOne : LinePosition
  lineTwo : LinePosition
  lineThree : LinePosition
  lineFour : LinePosition
  lineFive : LinePosition
  lineSix : LinePosition

data PositionalStage : Set where
  entryStage : PositionalStage
  innerDevelopmentStage : PositionalStage
  lowerThresholdStage : PositionalStage
  outerEntryStage : PositionalStage
  governingCentreStage : PositionalStage
  culminationStage : PositionalStage

stageAt : LinePosition → PositionalStage
stageAt lineOne = entryStage
stageAt lineTwo = innerDevelopmentStage
stageAt lineThree = lowerThresholdStage
stageAt lineFour = outerEntryStage
stageAt lineFive = governingCentreStage
stageAt lineSix = culminationStage

lineAt : LinePosition → Yijing.TernaryHexagram → Triadic.KernelTrit
lineAt lineOne
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = a
lineAt lineTwo
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = b
lineAt lineThree
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = c
lineAt lineFour
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = d
lineAt lineFive
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = e
lineAt lineSix
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = f

isCentralPosition : LinePosition → Bool
isCentralPosition lineTwo = true
isCentralPosition lineFive = true
isCentralPosition position = false

expectedPositionalTrit : LinePosition → Triadic.KernelTrit
expectedPositionalTrit lineOne = Triadic.positiveTrit
expectedPositionalTrit lineTwo = Triadic.negativeTrit
expectedPositionalTrit lineThree = Triadic.positiveTrit
expectedPositionalTrit lineFour = Triadic.negativeTrit
expectedPositionalTrit lineFive = Triadic.positiveTrit
expectedPositionalTrit lineSix = Triadic.negativeTrit

tritEqual : Triadic.KernelTrit → Triadic.KernelTrit → Bool
tritEqual Triadic.negativeTrit Triadic.negativeTrit = true
tritEqual Triadic.zeroTrit Triadic.zeroTrit = true
tritEqual Triadic.positiveTrit Triadic.positiveTrit = true
tritEqual x y = false

positionIsCorrect : LinePosition → Yijing.TernaryHexagram → Bool
positionIsCorrect position hexagram =
  tritEqual (lineAt position hexagram) (expectedPositionalTrit position)

correspondingPosition : LinePosition → LinePosition
correspondingPosition lineOne = lineFour
correspondingPosition lineTwo = lineFive
correspondingPosition lineThree = lineSix
correspondingPosition lineFour = lineOne
correspondingPosition lineFive = lineTwo
correspondingPosition lineSix = lineThree

correspondenceIsInvolutive :
  (position : LinePosition) →
  correspondingPosition (correspondingPosition position) ≡ position
correspondenceIsInvolutive lineOne = refl
correspondenceIsInvolutive lineTwo = refl
correspondenceIsInvolutive lineThree = refl
correspondenceIsInvolutive lineFour = refl
correspondenceIsInvolutive lineFive = refl
correspondenceIsInvolutive lineSix = refl

areOpposedNonzero :
  Triadic.KernelTrit → Triadic.KernelTrit → Bool
areOpposedNonzero Triadic.negativeTrit Triadic.positiveTrit = true
areOpposedNonzero Triadic.positiveTrit Triadic.negativeTrit = true
areOpposedNonzero x y = false

positionCorresponds : LinePosition → Yijing.TernaryHexagram → Bool
positionCorresponds position hexagram =
  areOpposedNonzero
    (lineAt position hexagram)
    (lineAt (correspondingPosition position) hexagram)

canonicalLineTwoIsCentral : isCentralPosition lineTwo ≡ true
canonicalLineTwoIsCentral = refl

canonicalLineFiveIsCentral : isCentralPosition lineFive ≡ true
canonicalLineFiveIsCentral = refl

canonicalCastLineOneCorresponds :
  positionCorresponds lineOne canonicalCastInitial ≡ true
canonicalCastLineOneCorresponds = refl

------------------------------------------------------------------------
-- Reversal, global complement, trigram exchange, and nuclear extraction.

reverseHexagram : Yijing.TernaryHexagram → Yijing.TernaryHexagram
reverseHexagram
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) =
  f vcons e vcons d vcons c vcons b vcons a vcons vnil

complementHexagram : Yijing.TernaryHexagram → Yijing.TernaryHexagram
complementHexagram
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) =
  Triadic.negateTrit a vcons
  Triadic.negateTrit b vcons
  Triadic.negateTrit c vcons
  Triadic.negateTrit d vcons
  Triadic.negateTrit e vcons
  Triadic.negateTrit f vcons
  vnil

exchangeTrigrams : Yijing.TernaryHexagram → Yijing.TernaryHexagram
exchangeTrigrams
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) =
  d vcons e vcons f vcons a vcons b vcons c vcons vnil

nuclearHexagram : Yijing.TernaryHexagram → Yijing.TernaryHexagram
nuclearHexagram
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) =
  b vcons c vcons d vcons c vcons d vcons e vcons vnil

reverseIsInvolutive :
  (x : Yijing.TernaryHexagram) → reverseHexagram (reverseHexagram x) ≡ x
reverseIsInvolutive
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = refl

exchangeIsInvolutive :
  (x : Yijing.TernaryHexagram) → exchangeTrigrams (exchangeTrigrams x) ≡ x
exchangeIsInvolutive
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = refl

complementIsInvolutive :
  (x : Yijing.TernaryHexagram) →
  complementHexagram (complementHexagram x) ≡ x
complementIsInvolutive
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil)
  with Triadic.negateTritInvolutive a
     | Triadic.negateTritInvolutive b
     | Triadic.negateTritInvolutive c
     | Triadic.negateTritInvolutive d
     | Triadic.negateTritInvolutive e
     | Triadic.negateTritInvolutive f
... | refl | refl | refl | refl | refl | refl = refl

canonicalNuclearExtraction :
  nuclearHexagram canonicalCastInitial
  ≡
  (Triadic.positiveTrit vcons
   Triadic.negativeTrit vcons
   Triadic.positiveTrit vcons
   Triadic.negativeTrit vcons
   Triadic.positiveTrit vcons
   Triadic.positiveTrit vcons
   vnil)
canonicalNuclearExtraction = refl

------------------------------------------------------------------------
-- Boundary declarations.

record YijingRelationalBoundary : Set where
  constructor yijingRelationalBoundary
  field
    positionalCorrectnessEntailsMoralGoodness : Bool
    positionalCorrectnessEntailsMoralGoodnessIsFalse :
      positionalCorrectnessEntailsMoralGoodness ≡ false

    everyTernaryTrigramHasReceivedBinaryImage : Bool
    everyTernaryTrigramHasReceivedBinaryImageIsFalse :
      everyTernaryTrigramHasReceivedBinaryImage ≡ false

    nuclearExtractionWasProvedEarliestZhouyiLayer : Bool
    nuclearExtractionWasProvedEarliestZhouyiLayerIsFalse :
      nuclearExtractionWasProvedEarliestZhouyiLayer ≡ false

    castTransformationEntailsExternalPrediction : Bool
    castTransformationEntailsExternalPredictionIsFalse :
      castTransformationEntailsExternalPrediction ≡ false

    correspondenceAtZeroCountsAsOpposition : Bool
    correspondenceAtZeroCountsAsOppositionIsFalse :
      correspondenceAtZeroCountsAsOpposition ≡ false

open YijingRelationalBoundary public

canonicalYijingRelationalBoundary : YijingRelationalBoundary
canonicalYijingRelationalBoundary =
  yijingRelationalBoundary false refl false refl false refl false refl false refl
