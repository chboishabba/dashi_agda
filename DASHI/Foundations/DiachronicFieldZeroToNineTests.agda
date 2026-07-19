module DASHI.Foundations.DiachronicFieldZeroToNineTests where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (neg; zer; pos)
open import DASHI.Foundations.DiachronicFieldZeroToNine

stage2-is-the-live-trans-opposition : Opposition
stage2-is-the-live-trans-opposition = transOpposition

self-resolution-is-stable :
  LocalClosure.close stage3Closure
    (LocalClosure.close stage3Closure resolveAtSelf)
  ≡ LocalClosure.close stage3Closure resolveAtSelf
self-resolution-is-stable = refl

sampleSix : SixField
sampleSix = sixView indeterminate transClaim transClaim notTransClaim

sampleSix-folds-twice : sixFold (sixFold sampleSix) ≡ sampleSix
sampleSix-folds-twice = refl

sampleSix-closure-is-idempotent :
  LocalClosure.close stage6Closure
    (LocalClosure.close stage6Closure sampleSix)
  ≡ LocalClosure.close stage6Closure sampleSix
sampleSix-closure-is-idempotent = refl

sampleNine : NineField
sampleNine = embed6Into9 sampleSix

sampleNine-closure-is-idempotent :
  LocalClosure.close stage9Closure
    (LocalClosure.close stage9Closure sampleNine)
  ≡ LocalClosure.close stage9Closure sampleNine
sampleNine-closure-is-idempotent = refl

three-closure-survives-six :
  PreservesLower.embed threeInsideSix
    (LocalClosure.close stage3Closure resolveAtSelf)
  ≡
  LocalClosure.close stage6Closure
    (PreservesLower.embed threeInsideSix resolveAtSelf)
three-closure-survives-six = refl

six-closure-survives-nine :
  PreservesLower.embed sixInsideNine
    (LocalClosure.close stage6Closure sampleSix)
  ≡
  LocalClosure.close stage9Closure
    (PreservesLower.embed sixInsideNine sampleSix)
six-closure-survives-nine = refl

data Axis3 : Set where
  somatic temporal social : Axis3

data Axis9 : Set where
  old : Axis3 → Axis9
  legal cultural physical unrelated selfOther foldOrder : Axis9

samplePattern3 : DiffractionPattern Axis3
samplePattern3 somatic = pos
samplePattern3 temporal = zer
samplePattern3 social = neg

promote3to9 : DiffractionPattern Axis3 → DiffractionPattern Axis9
promote3to9 p (old a) = p a
promote3to9 p legal = zer
promote3to9 p cultural = zer
promote3to9 p physical = zer
promote3to9 p unrelated = zer
promote3to9 p selfOther = zer
promote3to9 p foldOrder = zer

threeToNineDiffraction : DiffractionPromotion Axis3 Axis9
threeToNineDiffraction = record
  { injectAxis = old
  ; promote = promote3to9
  ; preservesOldAxes = λ _ _ → refl
  }

somatic-sign-survives-promotion :
  DiffractionPromotion.promote threeToNineDiffraction samplePattern3
    (DiffractionPromotion.injectAxis threeToNineDiffraction somatic)
  ≡ pos
somatic-sign-survives-promotion = refl

mirror-is-bidirectional-on-social-axis :
  pointwiseMirror (pointwiseMirror samplePattern3) social ≡ neg
mirror-is-bidirectional-on-social-axis = refl
