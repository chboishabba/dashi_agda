module DASHI.Visualisation.CMYKARendererAttachmentExact where

-- Literal original finite renderer and CMYKA source carrier. In particular
-- RendererParityExact uses red <- magenta, green <- yellow, blue <- cyan.
-- Do not silently change its channels to an external display convention.
open import DASHI.Core.Prelude
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
import DASHI.Visual.ColourPerceptionDASHI as Colour
import DASHI.Visualisation.RendererParityExact as R
import DASHI.Visualisation.RendererStabilityExact as S

record Sample : Set where
  constructor sample
  field
    ink : R.CMYK
    alpha : R.BitChannel
open Sample public

asNat : R.BitChannel → Nat
asNat R.channelZero = zero
asNat R.channelOne = 1

asBit : Nat → Maybe R.BitChannel
asBit zero = just R.channelZero
asBit (suc zero) = just R.channelOne
asBit (suc (suc n)) = nothing

bitReopens : (b : R.BitChannel) → asBit (asNat b) ≡ just b
bitReopens R.channelZero = refl
bitReopens R.channelOne = refl

embed : Sample → Colour.CMYKA
embed (sample (R.cmyk c m y k) a) = record
  { cmykaCyan = asNat c
  ; cmykaMagenta = asNat m
  ; cmykaYellow = asNat y
  ; cmykaKey = asNat k
  ; cmykaAlpha = asNat a }

-- Reject uncalibrated general Nat colour values, not silently clip them.
decode : Colour.CMYKA → Maybe Sample
decode x with asBit (Colour.CMYKA.cmykaCyan x)
             | asBit (Colour.CMYKA.cmykaMagenta x)
             | asBit (Colour.CMYKA.cmykaYellow x)
             | asBit (Colour.CMYKA.cmykaKey x)
             | asBit (Colour.CMYKA.cmykaAlpha x)
... | just c | just m | just y | just k | just a =
  just (sample (R.cmyk c m y k) a)
... | _ | _ | _ | _ | _ = nothing

reopen : (s : Sample) → decode (embed s) ≡ just s
reopen (sample (R.cmyk c m y k) a)
  rewrite bitReopens c | bitReopens m | bitReopens y | bitReopens k
        | bitReopens a = refl

premultiply : R.BitChannel → R.RGB → R.RGB
premultiply a (R.rgb r g b) =
  R.rgb (R.multiplyChannel a r) (R.multiplyChannel a g) (R.multiplyChannel a b)

read : Sample → R.RGB
read s = premultiply (alpha s) (R.cmykToRGB (ink s))

opaqueParity : (ink : R.CMYK) →
  read (sample ink R.channelOne) ≡ R.cmykToRGB ink
opaqueParity (R.cmyk c m y k) = refl

transparentParity : (ink : R.CMYK) →
  read (sample ink R.channelZero) ≡ R.rgb R.channelZero R.channelZero R.channelZero
transparentParity (R.cmyk c m y k) = refl

-- Actual original front-to-back Fraction operators, not a competing
-- straight-alpha renderer. Accumulated channels are premultiplied.
record Accumulator : Set where
  constructor accum
  field
    red green blue opacity : S.Fraction
open Accumulator public

bitFraction : R.BitChannel → S.Fraction
bitFraction b = S.fraction (asNat b) 1

empty : Accumulator
empty = accum (S.fraction 0 1) (S.fraction 0 1)
              (S.fraction 0 1) (S.fraction 0 1)

append : Accumulator → Sample → Accumulator
append (accum r g b a) (sample i k) with R.cmykToRGB i
... | R.rgb x y z = accum
  (S.frontToBackColour r a (bitFraction x) (bitFraction k))
  (S.frontToBackColour g a (bitFraction y) (bitFraction k))
  (S.frontToBackColour b a (bitFraction z) (bitFraction k))
  (S.frontToBackAlpha a (bitFraction k))

render : Accumulator → List Sample → Accumulator
render a [] = a
render a (p ∷ ps) = render (append a p) ps

join : {X : Set} → List X → List X → List X
join [] ys = ys
join (x ∷ xs) ys = x ∷ join xs ys

-- Ordered chunking is exact even for the original unreduced fractions,
-- because evaluation preserves the literal source sequence.
orderedChunk : (a : Accumulator) (xs ys : List Sample) →
  render a (join xs ys) ≡ render (render a xs) ys
orderedChunk a [] ys = refl
orderedChunk a (x ∷ xs) ys = orderedChunk (append a x) xs ys

-- Transparent samples can carry different original material values;
-- retain actual source and execution history separately from readout.
record Receipt : Set where
  constructor receipt
  field
    original : List Sample
    rendered : Accumulator
    rendererMatches : rendered ≡ render empty original

makeReceipt : (xs : List Sample) → Receipt
makeReceipt xs = receipt xs (render empty xs) refl

-- This attaches the exact finite source bit renderer. General rational
-- moments/ordered segment algebra have independent local acceptance;
-- physical colour profile, video pixel producer and kernel remain separate.
