module DASHI.ComputerScience.TekumRegimeExponentExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _∸_)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem

------------------------------------------------------------------------
-- Exact finite regime table from Hunhold Definition 8.
--
-- The allowed anchored three-trit prefixes are precisely the balanced-ternary
-- representations of -7..7, rather than all 27 possible three-trit words.

data RegimeCode : Set where
  rm7 rm6 rm5 rm4 rm3 rm2 rm1 r0 rp1 rp2 rp3 rp4 rp5 rp6 rp7 : RegimeCode

regimeTrits : RegimeCode → Anchor.Regime3
regimeTrits rm7 = Anchor.regime3 Trit.neg Trit.pos Trit.neg
regimeTrits rm6 = Anchor.regime3 Trit.neg Trit.pos Trit.zer
regimeTrits rm5 = Anchor.regime3 Trit.neg Trit.pos Trit.pos
regimeTrits rm4 = Anchor.regime3 Trit.zer Trit.neg Trit.neg
regimeTrits rm3 = Anchor.regime3 Trit.zer Trit.neg Trit.zer
regimeTrits rm2 = Anchor.regime3 Trit.zer Trit.neg Trit.pos
regimeTrits rm1 = Anchor.regime3 Trit.zer Trit.zer Trit.neg
regimeTrits r0  = Anchor.regime3 Trit.zer Trit.zer Trit.zer
regimeTrits rp1 = Anchor.regime3 Trit.zer Trit.zer Trit.pos
regimeTrits rp2 = Anchor.regime3 Trit.zer Trit.pos Trit.neg
regimeTrits rp3 = Anchor.regime3 Trit.zer Trit.pos Trit.zer
regimeTrits rp4 = Anchor.regime3 Trit.zer Trit.pos Trit.pos
regimeTrits rp5 = Anchor.regime3 Trit.pos Trit.neg Trit.neg
regimeTrits rp6 = Anchor.regime3 Trit.pos Trit.neg Trit.zer
regimeTrits rp7 = Anchor.regime3 Trit.pos Trit.neg Trit.pos

decodeRegime : Anchor.Regime3 → Maybe RegimeCode
decodeRegime (Anchor.regime3 Trit.neg Trit.pos Trit.neg) = just rm7
decodeRegime (Anchor.regime3 Trit.neg Trit.pos Trit.zer) = just rm6
decodeRegime (Anchor.regime3 Trit.neg Trit.pos Trit.pos) = just rm5
decodeRegime (Anchor.regime3 Trit.zer Trit.neg Trit.neg) = just rm4
decodeRegime (Anchor.regime3 Trit.zer Trit.neg Trit.zer) = just rm3
decodeRegime (Anchor.regime3 Trit.zer Trit.neg Trit.pos) = just rm2
decodeRegime (Anchor.regime3 Trit.zer Trit.zer Trit.neg) = just rm1
decodeRegime (Anchor.regime3 Trit.zer Trit.zer Trit.zer) = just r0
decodeRegime (Anchor.regime3 Trit.zer Trit.zer Trit.pos) = just rp1
decodeRegime (Anchor.regime3 Trit.zer Trit.pos Trit.neg) = just rp2
decodeRegime (Anchor.regime3 Trit.zer Trit.pos Trit.zer) = just rp3
decodeRegime (Anchor.regime3 Trit.zer Trit.pos Trit.pos) = just rp4
decodeRegime (Anchor.regime3 Trit.pos Trit.neg Trit.neg) = just rp5
decodeRegime (Anchor.regime3 Trit.pos Trit.neg Trit.zer) = just rp6
decodeRegime (Anchor.regime3 Trit.pos Trit.neg Trit.pos) = just rp7
decodeRegime _ = nothing

decodeEncodeRegime :
  (r : RegimeCode) → decodeRegime (regimeTrits r) ≡ just r
decodeEncodeRegime rm7 = refl
decodeEncodeRegime rm6 = refl
decodeEncodeRegime rm5 = refl
decodeEncodeRegime rm4 = refl
decodeEncodeRegime rm3 = refl
decodeEncodeRegime rm2 = refl
decodeEncodeRegime rm1 = refl
decodeEncodeRegime r0 = refl
decodeEncodeRegime rp1 = refl
decodeEncodeRegime rp2 = refl
decodeEncodeRegime rp3 = refl
decodeEncodeRegime rp4 = refl
decodeEncodeRegime rp5 = refl
decodeEncodeRegime rp6 = refl
decodeEncodeRegime rp7 = refl

absRegime : RegimeCode → Nat
absRegime rm7 = 7
absRegime rm6 = 6
absRegime rm5 = 5
absRegime rm4 = 4
absRegime rm3 = 3
absRegime rm2 = 2
absRegime rm1 = 1
absRegime r0 = 0
absRegime rp1 = 1
absRegime rp2 = 2
absRegime rp3 = 3
absRegime rp4 = 4
absRegime rp5 = 5
absRegime rp6 = 6
absRegime rp7 = 7

exponentCount : RegimeCode → Nat
exponentCount r = absRegime r ∸ 2

biasMagnitude : RegimeCode → Nat
biasMagnitude rm7 = 244
biasMagnitude rm6 = 82
biasMagnitude rm5 = 28
biasMagnitude rm4 = 10
biasMagnitude rm3 = 4
biasMagnitude rm2 = 2
biasMagnitude rm1 = 1
biasMagnitude r0 = 0
biasMagnitude rp1 = 1
biasMagnitude rp2 = 2
biasMagnitude rp3 = 4
biasMagnitude rp4 = 10
biasMagnitude rp5 = 28
biasMagnitude rp6 = 82
biasMagnitude rp7 = 244

bias : RegimeCode → Sem.IntCode
bias rm7 = Sem.negative 244
bias rm6 = Sem.negative 82
bias rm5 = Sem.negative 28
bias rm4 = Sem.negative 10
bias rm3 = Sem.negative 4
bias rm2 = Sem.negative 2
bias rm1 = Sem.negative 1
bias r0 = Sem.nonnegative 0
bias rp1 = Sem.nonnegative 1
bias rp2 = Sem.nonnegative 2
bias rp3 = Sem.nonnegative 4
bias rp4 = Sem.nonnegative 10
bias rp5 = Sem.nonnegative 28
bias rp6 = Sem.nonnegative 82
bias rp7 = Sem.nonnegative 244

fractionCount : Nat → RegimeCode → Nat
fractionCount n r = n ∸ (exponentCount r + 3)

outerRegimeUsesFiveExponentTrits :
  exponentCount rp7 ≡ 5
outerRegimeUsesFiveExponentTrits = refl

centralRegimeUsesNoExponentTrits :
  exponentCount r0 ≡ 0
centralRegimeUsesNoExponentTrits = refl

outerPositiveBiasIs244 : bias rp7 ≡ Sem.nonnegative 244
outerPositiveBiasIs244 = refl

outerNegativeBiasIsMinus244 : bias rm7 ≡ Sem.negative 244
outerNegativeBiasIsMinus244 = refl

record TekumRegimeBoundary : Set where
  constructor tekumRegimeBoundary
  field
    fifteenAnchoredRegimesEncoded : Bool
    regimeCodecRoundTripsOnImage : Bool
    exponentCountRuleImplemented : Bool
    sourceBiasTableImplemented : Bool

canonicalTekumRegimeBoundary : TekumRegimeBoundary
canonicalTekumRegimeBoundary =
  tekumRegimeBoundary true true true true
