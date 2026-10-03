module DASHI.ComputerScience.TekumAnchorCodecExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Vec using (Vec)

import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- The anchor is a same-width balanced-ternary word. Hunhold Definition 7 is
-- anc_n(t)=|t|-1T...1T at even source widths. The arithmetic constructor and
-- literal alternating midpoint are owned by TekumFixedWidthBalancedArithmetic-
-- Exact / TekumSourceAnchorCenterExact; this module owns only the lossless
-- field split/rejoin used downstream.
------------------------------------------------------------------------

record Regime3 : Set where
  constructor regime3
  field
    r2 r1 r0 : Trit.Trit
open Regime3 public

record AnchorFields (n : Nat) : Set where
  constructor anchorFields
  field
    regime : Regime3
    exponentCount : Nat
    fractionCount : Nat
    exponentPlusFraction : Vec Trit.Trit n
open AnchorFields public

record CertifiedAnchorFields (n : Nat) : Set where
  constructor certifiedAnchorFields
  field
    fields : AnchorFields n
    payloadLengthConserved :
      exponentCount fields + fractionCount fields ≡ n
open CertifiedAnchorFields public

data TekumSign : Set where
  negativeSign : TekumSign
  zeroSign : TekumSign
  positiveSign : TekumSign

flipSign : TekumSign → TekumSign
flipSign negativeSign = positiveSign
flipSign zeroSign = zeroSign
flipSign positiveSign = negativeSign

flipSign-involutive : (s : TekumSign) → flipSign (flipSign s) ≡ s
flipSign-involutive negativeSign = refl
flipSign-involutive zeroSign = refl
flipSign-involutive positiveSign = refl

record AnchoredTekum (n : Nat) : Set where
  constructor anchoredTekum
  field
    sign : TekumSign
    anchorFieldsCertified : CertifiedAnchorFields n
open AnchoredTekum public

negateAnchored : ∀ {n} → AnchoredTekum n → AnchoredTekum n
negateAnchored (anchoredTekum s a) = anchoredTekum (flipSign s) a

negateAnchored-involutive :
  ∀ {n} (x : AnchoredTekum n) → negateAnchored (negateAnchored x) ≡ x
negateAnchored-involutive (anchoredTekum negativeSign a) = refl
negateAnchored-involutive (anchoredTekum zeroSign a) = refl
negateAnchored-involutive (anchoredTekum positiveSign a) = refl
