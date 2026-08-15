module DASHI.Physics.Closure.NSTriadKNLiteralDyadicConsequencesClosed where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; ∣_-_∣)
import Data.Nat.Properties as Nat
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNCeilLogShellBounds as Bounds
import DASHI.Physics.Closure.NSTriadKNShellFactorTwo as FactorTwo

------------------------------------------------------------------------
-- A sum of two magnitudes lies at most one shell above the larger input.
------------------------------------------------------------------------

doublePow2 : ∀ n → Shell.pow2 n + Shell.pow2 n ≡ Shell.pow2 (suc n)
doublePow2 n =
  trans
    (cong
      (λ right → Shell.pow2 n + right)
      (sym (Nat.*-identityʳ (Shell.pow2 n))))
    (trans
      (sym (Nat.*-suc (Shell.pow2 n) 1))
      (Nat.*-comm (Shell.pow2 n) 2))

shellOfNormSumUpperRight :
  ∀ {left right output} →
  output ≤ left + right →
  Shell.shellIndexMagnitude left ≤ Shell.shellIndexMagnitude right →
  Shell.shellIndexMagnitude output
  ≤ suc (Shell.shellIndexMagnitude right)
shellOfNormSumUpperRight {left} {right} {output} output≤sum leftShell≤rightShell =
  subst
    (λ upper → Shell.shellIndexMagnitude output ≤ upper)
    (Shell.shellIndexPowerOfTwo (suc (Shell.shellIndexMagnitude right)))
    (Shell.shellIndexMonotone output≤power)
  where
  left≤rightPower :
    left ≤ Shell.pow2 (Shell.shellIndexMagnitude right)
  left≤rightPower =
    Nat.≤-trans
      (Bounds.ceilLogShellUpperMagnitude left)
      (Nat.^-monoʳ-≤ 2 leftShell≤rightShell)

  right≤rightPower :
    right ≤ Shell.pow2 (Shell.shellIndexMagnitude right)
  right≤rightPower = Bounds.ceilLogShellUpperMagnitude right

  output≤double :
    output ≤
    Shell.pow2 (Shell.shellIndexMagnitude right)
    + Shell.pow2 (Shell.shellIndexMagnitude right)
  output≤double =
    Nat.≤-trans output≤sum
      (Nat.+-mono-≤ left≤rightPower right≤rightPower)

  output≤power :
    output ≤ Shell.pow2 (suc (Shell.shellIndexMagnitude right))
  output≤power =
    subst
      (λ bound → output ≤ bound)
      (doublePow2 (Shell.shellIndexMagnitude right))
      output≤double

shellGapThreeImpliesLowerShellLeHigher :
  ∀ {lower higher} → lower + 3 ≤ higher → lower ≤ higher
shellGapThreeImpliesLowerShellLeHigher {lower} gap =
  Nat.≤-trans (Nat.m≤m+n lower 3) gap

threeNotLeOne : 3 ≤ 1 → ⊥
threeNotLeOne (s≤s ())

gapThreeContradictsUpperSuccessor :
  ∀ {lower higher} →
  lower + 3 ≤ higher →
  higher ≤ suc lower →
  ⊥
gapThreeContradictsUpperSuccessor {lower} {higher} gap upper =
  threeNotLeOne
    (Nat.+-cancelˡ-≤ lower 3 1
      (subst
        (λ right → lower + 3 ≤ right)
        (sym (Nat.+-comm lower 1))
        (Nat.≤-trans gap upper)))

one≤two : 1 ≤ 2
one≤two = s≤s z≤n

------------------------------------------------------------------------
-- Low-high and high-low output tracking.
------------------------------------------------------------------------

lowHighOutputTracksHighOne :
  (τ : Physical.PhysicalTriadIncidence) →
  Shell.shellIndex (Physical.p τ) + 3
    ≤ Shell.shellIndex (Physical.q τ) →
  ∣ Shell.shellIndex (Physical.k τ)
    - Shell.shellIndex (Physical.q τ) ∣ ≤ 1
lowHighOutputTracksHighOne τ gap =
  FactorTwo.shellDistanceAtMostOne outputUpper highUpper
  where
  consequences : Infinity.OfficialResonantNormConsequences τ
  consequences = Infinity.officialResonantNormConsequences τ

  pShell≤qShell :
    Shell.shellIndex (Physical.p τ)
    ≤ Shell.shellIndex (Physical.q τ)
  pShell≤qShell = shellGapThreeImpliesLowerShellLeHigher gap

  outputUpper :
    Shell.shellIndex (Physical.k τ)
    ≤ suc (Shell.shellIndex (Physical.q τ))
  outputUpper =
    shellOfNormSumUpperRight
      {left = Infinity.infinityNorm (Physical.p τ)}
      {right = Infinity.infinityNorm (Physical.q τ)}
      {output = Infinity.infinityNorm (Physical.k τ)}
      (Infinity.outputTriangle consequences)
      pShell≤qShell

  highUpper :
    Shell.shellIndex (Physical.q τ)
    ≤ suc (Shell.shellIndex (Physical.k τ))
  highUpper with
    Nat.≤-total
      (Shell.shellIndex (Physical.p τ))
      (Shell.shellIndex (Physical.k τ))
  ... | inj₁ pShell≤kShell =
    shellOfNormSumUpperRight
      {left = Infinity.infinityNorm (Physical.p τ)}
      {right = Infinity.infinityNorm (Physical.k τ)}
      {output = Infinity.infinityNorm (Physical.q τ)}
      (subst
        (λ sum → Infinity.infinityNorm (Physical.q τ) ≤ sum)
        (Nat.+-comm
          (Infinity.infinityNorm (Physical.k τ))
          (Infinity.infinityNorm (Physical.p τ)))
        (Infinity.qReverseTriangle consequences))
      pShell≤kShell
  ... | inj₂ kShell≤pShell =
    ⊥-elim
      (gapThreeContradictsUpperSuccessor gap
        (shellOfNormSumUpperRight
          {left = Infinity.infinityNorm (Physical.k τ)}
          {right = Infinity.infinityNorm (Physical.p τ)}
          {output = Infinity.infinityNorm (Physical.q τ)}
          (Infinity.qReverseTriangle consequences)
          kShell≤pShell))

highLowOutputTracksHighOne :
  (τ : Physical.PhysicalTriadIncidence) →
  Shell.shellIndex (Physical.q τ) + 3
    ≤ Shell.shellIndex (Physical.p τ) →
  ∣ Shell.shellIndex (Physical.k τ)
    - Shell.shellIndex (Physical.p τ) ∣ ≤ 1
highLowOutputTracksHighOne τ gap =
  FactorTwo.shellDistanceAtMostOne outputUpper highUpper
  where
  consequences : Infinity.OfficialResonantNormConsequences τ
  consequences = Infinity.officialResonantNormConsequences τ

  qShell≤pShell :
    Shell.shellIndex (Physical.q τ)
    ≤ Shell.shellIndex (Physical.p τ)
  qShell≤pShell = shellGapThreeImpliesLowerShellLeHigher gap

  outputUpper :
    Shell.shellIndex (Physical.k τ)
    ≤ suc (Shell.shellIndex (Physical.p τ))
  outputUpper =
    shellOfNormSumUpperRight
      {left = Infinity.infinityNorm (Physical.q τ)}
      {right = Infinity.infinityNorm (Physical.p τ)}
      {output = Infinity.infinityNorm (Physical.k τ)}
      (subst
        (λ sum → Infinity.infinityNorm (Physical.k τ) ≤ sum)
        (Nat.+-comm
          (Infinity.infinityNorm (Physical.p τ))
          (Infinity.infinityNorm (Physical.q τ)))
        (Infinity.outputTriangle consequences))
      qShell≤pShell

  highUpper :
    Shell.shellIndex (Physical.p τ)
    ≤ suc (Shell.shellIndex (Physical.k τ))
  highUpper with
    Nat.≤-total
      (Shell.shellIndex (Physical.q τ))
      (Shell.shellIndex (Physical.k τ))
  ... | inj₁ qShell≤kShell =
    shellOfNormSumUpperRight
      {left = Infinity.infinityNorm (Physical.q τ)}
      {right = Infinity.infinityNorm (Physical.k τ)}
      {output = Infinity.infinityNorm (Physical.p τ)}
      (subst
        (λ sum → Infinity.infinityNorm (Physical.p τ) ≤ sum)
        (Nat.+-comm
          (Infinity.infinityNorm (Physical.k τ))
          (Infinity.infinityNorm (Physical.q τ)))
        (Infinity.pReverseTriangle consequences))
      qShell≤kShell
  ... | inj₂ kShell≤qShell =
    ⊥-elim
      (gapThreeContradictsUpperSuccessor gap
        (shellOfNormSumUpperRight
          {left = Infinity.infinityNorm (Physical.k τ)}
          {right = Infinity.infinityNorm (Physical.q τ)}
          {output = Infinity.infinityNorm (Physical.p τ)}
          (Infinity.pReverseTriangle consequences)
          kShell≤qShell))

------------------------------------------------------------------------
-- High-high-to-low input comparability.
------------------------------------------------------------------------

highHighToLowInputsComparableOne :
  (τ : Physical.PhysicalTriadIncidence) →
  Shell.shellIndex (Physical.k τ) + 3
    ≤ Shell.shellIndex (Physical.p τ) →
  Shell.shellIndex (Physical.k τ) + 3
    ≤ Shell.shellIndex (Physical.q τ) →
  ∣ Shell.shellIndex (Physical.p τ)
    - Shell.shellIndex (Physical.q τ) ∣ ≤ 1
highHighToLowInputsComparableOne τ kGapP kGapQ =
  FactorTwo.shellDistanceAtMostOne pUpper qUpper
  where
  consequences : Infinity.OfficialResonantNormConsequences τ
  consequences = Infinity.officialResonantNormConsequences τ

  kShell≤pShell :
    Shell.shellIndex (Physical.k τ)
    ≤ Shell.shellIndex (Physical.p τ)
  kShell≤pShell = shellGapThreeImpliesLowerShellLeHigher kGapP

  kShell≤qShell :
    Shell.shellIndex (Physical.k τ)
    ≤ Shell.shellIndex (Physical.q τ)
  kShell≤qShell = shellGapThreeImpliesLowerShellLeHigher kGapQ

  pUpper :
    Shell.shellIndex (Physical.p τ)
    ≤ suc (Shell.shellIndex (Physical.q τ))
  pUpper =
    shellOfNormSumUpperRight
      {left = Infinity.infinityNorm (Physical.k τ)}
      {right = Infinity.infinityNorm (Physical.q τ)}
      {output = Infinity.infinityNorm (Physical.p τ)}
      (Infinity.pReverseTriangle consequences)
      kShell≤qShell

  qUpper :
    Shell.shellIndex (Physical.q τ)
    ≤ suc (Shell.shellIndex (Physical.p τ))
  qUpper =
    shellOfNormSumUpperRight
      {left = Infinity.infinityNorm (Physical.k τ)}
      {right = Infinity.infinityNorm (Physical.p τ)}
      {output = Infinity.infinityNorm (Physical.q τ)}
      (Infinity.qReverseTriangle consequences)
      kShell≤pShell

------------------------------------------------------------------------
-- Official record at the selected conservative constants Cout = Cin = 2.
------------------------------------------------------------------------

literalDyadicConsequencesClosed :
  Shell.LiteralDyadicConsequences Bounds.literalDyadicShellBoundsClosed
literalDyadicConsequencesClosed = record
  { lowHighOutputTracksHigh = λ τ pNZ qNZ kNZ gap →
      Nat.≤-trans (lowHighOutputTracksHighOne τ gap) one≤two
  ; highLowOutputTracksHigh = λ τ pNZ qNZ kNZ gap →
      Nat.≤-trans (highLowOutputTracksHighOne τ gap) one≤two
  ; highHighToLowInputsComparable = λ τ pNZ qNZ kNZ gapP gapQ →
      Nat.≤-trans
        (highHighToLowInputsComparableOne τ gapP gapQ)
        one≤two
  }

fullLiteralDyadicConsequencesClosed : Bool
fullLiteralDyadicConsequencesClosed = true

fullLiteralDyadicConsequencesClosedIsTrue :
  fullLiteralDyadicConsequencesClosed ≡ true
fullLiteralDyadicConsequencesClosedIsTrue = refl
