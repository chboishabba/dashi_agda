module DASHI.Physics.Closure.NSTriadKNComResidualShellCapRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 63 B0 RESIDUAL CAP
--
-- After routing the three separated Bony classes LH / HL / HH->L, the residual
-- class is not automatically width one.  Resonance forces the exact finite band
--
--   j(k) <= j(q)+3,     j(q) <= j(k)+3.
--
-- The proof uses only failure of the three separation tests plus the already
-- proved infinity-norm resonance triangles.  Hence post-routing Com analysis
-- has a finite transition band: separations 0,1,2,3.  Gaps 2/3 cannot be hidden
-- in a width-one common hat.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; ∣_-_∣)
import Data.Nat.Properties as Nat
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicConsequencesClosed as Dyadic

leOneSuccessor : (n : Nat) → n ≤ suc n
leOneSuccessor zero = z≤n
leOneSuccessor (suc n) = s≤s (leOneSuccessor n)

leTwoSuccessors : (n : Nat) → n ≤ suc (suc n)
leTwoSuccessors n = Nat.≤-trans (leOneSuccessor n) (leOneSuccessor (suc n))

notGapThreeImpliesUpperTwo :
  (lower higher : Nat) →
  ¬ (lower + 3 ≤ higher) →
  higher ≤ suc (suc lower)
notGapThreeImpliesUpperTwo zero zero notGap = z≤n
notGapThreeImpliesUpperTwo zero (suc zero) notGap = s≤s z≤n
notGapThreeImpliesUpperTwo zero (suc (suc zero)) notGap = s≤s (s≤s z≤n)
notGapThreeImpliesUpperTwo zero (suc (suc (suc higher))) notGap =
  ⊥-elim (notGap (s≤s (s≤s (s≤s z≤n))))
notGapThreeImpliesUpperTwo (suc lower) zero notGap = z≤n
notGapThreeImpliesUpperTwo (suc lower) (suc higher) notGap =
  s≤s
    (notGapThreeImpliesUpperTwo lower higher
      (λ gap → notGap (s≤s gap)))

record ResidualInputOutputBand
    (tau : Physical.PhysicalTriadIncidence) : Set where
  field
    outputAtMostThreeAboveInput :
      Shell.shellIndex (Physical.k tau)
      ≤ suc (suc (suc (Shell.shellIndex (Physical.q tau))))
    inputAtMostThreeAboveOutput :
      Shell.shellIndex (Physical.q tau)
      ≤ suc (suc (suc (Shell.shellIndex (Physical.k tau))))

open ResidualInputOutputBand public

residualInputOutputBand :
  (tau : Physical.PhysicalTriadIncidence) →
  (notLH : ¬ (Shell.shellIndex (Physical.p tau) + Shell.Csep
    ≤ Shell.shellIndex (Physical.q tau))) →
  (notHL : ¬ (Shell.shellIndex (Physical.q tau) + Shell.Csep
    ≤ Shell.shellIndex (Physical.p tau))) →
  (notHH :
    (¬ (Shell.shellIndex (Physical.k tau) + Shell.Csep
      ≤ Shell.shellIndex (Physical.p tau)))
    ⊎
    (¬ (Shell.shellIndex (Physical.k tau) + Shell.Csep
      ≤ Shell.shellIndex (Physical.q tau)))) →
  ResidualInputOutputBand tau
residualInputOutputBand tau notLH notHL notHH = record
  { outputAtMostThreeAboveInput = outputUpper
  ; inputAtMostThreeAboveOutput = inputUpper
  }
  where
  jp = Shell.shellIndex (Physical.p tau)
  jq = Shell.shellIndex (Physical.q tau)
  jk = Shell.shellIndex (Physical.k tau)

  pAtMostTwoAboveQ : jp ≤ suc (suc jq)
  pAtMostTwoAboveQ = notGapThreeImpliesUpperTwo jq jp notHL

  consequences : Infinity.OfficialResonantNormConsequences tau
  consequences = Infinity.officialResonantNormConsequences tau

  outputUpper : jk ≤ suc (suc (suc jq))
  outputUpper with Nat.≤-total jp jq
  ... | inj₁ p≤q =
    Nat.≤-trans
      (Dyadic.shellOfNormSumUpperRight
        {left = Infinity.infinityNorm (Physical.p tau)}
        {right = Infinity.infinityNorm (Physical.q tau)}
        {output = Infinity.infinityNorm (Physical.k tau)}
        (Infinity.outputTriangle consequences)
        p≤q)
      (s≤s (leTwoSuccessors jq))
  ... | inj₂ q≤p =
    Nat.≤-trans
      (Dyadic.shellOfNormSumUpperRight
        {left = Infinity.infinityNorm (Physical.q tau)}
        {right = Infinity.infinityNorm (Physical.p tau)}
        {output = Infinity.infinityNorm (Physical.k tau)}
        (subst
          (λ sum → Infinity.infinityNorm (Physical.k tau) ≤ sum)
          (Nat.+-comm
            (Infinity.infinityNorm (Physical.p tau))
            (Infinity.infinityNorm (Physical.q tau)))
          (Infinity.outputTriangle consequences))
        q≤p)
      (s≤s pAtMostTwoAboveQ)

  inputUpper : jq ≤ suc (suc (suc jk))
  inputUpper with notHH
  ... | inj₂ notKGapQ =
    Nat.≤-trans
      (notGapThreeImpliesUpperTwo jk jq notKGapQ)
      (leOneSuccessor (suc (suc jk)))
  ... | inj₁ notKGapP =
    inputFromP
      (notGapThreeImpliesUpperTwo jk jp notKGapP)
      (Nat.≤-total jp jk)
    where
    inputFromP :
      jp ≤ suc (suc jk) →
      (jp ≤ jk ⊎ jk ≤ jp) →
      jq ≤ suc (suc (suc jk))
    inputFromP p≤k2 (inj₁ p≤k) =
      Nat.≤-trans
        (Dyadic.shellOfNormSumUpperRight
          {left = Infinity.infinityNorm (Physical.p tau)}
          {right = Infinity.infinityNorm (Physical.k tau)}
          {output = Infinity.infinityNorm (Physical.q tau)}
          (subst
            (λ sum → Infinity.infinityNorm (Physical.q tau) ≤ sum)
            (Nat.+-comm
              (Infinity.infinityNorm (Physical.k tau))
              (Infinity.infinityNorm (Physical.p tau)))
            (Infinity.qReverseTriangle consequences))
          p≤k)
        (s≤s (leTwoSuccessors jk))
    inputFromP p≤k2 (inj₂ k≤p) =
      Nat.≤-trans
        (Dyadic.shellOfNormSumUpperRight
          {left = Infinity.infinityNorm (Physical.k tau)}
          {right = Infinity.infinityNorm (Physical.p tau)}
          {output = Infinity.infinityNorm (Physical.q tau)}
          (Infinity.qReverseTriangle consequences)
          k≤p)
        (s≤s p≤k2)

mutual
  shellDistanceAtMostThree :
    ∀ {left right} →
    left ≤ suc (suc (suc right)) →
    right ≤ suc (suc (suc left)) →
    ∣ left - right ∣ ≤ 3
  shellDistanceAtMostThree {zero} {zero} leftBound rightBound = z≤n
  shellDistanceAtMostThree {zero} {suc zero} leftBound rightBound = s≤s z≤n
  shellDistanceAtMostThree {zero} {suc (suc zero)} leftBound rightBound =
    s≤s (s≤s z≤n)
  shellDistanceAtMostThree {zero} {suc (suc (suc zero))} leftBound rightBound =
    s≤s (s≤s (s≤s z≤n))
  shellDistanceAtMostThree {zero} {suc (suc (suc (suc right)))}
    leftBound (s≤s (s≤s (s≤s ())))
  shellDistanceAtMostThree {suc zero} {zero} leftBound rightBound = s≤s z≤n
  shellDistanceAtMostThree {suc (suc zero)} {zero} leftBound rightBound =
    s≤s (s≤s z≤n)
  shellDistanceAtMostThree {suc (suc (suc zero))} {zero} leftBound rightBound =
    s≤s (s≤s (s≤s z≤n))
  shellDistanceAtMostThree {suc (suc (suc (suc left)))} {zero}
    (s≤s (s≤s (s≤s ()))) rightBound
  shellDistanceAtMostThree {suc left} {suc right}
    (s≤s leftBound) (s≤s rightBound) =
    shellDistanceAtMostThree leftBound rightBound

residualInputOutputDistanceAtMostThree :
  (tau : Physical.PhysicalTriadIncidence) →
  (notLH : ¬ (Shell.shellIndex (Physical.p tau) + Shell.Csep
    ≤ Shell.shellIndex (Physical.q tau))) →
  (notHL : ¬ (Shell.shellIndex (Physical.q tau) + Shell.Csep
    ≤ Shell.shellIndex (Physical.p tau))) →
  (notHH :
    (¬ (Shell.shellIndex (Physical.k tau) + Shell.Csep
      ≤ Shell.shellIndex (Physical.p tau)))
    ⊎
    (¬ (Shell.shellIndex (Physical.k tau) + Shell.Csep
      ≤ Shell.shellIndex (Physical.q tau)))) →
  ∣ Shell.shellIndex (Physical.k tau)
    - Shell.shellIndex (Physical.q tau) ∣ ≤ 3
residualInputOutputDistanceAtMostThree tau notLH notHL notHH =
  let band = residualInputOutputBand tau notLH notHL notHH
  in shellDistanceAtMostThree
      (outputAtMostThreeAboveInput band)
      (inputAtMostThreeAboveOutput band)

literalBonyResidualHasFiniteThreeShellBand : Bool
literalBonyResidualHasFiniteThreeShellBand = true

literalBonyResidualHasFiniteThreeShellBandIsTrue :
  literalBonyResidualHasFiniteThreeShellBand ≡ true
literalBonyResidualHasFiniteThreeShellBandIsTrue = refl
