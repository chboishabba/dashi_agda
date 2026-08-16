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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 63 B0 AUTHORITY-CORRECTED COMPARABLE CAP
--
-- Historical filename note: an earlier draft called this the `residual` cap
-- and used weak j+3<=j' separation.  The mature physical classifier instead
-- uses strict `natLess (j+3) j'`, and calls the fourth triadic class CC /
-- comparable.  This file now proves the correct theorem for that authoritative
-- class.
--
-- For every physical triad classified CC,
--
--   j(k) <= j(q)+4,
--   j(q) <= j(k)+4,
--
-- hence |j(k)-j(q)|<=4.
--
-- The extra shell versus the provisional three-shell theorem is the exact
-- off-by-one introduced by strict versus weak collar semantics.  This theorem
-- is diagnostic for the triadic summands of the differentiated commutator; it
-- does NOT identify CC with the fifth Com owner.  Round25 keeps CC and Com as
-- distinct sources.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; ∣_-_∣)
import Data.Nat.Properties as Nat
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSPeriodicNearTriadClassification as Near
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicConsequencesClosed as Dyadic
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale

natLessFalseImpliesReverseLe :
  (left right : Nat) →
  Near.natLess left right ≡ false →
  right ≤ left
natLessFalseImpliesReverseLe zero zero proof = z≤n
natLessFalseImpliesReverseLe zero (suc right) ()
natLessFalseImpliesReverseLe (suc left) zero proof = z≤n
natLessFalseImpliesReverseLe (suc left) (suc right) proof =
  s≤s (natLessFalseImpliesReverseLe left right proof)

leOneSuccessor : (n : Nat) → n ≤ suc n
leOneSuccessor zero = z≤n
leOneSuccessor (suc n) = s≤s (leOneSuccessor n)

leThreeSuccessors : (n : Nat) → n ≤ suc (suc (suc n))
leThreeSuccessors n =
  Nat.≤-trans
    (Nat.≤-trans (leOneSuccessor n) (leOneSuccessor (suc n)))
    (leOneSuccessor (suc (suc n)))

leFourSuccessors : (n : Nat) → n ≤ suc (suc (suc (suc n)))
leFourSuccessors n =
  Nat.≤-trans (leThreeSuccessors n) (leOneSuccessor (suc (suc (suc n))))

record ComparableInputOutputBand
    (tau : Physical.PhysicalTriadIncidence) : Set where
  field
    outputAtMostFourAboveInput :
      Support.literalShellPolicy Scale.PhysicalShellPolicy.shellLevel (Physical.k tau)
      ≤ suc (suc (suc (suc
          (Support.literalShellPolicy Scale.PhysicalShellPolicy.shellLevel (Physical.q tau)))))

    inputAtMostFourAboveOutput :
      Support.literalShellPolicy Scale.PhysicalShellPolicy.shellLevel (Physical.q tau)
      ≤ suc (suc (suc (suc
          (Support.literalShellPolicy Scale.PhysicalShellPolicy.shellLevel (Physical.k tau)))))

open ComparableInputOutputBand public

-- Use the shorter exported shell-level projection below.  It is definitionally
-- the literal shell index from the authoritative policy.
shell : Physical.PhysicalTriadIncidence → (Physical.PhysicalTriadIncidence → _) → Nat
shell tau projection = Scale.shellLevel Support.literalShellPolicy (projection tau)

comparableInputOutputBand :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.CC →
  ( Scale.shellLevel Support.literalShellPolicy (Physical.k tau)
      ≤ suc (suc (suc (suc
          (Scale.shellLevel Support.literalShellPolicy (Physical.q tau))))) )
  ×
  ( Scale.shellLevel Support.literalShellPolicy (Physical.q tau)
      ≤ suc (suc (suc (suc
          (Scale.shellLevel Support.literalShellPolicy (Physical.k tau))))) )
comparableInputOutputBand {tau} certificate
  with Support.classMeaning certificate
... | Scale.comparableCondition notLH notHL notHH = outputUpper , inputUpper
  where
  jp = Scale.shellLevel Support.literalShellPolicy (Physical.p tau)
  jq = Scale.shellLevel Support.literalShellPolicy (Physical.q tau)
  jk = Scale.shellLevel Support.literalShellPolicy (Physical.k tau)
  radius = Scale.overlapRadius Support.literalShellPolicy

  pAtMostQPlusRadius : jp ≤ jq + radius
  pAtMostQPlusRadius =
    natLessFalseImpliesReverseLe (jq + radius) jp notHL

  qAtMostPPlusRadius : jq ≤ jp + radius
  qAtMostPPlusRadius =
    natLessFalseImpliesReverseLe (jp + radius) jq notLH

  consequences : Infinity.OfficialResonantNormConsequences tau
  consequences = Infinity.officialResonantNormConsequences tau

  outputUpper : jk ≤ suc (suc (suc (suc jq)))
  outputUpper with Nat.≤-total jp jq
  ... | inj₁ p≤q =
    Nat.≤-trans
      (Dyadic.shellOfNormSumUpperRight
        {left = Infinity.infinityNorm (Physical.p tau)}
        {right = Infinity.infinityNorm (Physical.q tau)}
        {output = Infinity.infinityNorm (Physical.k tau)}
        (Infinity.outputTriangle consequences)
        p≤q)
      (Nat.≤-trans
        (leOneSuccessor jq)
        (leThreeSuccessors (suc jq)))
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
      (s≤s pAtMostQPlusRadius)
    where
    open import Relation.Binary.PropositionalEquality using (subst)

  inputUpper : jq ≤ suc (suc (suc (suc jk)))
  inputUpper with notHH
  ... | inj₂ notKBelowQ =
    Nat.≤-trans
      (natLessFalseImpliesReverseLe (jk + radius) jq notKBelowQ)
      (leOneSuccessor (suc (suc (suc jk))))
  ... | inj₁ notKBelowP =
    inputFromP
      (natLessFalseImpliesReverseLe (jk + radius) jp notKBelowP)
      (Nat.≤-total jp jk)
    where
    inputFromP :
      jp ≤ jk + radius →
      (jp ≤ jk ⊎ jk ≤ jp) →
      jq ≤ suc (suc (suc (suc jk)))
    inputFromP p≤kPlusRadius (inj₁ p≤k) =
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
        (Nat.≤-trans
          (leOneSuccessor jk)
          (leThreeSuccessors (suc jk)))
    inputFromP p≤kPlusRadius (inj₂ k≤p) =
      Nat.≤-trans
        (Dyadic.shellOfNormSumUpperRight
          {left = Infinity.infinityNorm (Physical.k tau)}
          {right = Infinity.infinityNorm (Physical.p tau)}
          {output = Infinity.infinityNorm (Physical.q tau)}
          (Infinity.qReverseTriangle consequences)
          k≤p)
        (s≤s p≤kPlusRadius)

mutual
  shellDistanceAtMostFour :
    ∀ {left right} →
    left ≤ suc (suc (suc (suc right))) →
    right ≤ suc (suc (suc (suc left))) →
    ∣ left - right ∣ ≤ 4
  shellDistanceAtMostFour {zero} {zero} leftBound rightBound = z≤n
  shellDistanceAtMostFour {zero} {suc zero} leftBound rightBound = s≤s z≤n
  shellDistanceAtMostFour {zero} {suc (suc zero)} leftBound rightBound =
    s≤s (s≤s z≤n)
  shellDistanceAtMostFour {zero} {suc (suc (suc zero))} leftBound rightBound =
    s≤s (s≤s (s≤s z≤n))
  shellDistanceAtMostFour {zero} {suc (suc (suc (suc zero)))} leftBound rightBound =
    s≤s (s≤s (s≤s (s≤s z≤n)))
  shellDistanceAtMostFour {zero} {suc (suc (suc (suc (suc right))))}
    leftBound (s≤s (s≤s (s≤s (s≤s ()))))
  shellDistanceAtMostFour {suc zero} {zero} leftBound rightBound = s≤s z≤n
  shellDistanceAtMostFour {suc (suc zero)} {zero} leftBound rightBound =
    s≤s (s≤s z≤n)
  shellDistanceAtMostFour {suc (suc (suc zero))} {zero} leftBound rightBound =
    s≤s (s≤s (s≤s z≤n))
  shellDistanceAtMostFour {suc (suc (suc (suc zero)))} {zero} leftBound rightBound =
    s≤s (s≤s (s≤s (s≤s z≤n)))
  shellDistanceAtMostFour {suc (suc (suc (suc (suc left))))} {zero}
    (s≤s (s≤s (s≤s (s≤s ())))) rightBound
  shellDistanceAtMostFour {suc left} {suc right}
    (s≤s leftBound) (s≤s rightBound) =
    shellDistanceAtMostFour leftBound rightBound

comparableInputOutputDistanceAtMostFour :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.CC →
  ∣ Scale.shellLevel Support.literalShellPolicy (Physical.k tau)
    - Scale.shellLevel Support.literalShellPolicy (Physical.q tau) ∣ ≤ 4
comparableInputOutputDistanceAtMostFour certificate =
  let band = comparableInputOutputBand certificate
  in shellDistanceAtMostFour (proj₁ band) (proj₂ band)
  where
  open import Data.Product.Base using (proj₁; proj₂)

comparableTriadicBandIsFour : Bool
comparableTriadicBandIsFour = true

comparableIsDistinctFromFifthComOwner : Bool
comparableIsDistinctFromFifthComOwner = true

comparableTriadicBandIsFourIsTrue : comparableTriadicBandIsFour ≡ true
comparableTriadicBandIsFourIsTrue = refl

comparableIsDistinctFromFifthComOwnerIsTrue :
  comparableIsDistinctFromFifthComOwner ≡ true
comparableIsDistinctFromFifthComOwnerIsTrue = refl
