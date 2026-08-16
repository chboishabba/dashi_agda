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
-- and reimplemented the collar with weak inequalities.  The mature physical
-- classifier uses strict `natLess (j+Csep) j'`, and names the fourth TRIADIC
-- class CC/comparable.  This module now reasons directly from that certificate.
--
-- If radius=Csep, a comparable triad satisfies the classifier-native bounds
--
--   j(k) <= suc (j(q) + radius),
--   j(q) <= suc (j(k) + radius).
--
-- Since the authoritative literal policy has radius=Csep=3, this is precisely
-- the finite four-shell band.  The theorem intentionally keeps the native
-- `suc (j+radius)` form instead of normalizing Nat addition inside dependent
-- types.
--
-- This is a statement about the triadic CC summands.  It does NOT identify CC
-- with the fifth Com owner; Round25 keeps the appended differentiated
-- commutator as a separate source.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

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

leSelfPlus : (left right : Nat) → left ≤ left + right
leSelfPlus zero right = z≤n
leSelfPlus (suc left) right = s≤s (leSelfPlus left right)

comparableInputOutputNativeBand :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.CC →
  let policy = Support.literalShellPolicy
      jp = Scale.shellLevel policy (Physical.p tau)
      jq = Scale.shellLevel policy (Physical.q tau)
      jk = Scale.shellLevel policy (Physical.k tau)
      radius = Scale.overlapRadius policy
  in
  (jk ≤ suc (jq + radius)) × (jq ≤ suc (jk + radius))
comparableInputOutputNativeBand {tau} certificate
  with Support.classMeaning certificate
... | Scale.comparableCondition notLH notHL notHH = outputUpper , inputUpper
  where
  policy = Support.literalShellPolicy
  jp = Scale.shellLevel policy (Physical.p tau)
  jq = Scale.shellLevel policy (Physical.q tau)
  jk = Scale.shellLevel policy (Physical.k tau)
  radius = Scale.overlapRadius policy

  pAtMostQPlusRadius : jp ≤ jq + radius
  pAtMostQPlusRadius =
    natLessFalseImpliesReverseLe (jq + radius) jp notHL

  consequences : Infinity.OfficialResonantNormConsequences tau
  consequences = Infinity.officialResonantNormConsequences tau

  outputUpper : jk ≤ suc (jq + radius)
  outputUpper with Nat.≤-total jp jq
  ... | inj₁ p≤q =
    Nat.≤-trans
      (Dyadic.shellOfNormSumUpperRight
        {left = Infinity.infinityNorm (Physical.p tau)}
        {right = Infinity.infinityNorm (Physical.q tau)}
        {output = Infinity.infinityNorm (Physical.k tau)}
        (Infinity.outputTriangle consequences)
        p≤q)
      (s≤s (leSelfPlus jq radius))
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

  inputUpper : jq ≤ suc (jk + radius)
  inputUpper with notHH
  ... | inj₂ notKBelowQ =
    Nat.≤-trans
      (natLessFalseImpliesReverseLe (jk + radius) jq notKBelowQ)
      (leOneSuccessor (jk + radius))
  ... | inj₁ notKBelowP =
    inputFromP
      (natLessFalseImpliesReverseLe (jk + radius) jp notKBelowP)
      (Nat.≤-total jp jk)
    where
    inputFromP :
      jp ≤ jk + radius →
      (jp ≤ jk ⊎ jk ≤ jp) →
      jq ≤ suc (jk + radius)
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
        (s≤s (leSelfPlus jk radius))
    inputFromP p≤kPlusRadius (inj₂ k≤p) =
      Nat.≤-trans
        (Dyadic.shellOfNormSumUpperRight
          {left = Infinity.infinityNorm (Physical.k tau)}
          {right = Infinity.infinityNorm (Physical.p tau)}
          {output = Infinity.infinityNorm (Physical.q tau)}
          (Infinity.qReverseTriangle consequences)
          k≤p)
        (s≤s p≤kPlusRadius)

literalComparableCollarIsThree :
  Scale.overlapRadius Support.literalShellPolicy ≡ suc (suc (suc zero))
literalComparableCollarIsThree = Support.separationCollarIsThree

comparableOutputNativeCap :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.CC →
  Scale.shellLevel Support.literalShellPolicy (Physical.k tau)
  ≤ suc
      (Scale.shellLevel Support.literalShellPolicy (Physical.q tau)
       + Scale.overlapRadius Support.literalShellPolicy)
comparableOutputNativeCap certificate =
  proj₁ (comparableInputOutputNativeBand certificate)

comparableInputNativeCap :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.CC →
  Scale.shellLevel Support.literalShellPolicy (Physical.q tau)
  ≤ suc
      (Scale.shellLevel Support.literalShellPolicy (Physical.k tau)
       + Scale.overlapRadius Support.literalShellPolicy)
comparableInputNativeCap certificate =
  proj₂ (comparableInputOutputNativeBand certificate)

comparableTriadicBandIsCollarPlusOne : Bool
comparableTriadicBandIsCollarPlusOne = true

comparableIsDistinctFromFifthComOwner : Bool
comparableIsDistinctFromFifthComOwner = true

comparableTriadicBandIsCollarPlusOneIsTrue :
  comparableTriadicBandIsCollarPlusOne ≡ true
comparableTriadicBandIsCollarPlusOneIsTrue = refl

comparableIsDistinctFromFifthComOwnerIsTrue :
  comparableIsDistinctFromFifthComOwner ≡ true
comparableIsDistinctFromFifthComOwnerIsTrue = refl
