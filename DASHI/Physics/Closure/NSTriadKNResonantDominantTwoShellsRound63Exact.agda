module DASHI.Physics.Closure.NSTriadKNResonantDominantTwoShellsRound63Exact where

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
-- ROUND 63 / UNIVERSAL DOMINANT-HAT GEOMETRY
--
-- For every exact resonant triangle p+q=k, choose the two largest of the three
-- infinity norms |p|_inf, |q|_inf, |k|_inf.  The triangle/reverse-triangle
-- inequalities imply that the largest is at most twice the second-largest.
-- Hence the repository's exact factor-two shell theorem gives dyadic shell
-- distance at most one for that dominant pair.
--
-- This is stronger and cleaner than class-specific LH/HL/HH routing: it also
-- covers the CC case.  The remaining third leg is where the high-low gap (and
-- therefore the six-three Taylor gain) lives; the common hat itself is owned
-- by the two dominant legs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; _+_; _*_; z≤n; s≤s; ∣_-_∣)
import Data.Nat.Properties as Nat
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNShellFactorTwo as FactorTwo
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width

sumBelowDoubleRight : ∀ {a b} → a ≤ b → a + b ≤ 2 * b
sumBelowDoubleRight {a} {b} a≤b =
  subst
    (λ target → a + b ≤ target)
    (sym doubleMeaning)
    (Nat.+-mono-≤ a≤b Nat.≤-refl)
  where
  doubleMeaning : 2 * b ≡ b + b
  doubleMeaning =
    trans
      (Nat.*-comm 2 b)
      (trans
        (Nat.*-suc b 1)
        (cong (b +_) (Nat.*-identityʳ b)))

selfBelowDouble : ∀ n → n ≤ 2 * n
selfBelowDouble n =
  Nat.≤-trans
    (Nat.m≤m+n n n)
    (subst (n ≤_) (sym doubleMeaning) Nat.≤-refl)
  where
  doubleMeaning : 2 * n ≡ n + n
  doubleMeaning =
    trans
      (Nat.*-comm 2 n)
      (trans
        (Nat.*-suc n 1)
        (cong (n +_) (Nat.*-identityʳ n)))

mutual
  shellWithinOneFromFactorTwo :
    ∀ (left right : Z3.FourierMode) →
    Infinity.infinityNorm left ≤ 2 * Infinity.infinityNorm right →
    Infinity.infinityNorm right ≤ 2 * Infinity.infinityNorm left →
    Width.WithinOne (Shell.shellIndex left) (Shell.shellIndex right)
  shellWithinOneFromFactorTwo left right left≤2right right≤2left =
    distanceOneToWithinOne
      (Shell.shellIndex left)
      (Shell.shellIndex right)
      (FactorTwo.factorTwoNormsGiveShellDistanceOne
        left≤2right right≤2left)

  distanceOneToWithinOne :
    ∀ left right →
    ∣ left - right ∣ ≤ 1 →
    Width.WithinOne left right
  distanceOneToWithinOne zero zero bound = Width.same zero
  distanceOneToWithinOne zero (suc zero) bound = Width.next zero
  distanceOneToWithinOne zero (suc (suc right)) (s≤s (s≤s ()))
  distanceOneToWithinOne (suc zero) zero bound = Width.previous zero
  distanceOneToWithinOne (suc (suc left)) zero (s≤s (s≤s ()))
  distanceOneToWithinOne (suc left) (suc right) bound =
    liftWithinOne (distanceOneToWithinOne left right bound)
    where
    liftWithinOne :
      Width.WithinOne left right →
      Width.WithinOne (suc left) (suc right)
    liftWithinOne (Width.same n) = Width.same (suc n)
    liftWithinOne (Width.next n) = Width.next (suc n)
    liftWithinOne (Width.previous n) = Width.previous (suc n)

data DominantLegPair (tau : Physical.PhysicalTriadIncidence) : Set where
  dominantPQ :
    Width.WithinOne
      (Shell.shellIndex (Physical.p tau))
      (Shell.shellIndex (Physical.q tau)) →
    DominantLegPair tau
  dominantPK :
    Width.WithinOne
      (Shell.shellIndex (Physical.p tau))
      (Shell.shellIndex (Physical.k tau)) →
    DominantLegPair tau
  dominantQK :
    Width.WithinOne
      (Shell.shellIndex (Physical.q tau))
      (Shell.shellIndex (Physical.k tau)) →
    DominantLegPair tau

resonantDominantTwoShells :
  (tau : Physical.PhysicalTriadIncidence) → DominantLegPair tau
resonantDominantTwoShells tau
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.p tau))
    (Infinity.infinityNorm (Physical.q tau))
... | inj₁ p≤q
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.q tau))
    (Infinity.infinityNorm (Physical.k tau))
...   | inj₁ q≤k =
      dominantQK
        (shellWithinOneFromFactorTwo
          (Physical.q tau) (Physical.k tau)
          (Nat.≤-trans q≤k (selfBelowDouble _))
          (Nat.≤-trans
            (Infinity.outputTriangle
              (Infinity.officialResonantNormConsequences tau))
            (sumBelowDoubleRight p≤q)))
...   | inj₂ k≤q
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.p tau))
    (Infinity.infinityNorm (Physical.k tau))
...     | inj₁ p≤k =
        dominantQK
          (shellWithinOneFromFactorTwo
            (Physical.q tau) (Physical.k tau)
            (Nat.≤-trans
              (Infinity.qReverseTriangle
                (Infinity.officialResonantNormConsequences tau))
              (sumBelowDoubleRight p≤k))
            (Nat.≤-trans k≤q (selfBelowDouble _)))
...     | inj₂ k≤p =
        dominantPQ
          (shellWithinOneFromFactorTwo
            (Physical.p tau) (Physical.q tau)
            (Nat.≤-trans p≤q (selfBelowDouble _))
            (Nat.≤-trans
              (Infinity.qReverseTriangle
                (Infinity.officialResonantNormConsequences tau))
              (sumBelowDoubleRight k≤p)))
... | inj₂ q≤p
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.p tau))
    (Infinity.infinityNorm (Physical.k tau))
...   | inj₁ p≤k =
      dominantPK
        (shellWithinOneFromFactorTwo
          (Physical.p tau) (Physical.k tau)
          (Nat.≤-trans p≤k (selfBelowDouble _))
          (Nat.≤-trans
            (Infinity.outputTriangle
              (Infinity.officialResonantNormConsequences tau))
            (sumBelowDoubleRight q≤p)))
...   | inj₂ k≤p
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.q tau))
    (Infinity.infinityNorm (Physical.k tau))
...     | inj₁ q≤k =
        dominantPK
          (shellWithinOneFromFactorTwo
            (Physical.p tau) (Physical.k tau)
            (Nat.≤-trans
              (Infinity.pReverseTriangle
                (Infinity.officialResonantNormConsequences tau))
              (sumBelowDoubleRight q≤k))
            (Nat.≤-trans k≤p (selfBelowDouble _)))
...     | inj₂ k≤q =
        dominantPQ
          (shellWithinOneFromFactorTwo
            (Physical.p tau) (Physical.q tau)
            (Nat.≤-trans
              (Infinity.pReverseTriangle
                (Infinity.officialResonantNormConsequences tau))
              (sumBelowDoubleRight k≤q))
            (Nat.≤-trans q≤p (selfBelowDouble _)))

round63EveryResonantTriadHasWidthOneDominantShellPair : Bool
round63EveryResonantTriadHasWidthOneDominantShellPair = true

round63EveryResonantTriadHasWidthOneDominantShellPairIsTrue :
  round63EveryResonantTriadHasWidthOneDominantShellPair ≡ true
round63EveryResonantTriadHasWidthOneDominantShellPairIsTrue = refl
