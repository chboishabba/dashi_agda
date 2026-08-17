module DASHI.Physics.Closure.NSTriadKNResonantDominantLowLegSplitRound66Exact where

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
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 66 / B3 DOMINANT-LOW SPLIT
--
-- Round63 constructed the common hat carried by the two dominant legs of every
-- exact resonant triad p+q=k.  Its `DominantLegPair` intentionally retained
-- only the width-one shell conclusion.  For the six-three estimate that loses
-- one analytically essential fact: the omitted third leg is the low leg, hence
-- is no larger than EITHER member of the dominant pair.
--
-- This module strengthens the same finite resonance case split without adding
-- an assumption.  For every `PhysicalTriadIncidence` it returns exactly one of
--
--   lowP : |p| <= |q| and |p| <= |k|, with q/k in one common hat,
--   lowQ : |q| <= |p| and |q| <= |k|, with p/k in one common hat,
--   lowK : |k| <= |p| and |k| <= |q|, with p/q in one common hat.
--
-- Thus the B3 Taylor variable is now canonically exposed on the SAME literal
-- triad: the third leg is the only candidate for the low-vs-dominant gap, while
-- the other two legs are already within one dyadic shell.  No LH/HL/HH/CC
-- re-enumeration is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as Nat
open import Data.Sum.Base using (inj₁; inj₂)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width
import DASHI.Physics.Closure.NSTriadKNResonantDominantTwoShellsRound63Exact as Dominant

-- The constructors retain both pieces needed downstream: (i) the omitted leg
-- is genuinely no larger than either dominant leg, and (ii) the two dominant
-- shells fit in the already-constructed width-one hat geometry.
data DominantLowLegSplit (tau : Physical.PhysicalTriadIncidence) : Set where
  lowP :
    Infinity.infinityNorm (Physical.p tau)
      ≤ Infinity.infinityNorm (Physical.q tau) →
    Infinity.infinityNorm (Physical.p tau)
      ≤ Infinity.infinityNorm (Physical.k tau) →
    Width.WithinOne
      (Shell.shellIndex (Physical.q tau))
      (Shell.shellIndex (Physical.k tau)) →
    DominantLowLegSplit tau

  lowQ :
    Infinity.infinityNorm (Physical.q tau)
      ≤ Infinity.infinityNorm (Physical.p tau) →
    Infinity.infinityNorm (Physical.q tau)
      ≤ Infinity.infinityNorm (Physical.k tau) →
    Width.WithinOne
      (Shell.shellIndex (Physical.p tau))
      (Shell.shellIndex (Physical.k tau)) →
    DominantLowLegSplit tau

  lowK :
    Infinity.infinityNorm (Physical.k tau)
      ≤ Infinity.infinityNorm (Physical.p tau) →
    Infinity.infinityNorm (Physical.k tau)
      ≤ Infinity.infinityNorm (Physical.q tau) →
    Width.WithinOne
      (Shell.shellIndex (Physical.p tau))
      (Shell.shellIndex (Physical.q tau)) →
    DominantLowLegSplit tau

resonantDominantLowLegSplit :
  (tau : Physical.PhysicalTriadIncidence) → DominantLowLegSplit tau
resonantDominantLowLegSplit tau
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.p tau))
    (Infinity.infinityNorm (Physical.q tau))
... | inj₁ p≤q
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.q tau))
    (Infinity.infinityNorm (Physical.k tau))
...   | inj₁ q≤k =
      lowP
        p≤q
        (Nat.≤-trans p≤q q≤k)
        (Dominant.shellWithinOneFromFactorTwo
          (Physical.q tau) (Physical.k tau)
          (Nat.≤-trans q≤k
            (Dominant.selfBelowDouble _))
          (Nat.≤-trans
            (Infinity.outputTriangle
              (Infinity.officialResonantNormConsequences tau))
            (Dominant.sumBelowDoubleRight p≤q)))
...   | inj₂ k≤q
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.p tau))
    (Infinity.infinityNorm (Physical.k tau))
...     | inj₁ p≤k =
        lowP
          p≤q
          p≤k
          (Dominant.shellWithinOneFromFactorTwo
            (Physical.q tau) (Physical.k tau)
            (Nat.≤-trans
              (Infinity.qReverseTriangle
                (Infinity.officialResonantNormConsequences tau))
              (Dominant.sumBelowDoubleRight p≤k))
            (Nat.≤-trans k≤q
              (Dominant.selfBelowDouble _)))
...     | inj₂ k≤p =
        lowK
          k≤p
          (Nat.≤-trans k≤p p≤q)
          (Dominant.shellWithinOneFromFactorTwo
            (Physical.p tau) (Physical.q tau)
            (Nat.≤-trans p≤q
              (Dominant.selfBelowDouble _))
            (Nat.≤-trans
              (Infinity.qReverseTriangle
                (Infinity.officialResonantNormConsequences tau))
              (Dominant.sumBelowDoubleRight k≤p)))
... | inj₂ q≤p
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.p tau))
    (Infinity.infinityNorm (Physical.k tau))
...   | inj₁ p≤k =
      lowQ
        q≤p
        (Nat.≤-trans q≤p p≤k)
        (Dominant.shellWithinOneFromFactorTwo
          (Physical.p tau) (Physical.k tau)
          (Nat.≤-trans p≤k
            (Dominant.selfBelowDouble _))
          (Nat.≤-trans
            (Infinity.outputTriangle
              (Infinity.officialResonantNormConsequences tau))
            (Dominant.sumBelowDoubleRight q≤p)))
...   | inj₂ k≤p
  with Nat.≤-total
    (Infinity.infinityNorm (Physical.q tau))
    (Infinity.infinityNorm (Physical.k tau))
...     | inj₁ q≤k =
        lowQ
          q≤p
          q≤k
          (Dominant.shellWithinOneFromFactorTwo
            (Physical.p tau) (Physical.k tau)
            (Nat.≤-trans
              (Infinity.pReverseTriangle
                (Infinity.officialResonantNormConsequences tau))
              (Dominant.sumBelowDoubleRight q≤k))
            (Nat.≤-trans k≤p
              (Dominant.selfBelowDouble _)))
...     | inj₂ k≤q =
        lowK
          (Nat.≤-trans k≤q q≤p)
          k≤q
          (Dominant.shellWithinOneFromFactorTwo
            (Physical.p tau) (Physical.q tau)
            (Nat.≤-trans
              (Infinity.pReverseTriangle
                (Infinity.officialResonantNormConsequences tau))
              (Dominant.sumBelowDoubleRight k≤q))
            (Nat.≤-trans q≤p
              (Dominant.selfBelowDouble _)))

-- Forgetting the low-leg inequalities recovers exactly the semantic shape of
-- the Round63 dominant-pair theorem.  This is useful for consumers that only
-- need the common hat while B3 keeps the stronger split.
forgetLowLeg :
  ∀ {tau} → DominantLowLegSplit tau → Dominant.DominantLegPair tau
forgetLowLeg (lowP _ _ within) = Dominant.dominantQK within
forgetLowLeg (lowQ _ _ within) = Dominant.dominantPK within
forgetLowLeg (lowK _ _ within) = Dominant.dominantPQ within

round66DominantCommonHatRetainsCanonicalLowLeg : Bool
round66DominantCommonHatRetainsCanonicalLowLeg = true

round66DominantCommonHatRetainsCanonicalLowLegIsTrue :
  round66DominantCommonHatRetainsCanonicalLowLeg ≡ true
round66DominantCommonHatRetainsCanonicalLowLegIsTrue = refl
