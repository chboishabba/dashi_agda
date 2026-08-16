module DASHI.Physics.Closure.NSTriadKNComDominantInteractionHatRound63Exact where

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
-- ROUND 63 / B0 DOMINANT INTERACTION HAT
--
-- The simple projector-annulus index is not the physical common-hat index.
-- Bony localization instead follows the dominant comparable frequencies.
-- The mature exact five-class classifier already proves:
--
--   LH : high q and output k differ by at most one shell;
--   HL : high p and output k differ by at most one shell;
--   HH : the two high inputs p and q differ by at most one shell.
--
-- This file converts those exact Nat shell-distance statements into the
-- repository's `WithinOne` hat geometry and packages the dominant pair.
--
-- CC is deliberately NOT included: the existing comparable certificate only
-- excludes a three-shell strict separation and does not by itself prove a
-- width-one dominant pair.  Thus the remaining B0 support theorem is now
-- sharply localized to CC plus the differentiated Com ownership rule.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; ∣_-_∣)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Five
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width

absoluteDistanceOneGivesWithinOne :
  ∀ left right →
  ∣ left - right ∣ ≤ suc zero →
  Width.WithinOne left right
absoluteDistanceOneGivesWithinOne zero zero bound = Width.same zero
absoluteDistanceOneGivesWithinOne zero (suc zero) bound = Width.next zero
absoluteDistanceOneGivesWithinOne zero (suc (suc right)) (s≤s (s≤s ()))
absoluteDistanceOneGivesWithinOne (suc zero) zero bound = Width.previous zero
absoluteDistanceOneGivesWithinOne (suc (suc left)) zero (s≤s (s≤s ()))
absoluteDistanceOneGivesWithinOne (suc left) (suc right) bound =
  lift (absoluteDistanceOneGivesWithinOne left right bound)
  where
  lift : Width.WithinOne left right → Width.WithinOne (suc left) (suc right)
  lift (Width.same q) = Width.same (suc q)
  lift (Width.next q) = Width.next (suc q)
  lift (Width.previous q) = Width.previous (suc q)

data DominantInteractionPair
    (tau : Physical.PhysicalTriadIncidence) : Set where
  lowHighDominant :
    Five.TriadicClassCertificate tau Five.LH →
    DominantInteractionPair tau
  highLowDominant :
    Five.TriadicClassCertificate tau Five.HL →
    DominantInteractionPair tau
  highHighDominant :
    Five.TriadicClassCertificate tau Five.HH →
    DominantInteractionPair tau

dominantLeftShell :
  ∀ {tau} → DominantInteractionPair tau → Nat
dominantLeftShell {tau} (lowHighDominant certificate) =
  Shell.shellIndex (Physical.q tau)
dominantLeftShell {tau} (highLowDominant certificate) =
  Shell.shellIndex (Physical.p tau)
dominantLeftShell {tau} (highHighDominant certificate) =
  Shell.shellIndex (Physical.p tau)

dominantRightShell :
  ∀ {tau} → DominantInteractionPair tau → Nat
dominantRightShell {tau} (lowHighDominant certificate) =
  Shell.shellIndex (Physical.k tau)
dominantRightShell {tau} (highLowDominant certificate) =
  Shell.shellIndex (Physical.k tau)
dominantRightShell {tau} (highHighDominant certificate) =
  Shell.shellIndex (Physical.q tau)

dominantPairWithinOne :
  ∀ {tau} (pair : DominantInteractionPair tau) →
  Width.WithinOne (dominantLeftShell pair) (dominantRightShell pair)
dominantPairWithinOne {tau} (lowHighDominant certificate) =
  Width.withinOneSymmetric
    (absoluteDistanceOneGivesWithinOne
      (Shell.shellIndex (Physical.k tau))
      (Shell.shellIndex (Physical.q tau))
      (Five.lowHighOutputTracksHighOne certificate))
dominantPairWithinOne {tau} (highLowDominant certificate) =
  Width.withinOneSymmetric
    (absoluteDistanceOneGivesWithinOne
      (Shell.shellIndex (Physical.k tau))
      (Shell.shellIndex (Physical.p tau))
      (Five.highLowOutputTracksHighOne certificate))
dominantPairWithinOne {tau} (highHighDominant certificate) =
  absoluteDistanceOneGivesWithinOne
    (Shell.shellIndex (Physical.p tau))
    (Shell.shellIndex (Physical.q tau))
    (Five.highHighInputsComparableOne certificate)

record DominantHatWitness
    (tau : Physical.PhysicalTriadIncidence) : Set where
  field
    pair : DominantInteractionPair tau
    leftShell : Nat
    rightShell : Nat
    leftMeaning : leftShell ≡ dominantLeftShell pair
    rightMeaning : rightShell ≡ dominantRightShell pair
    widthOne : Width.WithinOne leftShell rightShell

open DominantHatWitness public

constructDominantHatWitness :
  ∀ {tau} (pair : DominantInteractionPair tau) → DominantHatWitness tau
constructDominantHatWitness pair = record
  { pair = pair
  ; leftShell = dominantLeftShell pair
  ; rightShell = dominantRightShell pair
  ; leftMeaning = refl
  ; rightMeaning = refl
  ; widthOne = dominantPairWithinOne pair
  }

round63LHHHLHHDominantInteractionHatsConstructed : Bool
round63LHHHLHHDominantInteractionHatsConstructed = true

round63CCDominantWidthOneStillSeparate : Bool
round63CCDominantWidthOneStillSeparate = true

round63LHHHLHHDominantInteractionHatsConstructedIsTrue :
  round63LHHHLHHDominantInteractionHatsConstructed ≡ true
round63LHHHLHHDominantInteractionHatsConstructedIsTrue = refl

round63CCDominantWidthOneStillSeparateIsTrue :
  round63CCDominantWidthOneStillSeparate ≡ true
round63CCDominantWidthOneStillSeparateIsTrue = refl
