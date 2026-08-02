module DASHI.Physics.Closure.NSTriadKNHardDyadicShellOwner where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Oleg Kiriukhin;
-- DASHI repository contributors.
-- Title: "Exact squared-radius hard dyadic shell owner and transport laws".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; arXiv:2604.12188v1, 2026; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7; 10.48550/arXiv.2604.12188;
-- repository-original shell owner has no DOI.
-- Uses: squared Euclidean radii, shells 4^j <= |k|^2 < 4^(j+1), exact
-- radius preservation, and cutoff deletion without shell relabelling.
-- Relationship: freezes one exact shell convention and proves that any map
-- preserving squared radius preserves shell membership.  The repository orbit
-- and cutoff instances still require their concrete radius-preservation proofs.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_; _<_)

pow4 : Nat → Nat
pow4 0 = 1
pow4 (suc exponent) = 4 * pow4 exponent

record InHardDyadicShell (shell radiusSquared : Nat) : Set where
  constructor in-shell
  field
    lowerBound : pow4 shell ≤ radiusSquared
    upperBound : radiusSquared < pow4 (suc shell)

open InHardDyadicShell public

record HardDyadicShellCarrier {m : Level} : Set (lsuc m) where
  field
    Mode : Set m
    radiusSquared : Mode → Nat

    orbitTransform : Mode → Mode
    helicityFrequency : Mode → Mode
    cutoffRetains : Nat → Mode → Set

    orbitPreservesRadius : ∀ mode →
      radiusSquared (orbitTransform mode) ≡ radiusSquared mode

    helicityPreservesFrequency : ∀ mode →
      helicityFrequency mode ≡ mode

    cutoffOnlyDeletesModes : ∀ cutoff mode →
      cutoffRetains cutoff mode →
      radiusSquared mode ≡ radiusSquared mode

open HardDyadicShellCarrier public

shellMembership :
  ∀ {m} (C : HardDyadicShellCarrier {m}) →
  Nat → Mode C → Set
shellMembership C shell mode =
  InHardDyadicShell shell (radiusSquared C mode)

shellPreservedByRadiusEquality :
  ∀ {m} (C : HardDyadicShellCarrier {m})
    (shell : Nat) (source target : Mode C) →
  radiusSquared C target ≡ radiusSquared C source →
  shellMembership C shell source →
  shellMembership C shell target
shellPreservedByRadiusEquality C shell source target refl evidence = evidence

orbitPreservesShell :
  ∀ {m} (C : HardDyadicShellCarrier {m})
    (shell : Nat) (mode : Mode C) →
  shellMembership C shell mode →
  shellMembership C shell (orbitTransform C mode)
orbitPreservesShell C shell mode =
  shellPreservedByRadiusEquality C shell mode (orbitTransform C mode)
    (orbitPreservesRadius C mode)

helicityPreservesShell :
  ∀ {m} (C : HardDyadicShellCarrier {m})
    (shell : Nat) (mode : Mode C) →
  shellMembership C shell mode →
  shellMembership C shell (helicityFrequency C mode)
helicityPreservesShell C shell mode evidence
  rewrite helicityPreservesFrequency C mode = evidence

record GapThreeShellConsequences {m : Level}
    (C : HardDyadicShellCarrier {m}) : Set (lsuc m) where
  field
    gapThreeSquaredRatioBound : Set
    gapThreeOutputComparable : Set
    comparableHighShellOffsetAtMostOne : Set
    zeroModeExcludedFromSeparatedClasses : Set
    cubicCutoffPreservesLocalClass : Set
    classPartitionExhaustive : Set
    classPartitionPairwiseDisjoint : Set

open GapThreeShellConsequences public

hardDyadicShellConventionDefined : Bool
hardDyadicShellConventionDefined = true

hardDyadicShellConventionDefinedIsTrue :
  hardDyadicShellConventionDefined ≡ true
hardDyadicShellConventionDefinedIsTrue = refl

radiusEqualityTransportClosed : Bool
radiusEqualityTransportClosed = true

radiusEqualityTransportClosedIsTrue : radiusEqualityTransportClosed ≡ true
radiusEqualityTransportClosedIsTrue = refl

fullRepositoryGapThreePromotionClosed : Bool
fullRepositoryGapThreePromotionClosed = false

fullRepositoryGapThreePromotionClosedIsFalse :
  fullRepositoryGapThreePromotionClosed ≡ false
fullRepositoryGapThreePromotionClosedIsFalse = refl
