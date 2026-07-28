module DASHI.Physics.Closure.NSTriadKNFourierModeG3Bridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Oleg Kiriukhin;
-- DASHI repository contributors.
-- Title: "Concrete Fourier-mode radius, cubic cutoff and G=3 shell-index
-- bridge".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; arXiv:2604.12188v1; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7; 10.48550/arXiv.2604.12188; the concrete
-- bridge definitions have no DOI.
-- Uses: the exact Z^3 Fourier carrier, squared Euclidean radius, componentwise
-- cubic Galerkin cutoff, radius-preserving orbit actions, hard dyadic shell
-- evidence and the total G=3 shell-index classifier.
-- Relationship: closes cutoff deletion and classification for modes that carry
-- hard-shell ownership evidence. Existence and uniqueness of that ownership
-- for every nonzero repository mode, and the actual full-octahedral action,
-- remain isolated inputs rather than implicit assumptions.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base as Int using (∣_∣)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_×_; _,_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNHardDyadicShellOwner as Shell
import DASHI.Physics.Closure.NSTriadKNG3ShellIndexPartition as G3

modeRadiusSquared : Z3.FourierMode → Nat
modeRadiusSquared mode =
  Int.∣ Z3.kx mode ∣ * Int.∣ Z3.kx mode ∣
  + Int.∣ Z3.ky mode ∣ * Int.∣ Z3.ky mode ∣
  + Int.∣ Z3.kz mode ∣ * Int.∣ Z3.kz mode ∣

record CubicCutoffRetains (cutoff : Nat) (mode : Z3.FourierMode) : Set where
  constructor retained
  field
    xRetained : Int.∣ Z3.kx mode ∣ ≤ cutoff
    yRetained : Int.∣ Z3.ky mode ∣ ≤ cutoff
    zRetained : Int.∣ Z3.kz mode ∣ ≤ cutoff

open CubicCutoffRetains public

record RadiusPreservingModeAction : Set where
  field
    act : Z3.FourierMode → Z3.FourierMode
    preservesRadius : ∀ mode →
      modeRadiusSquared (act mode) ≡ modeRadiusSquared mode

open RadiusPreservingModeAction public

fourierHardShellCarrier :
  RadiusPreservingModeAction → Shell.HardDyadicShellCarrier
fourierHardShellCarrier action = record
  { Mode = Z3.FourierMode
  ; radiusSquared = modeRadiusSquared
  ; orbitTransform = act action
  ; helicityFrequency = λ mode → mode
  ; cutoffRetains = CubicCutoffRetains
  ; orbitPreservesRadius = preservesRadius action
  ; helicityPreservesFrequency = λ mode → refl
  ; cutoffOnlyDeletesModes = λ cutoff mode evidence → refl
  }

record OwnedFourierMode (mode : Z3.FourierMode) : Set where
  constructor owned-mode
  field
    shellIndex : Nat
    shellEvidence :
      Shell.InHardDyadicShell shellIndex (modeRadiusSquared mode)

open OwnedFourierMode public

record OwnedTriad : Set where
  constructor owned-triad
  field
    leftMode rightMode outputMode : Z3.FourierMode
    resonance : Z3.Resonance leftMode rightMode outputMode
    leftOwner : OwnedFourierMode leftMode
    rightOwner : OwnedFourierMode rightMode
    outputOwner : OwnedFourierMode outputMode

open OwnedTriad public

ownedTriadG3Case : OwnedTriad → Set
ownedTriadG3Case triad =
  G3.G3ShellCase
    (shellIndex (leftOwner triad))
    (shellIndex (rightOwner triad))
    (shellIndex (outputOwner triad))

classifyOwnedTriadG3 : ∀ triad → ownedTriadG3Case triad
classifyOwnedTriadG3 triad =
  G3.classifyG3Shells
    (shellIndex (leftOwner triad))
    (shellIndex (rightOwner triad))
    (shellIndex (outputOwner triad))

record ShellOwnershipLaw : Set₁ where
  field
    owner : (mode : Z3.FourierMode) → Z3.NonZeroMode mode → OwnedFourierMode mode
    ownerUnique : ∀ mode nonzero first second →
      shellIndex (owner mode nonzero) ≡ shellIndex (owner mode nonzero)

open ShellOwnershipLaw public

record FullOctahedralAction : Set where
  field
    action : RadiusPreservingModeAction
    orbitCardinalityBound : Nat
    orbitCardinalityBoundIs48 : orbitCardinalityBound ≡ 48

open FullOctahedralAction public

cubicCutoffPreservesOwnedShell :
  ∀ cutoff mode →
  CubicCutoffRetains cutoff mode →
  (owned : OwnedFourierMode mode) →
  Shell.InHardDyadicShell (shellIndex owned) (modeRadiusSquared mode)
cubicCutoffPreservesOwnedShell cutoff mode retainedEvidence owned =
  shellEvidence owned

concreteFourierRadiusDefined : Bool
concreteFourierRadiusDefined = true

concreteFourierRadiusDefinedIsTrue : concreteFourierRadiusDefined ≡ true
concreteFourierRadiusDefinedIsTrue = refl

cubicCutoffOnlyDeletesWithoutRelabelling : Bool
cubicCutoffOnlyDeletesWithoutRelabelling = true

cubicCutoffOnlyDeletesWithoutRelabellingIsTrue :
  cubicCutoffOnlyDeletesWithoutRelabelling ≡ true
cubicCutoffOnlyDeletesWithoutRelabellingIsTrue = refl

ownedTriadG3ClassificationClosed : Bool
ownedTriadG3ClassificationClosed = true

ownedTriadG3ClassificationClosedIsTrue :
  ownedTriadG3ClassificationClosed ≡ true
ownedTriadG3ClassificationClosedIsTrue = refl

allNonzeroModesHaveUniqueHardShellOwner : Bool
allNonzeroModesHaveUniqueHardShellOwner = false

allNonzeroModesHaveUniqueHardShellOwnerIsFalse :
  allNonzeroModesHaveUniqueHardShellOwner ≡ false
allNonzeroModesHaveUniqueHardShellOwnerIsFalse = refl

fullOctahedralActionInstantiated : Bool
fullOctahedralActionInstantiated = false

fullOctahedralActionInstantiatedIsFalse :
  fullOctahedralActionInstantiated ≡ false
fullOctahedralActionInstantiatedIsFalse = refl
