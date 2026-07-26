module DASHI.Physics.Closure.NSTriadKNPhysicalSymmetryEnumerationClosure where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry

CanonicalPhysicalListing :
  Nat → Physical.PhysicalTriadIncidence → Set
CanonicalPhysicalListing cutoff τ =
  Physical.PhysicalTriadEnumerationHit cutoff τ

listedTriadIsBounded :
  ∀ {cutoff τ} →
  Cube._∈_ τ (Physical.physicalTriadEnumeration cutoff) →
  Physical.PhysicalTriadInCutoff cutoff τ
listedTriadIsBounded = Physical.physicalTriadEnumerationCutoffSound

swapPreservesCutoff :
  ∀ {cutoff τ} →
  Physical.PhysicalTriadInCutoff cutoff τ →
  Physical.PhysicalTriadInCutoff cutoff (Symmetry.swapTriad τ)
swapPreservesCutoff bounded =
  Physical.triad-in-cutoff
    (Physical.qBounded bounded)
    (Physical.pBounded bounded)
    (Physical.kBounded bounded)

conjugationPreservesCutoff :
  ∀ {cutoff τ} →
  Physical.PhysicalTriadInCutoff cutoff τ →
  Physical.PhysicalTriadInCutoff cutoff (Symmetry.conjugateTriad τ)
conjugationPreservesCutoff {cutoff} {τ} bounded =
  Physical.triad-in-cutoff
    (Physical.carrierNegationClosed policy
      (Physical.p τ) (Physical.pBounded bounded))
    (Physical.carrierNegationClosed policy
      (Physical.q τ) (Physical.qBounded bounded))
    (Physical.carrierNegationClosed policy
      (Physical.k τ) (Physical.kBounded bounded))
  where
  policy : Physical.PhysicalTriadRealityPolicy cutoff
  policy = Physical.literalCutoffRealityPolicy cutoff

swapEnumerationClosure :
  ∀ {cutoff τ} →
  Physical.PhysicalTriadInCutoff cutoff τ →
  CanonicalPhysicalListing cutoff (Symmetry.swapTriad τ)
swapEnumerationClosure bounded =
  Physical.physicalTriadEnumerationComplete
    (swapPreservesCutoff bounded)

conjugationEnumerationClosure :
  ∀ {cutoff τ} →
  Physical.PhysicalTriadInCutoff cutoff τ →
  CanonicalPhysicalListing cutoff (Symmetry.conjugateTriad τ)
conjugationEnumerationClosure bounded =
  Physical.physicalTriadEnumerationComplete
    (conjugationPreservesCutoff bounded)

listedSwapHasRepresentative :
  ∀ {cutoff τ} →
  Cube._∈_ τ (Physical.physicalTriadEnumeration cutoff) →
  CanonicalPhysicalListing cutoff (Symmetry.swapTriad τ)
listedSwapHasRepresentative listed =
  swapEnumerationClosure (listedTriadIsBounded listed)

listedConjugateHasRepresentative :
  ∀ {cutoff τ} →
  Cube._∈_ τ (Physical.physicalTriadEnumeration cutoff) →
  CanonicalPhysicalListing cutoff (Symmetry.conjugateTriad τ)
listedConjugateHasRepresentative listed =
  conjugationEnumerationClosure (listedTriadIsBounded listed)

physicalSymmetryEnumerationClosureImplemented : Bool
physicalSymmetryEnumerationClosureImplemented = true

physicalSymmetryEnumerationClosureImplementedIsTrue :
  physicalSymmetryEnumerationClosureImplemented ≡ true
physicalSymmetryEnumerationClosureImplementedIsTrue = refl
