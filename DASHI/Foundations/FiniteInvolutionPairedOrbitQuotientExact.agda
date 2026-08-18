module DASHI.Foundations.FiniteInvolutionPairedOrbitQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", GTM 42, Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- The repository already owns the normal form for a finite involution:
--
--   Fin fixed  ⊎  (Fin paired × Bit2),
--
-- with the involution fixing the first summand and flipping Bit2 on the
-- second.  This module extracts the exact quotient coordinate carried by the
-- nonfixed part.  Every two-cycle has one and only one pair index; the quotient
-- map forgets the Bit2 orientation, is invariant under the involution, and has
-- an explicit section.
--
-- This is finite orbit algebra only.  A geometric application must still prove
-- that its actual singular quotient nodes are represented by these nonfixed
-- involution orbits.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit

PairedOrbitCarrier : Nat → Set
PairedOrbitCarrier paired = Fin paired × Orbit.Bit2

pairedOrbitInvolution :
  ∀ {paired} → PairedOrbitCarrier paired → PairedOrbitCarrier paired
pairedOrbitInvolution (index , bit) = index , Orbit.flipBit bit

pairedOrbitInvolutionInvolutive :
  ∀ {paired} (x : PairedOrbitCarrier paired) →
  pairedOrbitInvolution (pairedOrbitInvolution x) ≡ x
pairedOrbitInvolutionInvolutive (index , Orbit.bit0) = refl
pairedOrbitInvolutionInvolutive (index , Orbit.bit1) = refl

pairedOrbitInvolutionFixedPointFree :
  ∀ {paired} (x : PairedOrbitCarrier paired) →
  pairedOrbitInvolution x ≡ x → ⊥
pairedOrbitInvolutionFixedPointFree (index , Orbit.bit0) ()
pairedOrbitInvolutionFixedPointFree (index , Orbit.bit1) ()

------------------------------------------------------------------------
-- Quotient coordinate: forget only the orientation inside a two-cycle.
------------------------------------------------------------------------

pairedOrbitNode : ∀ {paired} → PairedOrbitCarrier paired → Fin paired
pairedOrbitNode = proj₁

pairedOrbitNodeInvariant :
  ∀ {paired} (x : PairedOrbitCarrier paired) →
  pairedOrbitNode (pairedOrbitInvolution x) ≡ pairedOrbitNode x
pairedOrbitNodeInvariant (index , bit) = refl

pairedOrbitNodeSection : ∀ {paired} → Fin paired → PairedOrbitCarrier paired
pairedOrbitNodeSection index = index , Orbit.bit0

pairedOrbitNodeAfterSection :
  ∀ {paired} (index : Fin paired) →
  pairedOrbitNode (pairedOrbitNodeSection index) ≡ index
pairedOrbitNodeAfterSection index = refl

------------------------------------------------------------------------
-- The two oriented representatives of each node are exactly the Bit2 fibre.
------------------------------------------------------------------------

pairedOrbitRepresentatives :
  ∀ {paired} → Fin paired → PairedOrbitCarrier paired × PairedOrbitCarrier paired
pairedOrbitRepresentatives index =
  (index , Orbit.bit0) , (index , Orbit.bit1)

pairedOrbitRepresentativesHaveSameNode :
  ∀ {paired} (index : Fin paired) →
  pairedOrbitNode (proj₁ (pairedOrbitRepresentatives index))
  ≡ pairedOrbitNode (proj₂ (pairedOrbitRepresentatives index))
pairedOrbitRepresentativesHaveSameNode index = refl

pairedOrbitRepresentativesAreExchanged :
  ∀ {paired} (index : Fin paired) →
  pairedOrbitInvolution (proj₁ (pairedOrbitRepresentatives index))
  ≡ proj₂ (pairedOrbitRepresentatives index)
pairedOrbitRepresentativesAreExchanged index = refl

pairedOrbitRepresentativesDistinct :
  ∀ {paired} (index : Fin paired) →
  proj₁ (pairedOrbitRepresentatives index)
  ≡ proj₂ (pairedOrbitRepresentatives index) → ⊥
pairedOrbitRepresentativesDistinct index ()

------------------------------------------------------------------------
-- Reusable quotient witness.  No quotient type is manufactured: the pair
-- index, section, invariance and exact two representatives are the proof-
-- relevant quotient data consumed by geometric applications.
------------------------------------------------------------------------

record PairedOrbitQuotientWitness (paired : Nat) : Set where
  field
    quotient : PairedOrbitCarrier paired → Fin paired
    section : Fin paired → PairedOrbitCarrier paired
    quotientInvariant :
      (x : PairedOrbitCarrier paired) →
      quotient (pairedOrbitInvolution x) ≡ quotient x
    quotientAfterSection :
      (index : Fin paired) → quotient (section index) ≡ index

open PairedOrbitQuotientWitness public

canonicalPairedOrbitQuotientWitness :
  (paired : Nat) → PairedOrbitQuotientWitness paired
canonicalPairedOrbitQuotientWitness paired = record
  { quotient = pairedOrbitNode
  ; section = pairedOrbitNodeSection
  ; quotientInvariant = pairedOrbitNodeInvariant
  ; quotientAfterSection = pairedOrbitNodeAfterSection
  }

record FiniteInvolutionPairedOrbitQuotientBoundary : Set where
  field
    pairedSummandQuotientConstructed : Bool
    quotientInvariantUnderInvolution : Bool
    explicitPairIndexSectionConstructed : Bool
    geometricNodeIdentificationAutomatic : Bool

canonicalFiniteInvolutionPairedOrbitQuotientBoundary :
  FiniteInvolutionPairedOrbitQuotientBoundary
canonicalFiniteInvolutionPairedOrbitQuotientBoundary = record
  { pairedSummandQuotientConstructed = true
  ; quotientInvariantUnderInvolution = true
  ; explicitPairIndexSectionConstructed = true
  ; geometricNodeIdentificationAutomatic = false
  }
