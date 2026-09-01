{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.RequestedFibreInvolutionFoldExact where

------------------------------------------------------------------------
-- Fine-fibre fold semantics.
--
-- A ternary zero is not intrinsically a zero vector.  For an arbitrary fine
-- fibre with involution iota, the exact fold is its fixed locus
--
--   Fix(iota) = { x | iota x = x }.
--
-- If the requested coarse observation intertwines the fine involution with
-- signed ternary negation, every exact fine fixed point necessarily observes as
-- SSP zero.  The converse is intentionally NOT asserted: query projection may
-- also send unresolved, unobserved or otherwise collapsed fine states to zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.HypercomplexRequestedFractranComponentExact as Fine

record FineInvolution (A : Set) : Set₁ where
  constructor fineInvolution
  field
    invert : A → A
    involutive : ∀ x → invert (invert x) ≡ x

open FineInvolution public

record FixedPoint {A : Set} (involution : FineInvolution A) : Set where
  constructor fixedPoint
  field
    point : A
    fixed : invert involution point ≡ point

open FixedPoint public

record RequestedComponentInvolution
    (component : Fine.RequestedFractranComponent) : Set₁ where
  constructor requestedComponentInvolution
  field
    fineInvolution : FineInvolution (Fine.FineCarrier component)
    observationIntertwines : ∀ state →
      Fine.observeFine component (invert fineInvolution state)
      ≡ Context.negateTrit (Fine.observeFine component state)

open RequestedComponentInvolution public

-- Signed ternary negation has exactly one fixed coarse point.
negationFixedImpliesZero :
  (t : Trit.SSPTrit) → Context.negateTrit t ≡ t → t ≡ Trit.sspZero
negationFixedImpliesZero Trit.sspNegOne ()
negationFixedImpliesZero Trit.sspZero proof = refl
negationFixedImpliesZero Trit.sspPosOne ()

fixedFinePointObservesZero :
  ∀ {component}
    (structure : RequestedComponentInvolution component)
    (state : Fine.FineCarrier component) →
  invert (fineInvolution structure) state ≡ state →
  Fine.observeFine component state ≡ Trit.sspZero
fixedFinePointObservesZero {component} structure state fixedState =
  negationFixedImpliesZero
    (Fine.observeFine component state)
    (trans
      (sym (observationIntertwines structure state))
      (congObserve fixedState))
  where
  congObserve :
    invert (fineInvolution structure) state ≡ state →
    Fine.observeFine component (invert (fineInvolution structure) state)
    ≡ Fine.observeFine component state
  congObserve refl = refl

record FoldPreimage
    (component : Fine.RequestedFractranComponent)
    (structure : RequestedComponentInvolution component) : Set₁ where
  constructor foldPreimage
  field
    state : Fine.FineCarrier component
    isFineFixedPoint : invert (fineInvolution structure) state ≡ state

open FoldPreimage public

foldPreimageLandsInZero :
  ∀ {component}
    {structure : RequestedComponentInvolution component}
    (fold : FoldPreimage component structure) →
  Fine.observeFine component (state fold) ≡ Trit.sspZero
foldPreimageLandsInZero {structure = structure} fold =
  fixedFinePointObservesZero structure (state fold) (isFineFixedPoint fold)

------------------------------------------------------------------------
-- Crucial firewall: coarse zero can be larger than the exact fixed locus.
------------------------------------------------------------------------

record ZeroBeyondFixedLocus
    (component : Fine.RequestedFractranComponent)
    (structure : RequestedComponentInvolution component) : Set₁ where
  constructor zeroBeyondFixedLocus
  field
    state : Fine.FineCarrier component
    observesZero : Fine.observeFine component state ≡ Trit.sspZero
    NotFixed : Set

open ZeroBeyondFixedLocus public

record RequestedFibreFoldBoundary : Set where
  constructor requestedFibreFoldBoundary
  field
    foldMustBeSinglePoint : Bool
    fineFixedPointImpliesCoarseZero : Bool
    coarseZeroImpliesFineFixedPoint : Bool
    roleSwapFoldMayBeDiagonalSubspace : Bool
    conjugationFoldMayBeRealSubspace : Bool
    queryCollapseMayEnlargeZeroFibre : Bool

canonicalRequestedFibreFoldBoundary : RequestedFibreFoldBoundary
canonicalRequestedFibreFoldBoundary =
  requestedFibreFoldBoundary false true false true true true
