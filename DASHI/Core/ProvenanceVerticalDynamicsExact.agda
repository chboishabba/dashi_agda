module DASHI.Core.ProvenanceVerticalDynamicsExact where

------------------------------------------------------------------------
-- HIDDEN / VERTICAL DYNAMICS OVER AN EXACT REOPENABLE QUOTIENT
--
-- This extends the existing ProvenanceBearingQuotient and
-- ProvenanceQuotientDynamics surfaces rather than creating a second quotient
-- theory.  The key theorem is exact:
--
--   same public surface + same provenance receipt => same fine carrier.
--
-- Therefore every nontrivial fibre-preserving transition must move the
-- provenance/residual coordinate of an exact reopenable quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as PBQ

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

------------------------------------------------------------------------
-- Surface + receipt is an exact separating observer.
------------------------------------------------------------------------

surfaceReceiptObserver :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : PBQ.ProvenanceBearingQuotient core) →
  Fibre.Carrier core → Fibre.Surface core × PBQ.Receipt quotient
surfaceReceiptObserver {core} quotient x =
  Fibre.project core x , PBQ.receipt quotient x

surfaceAndReceiptDetermineCarrier :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : PBQ.ProvenanceBearingQuotient core)
    {x y : Fibre.Carrier core} →
  Fibre.project core x ≡ Fibre.project core y →
  PBQ.receipt quotient x ≡ PBQ.receipt quotient y →
  x ≡ y
surfaceAndReceiptDetermineCarrier {core} quotient {x} {y}
  sameSurface sameReceipt =
  trans
    (sym (PBQ.reopenExact quotient x))
    (trans
      (cong
        (λ surface → PBQ.reopen quotient surface (PBQ.receipt quotient x))
        sameSurface)
      (trans
        (cong
          (PBQ.reopen quotient (Fibre.project core y))
          sameReceipt)
        (PBQ.reopenExact quotient y)))

surfaceReceiptObserverInjective :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : PBQ.ProvenanceBearingQuotient core) →
  Injective (surfaceReceiptObserver quotient)
surfaceReceiptObserverInjective quotient same =
  surfaceAndReceiptDetermineCarrier quotient
    (cong proj₁ same)
    (cong proj₂ same)

------------------------------------------------------------------------
-- Vertical operators preserve the public quotient surface.
------------------------------------------------------------------------

record VerticalOperator
    (core : Fibre.FibreRestrictionCore) : Set₁ where
  constructor verticalOperator
  field
    step : Fibre.Carrier core → Fibre.Carrier core
    surfaceInvariant :
      (x : Fibre.Carrier core) →
      Fibre.project core (step x) ≡ Fibre.project core x

open VerticalOperator public

record HiddenVerticalTransition
    (core : Fibre.FibreRestrictionCore)
    (operator : VerticalOperator core) : Set where
  constructor hiddenVerticalTransition
  field
    state : Fibre.Carrier core
    nontrivial : step operator state ≢ state

open HiddenVerticalTransition public

hiddenVerticalTransitionChangesReceipt :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : PBQ.ProvenanceBearingQuotient core)
    (operator : VerticalOperator core) →
  (hidden : HiddenVerticalTransition core operator) →
  PBQ.receipt quotient (step operator (state hidden))
    ≢ PBQ.receipt quotient (state hidden)
hiddenVerticalTransitionChangesReceipt quotient operator hidden sameReceipt =
  nontrivial hidden
    (surfaceAndReceiptDetermineCarrier quotient
      (surfaceInvariant operator (state hidden))
      sameReceipt)

------------------------------------------------------------------------
-- Reversible vertical dynamics: a fibre automorphism is a vertical operator
-- together with an explicit inverse.  This is enough for group-action
-- specializations without building a second quotient core.
------------------------------------------------------------------------

record FibreAutomorphism
    (core : Fibre.FibreRestrictionCore) : Set₁ where
  constructor fibreAutomorphism
  field
    forward backward : Fibre.Carrier core → Fibre.Carrier core
    forwardBackward :
      (x : Fibre.Carrier core) → backward (forward x) ≡ x
    backwardForward :
      (x : Fibre.Carrier core) → forward (backward x) ≡ x
    forwardSurfaceInvariant :
      (x : Fibre.Carrier core) →
      Fibre.project core (forward x) ≡ Fibre.project core x

open FibreAutomorphism public

automorphismAsVerticalOperator :
  ∀ {core : Fibre.FibreRestrictionCore} →
  FibreAutomorphism core → VerticalOperator core
automorphismAsVerticalOperator automorphism =
  verticalOperator
    (forward automorphism)
    (forwardSurfaceInvariant automorphism)

nontrivialAutomorphismChangesReceipt :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : PBQ.ProvenanceBearingQuotient core)
    (automorphism : FibreAutomorphism core)
    (x : Fibre.Carrier core) →
  forward automorphism x ≢ x →
  PBQ.receipt quotient (forward automorphism x)
    ≢ PBQ.receipt quotient x
nontrivialAutomorphismChangesReceipt quotient automorphism x differs =
  hiddenVerticalTransitionChangesReceipt
    quotient
    (automorphismAsVerticalOperator automorphism)
    (hiddenVerticalTransition x differs)
