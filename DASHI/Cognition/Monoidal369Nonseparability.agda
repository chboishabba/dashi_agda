module DASHI.Cognition.Monoidal369Nonseparability where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Cognition.Base369ZeroFibre as Fibre

------------------------------------------------------------------------
-- Composite carrier and product-state boundary.
--
-- The unconstrained zero-sector composite is the six-state product
-- ZeroFibre6 x ZeroFibre9.  A joint admissibility relation can be strictly
-- smaller and fail to factor into independent local predicates.
------------------------------------------------------------------------

ZeroComposite : Set
ZeroComposite = Fibre.ZeroFibre6 × Fibre.ZeroFibre9

canonicalZeroComposite : ZeroComposite
canonicalZeroComposite = Fibre.zeroForward , Fibre.zeroRelMid

------------------------------------------------------------------------
-- Non-rectangular joint support.
--
-- Allowed pairs:
--   forward x low
--   forward x mid
--   reverse x mid
--   reverse x high
--
-- This relation cannot equal LeftAllowed x RightAllowed: the allowed
-- forward-low and reverse-high pairs would force forward-high into any
-- Cartesian product, but that pair is absent.
------------------------------------------------------------------------

data JointAllowed : Fibre.ZeroFibre6 → Fibre.ZeroFibre9 → Set where
  allowForwardLow : JointAllowed Fibre.zeroForward Fibre.zeroRelLow
  allowForwardMid : JointAllowed Fibre.zeroForward Fibre.zeroRelMid
  allowReverseMid : JointAllowed Fibre.zeroReverse Fibre.zeroRelMid
  allowReverseHigh : JointAllowed Fibre.zeroReverse Fibre.zeroRelHigh

record ProductFactorisation : Set₁ where
  field
    leftAllowed  : Fibre.ZeroFibre6 → Set
    rightAllowed : Fibre.ZeroFibre9 → Set
    toProduct : ∀ {left right} →
      JointAllowed left right → leftAllowed left × rightAllowed right
    fromProduct : ∀ {left right} →
      leftAllowed left × rightAllowed right → JointAllowed left right

open ProductFactorisation public

jointSupportDoesNotFactor : ProductFactorisation → ⊥
jointSupportDoesNotFactor factorisation with
  fromProduct factorisation
    ( proj₁ (toProduct factorisation allowForwardLow)
    , proj₂ (toProduct factorisation allowReverseHigh)
    )
... | ()

record StructuralNonseparabilityWitness : Set where
  constructor structuralNonseparabilityWitness
  field
    compositeCarrier : Set
    factorisationImpossible : ProductFactorisation → ⊥

zeroFibreNonseparability : StructuralNonseparabilityWitness
zeroFibreNonseparability =
  structuralNonseparabilityWitness ZeroComposite jointSupportDoesNotFactor

------------------------------------------------------------------------
-- This theorem is stronger than mere cardinality mismatch and weaker than a
-- physical entanglement theorem.  No complex tensor amplitudes, probability
-- valuation, no-signalling condition or Bell inequality is supplied here.
------------------------------------------------------------------------

data CompositeAuthority : Set where
  cartesianCompositeDefined
  nonrectangularSupportProved
  quantumEntanglementNotYetDerived
  bellViolationNotYetDerived : CompositeAuthority
