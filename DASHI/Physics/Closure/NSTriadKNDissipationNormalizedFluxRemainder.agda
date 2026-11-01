module DASHI.Physics.Closure.NSTriadKNDissipationNormalizedFluxRemainder where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNLocalViscousEdgeAllocation as Allocation
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Dissipation-normalised Young remainder.
--
-- The quotient is extended-valued: d = 0 is harmless only when the
-- numerator is also zero.  A future ordered-field instance must prove that
-- alternative; this module never replaces the denominator by an arbitrary
-- delta regularisation.
------------------------------------------------------------------------

data ExtendedFlux (S : Scalar.ExactOrderedScalar) : Set where
  finite : Scalar.Scalar S → ExtendedFlux S
  infinity : ExtendedFlux S

infix 4 _≤∞_
data _≤∞_ {S : Scalar.ExactOrderedScalar} :
  ExtendedFlux S → ExtendedFlux S → Set where
  finite≤finite :
    {a b : Scalar.Scalar S} → Scalar._≤_ S a b → finite a ≤∞ finite b
  finite≤infinity : {a : Scalar.Scalar S} → finite a ≤∞ infinity
  infinity≤infinity : infinity ≤∞ infinity

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record DissipationNormalisedFluxAuthority
    (S : Scalar.ExactOrderedScalar) : Set₁ where
  field
    abs : Scalar.Scalar S → Scalar.Scalar S
    square : Scalar.Scalar S → Scalar.Scalar S
    divideByPositive : Scalar.Scalar S → Scalar.Scalar S → Scalar.Scalar S
    normalisedQuotient : Scalar.Scalar S → Scalar.Scalar S → ExtendedFlux S

    -- Exact extended-zero convention.  The branch is determined by the
    -- numerator; an arbitrary finite/infinite choice is not admissible.
    zeroOverZero :
      normalisedQuotient (Scalar.zero S) (Scalar.zero S) ≡
      finite (Scalar.zero S)

    nonzeroOverZero :
      (numerator : Scalar.Scalar S) →
      numerator ≢ Scalar.zero S →
      normalisedQuotient numerator (Scalar.zero S) ≡ infinity

    -- A finite quotient is genuinely finite.  This is the order fact later
    -- needed to force a zero numerator on any zero-density edge carrying a
    -- finite local hierarchy bound.
    infinityNotLeFinite :
      (a : Scalar.Scalar S) → (infinity {S = S} ≤∞ finite a) → ⊥

open DissipationNormalisedFluxAuthority public

-- We keep the finite/infinite branch explicit.  The quotient is defined from
-- the physical edge difference, not from the diagnostic Gram coefficients.
edgeFluxNumerator :
  (S : Scalar.ExactOrderedScalar) →
  (zΔ TΔ : Scalar.Scalar S) → Scalar.Scalar S
edgeFluxNumerator S zΔ TΔ =
  Scalar._*_ S
    (Scalar._*_ S zΔ zΔ)
    (Scalar._*_ S TΔ TΔ)

edgeFluxQuotient :
  (S : Scalar.ExactOrderedScalar) →
  DissipationNormalisedFluxAuthority S →
  (zΔ TΔ d : Scalar.Scalar S) → ExtendedFlux S
edgeFluxQuotient S A zΔ TΔ d =
  normalisedQuotient A (edgeFluxNumerator S zΔ TΔ) d

record DissipationNormalisedYoungControl
    (S : Scalar.ExactOrderedScalar)
    (A : DissipationNormalisedFluxAuthority S)
    (M : Nat) (z : Energy.AdmissibleFourierMultiplier S M)
    (T : Energy.ZeroSumTriadTransferField S)
    (triads : List Energy.ZeroSumTriad)
    (allocation : Allocation.LocalViscousEdgeAllocation S M z triads) : Set₁ where
  field
    epsilon : Scalar.Scalar S
    fluxRemainder : ExtendedFlux S

    -- This is an explicitly typed conditional Young conclusion.  The two
    -- finite budgets are supplied by the future ordered-field/Cauchy proof;
    -- no arbitrary regularisation at d = 0 is hidden here.
    viscousBudget : Scalar.Scalar S
    dualFluxBudget : ExtendedFlux S
    localYoungSplit : fluxRemainder ≤∞ dualFluxBudget

open DissipationNormalisedYoungControl public

dissipationNormalisedFluxRemainderClosed : Bool
dissipationNormalisedFluxRemainderClosed = false
