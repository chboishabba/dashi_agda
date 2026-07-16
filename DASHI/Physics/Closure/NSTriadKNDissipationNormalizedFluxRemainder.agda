module DASHI.Physics.Closure.NSTriadKNDissipationNormalizedFluxRemainder where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base using (_⊎_)

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

record DissipationNormalisedFluxAuthority
    (S : Scalar.ExactOrderedScalar) : Set₁ where
  field
    abs : Scalar.Scalar S → Scalar.Scalar S
    square : Scalar.Scalar S → Scalar.Scalar S
    divideByPositive : Scalar.Scalar S → Scalar.Scalar S → Scalar.Scalar S
    normalisedQuotient : Scalar.Scalar S → Scalar.Scalar S → ExtendedFlux S

    -- Exact extended-zero convention:
    -- numerator / 0 = 0 only if numerator = 0; otherwise it is infinity.
    zeroDenominatorConvention :
      (numerator : Scalar.Scalar S) →
      normalisedQuotient numerator (Scalar.zero S) ≡ finite (Scalar.zero S)
      ⊎ normalisedQuotient numerator (Scalar.zero S) ≡ infinity

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

    -- This is the exact desired Young split.  It remains an explicit theorem
    -- obligation until the repository has a concrete ordered field,
    -- positivity of epsilon and each local density, and an extended-order
    -- calculus.  No false finite quotient is introduced at zero density.
    localYoungSplit : Set

open DissipationNormalisedYoungControl public

dissipationNormalisedFluxRemainderClosed : Bool
dissipationNormalisedFluxRemainderClosed = false
