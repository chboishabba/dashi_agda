module DASHI.Physics.Closure.NSTriadKNDepletionBarrier where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar

------------------------------------------------------------------------
-- Finite good/bad depletion barrier.
--
-- This module proves only the bookkeeping step.  Its two physical inputs are
-- deliberately visible:
--
--   (i)  a local hierarchy estimate on the good edges; and
--   (ii) a bad-edge sparsity/profile estimate.
--
-- It does not assert either input for arbitrary Navier--Stokes data.
------------------------------------------------------------------------

record BarrierAdditiveOrderAuthority (S : Scalar.ExactOrderedScalar) : Set₁ where
  field
    addMonotone :
      {a b c d : Scalar.Scalar S} →
      Scalar._≤_ S a b → Scalar._≤_ S c d →
      Scalar._≤_ S (Scalar._+_ S a c) (Scalar._+_ S b d)

    transportLeft :
      {a b c : Scalar.Scalar S} →
      a ≡ b → Scalar._≤_ S b c → Scalar._≤_ S a c

open BarrierAdditiveOrderAuthority public

record DepletionBarrierPremises
    (S : Scalar.ExactOrderedScalar) : Set₁ where
  field
    -- The finite edge quotient has already been split by the threshold eta.
    totalFlux goodFlux badFlux : Scalar.Scalar S
    goodHierarchyBound badSparsityBound : Scalar.Scalar S

    splitFlux : totalFlux ≡ Scalar._+_ S goodFlux badFlux

    -- These are exactly the nonclassical inputs.  In the intended use,
    -- `goodHierarchyBound` is eta^2 * Cmult * X * D, while
    -- `badSparsityBound` is Sigma(eta,u).
    goodEdgeHierarchy : Scalar._≤_ S goodFlux goodHierarchyBound
    badEdgeSparsity : Scalar._≤_ S badFlux badSparsityBound

open DepletionBarrierPremises public

-- Mechanical finite recombination of the good/bad split.  This is the
-- theorem used by the later energy estimate; it introduces no analytic
-- assumption beyond the two named premises above.
depletionBarrierImpliesFluxHierarchy :
  (S : Scalar.ExactOrderedScalar) →
  (O : BarrierAdditiveOrderAuthority S) →
  (P : DepletionBarrierPremises S) →
  Scalar._≤_ S
    (totalFlux P)
    (Scalar._+_ S (goodHierarchyBound P) (badSparsityBound P))
depletionBarrierImpliesFluxHierarchy S O P =
  transportLeft O (splitFlux P)
    (addMonotone O (goodEdgeHierarchy P) (badEdgeSparsity P))

-- A strict barrier is an additional PDE/dynamical statement.  The local
-- algebra above reduces it to this exact target; neither its strict margin
-- nor the time-integrated energy inequality is manufactured here.
record StrictDepletionBarrierTarget
    (S : Scalar.ExactOrderedScalar) : Set₁ where
  field
    eta : Scalar.Scalar S
    hierarchyContribution : Scalar.Scalar S
    badContribution : Scalar.Scalar S
    dissipation : Scalar.Scalar S
    strictMargin : Scalar.Scalar S

    -- Intended conclusion after a concrete threshold/profile proof:
    -- hierarchyContribution + badContribution + strictMargin <= dissipation.
    strictBarrier : Set

open StrictDepletionBarrierTarget public

depletionBarrierClosed : Bool
depletionBarrierClosed = false
