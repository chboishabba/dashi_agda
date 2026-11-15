module DASHI.Analysis.BishopOriginalEtaFiniteAbelSourceExact where

------------------------------------------------------------------------
-- P2 ORIGINAL BISHOP FINITE ABEL / PAIR-VARIATION TRANSPORT.
--
-- Pure finite algebra on the actual BishopComplex (two Murray/Bishop
-- real setoid coordinates). No native complex replacement and no
-- assumptions about canonicalNatLog, derivatives, FTC, convergence.
--
-- For arbitrary a_j,b_j in the original source complex setoid:
--
-- sum_(j<n) (a_j - b_j)
--   = a_0 - a_n + sum_(j<n) (a_(j+1) - b_j).
--
-- Instantiated below with a_j=term(2j), b_j=term(2j+1),
-- where term may be the literal Round11 Dirichlet source.
--
-- SOURCE-WRITTEN, NOT YET PINNED AGDA 2.9 KERNEL ACCEPTED.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import RealProperties as RP
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta

infix 4 _≈C_
_≈C_ : BC.BishopComplex → BC.BishopComplex → Set
_≈C_ = Eta._≈C_

originalAbelDifferencePrefix :
  (a b : Nat → BC.BishopComplex) → Nat → BC.BishopComplex
originalAbelDifferencePrefix a b =
  Eta.originalBishopPrefix
    (λ j → BC._+C_ (a (suc j)) (BC.negC (b j)))

-- Setoid cancellation in the true complex source, component by component.
originalAbelBase :
  (a : BC.BishopComplex) →
  BC._+C_ (BC._+C_ a (BC.negC a)) BC.zeroC ≈C BC.zeroC
originalAbelBase (BC.bishop-complex ar ai) =
  (let open RP.ℝ-Solver in
   solve 1
     (λ a → (a ⊕ (⊝ a)) ⊕ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
     RP.≃-refl ar)
  ,
  (let open RP.ℝ-Solver in
   solve 1
     (λ a → (a ⊕ (⊝ a)) ⊕ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
     RP.≃-refl ai)

-- The complete induction step is a real polynomial ring identity
-- independently in both source coordinates.
originalAbelStep :
  (a b c d v : BC.BishopComplex) →
  BC._+C_
    (BC._+C_ a (BC.negC d))
    (BC._+C_ v (BC._+C_ d (BC.negC c)))
  ≈C
  BC._+C_
    (BC._+C_ (BC._+C_ a (BC.negC b)) v)
    (BC._+C_ b (BC.negC c))
originalAbelStep
    (BC.bishop-complex ar ai)
    (BC.bishop-complex br bi)
    (BC.bishop-complex cr ci)
    (BC.bishop-complex dr di)
    (BC.bishop-complex vr vi) =
  (let open RP.ℝ-Solver in
   solve 5
     (λ a b c d v →
       (a ⊕ (⊝ d)) ⊕ (v ⊕ (d ⊕ (⊝ c)))
       ⊜
       ((a ⊕ (⊝ b)) ⊕ v) ⊕ (b ⊕ (⊝ c)))
     RP.≃-refl ar br cr dr vr)
  ,
  (let open RP.ℝ-Solver in
   solve 5
     (λ a b c d v →
       (a ⊕ (⊝ d)) ⊕ (v ⊕ (d ⊕ (⊝ c)))
       ⊜
       ((a ⊕ (⊝ b)) ⊕ v) ⊕ (b ⊕ (⊝ c)))
     RP.≃-refl ai bi ci di vi)

originalBishopAbelFinite :
  (a b : Nat → BC.BishopComplex) (n : Nat) →
  BC._+C_
    (BC._+C_ (a zero) (BC.negC (a n)))
    (originalAbelDifferencePrefix a b n)
  ≈C
  Eta.originalBishopPrefix
    (λ j → BC._+C_ (a j) (BC.negC (b j))) n
originalBishopAbelFinite a b zero = originalAbelBase (a zero)
originalBishopAbelFinite a b (suc n) =
  Eta.≈C-trans
    (originalAbelStep (a zero) (a n) (b n)
      (a (suc n)) (originalAbelDifferencePrefix a b n))
    (Eta.addRightCongruent
      (originalBishopAbelFinite a b n)
      (BC._+C_ (a n) (BC.negC (b n))))

-- This is the SAME source prefix, not an independently picked eta.
-- In particular, sourceTerms from OriginalRound11DirichletEta can be
-- passed directly as term, with its exact canonical Nat-log producer.
originalRound11EtaFiniteAbel :
  (term : Nat → BC.BishopComplex) (n : Nat) →
  BC._+C_
    (BC._+C_ (term zero)
      (BC.negC (term (Eta.twice n))))
    (originalAbelDifferencePrefix
      (λ j → term (Eta.twice j))
      (λ j → term (suc (Eta.twice j))) n)
  ≈C Eta.originalEtaPrefix term n
originalRound11EtaFiniteAbel term n =
  originalBishopAbelFinite
    (λ j → term (Eta.twice j))
    (λ j → term (suc (Eta.twice j))) n

-- Analytic gates remain: true canonical Nat-log identity, exp addition,
-- term derivative/FTC, cutoff-uniform Abel bound in Bishop absolute
-- value/order, SeriesOf completion, and original eta convergence.
