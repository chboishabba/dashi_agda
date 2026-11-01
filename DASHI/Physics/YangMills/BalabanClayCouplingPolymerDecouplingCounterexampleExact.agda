module DASHI.Physics.YangMills.BalabanClayCouplingPolymerDecouplingCounterexampleExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE FOR THE COMPARED REMAINDER SHAPE
--
-- Mir Faizal and Arshid Shabir,
-- "Reflection-Positive Construction of a Four-Dimensional SU(N) Yang-Mills
-- Theory with Mass Gap and Confinement", arXiv:2606.19362v1, 2026.
-- No DOI identified in version 1.
--
-- DASHI CONTRIBUTION
--
-- Give an exact rational counterexample to an invalid decoupling step.
-- A bound K <= delta with delta independent of g does not let one discard a
-- mixed g K term from
--
--   g' = g - beta g^3 + R(g,K).
--
-- At
--
--   g = 1/100, K = 1/100, beta = 1, R = g K,
--
-- the mixed remainder is 100 times the nominal one-loop decrement.  In fact
--
--   g' - g = 99/1,000,000 > 0.
--
-- Thus a g-dependent cone such as K <= eta g^2, or an equally strong coupled
-- invariant, is mathematically necessary for one-loop monotonicity.  The new
-- coupled-flow modules use precisely such a cone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

coupling polymer beta : ℚ
coupling = + 1 / 100
polymer = + 1 / 100
beta = + 1 / 1

couplingCube mixedRemainder oneLoopDecrement nextCoupling increase : ℚ
couplingCube = coupling * coupling * coupling
mixedRemainder = coupling * polymer
oneLoopDecrement = beta * couplingCube
nextCoupling = coupling - oneLoopDecrement + mixedRemainder
increase = + 99 / 1000000

mixedRemainderExact : mixedRemainder ≡ + 1 / 10000
mixedRemainderExact = ℚRing.solve []

oneLoopDecrementExact : oneLoopDecrement ≡ + 1 / 1000000
oneLoopDecrementExact = ℚRing.solve []

mixedTermIsHundredDecrements :
  mixedRemainder ≡ (+ 100 / 1) * oneLoopDecrement
mixedTermIsHundredDecrements = ℚRing.solve []

nextCouplingIsCurrentPlusIncrease :
  nextCoupling ≡ coupling + increase
nextCouplingIsCurrentPlusIncrease = ℚRing.solve []

increaseNonnegative : 0ℚ ≤ increase
increaseNonnegative = ℚP.nonNegative⁻¹ increase

couplingDoesNotDecrease : coupling ≤ nextCoupling
couplingDoesNotDecrease =
  subst
    (λ upper → coupling ≤ upper)
    (sym nextCouplingIsCurrentPlusIncrease)
    (let
      instance
        increaseNN : NonNegative increase
        increaseNN = ℚ.nonNegative increaseNonnegative
     in ℚP.p≤p+q coupling increase)

independentPolymerSmallness : polymer ≤ + 1 / 100
independentPolymerSmallness = ℚP.≤-refl

mixedTermCounterexampleLevel : ProofLevel
mixedTermCounterexampleLevel = machineChecked

independentPolydiscDoesNotEnsureMonotonicityLevel : ProofLevel
independentPolydiscDoesNotEnsureMonotonicityLevel = machineChecked
