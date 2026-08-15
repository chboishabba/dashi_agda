module DASHI.Physics.YangMills.BalabanCMP119RDecayReserveBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- DIRECT LOCATOR
--
-- Section 2, equation (2.31), p. 260: the localized R-terms satisfy a stronger
-- exponential diameter bound, and the text immediately following (2.31) says
-- that kappa_0 can be chosen arbitrarily large (similarly to K) after the other
-- constructive parameters are fixed appropriately.
--
-- IMPORTANT NORMALIZATION DISTINCTION
--
-- This R-operation decay reserve is not the same constant as the repository's
-- unit-normalized propagator/polymer link weight.  The latter may be normalized
-- to one without consuming the source freedom to choose the former larger.
-- Conflating them would throw away exactly the decay needed to beat rooted
-- entropy.
--
-- DASHI CONTRIBUTION
--
-- Record a concrete three-part reserve plan in normalized distance units:
--
--   kappa_R >= 3 = 1 (polymer norm weight)
--                    + 1 (rooted entropy payment)
--                    + 1 (strict shell-decay reserve).
--
-- The rational arithmetic is exact.  The only physical/source dictionary seam
-- is that Bałaban's d_j(X) and the repository normalized rooted diameter must be
-- compared in the same units.  Once that metric comparison is supplied, the
-- source statement "kappa_0 arbitrarily large" permits this finite reserve.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

unitWeightReserve entropyReserve shellReserve sourceReserveFloor : ℚ
unitWeightReserve = + 1 / 1
entropyReserve = + 1 / 1
shellReserve = + 1 / 1
sourceReserveFloor = + 3 / 1

threeWayReserveExact :
  unitWeightReserve + entropyReserve + shellReserve ≡ sourceReserveFloor
threeWayReserveExact = ℚRing.solve []

unitPlusEntropyBelowSourceFloor :
  unitWeightReserve + entropyReserve ≤ sourceReserveFloor
unitPlusEntropyBelowSourceFloor =
  ℚP.<⇒≤ (ℚP.positive⁻¹
    (sourceReserveFloor - (unitWeightReserve + entropyReserve)))

allThreeFitSourceFloor :
  unitWeightReserve + entropyReserve + shellReserve ≤ sourceReserveFloor
allThreeFitSourceFloor =
  subst
    (λ left → left ≤ sourceReserveFloor)
    threeWayReserveExact
    ℚP.≤-refl
  where
  open import Relation.Binary.PropositionalEquality using (subst)

cmp119Equation231ArbitraryRDecayReserveLevel : ProofLevel
cmp119Equation231ArbitraryRDecayReserveLevel = standardImported

cmp119ThreeWayDecayReserveArithmeticLevel : ProofLevel
cmp119ThreeWayDecayReserveArithmeticLevel = machineChecked

-- Compare source d_j(X) with the repository rooted/polymer diameter after all
-- scale normalizations.  No claim is made that this metric dictionary follows
-- merely from choosing kappa_R large.
cmp119SourceDistanceToRepositoryDiameterLevel : ProofLevel
cmp119SourceDistanceToRepositoryDiameterLevel = conditional
