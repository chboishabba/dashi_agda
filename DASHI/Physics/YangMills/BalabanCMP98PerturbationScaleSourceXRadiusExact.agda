module DASHI.Physics.YangMills.BalabanCMP98PerturbationScaleSourceXRadiusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- Equation (38) requires |X| <= 1/20.  In the first-order application X is a
-- scaled tangent generator.  There is therefore no global smallness condition
-- on the tangent direction itself: it suffices to restrict the local curve
-- parameter so that
--
--       20 * |t| * ||delta|| <= 1.
--
-- This module proves the exact rational implication
--
--       20 * scaledMagnitude <= 1  ==>  scaledMagnitude <= 1/20.
--
-- Hence G1's X-radius is a local-parameter condition, not an additional
-- selected-background estimate.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; _/_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38

_twenty : ℚ
_twenty = + 20 / 1

twentyPositiveProof : 0ℚ < _twenty
twentyPositiveProof = ℚP.positive⁻¹ _twenty

instance
  twentyPositive : Positive _twenty
  twentyPositive = ℚ.positive twentyPositiveProof

scaledMagnitudeInsideSourceX :
  ∀ scaledMagnitude →
  _twenty * scaledMagnitude ≤ 1ℚ →
  scaledMagnitude ≤ Eq38.sourceXRadius
scaledMagnitudeInsideSourceX scaledMagnitude scaled =
  let
    divided : scaledMagnitude ≤ 1ℚ / _twenty
    divided = ℚP.*-cancelˡ-≤-pos _twenty
      (subst
        (λ upper → _twenty * scaledMagnitude ≤ upper)
        (sym (ℚRing.solve [] : _twenty * (1ℚ / _twenty) ≡ 1ℚ))
        scaled)
  in
  subst
    (λ upper → scaledMagnitude ≤ upper)
    (ℚRing.solve [] : 1ℚ / _twenty ≡ Eq38.sourceXRadius)
    divided

cmp98PerturbationScaleSourceXRadiusLevel : ProofLevel
cmp98PerturbationScaleSourceXRadiusLevel = machineChecked
