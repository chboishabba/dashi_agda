module DASHI.Physics.Closure.NSTriadKNSelfPhaseSquareMassSignAuditRound109Exact where

------------------------------------------------------------------------
-- ROUND109 / THE EXACT SELF PHASE CHANNEL IS STRUCTURED, NOT SIGN-DEFINITE
--
-- Round106 proves the literal self-phase leg identity
--
--   <N_k^{p,q}, u_p x u_q>
--     = (lambda_q-lambda_p) <P_k X, P_k X>.
--
-- The projected-cross factor is a square mass.  That removes the self term
-- from the class of opaque external forcing, but it does NOT make the term
-- automatically favourable: the signed eigenvalue difference may have either
-- sign.  This tiny exact rational witness prevents the Clay frontier from
-- silently discarding the self channel merely because its mass factor is
-- nonnegative.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; -_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNSelfWaleffePhaseProjectedCrossMassRound106Exact as Self

signedSquareMass : ℚ → ℚ → ℚ
signedSquareMass eigenDifference squareMass = eigenDifference * squareMass

positiveDifferenceWitness : signedSquareMass 1ℚ 1ℚ ≡ 1ℚ
positiveDifferenceWitness = ℚP.*-identityˡ 1ℚ

negativeDifferenceWitness : signedSquareMass (- 1ℚ) 1ℚ ≡ - 1ℚ
negativeDifferenceWitness = ℚP.*-identityʳ (- 1ℚ)

minusOneStrictlyNegative : - 1ℚ < 0ℚ
minusOneStrictlyNegative = toWitness {a? = (- 1ℚ) <? 0ℚ} _

negativeSelfSquareMassWitness : signedSquareMass (- 1ℚ) 1ℚ < 0ℚ
negativeSelfSquareMassWitness rewrite negativeDifferenceWitness = minusOneStrictlyNegative

round109ExactSelfSquareMassGeometryReused : Bool
round109ExactSelfSquareMassGeometryReused =
  Self.round106SelfWaleffePhaseProjectedCrossMassClosed

round109SelfSquareMassAutomaticallyFavourable : Bool
round109SelfSquareMassAutomaticallyFavourable = false

round109SelfSquareMassRequiresOpaqueForcingEstimate : Bool
round109SelfSquareMassRequiresOpaqueForcingEstimate = false

round109ExactSelfSquareMassGeometryReusedIsTrue :
  round109ExactSelfSquareMassGeometryReused ≡ true
round109ExactSelfSquareMassGeometryReusedIsTrue = refl

round109SelfSquareMassAutomaticallyFavourableIsFalse :
  round109SelfSquareMassAutomaticallyFavourable ≡ false
round109SelfSquareMassAutomaticallyFavourableIsFalse = refl

round109SelfSquareMassRequiresOpaqueForcingEstimateIsFalse :
  round109SelfSquareMassRequiresOpaqueForcingEstimate ≡ false
round109SelfSquareMassRequiresOpaqueForcingEstimateIsFalse = refl
