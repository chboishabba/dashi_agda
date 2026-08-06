module DASHI.Physics.Closure.NSTriadKNCherevanSchurYoungLaneAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Source under audit:
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- Convolution reference:
-- Author: Loukas Grafakos.
-- Title: "Modern Fourier Analysis", second edition.
-- DOI: 10.1007/978-0-387-09432-8.
--
-- PURPOSE
-- Audit the TT* step that derives an L^(6/5) -> L^6 bound from Schur-type
-- L1 kernel masses.  Young's convolution relation is
--
--   1 + 1/q = 1/p + 1/r.
--
-- For p=6/5 and q=6, the required kernel exponent is r=3, because
--
--   1/r = 1 + 1/6 - 5/6 = 1/3.
--
-- An L1 kernel instead preserves p: it yields q=6/5, not q=6.  Schur's test
-- controls an L2 -> L2 lane.  A genuine L3-kernel, interpolation, restriction,
-- or other dispersive estimate is therefore a separate missing producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _<_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

one oneSixth fiveSixths oneThird : ℚ
one = Int.+ 1 / 1
oneSixth = Int.+ 1 / 6
fiveSixths = Int.+ 5 / 6
oneThird = Int.+ 1 / 3

youngRequiredKernelReciprocal : ℚ
youngRequiredKernelReciprocal = one + oneSixth - fiveSixths

youngSixFifthsToSixRequiresL3Kernel :
  youngRequiredKernelReciprocal ≡ oneThird
youngSixFifthsToSixRequiresL3Kernel = solve []

lOneKernelOutputReciprocal : ℚ
lOneKernelOutputReciprocal = fiveSixths

targetL6OutputReciprocal : ℚ
targetL6OutputReciprocal = oneSixth

lOneKernelDoesNotReachL6 :
  targetL6OutputReciprocal < lOneKernelOutputReciprocal
lOneKernelDoesNotReachL6 =
  toWitness
    {a? = targetL6OutputReciprocal <? lOneKernelOutputReciprocal}
    _

data KernelMappingLane : Set where
  schurL2ToL2 : KernelMappingLane
  youngL6FifthsToL6 : KernelMappingLane

schurLane targetTTStarLane : KernelMappingLane
schurLane = schurL2ToL2
targetTTStarLane = youngL6FifthsToL6

schurLaneIsNotTargetTTStarLane :
  schurLane ≢ targetTTStarLane
schurLaneIsNotTargetTTStarLane ()
