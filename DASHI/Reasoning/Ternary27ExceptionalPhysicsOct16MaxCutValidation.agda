module DASHI.Reasoning.Ternary27ExceptionalPhysicsOct16MaxCutValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.Ternary27ExceptionalPhysicsOct16MaxCutExact as M

unitSourceWritten : M.firstTitsTwoSidedUnitTermSourceWritten M.currentOct16MaxCut ≡ true
unitSourceWritten = refl

goldstoneSubspacePaidLocally : M.twoVEVHessianKernelEqualsGaugeOrbitLocally M.currentOct16MaxCut ≡ true
goldstoneSubspacePaidLocally = refl

incidenceGroundStatesPaidLocally : M.h3H2IncidenceExactCoverVacuaPaidLocally M.currentOct16MaxCut ≡ true
incidenceGroundStatesPaidLocally = refl

physicalEinsteinStillOpen : M.sameStateEinsteinMatterEqualityPaid M.currentOct16MaxCut ≡ false
physicalEinsteinStillOpen = refl
