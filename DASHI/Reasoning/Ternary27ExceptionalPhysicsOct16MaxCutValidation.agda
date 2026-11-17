module DASHI.Reasoning.Ternary27ExceptionalPhysicsOct16MaxCutValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.Ternary27ExceptionalPhysicsOct16MaxCutExact as M

unitSourceWritten : M.firstTitsTwoSidedUnitTermSourceWritten M.currentOct16MaxCut ≡ true
unitSourceWritten = refl

bilinearitySourceWritten : M.firstTitsFullBilinearityTermSourceWritten M.currentOct16MaxCut ≡ true
bilinearitySourceWritten = refl

cubicHomogeneitySourceWritten : M.firstTitsCubicHomogeneityTermSourceWritten M.currentOct16MaxCut ≡ true
cubicHomogeneitySourceWritten = refl

jordanStillNotKernelPaid : M.firstTitsJordanIdentityTermSourceWritten M.currentOct16MaxCut ≡ false
jordanStillNotKernelPaid = refl

goldstoneSubspacePaidLocally : M.twoVEVHessianKernelEqualsGaugeOrbitLocally M.currentOct16MaxCut ≡ true
goldstoneSubspacePaidLocally = refl

incidenceGroundStatesPaidLocally : M.h3H2IncidenceExactCoverVacuaPaidLocally M.currentOct16MaxCut ≡ true
incidenceGroundStatesPaidLocally = refl

equalGapNotPromotedToSameOperator : M.incidenceGapEqualsFibreGapBySameOperatorTheorem M.currentOct16MaxCut ≡ false
equalGapNotPromotedToSameOperator = refl

physicalEinsteinStillOpen : M.sameStateEinsteinMatterEqualityPaid M.currentOct16MaxCut ≡ false
physicalEinsteinStillOpen = refl
