module DASHI.Law.QueryWorldFormalWitnessStalenessRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.QueryWorldFormalWitnessStalenessExact as Stale

boundary : Stale.QueryWorldFormalWitnessStalenessBoundary
boundary = Stale.canonicalQueryWorldFormalWitnessStalenessBoundary

positiveBoundToDigest :
  Stale.factorsThroughWitnessRequiresExactProjectionDigest boundary ≡ true
positiveBoundToDigest =
  Stale.factorsThroughWitnessRequiresExactProjectionDigestIsTrue boundary

negativeBoundToDigest :
  Stale.nonfactorabilityWitnessRequiresExactProjectionDigest boundary ≡ true
negativeBoundToDigest =
  Stale.nonfactorabilityWitnessRequiresExactProjectionDigestIsTrue boundary

positiveMayGoStale :
  Stale.changedProjectionMayMakeOldPositiveWitnessStale boundary ≡ true
positiveMayGoStale =
  Stale.changedProjectionMayMakeOldPositiveWitnessStaleIsTrue boundary

negativeMayGoStale :
  Stale.changedProjectionMayMakeOldNegativeWitnessStale boundary ≡ true
negativeMayGoStale =
  Stale.changedProjectionMayMakeOldNegativeWitnessStaleIsTrue boundary

staleIsNotContradiction :
  Stale.staleWitnessIsRuntimeContradiction boundary ≡ false
staleIsNotContradiction =
  Stale.staleWitnessIsRuntimeContradictionIsFalse boundary
