module DASHI.Law.SensibLawTypedWorkbenchTransportBoundaryRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawTypedWorkbenchTransportBoundaryExact as T

boundary : T.TypedWorkbenchTransportBoundary
boundary = T.canonicalTypedWorkbenchTransportBoundary

postgresStillProductionInput :
  T.postgresRowsAreProductionAuthorityInput boundary ≡ true
postgresStillProductionInput = refl

typedRustStillProductionCarrier :
  T.typedRustIsProductionWorkbenchCarrier boundary ≡ true
typedRustStillProductionCarrier = refl

jsonStillReplayExportOnly :
  T.jsonIsReplayExportOnly boundary ≡ true
jsonStillReplayExportOnly = refl

jsonStillNotRequiredForNormalComparison :
  T.jsonIsRequiredForNormalComparison boundary ≡ false
jsonStillNotRequiredForNormalComparison = refl

dioxusStillNotSemanticComparisonOwner :
  T.dioxusOwnsSemanticComparison boundary ≡ false
dioxusStillNotSemanticComparisonOwner = refl

wgpuStillNotSemanticComparisonOwner :
  T.wgpuOwnsSemanticComparison boundary ≡ false
wgpuStillNotSemanticComparisonOwner = refl

transportStillCreatesNoAuthority :
  T.transportCreatesSemanticAuthority boundary ≡ false
transportStillCreatesNoAuthority = refl

transportStillCreatesNoTruth :
  T.transportCreatesClaimTruth boundary ≡ false
transportStillCreatesNoTruth = refl
