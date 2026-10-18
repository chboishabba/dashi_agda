module DASHI.Interop.SLRCanonicalEvidenceSubstrateRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Interop.SLRCanonicalEvidenceSubstrateExact as Canonical

manifestationCannotCreateAuthority :
  Canonical.ManifestationCreatesSemanticAuthority → ⊥
manifestationCannotCreateAuthority =
  Canonical.manifestationDoesNotCreateSemanticAuthority

observationCannotCreateTruth :
  Canonical.ObservationCreatesClaimTruth → ⊥
observationCannotCreateTruth =
  Canonical.observationDoesNotCreateClaimTruth

structuredEvidenceNeedNotBeText :
  Canonical.StructuredCoordinateMustBecomeTextRange → ⊥
structuredEvidenceNeedNotBeText =
  Canonical.structuredCoordinateDoesNotBecomeTextRange

wholeRevisionNeedNotBeText :
  Canonical.WholeRevisionMustBecomeTextRange → ⊥
wholeRevisionNeedNotBeText =
  Canonical.wholeRevisionDoesNotBecomeTextRange
