module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCanonicalSelectionContentValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCanonicalSelectionContentExact as Content

boundary = Content.canonicalAdKCanonicalSelectionContentBoundary

_ : Content.transparentCanonicalRowsRetained boundary ≡ true
_ = refl

_ : Content.fullEightSelectionPacketExplicit boundary ≡ true
_ = refl

_ : Content.massSourceAttributionRetained boundary ≡ true
_ = refl

_ : Content.contentEqualityDefinesSelectionEquivalence boundary ≡ true
_ = refl

_ : Content.contentSoundCOMCreatesThreeCVEquality boundary ≡ true
_ = refl

_ : Content.payloadHashRetainedAsAuditCoordinate boundary ≡ true
_ = refl

_ : Content.hashEqualityCreatesContentEquality boundary ≡ false
_ = refl

_ : Content.executableCanonicalisationCreatesScientificAuthority boundary ≡ false
_ = refl
