module DASHI.Analysis.RiemannUniversalEvenConeLeanSourceCustodyValidationExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannUniversalEvenConeLeanSourceCustodyExact as P

boundary : P.UniversalEvenConeLeanSourceCustodyBoundary
boundary = P.canonicalUniversalEvenConeLeanSourceCustodyBoundary

_ : P.agdaSourceClaimRecorded boundary ≡ true
_ = refl

_ : P.checkedLeanOwnerLocated boundary ≡ false
_ = refl

_ : P.checkedLeanKernelReceiptObserved boundary ≡ false
_ = refl

_ : P.agdaTransportObserved boundary ≡ false
_ = refl

_ : P.missingLeanOwnerMayBeReplacedByMinimalReproofProbe boundary ≡ true
_ = refl

_ : P.sourceClaimCreatesTransportAuthority boundary ≡ false
_ = refl
