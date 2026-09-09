module DASHI.Interop.SensibLawBrightonForm11SourceSpanVerificationValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.SensibLawBrightonForm11SourceSpanVerificationExact as Span

privateArtifactRemainsOutOfRepo :
  Span.BrightonForm11SourceSpanBoundary.privateArtifactRemainsOutOfRepo
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ true
privateArtifactRemainsOutOfRepo = refl

artifactDigestPinned :
  Span.BrightonForm11SourceSpanBoundary.artifactDigestPinned
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ true
artifactDigestPinned = refl

exactEvidenceLocatorPinned :
  Span.BrightonForm11SourceSpanBoundary.exactEvidenceLocatorPinned
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ true
exactEvidenceLocatorPinned = refl

exactTargetClaimDigestPinned :
  Span.BrightonForm11SourceSpanBoundary.exactTargetClaimDigestPinned
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ true
exactTargetClaimDigestPinned = refl

supportedDispositionPaid :
  Span.BrightonForm11SourceSpanBoundary.supportedDispositionPaid
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ true
supportedDispositionPaid = refl

positiveSupportTritPaid :
  Span.BrightonForm11SourceSpanBoundary.positiveSupportTritPaid
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ true
positiveSupportTritPaid = refl

authorityRemainsSeparate :
  Span.BrightonForm11SourceSpanBoundary.authorityRemainsSeparate
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ true
authorityRemainsSeparate = refl

privateBodyNotPublished :
  Span.BrightonForm11SourceSpanBoundary.publishesPrivateBody
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ false
privateBodyNotPublished = refl

healthCausationNotEstablished :
  Span.BrightonForm11SourceSpanBoundary.establishesHealthCausation
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ false
healthCausationNotEstablished = refl

retaliatoryMotiveNotEstablished :
  Span.BrightonForm11SourceSpanBoundary.establishesRetaliatoryMotive
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ false
retaliatoryMotiveNotEstablished = refl

statutoryBreachNotEstablished :
  Span.BrightonForm11SourceSpanBoundary.establishesStatutoryBreach
    Span.canonicalBrightonForm11SourceSpanBoundary ≡ false
statutoryBreachNotEstablished = refl
