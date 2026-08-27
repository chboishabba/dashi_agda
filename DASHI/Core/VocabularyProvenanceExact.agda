module DASHI.Core.VocabularyProvenanceExact where

------------------------------------------------------------------------
-- VOCABULARY PROVENANCE
--
-- SOURCE CALIBRATION
-- Miranda Fricker, Epistemic Injustice: Power and the Ethics of Knowing,
-- Oxford University Press, 2007.
-- DOI 10.1093/acprof:oso/9780198237907.001.0001.
--
-- Fricker motivates testimonial/hermeneutical injustice concerns. DASHI uses
-- vocabulary-origin metadata only as an audit surface; it does not claim that
-- every imported formal term constitutes an epistemic injustice.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data VocabularyOrigin : Set where
  sourceNative
  interlocutorSupplied
  dashiImported
  mathematicalImported
  mixedProvenance
  : VocabularyOrigin

record VocabularyEntry : Set where
  constructor vocabulary-entry
  field
    term : String
    origin : VocabularyOrigin
    sourceNote : String
    formalRoleNote : String

open VocabularyEntry public

record EpistemicAuthorityBoundary : Set where
  constructor epistemic-authority-boundary
  field
    kernelVerifiedImpliesInterpretivelyAuthoritative : Bool
    kernelVerifiedImpliesInterpretivelyAuthoritativeIsFalse :
      kernelVerifiedImpliesInterpretivelyAuthoritative ≡ false
    formalClarityTransfersEpistemicOwnership : Bool
    formalClarityTransfersEpistemicOwnershipIsFalse :
      formalClarityTransfersEpistemicOwnership ≡ false
    importedVocabularyIsAutomaticallySourceNative : Bool
    importedVocabularyIsAutomaticallySourceNativeIsFalse :
      importedVocabularyIsAutomaticallySourceNative ≡ false
    sourceSelfDescriptionIsOverriddenByMachineProof : Bool
    sourceSelfDescriptionIsOverriddenByMachineProofIsFalse :
      sourceSelfDescriptionIsOverriddenByMachineProof ≡ false

canonicalEpistemicAuthorityBoundary : EpistemicAuthorityBoundary
canonicalEpistemicAuthorityBoundary =
  epistemic-authority-boundary false refl false refl false refl false refl
