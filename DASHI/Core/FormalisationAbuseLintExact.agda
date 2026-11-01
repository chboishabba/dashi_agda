module DASHI.Core.FormalisationAbuseLintExact where

------------------------------------------------------------------------
-- FORMALISATION ABUSE LINT
--
-- CRITICAL CALIBRATION
-- Alan Sokal and Jean Bricmont, Fashionable Nonsense: Postmodern
-- Intellectuals' Abuse of Science, Picador, 1998. ISBN 9780312204075.
-- No DOI asserted for the book.
--
-- This module does not encode Sokal/Bricmont's critique as theorem authority.
-- It extracts a DASHI meta-level anti-promotion lint motivated by the general
-- problem of technical vocabulary being imported without justified semantic
-- work.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record FormalisationAbuseRisk : Set where
  constructor formalisation-abuse-risk
  field
    importedTechnicalTermUndefined : Bool
    analogyPromotedToIdentity : Bool
    formalTheoremPromotedToSourceClaim : Bool
    sourceClaimPromotedToEmpiricalLaw : Bool
    proofStatusUsedAsInterpretiveAuthority : Bool

open FormalisationAbuseRisk public

record CleanFormalisationLint (risk : FormalisationAbuseRisk) : Set where
  constructor clean-formalisation-lint
  field
    importedTechnicalTermDefined : importedTechnicalTermUndefined risk ≡ false
    analogyNotIdentity : analogyPromotedToIdentity risk ≡ false
    theoremNotSourceClaim : formalTheoremPromotedToSourceClaim risk ≡ false
    sourceNotEmpiricalLaw : sourceClaimPromotedToEmpiricalLaw risk ≡ false
    proofNotInterpretiveAuthority : proofStatusUsedAsInterpretiveAuthority risk ≡ false

canonicalRisk : FormalisationAbuseRisk
canonicalRisk = formalisation-abuse-risk false false false false false

canonicalCleanLint : CleanFormalisationLint canonicalRisk
canonicalCleanLint = clean-formalisation-lint refl refl refl refl refl

record FormalisationAbuseBoundary : Set where
  constructor formalisation-abuse-boundary
  field
    topologicalAnalogyProvesPsychologicalIdentity : Bool
    topologicalAnalogyProvesPsychologicalIdentityIsFalse :
      topologicalAnalogyProvesPsychologicalIdentity ≡ false
    ternaryGraphIsHistoricalAuthorsMathematics : Bool
    ternaryGraphIsHistoricalAuthorsMathematicsIsFalse :
      ternaryGraphIsHistoricalAuthorsMathematics ≡ false
    machineProofIsEmpiricalConfirmation : Bool
    machineProofIsEmpiricalConfirmationIsFalse :
      machineProofIsEmpiricalConfirmation ≡ false

canonicalFormalisationAbuseBoundary : FormalisationAbuseBoundary
canonicalFormalisationAbuseBoundary =
  formalisation-abuse-boundary false refl false refl false refl
