module DASHI.JohnAnthonyBrownPrimarySourceVerificationValidation where

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownPrimarySourceVerificationExact as V
import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as M

------------------------------------------------------------------------
-- Focused consumer root.
-- Suggested local command:
--   agda -i . DASHI/JohnAnthonyBrownPrimarySourceVerificationValidation.agda
------------------------------------------------------------------------

authorialProgrammePinned :
  V.PrimarySourceVerificationBoundary.authorialProgrammeAttributedToJohnAnthonyBrown
    V.canonicalPrimarySourceVerificationBoundary
  ≡ true
authorialProgrammePinned = refl

verifiedSourceDOIsPinned :
  V.PrimarySourceVerificationBoundary.verifiedSourcesCarryDOIWhenRecovered
    V.canonicalPrimarySourceVerificationBoundary
  ≡ true
verifiedSourceDOIsPinned = refl

sourceRoleSeparateFromQuality :
  V.PrimarySourceVerificationBoundary.sourceRoleSeparatedFromSourceQuality
    V.canonicalPrimarySourceVerificationBoundary
  ≡ true
sourceRoleSeparateFromQuality = refl

verifiedInstrumentNotTargetValidity :
  V.VerifiedInstrumentPromotesTargetPopulationValidity → ⊥
verifiedInstrumentNotTargetValidity =
  V.verifiedInstrumentDoesNotPromoteTargetPopulationValidity

qualitativeMechanismNotPopulationEffect :
  V.QualitativeMechanismPromotesPopulationEffectSize → ⊥
qualitativeMechanismNotPopulationEffect =
  V.qualitativeMechanismDoesNotPromotePopulationEffectSize

spiritualStruggleNotCoerciveExposure :
  V.SpiritualStrugglePromotesCoerciveExposure → ⊥
spiritualStruggleNotCoerciveExposure =
  V.spiritualStruggleDoesNotPromoteCoerciveExposure

institutionalBetrayalConstructNotH3Effect :
  V.InstitutionalBetrayalConstructPromotesIncrementalH3Effect → ⊥
institutionalBetrayalConstructNotH3Effect =
  V.institutionalBetrayalConstructDoesNotPromoteIncrementalH3Effect

christianEvidenceNotCatholicSpecific :
  V.ChristianSamplePromotesCatholicSpecificity → ⊥
christianEvidenceNotCatholicSpecific =
  V.christianSampleDoesNotPromoteCatholicSpecificity

h3ConstructMapped :
  V.SourceToHypothesis.hypothesis V.h3InstitutionalBetrayalConstruct
  ≡ M.H3
h3ConstructMapped = refl

h2AutonomyInstrumentMapped :
  V.SourceToHypothesis.hypothesis V.h2AutonomyInstrument
  ≡ M.H2
h2AutonomyInstrumentMapped = refl

h1QualitativeBridgeMapped :
  V.SourceToHypothesis.hypothesis V.h1QualitativeTargetBridge
  ≡ M.H1
h1QualitativeBridgeMapped = refl

directReligiousChildhoodEvidenceStillNeeded :
  V.PrimarySourceVerificationBoundary.directReligiousChildhoodEvidenceStillNeeded
    V.canonicalPrimarySourceVerificationBoundary
  ≡ true
directReligiousChildhoodEvidenceStillNeeded = refl
