module DASHI.Culture.CohnInstitutionalExpandedCandidateFibreAskRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalExpandedCandidateFibreAskExact as Ask

subjectPositionStillSeparates :
  Ask.subjectPositionOutcome Ask.canonicalExpandedCandidateFibreAsk ≡ Ask.separates
subjectPositionStillSeparates = refl

hermeneuticalRefusalStillSeparates :
  Ask.hermeneuticalRefusalOutcome Ask.canonicalExpandedCandidateFibreAsk ≡ Ask.separates
hermeneuticalRefusalStillSeparates = refl

provenanceStillDoesNotSeparate :
  Ask.provenanceOutcome Ask.canonicalExpandedCandidateFibreAsk ≡ Ask.doesNotSeparate
provenanceStillDoesNotSeparate = refl

newParticipationPowerNotInvented :
  Ask.participationPowerOutcome Ask.canonicalExpandedCandidateFibreAsk ≡ Ask.fixtureInsufficient
newParticipationPowerNotInvented = refl

newInternalExclusionNotInvented :
  Ask.internalExclusionOutcome Ask.canonicalExpandedCandidateFibreAsk ≡ Ask.fixtureInsufficient
newInternalExclusionNotInvented = refl

newEpistemicLabourNotInvented :
  Ask.epistemicLabourOutcome Ask.canonicalExpandedCandidateFibreAsk ≡ Ask.fixtureInsufficient
newEpistemicLabourNotInvented = refl

newRelationalResearchBurdenNotInvented :
  Ask.relationalResearchBurdenOutcome Ask.canonicalExpandedCandidateFibreAsk ≡ Ask.fixtureInsufficient
newRelationalResearchBurdenNotInvented = refl

sourceAcquisitionDoesNotRewriteFixture :
  Ask.acquisitionAloneMayRewriteExistingWorldFacts Ask.canonicalExpandedCandidateBoundary ≡ false
sourceAcquisitionDoesNotRewriteFixture = refl

selectedResidualUnchanged :
  Ask.currentFixtureStillSelectsHermeneuticalRefusal Ask.canonicalExpandedCandidateBoundary ≡ true
selectedResidualUnchanged = refl
