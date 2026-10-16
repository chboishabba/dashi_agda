module DASHI.Governance.BoloBoloOWSSpokesProposalLineageRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloOWSSpokesProposalLineageExact as Subject

proposalArtifactLineagePaid :
  Subject.proposalArtifactLineagePresent Subject.canonicalSpokesProposalLineageBoundary ≡ true
proposalArtifactLineagePaid = refl

rotationRecallDesignPaid :
  Subject.rotationRecallDesignSurfacePresent Subject.canonicalSpokesProposalLineageBoundary ≡ true
rotationRecallDesignPaid = refl

observerAccessDesignPaid :
  Subject.observerAccessDesignSurfacePresent Subject.canonicalSpokesProposalLineageBoundary ≡ true
observerAccessDesignPaid = refl

designDoesNotProveImplementation :
  Subject.proposalDesignProvesRealizedImplementation Subject.canonicalSpokesProposalLineageBoundary ≡ false
designDoesNotProveImplementation = refl

mirrorDoesNotBecomeOriginal :
  Subject.preservedMirrorEqualsOriginalNYCGAPage Subject.canonicalSpokesProposalLineageBoundary ≡ false
mirrorDoesNotBecomeOriginal = refl

intendedDesignCannotCertifyRealizedControl :
  Subject.IntendedDesignDeterminesRealizedControl → ⊥
intendedDesignCannotCertifyRealizedControl =
  Subject.intendedDesignDoesNotDetermineRealizedControl
