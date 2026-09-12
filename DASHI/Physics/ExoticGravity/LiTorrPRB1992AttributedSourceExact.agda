module DASHI.Physics.ExoticGravity.LiTorrPRB1992AttributedSourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Diligence

------------------------------------------------------------------------
-- PRIMARY APS ATTRIBUTION FOR LI/TORR PRB 46, 5489 (1992)
--
-- The APS landing page pays bibliographic identity and its own abstract-level
-- proposition.  It does not turn the source into an apparatus result and it
-- does not pay an exact equation/model locator without inspected full text.
------------------------------------------------------------------------

liTorrPRB1992APS : Source.AttributedSource
liTorrPRB1992APS = Source.mkDOISource
  "Ning Li; D. G. Torr"
  "Gravitational effects on the magnetic attenuation of superconductors"
  "Physical Review B 46(9), 5489-5495"
  "1992"
  "10.1103/PhysRevB.46.5489"
  "https://link.aps.org/doi/10.1103/PhysRevB.46.5489"
  Source.academicArticleSource
  "Primary APS landing manifestation. It pays author/title/journal/date/DOI identity and the abstract-bounded theoretical claim that including gravitational effects relates ideal-superconductor perfect conductivity and perfect diamagnetism in the paper's sigma-mu model. It does not pay an experimental anomalous-gravity result, apparatus performance, exact equation locator, or later programme continuity."
  Source.publicAttribution

liTorrPRB1992CanonicalAPSURL : Source.AttributedSource
liTorrPRB1992CanonicalAPSURL = Source.mkDOISource
  "Ning Li; D. G. Torr"
  "Gravitational effects on the magnetic attenuation of superconductors"
  "Physical Review B 46(9), 5489-5495"
  "1992"
  "10.1103/PhysRevB.46.5489"
  "https://journals.aps.org/prb/abstract/10.1103/PhysRevB.46.5489"
  Source.academicArticleSource
  "Canonical APS article landing URL for the same DOI object; duplicate manifestation identity is not independent corroboration."
  Source.publicAttribution

prb1992DiligenceCandidateStillPresent :
  Diligence.prb1992Candidate ≡ Diligence.prb1992Candidate
prb1992DiligenceCandidateStillPresent = refl

apsLandingPaysBibliographicIdentity : Bool
apsLandingPaysBibliographicIdentity = true

apsAbstractPaysAbstractLevelTheoryDescription : Bool
apsAbstractPaysAbstractLevelTheoryDescription = true

apsLandingPaysExactEquationLocator : Bool
apsLandingPaysExactEquationLocator = false

apsTheoryPaysExperimentalAntigravity : Bool
apsTheoryPaysExperimentalAntigravity = false

redirectAndCanonicalURLAreIndependentCorroboration : Bool
redirectAndCanonicalURLAreIndependentCorroboration = false

record LiTorrPRB1992AttributionBoundary : Set where
  constructor li-torr-prb1992-attribution-boundary
  field
    citationImportsProof : Bool
    theorySourceCreatesApparatusResult : Bool
    abstractEntitlesUnseenEquation : Bool
    duplicateManifestationCreatesIndependentSource : Bool
    exactLocatorStillRequiredForEquationPromotion : Bool

canonicalLiTorrPRB1992AttributionBoundary : LiTorrPRB1992AttributionBoundary
canonicalLiTorrPRB1992AttributionBoundary =
  li-torr-prb1992-attribution-boundary false false false false true
