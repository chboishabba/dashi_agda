module DASHI.Ethics.InstitutionalAgencySourceAtlas where

-- Source-bounded provenance for the separately authored DASHI model.
-- A source citation is NOT a theorem, endorsement, attribution of DASHI's
-- new constructions to the source author, or evidence about any institution.
-- No DOI is asserted for the items below; noDOIRecordedByAtlas is LOCAL.

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Ethics.InstitutionalAgencyChoiceExact as Agency

landryText : Attribution.AttributedSource
landryText = Attribution.mkNoDOISource
  "Forrest Landry"
  "An Immanent Metaphysics"
  "Author manuscript, PDF; section Self of Choice, page 40"
  "year not independently verified"
  "https://civilizationemerging.com/wp-content/uploads/2020/06/An-Immanent-Metaphysics-Forrest-Landry.pdf"
  Attribution.practitionerSource
  "Primary philosophical claims about potentiality, selection and consequence; NOT a proof of the DASHI contract countermodel"
  Attribution.publicAttribution

landryInterview : Attribution.AttributedSource
landryInterview = Attribution.mkNoDOISource
  "Forrest Landry (interviewee); Jim Rutt (interviewer)"
  "Forrest Landry on Immanent Metaphysics: Part 2 (EP109)"
  "Jim Rutt Show interview transcript"
  "2021"
  "https://jimrutt.substack.com/p/ep109-forrest-landry-on-immanent-079"
  (Attribution.namedSourceKind "interview transcript")
  "Secondary interview carrier for Landry's stated three modalities, axioms and choice triplet; philosophical claims are attributed, not established"
  Attribution.publicAttribution

-- From the user-provided screenshot only; a full episode transcript was
-- NOT inspected and must not be treated as source payment for its content.
mcnamaraScreenshot : Attribution.AttributedSource
mcnamaraScreenshot = Attribution.mkNoDOISource
  "Rob McNamara (presenter); uvsmpub (publisher account)"
  "A System of Wrong, Part 4: The Grid"
  "User-supplied social-media screenshot; caption only"
  "2026 screenshot observation; episode date unverified"
  "unresolved episode URL; screenshot supplied in conversation"
  (Attribution.namedSourceKind "social-media screenshot")
  "Screenshot title and opening framing only; NOT verified claims made in the episode"
  Attribution.publicAttribution

gridAtlas : Attribution.AttributedSourceAtlas
gridAtlas = Attribution.mkSourceAtlas
  "Institutional agency / immanent metaphysics source boundaries"
  "DASHI formalisation; source authors retained separately"
  (landryText ∷ landryInterview ∷ mcnamaraScreenshot ∷ [])
  "The ChoiceExact module proves a DASHI-defined feasible-choice inclusion and a toy countermodel only. No physical indeterminism, legal coercion, full episode reconstruction, or metaphysical theorem imported."

sourceCountIsThree : Attribution.sourceCount
  (Attribution.sources gridAtlas) ≡ 3
sourceCountIsThree = refl

