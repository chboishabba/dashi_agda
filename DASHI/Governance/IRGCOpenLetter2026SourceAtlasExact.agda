module DASHI.Governance.IRGCOpenLetter2026SourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Attribution

-- Provenance-only registry for a contemporary political communication.
-- Entries identify carriers and bounded source roles.  No entry imports
-- proposition truth, political authority, endorsement, or audience effect.

irgcPrimaryLetter : Attribution.AttributedSource
irgcPrimaryLetter = Attribution.mkNoDOISource
  "Islamic Revolutionary Guard Corps (IRGC)"
  "Open letter addressed to the people of the United States"
  "IRGC public political communication; English PDF"
  "2026"
  "https://newsmedia.tasnimmedia.com/Tasnim/Uploaded/Document/1405/07/07/140507071435363573839468.pdf"
  (Attribution.namedSourceKind "primary political communication")
  "Primary carrier for what the IRGC text itself says, cites, predicts, requests, warns, and frames; not independent evidence that its geopolitical or empirical propositions are true"
  Attribution.publicAttribution

reutersReport : Attribution.AttributedSource
reutersReport = Attribution.mkNoDOISource
  "Reuters"
  "Iran appeals to US voters as American troops leave Iraq"
  "Reuters report republished by The Korea Times"
  "2026"
  "https://www.koreatimes.co.kr/world/20260930/iran-appeals-to-us-voters-as-american-troops-leave-iraq"
  Attribution.newsSource
  "Independent report that the IRGC published the letter and urged Americans to use political power; secondary reporting is not a proof of the letter's contested claims"
  Attribution.publicAttribution

iranInternationalReport : Attribution.AttributedSource
iranInternationalReport = Attribution.mkNoDOISource
  "Niloufar Goudarzi"
  "Iran's Guards urge Americans to vote out their leaders in 26-page letter"
  "Iran International"
  "2026"
  "https://www.iranintl.com/en/202609298082"
  Attribution.newsSource
  "Secondary report used only as a competing-source receipt for publication, audience, length and political appeal; outlet framing remains source-local"
  Attribution.publicAttribution

letterAtlas : Attribution.AttributedSourceAtlas
letterAtlas = Attribution.mkSourceAtlas
  "IRGC 2026 open-letter source boundary"
  "DASHI.Governance.IRGCOpenLetter2026SourceAtlasExact"
  (irgcPrimaryLetter ∷ reutersReport ∷ iranInternationalReport ∷ [])
  "The primary artifact pays attribution of its own wording and structure. Secondary reports pay only their reported observations. No citation promotes propaganda intent, truth, threat classification, shared-interest fact, doctrinal identity, audience persuasion, or electoral effect."

sourceCountIsThree : Attribution.sourceCount
  (Attribution.sources letterAtlas) ≡ 3
sourceCountIsThree = refl

primaryCitationImportsNoProof :
  Attribution.citationImportsProof irgcPrimaryLetter ≡ false
primaryCitationImportsNoProof =
  Attribution.citationImportsProofIsFalse irgcPrimaryLetter

primaryCitationCreatesNoAuthority :
  Attribution.citationCreatesAuthority irgcPrimaryLetter ≡ false
primaryCitationCreatesNoAuthority =
  Attribution.citationCreatesAuthorityIsFalse irgcPrimaryLetter
