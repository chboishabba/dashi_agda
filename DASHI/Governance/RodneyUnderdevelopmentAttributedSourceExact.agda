module DASHI.Governance.RodneyUnderdevelopmentAttributedSourceExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- WALTER RODNEY / RELATIONAL UNDERDEVELOPMENT SOURCE OWNER
--
-- Rodney is admitted as a source genealogy node for colonial extraction,
-- capitalist development and relational underdevelopment.  No term here says
-- that every contemporary dependency relation is caused by Europe, that every
-- Third-Worldist claim follows from Rodney, or that Rodney directly influenced
-- any Iranian actor without a separate source receipt.
------------------------------------------------------------------------

rodney1972 : Source.AttributedSource
rodney1972 = Source.mkNoDOISource
  "Walter Rodney"
  "How Europe Underdeveloped Africa"
  "Bogle-L'Ouverture Publications; original 1972 book"
  "1972"
  "https://www.versobooks.com/en-gb/products/788-how-europe-underdeveloped-africa"
  Source.academicBookSource
  "source for Rodney's historical-materialist account of colonial extraction and the relational production of European development alongside African underdevelopment"
  Source.publicAttribution

rodneySnowballReceipt : Snowball.SourceRoleSnowballReceipt rodney1972
rodneySnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt rodney1972

record RelationalUnderdevelopmentClaim : Set where
  constructor relational-underdevelopment-claim
  field
    source : Source.AttributedSource
    extractingRelation : String
    enrichedPole : String
    impoverishedPole : String
    mechanismReceipt : String
    appliesToNamedContemporaryCase : Bool
    createsCausalClosure : Bool
    createsPoliticalAuthority : Bool

open RelationalUnderdevelopmentClaim public

rodneyColonialRelation : RelationalUnderdevelopmentClaim
rodneyColonialRelation = relational-underdevelopment-claim
  rodney1972
  "colonial extraction and incorporation into international capitalism"
  "European capitalist development"
  "African underdevelopment / constrained endogenous development"
  "Rodney 1972 source role; exact case-specific causal use requires separate historical evidence"
  false false false

data RodneyDirectlyInfluencedIranianRevolution : Set where
data RodneyModelAutomaticallyAppliesToIran : Set where
data RodneyModelAutomaticallyAppliesToPalestine : Set where

rodneyIranDirectInfluenceNeedsEvidence :
  RodneyDirectlyInfluencedIranianRevolution → ⊥
rodneyIranDirectInfluenceNeedsEvidence ()

rodneyIranApplicationNeedsEvidence :
  RodneyModelAutomaticallyAppliesToIran → ⊥
rodneyIranApplicationNeedsEvidence ()

rodneyPalestineApplicationNeedsEvidence :
  RodneyModelAutomaticallyAppliesToPalestine → ⊥
rodneyPalestineApplicationNeedsEvidence ()
