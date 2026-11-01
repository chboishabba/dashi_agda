module DASHI.Interop.FormalisationGovernanceAttributedSourceMigrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.FormalisationGovernanceSourceRegistryExact as Legacy
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SearchBridge

------------------------------------------------------------------------
-- LEGACY GOVERNANCE SOURCE -> CANONICAL ATTRIBUTED SOURCE MIGRATION
--
-- The older registry already carried author/title/venue/identifier/boundedRole.
-- We migrate only rows whose DOI/publication split can be recovered without
-- invention. Rows still lacking a canonical URL/edition split remain explicit
-- migration residuals rather than receiving guessed metadata.
------------------------------------------------------------------------

beethamLegitimacyAttributed : Source.AttributedSource
beethamLegitimacyAttributed = Source.mkDOISource
  "David Beetham"
  "The Legitimation of Power"
  "Macmillan, 1991"
  "1991"
  "10.1007/978-1-349-21599-7"
  "https://doi.org/10.1007/978-1-349-21599-7"
  Source.academicBookSource
  "legacy governance provenance: rule-conformity, justificatory belief and consent remain distinct legitimacy-evidence dimensions"
  Source.publicAttribution

mccallComplexityAttributed : Source.AttributedSource
mccallComplexityAttributed = Source.mkDOISource
  "Leslie McCall"
  "The Complexity of Intersectionality"
  "Signs 30(3):1771-1800"
  "2005"
  "10.1086/426800"
  "https://doi.org/10.1086/426800"
  Source.academicArticleSource
  "legacy governance provenance for anti/intra/intercategorical methodological strategy separation"
  Source.publicAttribution

harawaySituatedAttributed : Source.AttributedSource
harawaySituatedAttributed = Source.mkDOISource
  "Donna Haraway"
  "Situated Knowledges: The Science Question in Feminism and the Privilege of Partial Perspective"
  "Feminist Studies 14(3):575-599"
  "1988"
  "10.2307/3178066"
  "https://doi.org/10.2307/3178066"
  Source.academicArticleSource
  "legacy governance provenance for situated/partial knowledge; no view-from-nowhere authority is created"
  Source.publicAttribution

frickerEpistemicInjusticeAttributed : Source.AttributedSource
frickerEpistemicInjusticeAttributed = Source.mkDOISource
  "Miranda Fricker"
  "Epistemic Injustice: Power and the Ethics of Knowing"
  "Oxford University Press"
  "2007"
  "10.1093/acprof:oso/9780198237907.001.0001"
  "https://doi.org/10.1093/acprof:oso/9780198237907.001.0001"
  Source.academicBookSource
  "legacy governance provenance for testimonial/hermeneutical injustice calibration"
  Source.publicAttribution

lugonesPurityAttributed : Source.AttributedSource
lugonesPurityAttributed = Source.mkDOISource
  "Maria Lugones"
  "Purity, Impurity, and Separation"
  "Signs 19(2):458-479"
  "1994"
  "10.1086/494893"
  "https://doi.org/10.1086/494893"
  Source.academicArticleSource
  "legacy governance provenance for purity/impurity critique; DASHI anti-factorisation remains separately owned"
  Source.publicAttribution

migratedDOISources : List Source.AttributedSource
migratedDOISources =
  beethamLegitimacyAttributed
  ∷ mccallComplexityAttributed
  ∷ harawaySituatedAttributed
  ∷ frickerEpistemicInjusticeAttributed
  ∷ lugonesPurityAttributed
  ∷ []

migratedDOIAtlas : Source.AttributedSourceAtlas
migratedDOIAtlas = Source.mkSourceAtlas
  "Formalisation governance legacy DOI-source migration"
  "DASHI.Interop.FormalisationGovernanceAttributedSourceMigrationExact"
  migratedDOISources
  "Compatibility migration for DOI-bearing rows in FormalisationGovernanceSourceRegistryExact; legacy bounded roles remain provenance, not theorem authority"

------------------------------------------------------------------------
-- Rows that cannot yet be migrated without inventing canonical metadata.
------------------------------------------------------------------------

data LegacyMigrationGap : Set where
  canonicalURLUnresolved : LegacyMigrationGap
  editionIdentityUnresolved : LegacyMigrationGap
  identifierNeedsTypedParsing : LegacyMigrationGap
  publicationSplitUnresolved : LegacyMigrationGap

record LegacySourceMigrationResidual : Set where
  constructor legacy-source-migration-residual
  field
    legacyEntryReference : String
    legacyAuthorReference : String
    legacyTitleReference : String
    gap : LegacyMigrationGap
    nextProducer : SearchBridge.SourceDiligenceGap
    residualReference : String

open LegacySourceMigrationResidual public

lordeMigrationResidual : LegacySourceMigrationResidual
lordeMigrationResidual = legacy-source-migration-residual
  "DASHI.Core.FormalisationGovernanceSourceRegistryExact.lordeMastersTools"
  (Legacy.author Legacy.lordeMastersTools)
  (Legacy.title Legacy.lordeMastersTools)
  canonicalURLUnresolved
  SearchBridge.primarySourceNotSearched
  "retain 1979/Sister Outsider/ISBN metadata; locate and inspect a canonical primary or publisher carrier before typed migration rather than inventing a DOI/URL"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LegacyIdentifierStringAutomaticallyDOI : Set where
data MissingCanonicalURLMayBeGuessed : Set where
data MigrationChangesBoundedInterpretiveRole : Set where

legacyIdentifierRequiresParsing : LegacyIdentifierStringAutomaticallyDOI → ⊥
legacyIdentifierRequiresParsing ()

missingURLMustRemainResidual : MissingCanonicalURLMayBeGuessed → ⊥
missingURLMustRemainResidual ()

migrationDoesNotPromoteInterpretation : MigrationChangesBoundedInterpretiveRole → ⊥
migrationDoesNotPromoteInterpretation ()

record FormalisationGovernanceMigrationBoundary : Set where
  constructor formalisation-governance-migration-boundary
  field
    missingMetadataRemainsExplicit : Bool
    missingMetadataRemainsExplicitIsTrue : missingMetadataRemainsExplicit ≡ true
    doiBearingLegacyRowsMayUseCanonicalAttributedCarrier : Bool
    doiBearingLegacyRowsMayUseCanonicalAttributedCarrierIsTrue :
      doiBearingLegacyRowsMayUseCanonicalAttributedCarrier ≡ true
    migrationCreatesProofAuthority : Bool
    migrationCreatesProofAuthorityIsFalse : migrationCreatesProofAuthority ≡ false

canonicalFormalisationGovernanceMigrationBoundary :
  FormalisationGovernanceMigrationBoundary
canonicalFormalisationGovernanceMigrationBoundary =
  formalisation-governance-migration-boundary true refl true refl false refl
