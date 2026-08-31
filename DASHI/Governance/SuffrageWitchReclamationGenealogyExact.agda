module DASHI.Governance.SuffrageWitchReclamationGenealogyExact where

------------------------------------------------------------------------
-- SUFFRAGE / WITCH-PERSECUTION MEMORY / ALTERNATIVE-SPIRITUALITY GENEALOGY
--
-- Purpose: represent historically evidenced relations without collapsing them
-- into an unbroken practitioner lineage.  Relation kind and evidence strength
-- are independent axes.
--
-- Calibrating sources:
-- * Matilda Joslyn Gage, Woman, Church and State (1893), especially the chapter
--   "Witchcraft"; primary evidence that a major suffrage-era feminist writer
--   reinterpreted witch persecution within a critique of church/state power.
-- * Ann Braude, Radical Spirits, 2nd ed. (Indiana University Press, 2001),
--   DOI 10.2307/j.ctv11hpthg; scholarly synthesis supporting substantial overlap
--   between nineteenth-century Spiritualism and the women's-rights movement.
-- * Ronald Hutton, The Triumph of the Moon (Oxford University Press, 1999),
--   DOI 10.1093/acprof:oso/9780198207443.001.0001; historical synthesis of the
--   cultural antecedents and emergence of modern pagan witchcraft/Wicca.
-- * Starhawk, The Spiral Dance (Harper & Row, 1979), ISBN 9780060675356;
--   primary modern pagan/feminist source, not evidence of early-modern lineage.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Core.TrinhSubjectInMakingNoncollapseExact as Trinh
import DASHI.Core.IrigarayLabialRelationalCarrierExact as Irigaray
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.WitchTrialEvidenceSubjectAttributionExact as WitchTrial

------------------------------------------------------------------------
-- Historical nodes are positions in a comparison graph, not claims that every
-- person in a period occupied the corresponding identity.
------------------------------------------------------------------------

data HistoricalNode : Set where
  earlyModernWitchPersecution
  suffrageEraWitchPersecutionCritique
  spiritualistWomenReligiousAuthority
  modernPaganWitchcraftEmergence
  feministWitchReclamation
  : HistoricalNode

data GenealogyRelationKind : Set where
  archivalMemory
  politicalReinterpretation
  movementOverlap
  culturalAntecedent
  symbolicReclamation
  institutionalContinuity
  practitionerLineage
  : GenealogyRelationKind

data GenealogyEvidenceStrength : Set where
  primarySourceWitness
  scholarlySynthesis
  candidateNeighbourhood
  unsupportedForPromotion
  : GenealogyEvidenceStrength

record GenealogySource : Set where
  constructor genealogy-source
  field
    author : String
    title : String
    identifier : String
    boundedRole : String

open GenealogySource public

gageSource : GenealogySource
gageSource = genealogy-source
  "Matilda Joslyn Gage"
  "Woman, Church and State"
  "1893; no DOI asserted"
  "primary evidence of suffrage-era feminist reinterpretation of witch persecution and church/state subordination; not a neutral modern demographic history of witch trials"

braudeSource : GenealogySource
braudeSource = genealogy-source
  "Ann Braude"
  "Radical Spirits: Spiritualism and Women's Rights in Nineteenth-Century America, Second Edition"
  "DOI 10.2307/j.ctv11hpthg"
  "scholarly synthesis supporting substantial historical overlap between Spiritualism and the women's-rights movement"

huttonSource : GenealogySource
huttonSource = genealogy-source
  "Ronald Hutton"
  "The Triumph of the Moon: A History of Modern Pagan Witchcraft"
  "DOI 10.1093/acprof:oso/9780198207443.001.0001"
  "historical synthesis of cultural antecedents and emergence of modern pagan witchcraft; does not establish an unbroken early-modern Wiccan lineage"

starhawkSource : GenealogySource
starhawkSource = genealogy-source
  "Starhawk"
  "The Spiral Dance: A Rebirth of the Ancient Religion of the Great Goddess"
  "Harper & Row 1979; ISBN 9780060675356"
  "primary modern feminist-pagan text and evidence of self-articulated feminist witch spirituality; not proof of ancient institutional continuity"

record TypedGenealogyEdge : Set where
  constructor typed-genealogy-edge
  field
    from : HistoricalNode
    to : HistoricalNode
    relationKind : GenealogyRelationKind
    evidenceStrength : GenealogyEvidenceStrength
    source : GenealogySource

open TypedGenealogyEdge public

------------------------------------------------------------------------
-- Canonical bounded edges.
------------------------------------------------------------------------

gageReinterpretationEdge : TypedGenealogyEdge
gageReinterpretationEdge = typed-genealogy-edge
  earlyModernWitchPersecution
  suffrageEraWitchPersecutionCritique
  politicalReinterpretation
  primarySourceWitness
  gageSource

spiritualismWomensRightsOverlapEdge : TypedGenealogyEdge
spiritualismWomensRightsOverlapEdge = typed-genealogy-edge
  suffrageEraWitchPersecutionCritique
  spiritualistWomenReligiousAuthority
  movementOverlap
  scholarlySynthesis
  braudeSource

modernPaganCulturalAntecedentEdge : TypedGenealogyEdge
modernPaganCulturalAntecedentEdge = typed-genealogy-edge
  spiritualistWomenReligiousAuthority
  modernPaganWitchcraftEmergence
  culturalAntecedent
  scholarlySynthesis
  huttonSource

feministReclamationEdge : TypedGenealogyEdge
feministReclamationEdge = typed-genealogy-edge
  modernPaganWitchcraftEmergence
  feministWitchReclamation
  symbolicReclamation
  primarySourceWitness
  starhawkSource

------------------------------------------------------------------------
-- Explicitly unsupported promotions.  These are important because a cultural
-- or symbolic genealogy can be real without practitioner or institutional
-- continuity.
------------------------------------------------------------------------

data ReinterpretationPromotesPractitionerLineage : Set where
data CulturalAntecedentPromotesInstitutionalContinuity : Set where
data ModernWiccaPromotesSalemWiccanIdentity : Set where
data SymbolicReclamationRewritesOriginalSelfIdentification : Set where

reinterpretationDoesNotPromotePractitionerLineage :
  ReinterpretationPromotesPractitionerLineage → ⊥
reinterpretationDoesNotPromotePractitionerLineage ()

culturalAntecedentDoesNotPromoteInstitutionalContinuity :
  CulturalAntecedentPromotesInstitutionalContinuity → ⊥
culturalAntecedentDoesNotPromoteInstitutionalContinuity ()

modernWiccaDoesNotPromoteSalemWiccanIdentity :
  ModernWiccaPromotesSalemWiccanIdentity → ⊥
modernWiccaDoesNotPromoteSalemWiccanIdentity ()

symbolicReclamationDoesNotRewriteOriginalSelfIdentification :
  SymbolicReclamationRewritesOriginalSelfIdentification → ⊥
symbolicReclamationDoesNotRewriteOriginalSelfIdentification ()

------------------------------------------------------------------------
-- Reversal, reclamation, and reconstitution are distinct operations.
------------------------------------------------------------------------

data ReclamationOperation : Set where
  valueReversal
  imposedCategoryReclamation
  positiveSubjectReconstitution
  : ReclamationOperation

reversal≠reclamation : valueReversal ≡ imposedCategoryReclamation → ⊥
reversal≠reclamation ()

reclamation≠reconstitution :
  imposedCategoryReclamation ≡ positiveSubjectReconstitution → ⊥
reclamation≠reconstitution ()

------------------------------------------------------------------------
-- Cross-pollination with existing feminist theorem owners.
------------------------------------------------------------------------

feministPositiveRechartingExample :
  Feminist.PositiveRecharting Feminist.inheritedChart
feministPositiveRechartingExample = Feminist.canonicalPositiveRecharting

trinhCategoryStillDoesNotRecoverFormation :
  INF.FactorsThrough Trinh.publicCategory Trinh.subjectFormation → ⊥
trinhCategoryStillDoesNotRecoverFormation =
  Trinh.publicCategoryCannotRecoverSubjectFormation

irigarayReciprocalContactRetained : Irigaray.OrientationAmbiguity
irigarayReciprocalContactRetained = Irigaray.canonicalOrientationAmbiguity

accusedWitchStillDiffersFromSelfIdentifiedWitch :
  WitchTrial.externallyAccusedWitch ≡ WitchTrial.selfIdentifiedWitch → ⊥
accusedWitchStillDiffersFromSelfIdentifiedWitch =
  WitchTrial.accusation≠selfIdentification

------------------------------------------------------------------------
-- Historical-genealogy boundary.
------------------------------------------------------------------------

record SuffrageWitchGenealogyBoundary : Set where
  constructor suffrage-witch-genealogy-boundary
  field
    suffrageCritiqueEqualsModernWicca : Bool
    spiritualismEqualsWicca : Bool
    modernWiccaIsUnbrokenSalemPractitionerLineage : Bool
    feministReclamationErasesHistoricalAccusationStatus : Bool
    culturalGenealogyCanExistWithoutInstitutionalContinuity : Bool
    politicalSelfRepresentationAndReligiousSelfFormationAreIdentical : Bool
    positiveReconstitutionIsOnlyValueReversal : Bool

canonicalSuffrageWitchGenealogyBoundary : SuffrageWitchGenealogyBoundary
canonicalSuffrageWitchGenealogyBoundary =
  suffrage-witch-genealogy-boundary
    false false false false true false false
