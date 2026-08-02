module DASHI.Physics.YangMills.BalabanClayGate4ROperationPrimarySourceAuditExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source authority audit for the large-field/R-operation lane.
--
-- The peer-reviewed Bałaban papers below are the imported mathematical
-- authority.  Recent viXra/AI-assisted structural manuscripts supplied during
-- the research audit are retained only as conjectural extraction guides.  They
-- cannot inhabit an imported theorem field and no missing author or DOI is
-- invented.
------------------------------------------------------------------------

record PublicationRecord : Set where
  constructor publicationRecord
  field
    author title venue year pages doi : String
    peerReviewed : Bool
    authorityLevel : ProofLevel

open PublicationRecord public

largeFieldRenormalizationPartI : PublicationRecord
largeFieldRenormalizationPartI = publicationRecord
  "Tadeusz Bałaban"
  "Large Field Renormalization I: The Basic Step of the R-Operation"
  "Communications in Mathematical Physics 122"
  "1989"
  "175-202"
  "10.1007/BF01257412"
  true
  standardImported

largeFieldRenormalizationPartII : PublicationRecord
largeFieldRenormalizationPartII = publicationRecord
  "Tadeusz Bałaban"
  "Large Field Renormalization II: Localization, Exponentiation, and Bounds for the R-Operation"
  "Communications in Mathematical Physics 122"
  "1989"
  "355-392"
  "10.1007/BF01238433"
  true
  standardImported

uniformCoercivityAuditLead : PublicationRecord
uniformCoercivityAuditLead = publicationRecord
  "author not verified in the supplied audit"
  "Uniform Coercivity, Pointwise Large-Field Suppression"
  "recent non-peer-reviewed audit manuscript"
  "2026"
  "not verified"
  "no DOI verified"
  false
  conjectural

balabanDimockStructuralAuditLead : PublicationRecord
balabanDimockStructuralAuditLead = publicationRecord
  "author not verified in the supplied audit"
  "The Bałaban-Dimock Structural Package"
  "recent non-peer-reviewed audit manuscript"
  "2026"
  "not verified"
  "no DOI verified"
  false
  conjectural

record PrimaryROperationTheoremProfile : Set₁ where
  field
    basicStepConstruction : Set
    localizationAndExponentiation : Set
    largeFieldBounds : Set

    basicStepEvidence : basicStepConstruction
    localizationEvidence : localizationAndExponentiation
    largeFieldBoundsEvidence : largeFieldBounds

open PrimaryROperationTheoremProfile public

record ROperationRepositoryDictionary : Set₁ where
  field
    sourceLargeFieldPredicate : Set
    repositoryLargeFieldPredicate : Set
    predicateIdentification :
      sourceLargeFieldPredicate → repositoryLargeFieldPredicate

    sourceBadComponent : Set
    repositoryBadPolymer : Set
    componentIdentification :
      sourceBadComponent → repositoryBadPolymer

    sourceConditionalMeasure : Set
    repositoryConditionalMeasure : Set
    conditionalMeasureIdentification :
      sourceConditionalMeasure → repositoryConditionalMeasure

    sourcePenalty sourceOscillation sourceDecay sourceScaleRecursion : Set
    penaltyIdentification : sourcePenalty
    oscillationIdentification : sourceOscillation
    decayIdentification : sourceDecay
    scaleRecursionIdentification : sourceScaleRecursion

open ROperationRepositoryDictionary public

balabanROperationPartILevel : ProofLevel
balabanROperationPartILevel = standardImported

balabanROperationPartIILevel : ProofLevel
balabanROperationPartIILevel = standardImported

recentStructuralAuditAuthorityLevel : ProofLevel
recentStructuralAuditAuthorityLevel = conjectural

physicalROperationDictionaryInputsLevel : ProofLevel
physicalROperationDictionaryInputsLevel = conditional
