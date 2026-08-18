module DASHI.Ontology.LeanWikidataParentingPullbackBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.LeanWikidataFullSourceManifest
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
open import DASHI.Ontology.ProgenitorParentHyperfabric

------------------------------------------------------------------------
-- Exact source pins from the latest supplied Aristotle/JMD archive.
--
-- This is deliberately a source-faithful bridge: theorem names below are
-- statements actually present in the pinned Lean files.  DASHI refinements are
-- kept in a separate section and are not attributed back to the Lean source.
------------------------------------------------------------------------

parentingLatestSource : LeanSourceModule
parentingLatestSource = leanSourceModule
  "RequestProject.Parenting"
  "507219cc7af1354f2d73a44df935da3a24b2bab25e3e771ace24ecd0af051fa0"
  dataModel
  (derivationFibreAnchor ∷ contextualClaimAnchor ∷ [])

parentingExamplesLatestSource : LeanSourceModule
parentingExamplesLatestSource = leanSourceModule
  "RequestProject.ParentingExamples"
  "983b8f88c4c56c621e72f83c1f0ae78dce2190fbe028514c3680262de011e4fa"
  dataModel
  (derivationFibreAnchor ∷ contextualClaimAnchor ∷ [])

parentingDiagnosticsLatestSource : LeanSourceModule
parentingDiagnosticsLatestSource = leanSourceModule
  "RequestProject.ParentingDiagnostics"
  "d7834166c32cffdbbc8acada5dfcd2b14c15b8422604344cd2e832be5a30bdc0"
  propertyConstraints
  (derivationFibreAnchor ∷ repairReviewAnchor ∷ [])

pullbackComparisonLatestSource : LeanSourceModule
pullbackComparisonLatestSource = leanSourceModule
  "RequestProject.PullbackComparison"
  "9f9cbe4ab08dd4e7ea850c98e7d012ea7776d0919f77ee30ab888642cf97b855"
  classHierarchy
  (derivationFibreAnchor ∷ contextualClaimAnchor ∷ [])

pullbackRetractionLatestSource : LeanSourceModule
pullbackRetractionLatestSource = leanSourceModule
  "RequestProject.PullbackRetraction"
  "02528e58d642a49c953c5157c8ce4d523d458a6814ee3cf778ad5f9d9bff29fd"
  classHierarchy
  (derivationFibreAnchor ∷ identityTransport ∷ [])

metaFrobeniusLatestSource : LeanSourceModule
metaFrobeniusLatestSource = leanSourceModule
  "RequestProject.MetaFrobenius"
  "d8fa4791ca793d5bb773f0de3ad529ba9bb1ed545b5b643832cbaff550770f7a"
  classHierarchy
  (derivationFibreAnchor ∷ contextualClaimAnchor ∷ [])

categoryOntologiesLatestSource : LeanSourceModule
categoryOntologiesLatestSource = leanSourceModule
  "RequestProject.CategoryOfOntologies"
  "9e2570e5f8fe535b83a0d6bce8a7ca2bde735218d12bd1340eba50dab4ca272c"
  classHierarchy
  (derivationFibreAnchor ∷ contextualClaimAnchor ∷ [])

cubicalTypesLatestSource : LeanSourceModule
cubicalTypesLatestSource = leanSourceModule
  "RequestProject.CubicalTypes"
  "790f6a3f52d4fdd46c3952fb5eaef90c32ec92857c2c54ad634ec6ef5638e652"
  classHierarchy
  (derivationFibreAnchor ∷ contextualClaimAnchor ∷ [])

latestParentPullbackSources : List LeanSourceModule
latestParentPullbackSources =
  parentingLatestSource ∷ parentingExamplesLatestSource ∷
  parentingDiagnosticsLatestSource ∷ pullbackComparisonLatestSource ∷
  pullbackRetractionLatestSource ∷ metaFrobeniusLatestSource ∷
  categoryOntologiesLatestSource ∷ cubicalTypesLatestSource ∷ []

------------------------------------------------------------------------
-- Imported theorem contracts: these are the actual Lean statements we consume.
------------------------------------------------------------------------

jmdParentReachabilityExact : LeanTheoremContract
jmdParentReachabilityExact = leanTheoremContract parentingLatestSource
  "Wikidata.ParentingKB.descendsFromB_iff"
  "executable broad parent descent exactly decides reflexive-transitive parent closure"
  checkerExactness

jmdGeneticReachabilityExact : LeanTheoremContract
jmdGeneticReachabilityExact = leanTheoremContract parentingLatestSource
  "Wikidata.ParentingKB.geneticDescendsFromB_iff"
  "executable genetic descent exactly decides reflexive-transitive genetic-parent closure"
  checkerExactness

jmdGeneticBoundUnderTwoSlotProfile : LeanTheoremContract
jmdGeneticBoundUnderTwoSlotProfile = leanTheoremContract parentingLatestSource
  "Wikidata.ParentingKB.card_geneticParentsF_le_two"
  "at most two genetic parents under geneticSlotsTyped and singleGeneticParents"
  structuralTheorem

jmdClassicalKinshipConservative : LeanTheoremContract
jmdClassicalKinshipConservative = leanTheoremContract parentingLatestSource
  "Wikidata.FKB.pValid_toParentingKB"
  "validated classical P22/P25 kinship embeds into the parenting layer"
  preservationTheorem

jmdFourRecordedParents : LeanTheoremContract
jmdFourRecordedParents = leanTheoremContract parentingExamplesLatestSource
  "Wikidata.ParentingKB.rainbow_four_parents"
  "worked parenting KB has four recorded parents"
  semanticExactness

jmdAdoptionSeparatesLegalGenetic : LeanTheoremContract
jmdAdoptionSeparatesLegalGenetic = leanTheoremContract parentingExamplesLatestSource
  "Wikidata.ParentingKB.adoption_legal_disjoint_genetic"
  "worked adoption example separates legal and genetic parent sets"
  negativeConstraintTheorem

jmdSurrogacySeparatesBirthGenetic : LeanTheoremContract
jmdSurrogacySeparatesBirthGenetic = leanTheoremContract parentingExamplesLatestSource
  "Wikidata.ParentingKB.surrogacy_birth_not_genetic"
  "worked gestational-surrogacy example separates birth/gestation from genetic parenthood"
  negativeConstraintTheorem

jmdParentDiagnosticsExact : LeanTheoremContract
jmdParentDiagnosticsExact = leanTheoremContract parentingDiagnosticsLatestSource
  "Wikidata.ParentingKB.report_eq_nil_iff_pValid"
  "parenting diagnostic report is empty exactly when the parenting KB is valid"
  diagnosticExactness

jmdRetractsStableUnderBaseChange : LeanTheoremContract
jmdRetractsStableUnderBaseChange = leanTheoremContract pullbackRetractionLatestSource
  "Wikidata.Ontology.Retract.baseChange"
  "retracts over a reference ontology remain retracts after pullback/base change"
  structuralTheorem

jmdBaseChangeSubclassConservative : LeanTheoremContract
jmdBaseChangeSubclassConservative = leanTheoremContract pullbackRetractionLatestSource
  "Wikidata.Ontology.Retract.baseChange_subclassOf_iff"
  "base-changed retract reflects and preserves subclass facts"
  preservationTheorem

jmdBaseChangeInstanceConservative : LeanTheoremContract
jmdBaseChangeInstanceConservative = leanTheoremContract pullbackRetractionLatestSource
  "Wikidata.Ontology.Retract.baseChange_instanceOf_iff"
  "base-changed retract reflects and preserves instance facts"
  preservationTheorem

jmdMetaOntologyIsPullback : LeanTheoremContract
jmdMetaOntologyIsPullback = leanTheoremContract metaFrobeniusLatestSource
  "Wikidata.KB.metaLift_isPullback"
  "meta copy is the pullback of reduction along identity; comparison and first projection are inverse"
  structuralTheorem

latestParentPullbackTheoremContracts : List LeanTheoremContract
latestParentPullbackTheoremContracts =
  jmdParentReachabilityExact ∷ jmdGeneticReachabilityExact ∷
  jmdGeneticBoundUnderTwoSlotProfile ∷ jmdClassicalKinshipConservative ∷
  jmdFourRecordedParents ∷ jmdAdoptionSeparatesLegalGenetic ∷
  jmdSurrogacySeparatesBirthGenetic ∷ jmdParentDiagnosticsExact ∷
  jmdRetractsStableUnderBaseChange ∷ jmdBaseChangeSubclassConservative ∷
  jmdBaseChangeInstanceConservative ∷ jmdMetaOntologyIsPullback ∷ []

------------------------------------------------------------------------
-- Exact JMD role surface, then a DASHI refinement into orthogonal coordinates.
--
-- JMD's ParentRole is a flat tag on a recorded ParentEdge.  The functions
-- isGenetic/isLegal/isSocial are faithfully reproduced below.  The richer
-- RelationVector is a DASHI refinement and must not be read back as a theorem of
-- the Lean source.
------------------------------------------------------------------------

data JMDParentRole : Set where
  jmdBiological jmdDonor jmdSurrogate jmdAdoptive : JMDParentRole
  jmdStep jmdFoster jmdGuardian jmdGodparent : JMDParentRole

jmdIsGenetic : JMDParentRole → Bool
jmdIsGenetic jmdBiological = true
jmdIsGenetic jmdDonor = true
jmdIsGenetic _ = false

jmdIsLegal : JMDParentRole → Bool
jmdIsLegal jmdBiological = true
jmdIsLegal jmdAdoptive = true
jmdIsLegal jmdGuardian = true
jmdIsLegal _ = false

jmdIsSocial : JMDParentRole → Bool
jmdIsSocial jmdBiological = true
jmdIsSocial jmdAdoptive = true
jmdIsSocial jmdStep = true
jmdIsSocial jmdFoster = true
jmdIsSocial jmdGuardian = true
jmdIsSocial _ = false

-- Every constructor is a tag on a JMD ParentEdge, so recorded-parenthood is a
-- separate surface coordinate from DASHI genealogical/social parenthood.
jmdRecordedAsParent : JMDParentRole → Bool
jmdRecordedAsParent _ = true

refineJMDRole : JMDParentRole → RelationVector
refineJMDRole jmdBiological =
  relationVector true true true false false true true true true true true true
refineJMDRole jmdDonor =
  relationVector true true true false false false false false false false false false
refineJMDRole jmdSurrogate =
  relationVector false false false false true false false false false false true true
refineJMDRole jmdAdoptive =
  relationVector false false false false false true true true true true true true
refineJMDRole jmdStep =
  relationVector false false false false false false false false true true true true
refineJMDRole jmdFoster =
  relationVector false false false false false false false false true true true true
refineJMDRole jmdGuardian =
  relationVector false false false false false false false true true true true true
refineJMDRole jmdGodparent =
  relationVector false false false false false false false false false false true true

jmdGeneticPredicatePreserved :
  (role : JMDParentRole) →
  jmdIsGenetic role ≡ geneticContributor (refineJMDRole role)
jmdGeneticPredicatePreserved jmdBiological = refl
jmdGeneticPredicatePreserved jmdDonor = refl
jmdGeneticPredicatePreserved jmdSurrogate = refl
jmdGeneticPredicatePreserved jmdAdoptive = refl
jmdGeneticPredicatePreserved jmdStep = refl
jmdGeneticPredicatePreserved jmdFoster = refl
jmdGeneticPredicatePreserved jmdGuardian = refl
jmdGeneticPredicatePreserved jmdGodparent = refl

jmdLegalPredicatePreserved :
  (role : JMDParentRole) →
  jmdIsLegal role ≡ legalParent (refineJMDRole role)
jmdLegalPredicatePreserved jmdBiological = refl
jmdLegalPredicatePreserved jmdDonor = refl
jmdLegalPredicatePreserved jmdSurrogate = refl
jmdLegalPredicatePreserved jmdAdoptive = refl
jmdLegalPredicatePreserved jmdStep = refl
jmdLegalPredicatePreserved jmdFoster = refl
jmdLegalPredicatePreserved jmdGuardian = refl
jmdLegalPredicatePreserved jmdGodparent = refl

jmdSocialPredicatePreserved :
  (role : JMDParentRole) →
  jmdIsSocial role ≡ socialParent (refineJMDRole role)
jmdSocialPredicatePreserved jmdBiological = refl
jmdSocialPredicatePreserved jmdDonor = refl
jmdSocialPredicatePreserved jmdSurrogate = refl
jmdSocialPredicatePreserved jmdAdoptive = refl
jmdSocialPredicatePreserved jmdStep = refl
jmdSocialPredicatePreserved jmdFoster = refl
jmdSocialPredicatePreserved jmdGuardian = refl
jmdSocialPredicatePreserved jmdGodparent = refl

-- The flat recorded-parent tag does not recover the richer parent semantics.
-- Donor and adoptive roles are both recorded ParentEdges in JMD, while their
-- refined genealogical-parent coordinates differ.
jmdRecordedParentProjectionIsLossy :
  jmdRecordedAsParent jmdDonor ≡ jmdRecordedAsParent jmdAdoptive
  × genealogicalParent (refineJMDRole jmdDonor) ≡ false
  × genealogicalParent (refineJMDRole jmdAdoptive) ≡ true
jmdRecordedParentProjectionIsLossy = refl , (refl , refl)
