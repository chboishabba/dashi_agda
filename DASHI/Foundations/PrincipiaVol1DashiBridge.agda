module DASHI.Foundations.PrincipiaVol1DashiBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.FormalLensLawCore as LensLaw
import DASHI.Core.FormalLensVocabularyCore as LensVocabulary
import DASHI.Core.FormalStructureLawCore as Structure
import DASHI.Core.RelationAlgebraCore as RelationAlgebra
import DASHI.Foundations.PMApparentVariableDescriptionBoundary as ApparentVariable
import DASHI.Foundations.PMCardinalProlegomenaCore as Cardinal
import DASHI.Foundations.PMDeductionBridge as Deduction
import DASHI.Foundations.PMVol1ChapterIndexCore as ChapterIndex

------------------------------------------------------------------------
-- Principia Mathematica Volume I / Dashi comparison bridge.
--
-- This is an inventory surface, not a PM formalization.  It records the
-- OCR-derived Volume I chapter bands and the local Dashi substrate that can
-- receive them.  It deliberately does not claim that the numbered PM
-- propositions are formalized in this repository.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  0
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- OCR comparison facts.

record PMVol1OCRFacts : Set where
  constructor mkPMVol1OCRFacts
  field
    sourcePdf :
      String

    pageCount :
      Nat

    extractedTextLines :
      Nat

    detectedNumberedRows :
      Nat

    propositionKeywordHits :
      Nat

    relationKeywordHits :
      Nat

    classKeywordHits :
      Nat

    cardinalKeywordHits :
      Nat

    typeKeywordHits :
      Nat

    apparentVariableKeywordHits :
      Nat

canonicalPMVol1OCRFacts : PMVol1OCRFacts
canonicalPMVol1OCRFacts =
  mkPMVol1OCRFacts
    "Principia_Mathematica_vol1.pdf"
    719
    52986
    439
    2076
    1099
    637
    279
    383
    78

------------------------------------------------------------------------
-- Volume I bands.

data PMVol1Band : Set where
  introductionBand :
    PMVol1Band

  logicalTypesBand :
    PMVol1Band

  deductionBand :
    PMVol1Band

  apparentVariablesBand :
    PMVol1Band

  classesRelationsBand :
    PMVol1Band

  relationLogicBand :
    PMVol1Band

  productsSumsClassesBand :
    PMVol1Band

  unitClassesCouplesBand :
    PMVol1Band

  subclassesSubrelationsBand :
    PMVol1Band

  oneManyManyOneBand :
    PMVol1Band

  selectionsBand :
    PMVol1Band

  inductiveRelationsBand :
    PMVol1Band

  appendixDeductionBand :
    PMVol1Band

  appendixInductionBand :
    PMVol1Band

canonicalPMVol1Bands : List PMVol1Band
canonicalPMVol1Bands =
  introductionBand
  ∷ logicalTypesBand
  ∷ deductionBand
  ∷ apparentVariablesBand
  ∷ classesRelationsBand
  ∷ relationLogicBand
  ∷ productsSumsClassesBand
  ∷ unitClassesCouplesBand
  ∷ subclassesSubrelationsBand
  ∷ oneManyManyOneBand
  ∷ selectionsBand
  ∷ inductiveRelationsBand
  ∷ appendixDeductionBand
  ∷ appendixInductionBand
  ∷ []

canonicalPMVol1BandCount : Nat
canonicalPMVol1BandCount =
  listCount canonicalPMVol1Bands

------------------------------------------------------------------------
-- Local coverage classification.

data PMCoverageStatus : Set where
  dashiSubstratePresent :
    PMCoverageStatus

  dashiPartialSurface :
    PMCoverageStatus

  pmSpecificFormalizationMissing :
    PMCoverageStatus

  externalAgdaStdlibSubstrate :
    PMCoverageStatus

bandCoverageStatus :
  PMVol1Band →
  PMCoverageStatus
bandCoverageStatus introductionBand =
  pmSpecificFormalizationMissing
bandCoverageStatus logicalTypesBand =
  dashiPartialSurface
bandCoverageStatus deductionBand =
  externalAgdaStdlibSubstrate
bandCoverageStatus apparentVariablesBand =
  pmSpecificFormalizationMissing
bandCoverageStatus classesRelationsBand =
  dashiSubstratePresent
bandCoverageStatus relationLogicBand =
  dashiPartialSurface
bandCoverageStatus productsSumsClassesBand =
  dashiSubstratePresent
bandCoverageStatus unitClassesCouplesBand =
  dashiPartialSurface
bandCoverageStatus subclassesSubrelationsBand =
  dashiPartialSurface
bandCoverageStatus oneManyManyOneBand =
  dashiPartialSurface
bandCoverageStatus selectionsBand =
  pmSpecificFormalizationMissing
bandCoverageStatus inductiveRelationsBand =
  dashiPartialSurface
bandCoverageStatus appendixDeductionBand =
  externalAgdaStdlibSubstrate
bandCoverageStatus appendixInductionBand =
  dashiPartialSurface

bandStructureKinds :
  PMVol1Band →
  List Structure.FormalStructureLawKind
bandStructureKinds introductionBand =
  []
bandStructureKinds logicalTypesBand =
  Structure.equivalenceRelationLawKind
  ∷ Structure.quotientFiberProjectionLawKind
  ∷ []
bandStructureKinds deductionBand =
  []
bandStructureKinds apparentVariablesBand =
  Structure.canonicalEncodingLawKind
  ∷ []
bandStructureKinds classesRelationsBand =
  Structure.equivalenceRelationLawKind
  ∷ Structure.quotientFiberProjectionLawKind
  ∷ Structure.coordinateProjectionLawKind
  ∷ []
bandStructureKinds relationLogicBand =
  Structure.equivalenceRelationLawKind
  ∷ Structure.quotientFiberProjectionLawKind
  ∷ []
bandStructureKinds productsSumsClassesBand =
  Structure.vectorProductLawKind
  ∷ Structure.coordinateProjectionLawKind
  ∷ []
bandStructureKinds unitClassesCouplesBand =
  Structure.vectorProductLawKind
  ∷ Structure.equivalenceRelationLawKind
  ∷ []
bandStructureKinds subclassesSubrelationsBand =
  Structure.quotientFiberProjectionLawKind
  ∷ Structure.coordinateProjectionLawKind
  ∷ []
bandStructureKinds oneManyManyOneBand =
  Structure.coordinateProjectionLawKind
  ∷ Structure.quotientFiberProjectionLawKind
  ∷ []
bandStructureKinds selectionsBand =
  Structure.coordinateProjectionLawKind
  ∷ []
bandStructureKinds inductiveRelationsBand =
  Structure.equivalenceRelationLawKind
  ∷ Structure.quotientFiberProjectionLawKind
  ∷ []
bandStructureKinds appendixDeductionBand =
  []
bandStructureKinds appendixInductionBand =
  Structure.equivalenceRelationLawKind
  ∷ []

bandLensKinds :
  PMVol1Band →
  List LensVocabulary.FormalLensKind
bandLensKinds introductionBand =
  LensVocabulary.Logic
  ∷ LensVocabulary.TypeTheory
  ∷ []
bandLensKinds logicalTypesBand =
  LensVocabulary.TypeTheory
  ∷ LensVocabulary.Logic
  ∷ []
bandLensKinds deductionBand =
  LensVocabulary.Logic
  ∷ LensVocabulary.Proof
  ∷ []
bandLensKinds apparentVariablesBand =
  LensVocabulary.Logic
  ∷ LensVocabulary.TypeTheory
  ∷ LensVocabulary.Functional
  ∷ []
bandLensKinds classesRelationsBand =
  LensVocabulary.Order
  ∷ LensVocabulary.Lattice
  ∷ LensVocabulary.Category
  ∷ []
bandLensKinds relationLogicBand =
  LensVocabulary.Category
  ∷ LensVocabulary.Order
  ∷ LensVocabulary.Graph
  ∷ []
bandLensKinds productsSumsClassesBand =
  LensVocabulary.Algebra
  ∷ LensVocabulary.Category
  ∷ []
bandLensKinds unitClassesCouplesBand =
  LensVocabulary.Number
  ∷ LensVocabulary.Algebra
  ∷ []
bandLensKinds subclassesSubrelationsBand =
  LensVocabulary.Order
  ∷ LensVocabulary.Lattice
  ∷ []
bandLensKinds oneManyManyOneBand =
  LensVocabulary.Functional
  ∷ LensVocabulary.Category
  ∷ []
bandLensKinds selectionsBand =
  LensVocabulary.Functional
  ∷ LensVocabulary.DecisionTheory
  ∷ []
bandLensKinds inductiveRelationsBand =
  LensVocabulary.Order
  ∷ LensVocabulary.Graph
  ∷ []
bandLensKinds appendixDeductionBand =
  LensVocabulary.Logic
  ∷ LensVocabulary.Proof
  ∷ []
bandLensKinds appendixInductionBand =
  LensVocabulary.Number
  ∷ LensVocabulary.Order
  ∷ []

------------------------------------------------------------------------
-- Authority and proposition-corpus boundary.

record PMVol1BridgeAuthorityBoundary : Set where
  constructor mkPMVol1BridgeAuthorityBoundary
  field
    directPMFormalizationAuthority :
      Bool

    exactNotationAuthority :
      Bool

    propositionCorpusAuthority :
      Bool

    ramifiedTypeTheoryAuthority :
      Bool

    cardinalArithmeticAuthority :
      Bool

    directPMFormalizationAuthorityIsFalse :
      directPMFormalizationAuthority ≡ false

    exactNotationAuthorityIsFalse :
      exactNotationAuthority ≡ false

    propositionCorpusAuthorityIsFalse :
      propositionCorpusAuthority ≡ false

    ramifiedTypeTheoryAuthorityIsFalse :
      ramifiedTypeTheoryAuthority ≡ false

    cardinalArithmeticAuthorityIsFalse :
      cardinalArithmeticAuthority ≡ false

canonicalPMVol1BridgeAuthorityBoundary :
  PMVol1BridgeAuthorityBoundary
canonicalPMVol1BridgeAuthorityBoundary =
  mkPMVol1BridgeAuthorityBoundary
    false
    false
    false
    false
    false
    refl
    refl
    refl
    refl
    refl

record PMVol1DashiBridge : Set₁ where
  constructor mkPMVol1DashiBridge
  field
    ocrFacts :
      PMVol1OCRFacts

    volumeBands :
      List PMVol1Band

    volumeBandCount :
      Nat

    volumeBandCountIsCanonical :
      volumeBandCount ≡ listCount volumeBands

    localStructureSurface :
      Structure.FormalStructureLawSurface

    relationLawStyle :
      List LensVocabulary.FormalLensKind

    relationLawStyleIsCanonical :
      relationLawStyle ≡
      LensLaw.canonicalGraphStyleVocabularyKinds

    relationAlgebraSurfaceKinds :
      List RelationAlgebra.RelationAlgebraSurfaceKind

    relationAlgebraSurfaceKindCount :
      Nat

    relationAlgebraSurfaceKindCountIsCanonical :
      relationAlgebraSurfaceKindCount ≡
      RelationAlgebra.listCount relationAlgebraSurfaceKinds

    productVectorLawStyle :
      List LensVocabulary.FormalLensKind

    productVectorLawStyleIsCanonical :
      productVectorLawStyle ≡
      LensLaw.canonicalProductVectorStyleVocabularyKinds

    chapterRows :
      List ChapterIndex.PMVol1ChapterRow

    chapterRowCount :
      Nat

    chapterRowCountIsCanonical :
      chapterRowCount ≡ ChapterIndex.listCount chapterRows

    deductionAuthorityBoundary :
      Deduction.PMDeductionAuthorityBoundary

    descriptionAuthorityBoundary :
      ApparentVariable.DescriptionAuthorityBoundary

    cardinalAuthorityBoundary :
      Cardinal.CardinalArithmeticAuthorityBoundary

    authorityBoundary :
      PMVol1BridgeAuthorityBoundary

    candidateInventoryOnly :
      Bool

    candidateInventoryOnlyIsTrue :
      candidateInventoryOnly ≡ true

canonicalPMVol1DashiBridge :
  PMVol1DashiBridge
canonicalPMVol1DashiBridge =
  mkPMVol1DashiBridge
    canonicalPMVol1OCRFacts
    canonicalPMVol1Bands
    canonicalPMVol1BandCount
    refl
    Structure.canonicalFormalStructureLawSurface
    LensLaw.canonicalGraphStyleVocabularyKinds
    refl
    RelationAlgebra.canonicalRelationAlgebraSurfaceKinds
    RelationAlgebra.canonicalRelationAlgebraSurfaceKindCount
    refl
    LensLaw.canonicalProductVectorStyleVocabularyKinds
    refl
    ChapterIndex.canonicalPMVol1ChapterRows
    ChapterIndex.canonicalPMVol1ChapterRowCount
    refl
    Deduction.canonicalPMDeductionAuthorityBoundary
    ApparentVariable.canonicalDescriptionAuthorityBoundary
    Cardinal.canonicalCardinalArithmeticAuthorityBoundary
    canonicalPMVol1BridgeAuthorityBoundary
    true
    refl

pmVol1BridgeDoesNotFormalizePM :
  PMVol1BridgeAuthorityBoundary.directPMFormalizationAuthority
    (PMVol1DashiBridge.authorityBoundary canonicalPMVol1DashiBridge)
  ≡
  false
pmVol1BridgeDoesNotFormalizePM =
  refl

pmVol1BridgeDoesNotPromotePropositionCorpus :
  PMVol1BridgeAuthorityBoundary.propositionCorpusAuthority
    (PMVol1DashiBridge.authorityBoundary canonicalPMVol1DashiBridge)
  ≡
  false
pmVol1BridgeDoesNotPromotePropositionCorpus =
  refl

pmVol1BridgeKeepsCardinalArithmeticOpen :
  PMVol1BridgeAuthorityBoundary.cardinalArithmeticAuthority
    (PMVol1DashiBridge.authorityBoundary canonicalPMVol1DashiBridge)
  ≡
  false
pmVol1BridgeKeepsCardinalArithmeticOpen =
  refl

pmVol1ClassesRelationsUseLocalSubstrate :
  bandCoverageStatus classesRelationsBand ≡ dashiSubstratePresent
pmVol1ClassesRelationsUseLocalSubstrate =
  refl

pmVol1SelectionsRemainMissing :
  bandCoverageStatus selectionsBand ≡ pmSpecificFormalizationMissing
pmVol1SelectionsRemainMissing =
  refl

pmVol1BandInventoryCount :
  PMVol1DashiBridge.volumeBandCount canonicalPMVol1DashiBridge
  ≡
  14
pmVol1BandInventoryCount =
  refl

pmVol1ChapterInventoryCount :
  PMVol1DashiBridge.chapterRowCount canonicalPMVol1DashiBridge
  ≡
  100
pmVol1ChapterInventoryCount =
  refl

pmVol1RelationAlgebraBoundaryStaysNonPromoting :
  RelationAlgebra.RelationAlgebraAuthorityBoundary.pmRelationCalculusAuthority
    RelationAlgebra.canonicalRelationAlgebraAuthorityBoundary
  ≡
  false
pmVol1RelationAlgebraBoundaryStaysNonPromoting =
  refl

pmVol1DeductionCorpusAuthorityStaysFalse :
  Deduction.PMDeductionAuthorityBoundary.pmPropositionCorpusAuthority
    (PMVol1DashiBridge.deductionAuthorityBoundary canonicalPMVol1DashiBridge)
  ≡
  false
pmVol1DeductionCorpusAuthorityStaysFalse =
  refl

pmVol1DescriptionTotalityAuthorityStaysFalse :
  ApparentVariable.DescriptionAuthorityBoundary.descriptionTotalityAuthority
    (PMVol1DashiBridge.descriptionAuthorityBoundary canonicalPMVol1DashiBridge)
  ≡
  false
pmVol1DescriptionTotalityAuthorityStaysFalse =
  refl
