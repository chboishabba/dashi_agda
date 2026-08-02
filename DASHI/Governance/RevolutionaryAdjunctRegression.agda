module DASHI.Governance.RevolutionaryAdjunctRegression where

open import Agda.Primitive using (Setω)
open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.ComparativeCrisisClimateAtlas as Comparative
import DASHI.Governance.RevolutionaryPracticeBraid as Practice
import DASHI.Governance.RevolutionarySourceAtlas as Source
import DASHI.Governance.TraumaMemorySublationBoundary as Trauma
import DASHI.Governance.Sudan.RCEPPRegression as RCEPP

------------------------------------------------------------------------
-- Aggregate regression for the revolutionary-practice adjunct.
------------------------------------------------------------------------

record RevolutionaryAdjunctRegression : Setω where
  constructor revolutionaryAdjunctRegression
  field
    sourceAtlasBoundary : Source.RevolutionarySourceAtlasBoundary
    practiceBraidBoundary : Practice.RevolutionaryPracticeBraidBoundary
    traumaSublationBoundary : Trauma.TraumaMemorySublationBoundary
    comparativeAtlasBoundary : Comparative.ComparativeCrisisClimateAtlasBoundary
    rceppGovernanceRegression : RCEPP.RCEPPGovernanceRegression

    relationshipCategoryDoesNotCreateEntitlement :
      Practice.roleCategoryAloneCreatesEntitlement
        Practice.canonicalRelationalFreedomSurface
        ≡ false

    informalStructureDoesNotImplyEquality :
      Practice.informalStructureImpliesEquality
        Practice.canonicalRelationalFreedomSurface
        ≡ false

    priorInjuryDoesNotAuthoriseCivilianHarm :
      Trauma.priorInjuryAuthorisesCivilianHarm
        Trauma.canonicalPriorInjuryAuthorityBoundary
        ≡ false

    selectedOriginDoesNotCloseCause :
      Trauma.selectedOriginIsCompleteCause
        Trauma.iranNineteenFiftyThreeFrame
        ≡ false

    pflpObjectiveDoesNotLegitimateEveryTactic :
      Comparative.liberatoryObjectiveAutomaticallyLegitimatesEveryTactic
        Comparative.pflpPracticeAssessment
        ≡ false

    climateDoesNotActAsSoleWarCause :
      Comparative.climatePressureAloneCausesWar
        Comparative.canonicalClimateConflictBoundary
        ≡ false

    globalAttentionDoesNotMeasureSuffering :
      Comparative.sufferingScaleEqualsAttention
        Comparative.canonicalGlobalAttentionResidual
        ≡ false

    formalAtlasDoesNotPromotePoliticalAuthority :
      Comparative.formalAtlasCreatesPoliticalAuthority
        Comparative.canonicalComparativeCrisisClimateAtlasSurface
        ≡ false

open RevolutionaryAdjunctRegression public

canonicalRevolutionaryAdjunctRegression : RevolutionaryAdjunctRegression
canonicalRevolutionaryAdjunctRegression =
  revolutionaryAdjunctRegression
    Source.canonicalRevolutionarySourceAtlasBoundary
    Practice.canonicalRevolutionaryPracticeBraidBoundary
    Trauma.canonicalTraumaMemorySublationBoundary
    Comparative.canonicalComparativeCrisisClimateAtlasBoundary
    RCEPP.canonicalRCEPPGovernanceRegression
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalRevolutionaryAdjunctReceipts :
  List GenericReceipt.GenericReceipt
canonicalRevolutionaryAdjunctReceipts =
  Source.canonicalRevolutionarySourceAtlasReceipt
  ∷ Practice.canonicalRevolutionaryPracticeBraidReceipt
  ∷ Trauma.canonicalTraumaMemorySublationReceipt
  ∷ Comparative.canonicalComparativeCrisisClimateAtlasReceipt
  ∷ []

canonicalRevolutionaryAdjunctReceiptCount : Nat
canonicalRevolutionaryAdjunctReceiptCount =
  GenericReceipt.receiptCount canonicalRevolutionaryAdjunctReceipts

canonicalRevolutionaryAdjunctReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting canonicalRevolutionaryAdjunctReceipts
canonicalRevolutionaryAdjunctReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalRevolutionaryAdjunctReceipts
