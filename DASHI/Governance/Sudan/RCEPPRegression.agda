module DASHI.Governance.Sudan.RCEPPRegression where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Foundations.StageValuationBundleAtlas as Stage
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.CouncilDelegationGraph as Council
import DASHI.Governance.ExternalLegitimacyBoundary as Legitimacy
import DASHI.Governance.GovernedArtifactCore as Governed
import DASHI.Governance.RelationalMandateFibre as MandateFibre
import DASHI.Governance.SituatedConstituency as Situated
import DASHI.Governance.TransitionResidual as Transition
import DASHI.Governance.Sudan.RCEPPInstitutionalSurface as Institutional
import DASHI.Governance.Sudan.RCEPPPromotionBoundary as PromotionBoundary
import DASHI.Governance.Sudan.RCEPPSourceBoundary as Source

------------------------------------------------------------------------
-- Aggregate regression for the governance/RCEPP tranche.
------------------------------------------------------------------------

record RCEPPGovernanceRegression : Set where
  constructor rceppGovernanceRegression
  field
    coarseMandateFibre :
      MandateFibre.CoarseTriadHypervoxelBridge

    mandateAuthorityBoundary :
      Authority.MandateAuthorityBoundary

    situatedRepresentationBoundary :
      Situated.AxisAwareRepresentationBoundary

    councilGraphBoundary :
      Council.CouncilGraphBoundary

    transitionBoundary :
      Transition.TransitionAuthorityBoundary

    externalLegitimacyBoundary :
      Legitimacy.LegitimacyBoundary

    sourceBoundary :
      Source.RCEPPSourceBoundary

    institutionalBoundary :
      Institutional.RCEPPInstitutionalInterpretationBoundary

    promotionBoundary :
      PromotionBoundary.RCEPPPromotionBoundary

    rankOneFineRoleCountIsThree :
      MandateFibre.listCount MandateFibre.canonicalMandateFineRoles ≡ 3

    rankOneHypervoxelCountIsThree :
      Hyper.siteCount 1 1 ≡ 3

    militarySubordinateToPeople :
      Council.SubordinationPath
        Council.militaryInstitution
        Council.peopleInstitution

    forceSourceRejected :
      Authority.AdmissibleAuthoritySource Authority.possessionOfForce →
      Authority.Never

    sourceDOIAbsent :
      Source.doiAssigned Source.canonicalRCEPPSourceReceipt ≡ false

    sourceLegalOperationNotClaimed :
      Source.legalOperationClaimed Source.canonicalRCEPPSourceReceipt ≡ false

    formalLegitimacyNotMinted :
      Legitimacy.sourceCreatesPopularLegitimacy
        (Legitimacy.formalReceiptLegitimacySource
          Legitimacy.localTypecheckingReceipt)
      ≡ false

    stageCompressionAuthorityFalse :
      Stage.semanticAuthorityPromoted
        Stage.canonicalTransformativeJump3To14
      ≡ false

    citationOnlyAuthorizationAbstains :
      PromotionBoundary.Promotion.authorizationFromObligations
        (PromotionBoundary.ArtifactBridge.authorityPromotionObligations
          Source.canonicalRCEPPCitationBoundary
          true
          true
          true
          true)
      ≡ Governed.abstain

canonicalRCEPPGovernanceRegression : RCEPPGovernanceRegression
canonicalRCEPPGovernanceRegression =
  rceppGovernanceRegression
    MandateFibre.canonicalCoarseTriadHypervoxelBridge
    Authority.canonicalMandateAuthorityBoundary
    Situated.canonicalAxisAwareRepresentationBoundary
    Council.canonicalCouncilGraphBoundary
    Transition.canonicalTransitionAuthorityBoundary
    Legitimacy.canonicalLegitimacyBoundary
    Source.canonicalRCEPPSourceBoundary
    Institutional.canonicalRCEPPInstitutionalInterpretationBoundary
    PromotionBoundary.canonicalRCEPPPromotionBoundary
    MandateFibre.canonicalMandateFineRoleCountIsThree
    MandateFibre.rankOneDepthOneHasThreeSites
    Council.militaryToPeoplePath
    Authority.possessionOfForceRejected
    refl
    refl
    refl
    Transition.stageCompressionDoesNotPromoteAuthority
    PromotionBoundary.rceppCitationOnlyAuthorizationAbstains

canonicalRCEPPGovernanceReceipts :
  List GenericReceipt.GenericReceipt
canonicalRCEPPGovernanceReceipts =
  MandateFibre.canonicalRelationalMandateFibreReceipt
  ∷ Authority.canonicalAuthorityMandateCoreReceipt
  ∷ Situated.canonicalSituatedConstituencyReceipt
  ∷ Council.canonicalCouncilDelegationGraphReceipt
  ∷ Transition.canonicalTransitionResidualReceipt
  ∷ Legitimacy.canonicalExternalLegitimacyBoundaryReceipt
  ∷ Source.canonicalRCEPPSourceGenericReceipt
  ∷ Institutional.canonicalRCEPPInstitutionalSurfaceReceipt
  ∷ PromotionBoundary.canonicalRCEPPPromotionBoundaryReceipt
  ∷ []

canonicalRCEPPGovernanceReceiptCount : Nat
canonicalRCEPPGovernanceReceiptCount =
  GenericReceipt.receiptCount canonicalRCEPPGovernanceReceipts

canonicalRCEPPGovernanceReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting canonicalRCEPPGovernanceReceipts
canonicalRCEPPGovernanceReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalRCEPPGovernanceReceipts
