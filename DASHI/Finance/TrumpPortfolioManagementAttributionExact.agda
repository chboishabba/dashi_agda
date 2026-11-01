module DASHI.Finance.TrumpPortfolioManagementAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- ATTRIBUTED PORTFOLIO-MANAGEMENT DEFENSE
--
-- Reuters reported a Trump Organization spokesperson's statement that the
-- President's investment holdings are maintained in fully discretionary
-- accounts independently managed by third-party financial institutions, using
-- automated systems, with no Trump/family/company role in selecting, directing
-- or approving specific investments and no advance notice of trading activity.
--
-- This source pays the proposition "Reuters reports that the spokesperson made
-- this representation."  It does not independently identify the managers,
-- audit the mandates/systems, or prove absence of every communication/input.
------------------------------------------------------------------------

reutersManagementDefenseArtifact : Source.SourceArtifact
reutersManagementDefenseArtifact =
  Source.sourceArtifact
    "Reuters-2026-05-14-Trump-portfolio-management-defense"
    Source.derivedArtifact
    "https://www.reuters.com/legal/government/trump-ethics-filing-reveals-thousands-trades-tied-us-corporate-securities-2026-05-14/"
    "Reuters"

thirdPartyManagementDefense : Atlas.TradeEvidenceClaim
thirdPartyManagementDefense =
  Atlas.tradeEvidenceClaim
    "TrumpOrg-third-party-management-defense-2026-05-14"
    "Trump Organization spokesperson"
    "Donald J. Trump's reported stock/bond investment accounts"
    Atlas.financialDisclosureClaim
    "statement reported 2026-05-14"
    "2026-05-14"
    "Reuters reports that a Trump Organization spokesperson said President Trump's investment holdings were in fully discretionary accounts independently managed by third-party financial institutions with sole authority over investment decisions, that trades were executed/rebalanced through automated systems, and that Trump, his family and the Trump Organization had no role or advance notice regarding specific investments."
    Atlas.independentSynthesisSupport
    (Atlas.sourceCitation
      "Reuters"
      "Trump ethics filing reveals thousands of trades tied to US corporate securities"
      "2026-05-14"
      "no DOI"
      "https://www.reuters.com/legal/government/trump-ethics-filing-reveals-thousands-trades-tied-us-corporate-securities-2026-05-14/"
      Atlas.independentReporting)
    reutersManagementDefenseArtifact
    "Pays Reuters' attribution of the Trump Organization statement. It does not identify the managers, executed mandates, automated model rules, or independently prove zero input/advance notice."
    false true false false

------------------------------------------------------------------------
-- Attribution boundaries.
------------------------------------------------------------------------

data SpokespersonStatementAutomaticallyProvesManagerIdentity : Set where
data SpokespersonStatementAutomaticallyProvesNoInput : Set where
data AutomatedSystemClaimAutomaticallyProvesNoHumanDiscretion : Set where
data IndependentManagementClaimAutomaticallyResolvesConflictQuestion : Set where

statementDoesNotIdentifyManagers :
  SpokespersonStatementAutomaticallyProvesManagerIdentity → ⊥
statementDoesNotIdentifyManagers ()

statementDoesNotIndependentlyProveNoInput :
  SpokespersonStatementAutomaticallyProvesNoInput → ⊥
statementDoesNotIndependentlyProveNoInput ()

automationClaimDoesNotProveNoHumanDiscretion :
  AutomatedSystemClaimAutomaticallyProvesNoHumanDiscretion → ⊥
automationClaimDoesNotProveNoHumanDiscretion ()

managementClaimDoesNotResolveConflictQuestion :
  IndependentManagementClaimAutomaticallyResolvesConflictQuestion → ⊥
managementClaimDoesNotResolveConflictQuestion ()

record PortfolioManagementAttributionBoundary : Set where
  constructor portfolio-management-attribution-boundary
  field
    attributedThirdPartyManagementStatementPaid : Bool
    attributedAutomatedProcessStatementPaid : Bool
    namedManagerIdentityStillUnpaid : Bool
    mandateTermsStillUnpaid : Bool
    zeroInputNotIndependentlyProved : Bool
    conflictOrLegalityStillSeparate : Bool

canonicalPortfolioManagementAttributionBoundary :
  PortfolioManagementAttributionBoundary
canonicalPortfolioManagementAttributionBoundary =
  portfolio-management-attribution-boundary
    true true true true true true
