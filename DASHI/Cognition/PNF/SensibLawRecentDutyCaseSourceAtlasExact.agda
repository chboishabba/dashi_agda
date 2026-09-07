module DASHI.Cognition.PNF.SensibLawRecentDutyCaseSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- PRIMARY CASE-LAW SOURCE ATTRIBUTION FOR THE CURRENT DUTY LINEAGE
--
-- Court reasons are source objects.  DASHI graph compilation remains a
-- separate reconstruction unless an upstream owner identifies a proposition as
-- the court's ratio/holding with an exact locator.
------------------------------------------------------------------------

mallonlandHCA25 : Source.AttributedSource
mallonlandHCA25 =
  Source.mkNoDOISource
    "High Court of Australia; Gageler CJ, Gordon, Edelman, Steward, Gleeson, Jagot and Beech-Jones JJ"
    "Mallonland Pty Ltd v Advanta Seeds Pty Ltd [2024] HCA 25"
    "High Court of Australia, B60/2023"
    "2024"
    "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/mallonland-pty-ltd-v-advanta-seeds-pty-ltd"
    Source.governmentSource
    "primary reasons/court publication for the pure-economic-loss duty dispute; exact salient-feature propositions require paragraph-level source ownership before executable use"
    Source.publicAttribution

cullenHCA19 : Source.AttributedSource
cullenHCA19 =
  Source.mkNoDOISource
    "High Court of Australia; Gageler CJ, Gordon, Edelman, Steward, Gleeson, Jagot and Beech-Jones JJ"
    "Cullen v New South Wales [2026] HCA 19"
    "High Court of Australia, S47/2025"
    "2026"
    "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/cullen-v-new-south-wales"
    Source.governmentSource
    "primary reasons/court publication for the police crowd-control negligence appeal; any binding-ratio proposition must retain exact reasons/paragraph lineage and material-feature scope"
    Source.publicAttribution

pabaiFCA796 : Source.AttributedSource
pabaiFCA796 =
  Source.mkNoDOISource
    "Federal Court of Australia; Wigney J"
    "Pabai v Commonwealth of Australia (No 2) [2025] FCA 796"
    "Federal Court of Australia, VID 622 of 2021"
    "2025"
    "https://www.fedcourt.gov.au/"
    Source.governmentSource
    "primary Federal Court reasons for the Torres Strait climate-negligence proceeding; factual findings, duty reasoning, causation findings, international-law references and relief remain independently located propositions"
    Source.publicAttribution

record RecentDutyCaseSourceBoundary : Set where
  constructor recent-duty-case-source-boundary
  field
    sourceCoLocationCreatesSharedRatio : Bool
    sourceCoLocationCreatesSharedRatioIsFalse : sourceCoLocationCreatesSharedRatio ≡ false
    catchwordCreatesHolding : Bool
    catchwordCreatesHoldingIsFalse : catchwordCreatesHolding ≡ false
    oneCaseFactsTransferToAnotherCase : Bool
    oneCaseFactsTransferToAnotherCaseIsFalse : oneCaseFactsTransferToAnotherCase ≡ false
    dashGraphRuleIsCourtAuthorship : Bool
    dashGraphRuleIsCourtAuthorshipIsFalse : dashGraphRuleIsCourtAuthorship ≡ false

canonicalRecentDutyCaseSourceBoundary : RecentDutyCaseSourceBoundary
canonicalRecentDutyCaseSourceBoundary =
  recent-duty-case-source-boundary false refl false refl false refl false refl
