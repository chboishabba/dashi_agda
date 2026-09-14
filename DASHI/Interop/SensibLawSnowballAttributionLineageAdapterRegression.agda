module DASHI.Interop.SensibLawSnowballAttributionLineageAdapterRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Lineage
import DASHI.Interop.SensibLawSnowballAttributionLineageAdapterExact as Adapter

sourceReceiptRetainsSnowballRole :
  ∀ {p} (receipt : SourceRule.PropositionSourceReceipt p) →
  Snowball.SourceRoleSnowballReceipt (SourceRule.attributedSource receipt)
sourceReceiptRetainsSnowballRole = Adapter.propositionSourceSnowballReceipt

sourceReceiptHasExternalLineage :
  ∀ {p} (receipt : SourceRule.PropositionSourceReceipt p) →
  Lineage.ClaimLineageReceipt p
sourceReceiptHasExternalLineage = Adapter.propositionSourceExternalLineage

sourceReceiptHasReconstructionLineage :
  ∀ {p} (receipt : SourceRule.PropositionSourceReceipt p) →
  String →
  Lineage.ClaimLineageReceipt p
sourceReceiptHasReconstructionLineage = Adapter.propositionSourceReconstructionLineage

sameSourceDoesNotFixClaimStage :
  ∀ {p} (receipt : SourceRule.PropositionSourceReceipt p) (reference : String) →
  Lineage.stageOf (Adapter.propositionSourceExternalLineage receipt) ≡
  Lineage.stageOf (Adapter.propositionSourceReconstructionLineage receipt reference) →
  ⊥
sameSourceDoesNotFixClaimStage = Adapter.sameSourceReceiptDoesNotFixClaimStage
