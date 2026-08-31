module DASHI.Physics.YangMills.BalabanSourceResidualConsumerNonDescent369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation
import DASHI.Physics.YangMills.BalabanActiveSourceDiscriminator2026Exact as Source

------------------------------------------------------------------------
-- YM / 369 RESIDUAL-CONSUMER NON-DESCENT
--
-- The active Balaban source fixture already contains exactly the information
-- geometry highlighted by the 369 residual-fibre work: all fine source worlds
-- share one coarse public/source label, but literal-recovery readiness differs.
-- This file turns that observation into the repository's canonical consumer
-- non-descent theorem shape.
------------------------------------------------------------------------

sourceRecoveryNonDescentWitness :
  Descent.ConsumerNonDescentWitness Source.coarseSource Source.recoveryDecision
sourceRecoveryNonDescentWitness =
  Descent.consumerNonDescentWitness
    Source.labelsOnly
    Source.literalRecoveryReady
    refl
    (lambda ())

coarseBalabanClaimNotSufficientForRecoveryDecision :
  Descent.ConsumerSufficient Source.coarseSource Source.recoveryDecision -> ⊥
coarseBalabanClaimNotSufficientForRecoveryDecision =
  Descent.nonDescentWitnessBlocksSufficiency sourceRecoveryNonDescentWitness

coarseBalabanClaimCannotFactorRecoveryDecision :
  Descent.FactorsThrough Source.coarseSource Source.recoveryDecision -> ⊥
coarseBalabanClaimCannotFactorRecoveryDecision =
  Descent.nonDescentWitnessBlocksFactorization sourceRecoveryNonDescentWitness

ym369ResidualRelation : Relation.RelationKind
ym369ResidualRelation = Relation.provedSearchObstructionReuse

ym369ResidualReuse : Relation.ReuseCapability ym369ResidualRelation
ym369ResidualReuse = Relation.reuseProvedSearchObstruction

ym369ResidualNoDirectTheoremTransfer :
  Relation.TheoremTransferCapability ym369ResidualRelation -> ⊥
ym369ResidualNoDirectTheoremTransfer =
  Relation.searchPatternCannotDirectlyTransferTheorem

record BalabanSourceResidualBoundary : Set where
  constructor balabanSourceResidualBoundary
  field
    coarseSourceLabelDeterminesLiteralRecovery : Bool
    coarseSourceLabelDeterminesLiteralRecoveryIsFalse :
      coarseSourceLabelDeterminesLiteralRecovery ≡ false
    sourceResidualRefinementIsProofSearchRelevant : Bool
    sourceResidualRefinementIsProofSearchRelevantIsTrue :
      sourceResidualRefinementIsProofSearchRelevant ≡ true
    residualNonDescentProvesBalabanPhysicalSourceTheorem : Bool
    residualNonDescentProvesBalabanPhysicalSourceTheoremIsFalse :
      residualNonDescentProvesBalabanPhysicalSourceTheorem ≡ false

canonicalBalabanSourceResidualBoundary : BalabanSourceResidualBoundary
canonicalBalabanSourceResidualBoundary =
  balabanSourceResidualBoundary false refl true refl false refl
