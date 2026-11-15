{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredRawSourceFrontierRound217Exact where

------------------------------------------------------------------------
-- ROUND217 / CURRENT FIRST SOURCE COORDINATE
--
-- Round217 splits the last bundled CMP119 source leaf without changing any
-- Clay scoreboard.  The literal raw source objects must exist before the
-- Sect.-2 predicate vocabulary can be bound to that SAME object family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119RawSourceRealizationSplitRound217Exact as Split
import DASHI.Physics.YangMills.BalabanCMP119RegularSectorCMP109116Round215Exact as Regular
import DASHI.Physics.YangMills.BalabanCMP119RegularSectorBC1Round215Exact as BC1
import DASHI.Physics.YangMills.BalabanPreferredSourceRealizationFrontierRound212Exact as R212


data PreferredRawSourceLeaf217 : Set where
  literalCMP119RawObjects : PreferredRawSourceLeaf217
  literalCMP119PredicateVocabulary : PreferredRawSourceLeaf217
  rawRunningCouplingSameBetaHistory : PreferredRawSourceLeaf217
  activeSection2FromCMP122 : PreferredRawSourceLeaf217
  literalCMP119RegularESectorRealization : PreferredRawSourceLeaf217
  cmp119RegularEToCMP109116 : PreferredRawSourceLeaf217
  cmp119RegularEToBC1 : PreferredRawSourceLeaf217
  literalCMP109ResponseProducer : PreferredRawSourceLeaf217
  literalCMP109BetaDifferenceDecomposition : PreferredRawSourceLeaf217
  literalPhysicalCompositeD1ChainRule : PreferredRawSourceLeaf217

data LeafState217 : Set where
  leafClosed leafOpen leafBlocked : LeafState217

preferredLeafState217 : PreferredRawSourceLeaf217 → LeafState217
preferredLeafState217 literalCMP119RawObjects = leafOpen
preferredLeafState217 literalCMP119PredicateVocabulary = leafBlocked
preferredLeafState217 rawRunningCouplingSameBetaHistory = leafClosed
preferredLeafState217 activeSection2FromCMP122 = leafClosed
preferredLeafState217 literalCMP119RegularESectorRealization = leafBlocked
preferredLeafState217 cmp119RegularEToCMP109116 = leafClosed
preferredLeafState217 cmp119RegularEToBC1 = leafClosed
preferredLeafState217 literalCMP109ResponseProducer = leafOpen
preferredLeafState217 literalCMP109BetaDifferenceDecomposition = leafBlocked
preferredLeafState217 literalPhysicalCompositeD1ChainRule = leafBlocked

preferredFirstMissingCoordinate217 : PreferredRawSourceLeaf217
preferredFirstMissingCoordinate217 = literalCMP119RawObjects

preferredFirstMissingCoordinate217IsOpen :
  preferredLeafState217 preferredFirstMissingCoordinate217 ≡ leafOpen
preferredFirstMissingCoordinate217IsOpen = refl

rawCouplingSameObjectClosed :
  preferredLeafState217 rawRunningCouplingSameBetaHistory ≡ leafClosed
rawCouplingSameObjectClosed = refl

activeSection2CompilerClosed :
  preferredLeafState217 activeSection2FromCMP122 ≡ leafClosed
activeSection2CompilerClosed = refl

regularContinuationClosed :
  preferredLeafState217 cmp119RegularEToCMP109116 ≡ leafClosed
regularContinuationClosed = refl

regularBC1SameObjectClosed :
  preferredLeafState217 cmp119RegularEToBC1 ≡ leafClosed
regularBC1SameObjectClosed = refl

literalCMP119RawObjectsLevel : ProofLevel
literalCMP119RawObjectsLevel = Split.literalCMP119RawObjectsOverHistoryLevel

literalCMP119PredicateVocabularyLevel : ProofLevel
literalCMP119PredicateVocabularyLevel =
  Split.literalCMP119Section2PredicateVocabularyLevel

rawCouplingCompilerLevel : ProofLevel
rawCouplingCompilerLevel = Split.cmp119RawCouplingSameObjectLevel

activeSection2CompilerLevel : ProofLevel
activeSection2CompilerLevel = Split.cmp122ActiveSection2FromSplitLevel

literalCMP119RegularESectorRealizationLevel : ProofLevel
literalCMP119RegularESectorRealizationLevel = Regular.literalCMP119RegularSectorRealizationLevel

regularContinuationCompilerLevel : ProofLevel
regularContinuationCompilerLevel = Regular.cmp119RegularSectorContinuationCompilerLevel

regularBC1CompilerLevel : ProofLevel
regularBC1CompilerLevel = BC1.cmp119RegularSectorBC1CompilerLevel

literalCMP109ResponseProducerLevel : ProofLevel
literalCMP109ResponseProducerLevel =
  R212.literalCMP109GeneratedHistoryResponseProducerLevel

literalCMP109BetaDifferenceDecompositionLevel : ProofLevel
literalCMP109BetaDifferenceDecompositionLevel =
  R212.literalCMP109BetaDifferenceDecompositionLevel

literalPhysicalCompositeD1ChainRuleLevel : ProofLevel
literalPhysicalCompositeD1ChainRuleLevel =
  R212.literalPhysicalCompositeD1ChainRuleLevel

round217PhysicalSourceClosure : Bool
round217PhysicalSourceClosure = false

round217ClayPromotion : Bool
round217ClayPromotion = false

round217PhysicalSourceClosureIsFalse : round217PhysicalSourceClosure ≡ false
round217PhysicalSourceClosureIsFalse = refl

round217ClayPromotionIsFalse : round217ClayPromotion ≡ false
round217ClayPromotionIsFalse = refl
