{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredRawSourceFrontierRound216Exact where

------------------------------------------------------------------------
-- ROUND216 / PREFERRED RAW CMP119 SOURCE FRONTIER
--
-- Introspective reductions now give the following source order:
--
--   literal beta-driven CMP119 raw source family
--      {rho_k, U_k, E_k, R_k, B_k, A_k, Eq.(2.23)}
--     -> running coupling = finite beta-history coupling         [refl]
--     -> CMP122 Theorem 1 gives active Sect.-2 predicates        [compiler]
--     -> literal E_k pointwise/CMP116 localization
--     -> CMP109/CMP116 continuation                              [compiler]
--     -> BC1 effective potential = literal E_k                  [refl]
--
-- The complete action A_k must not be substituted for the Part-I/II regular
-- E_k effective action differentiated in CMP109 Eq.(5.1).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119RawStateRound216Exact as Raw
import DASHI.Physics.YangMills.BalabanCMP122Theorem1ToRawCMP119ActiveExact as T1
import DASHI.Physics.YangMills.BalabanCMP119RegularSectorCMP109116Round215Exact as Regular
import DASHI.Physics.YangMills.BalabanCMP119RegularSectorBC1Round215Exact as BC1
import DASHI.Physics.YangMills.BalabanPreferredSourceRealizationFrontierRound212Exact as R212


data PreferredRawSourceLeaf216 : Set where
  literalBetaDrivenCMP119RawSourceFamily : PreferredRawSourceLeaf216
  rawRunningCouplingSameBetaHistory : PreferredRawSourceLeaf216
  activeSection2PredicatesFromCMP122 : PreferredRawSourceLeaf216
  literalCMP119RegularESectorRealization : PreferredRawSourceLeaf216
  cmp119RegularEToCMP109116Continuation : PreferredRawSourceLeaf216
  cmp119RegularEToBC1Potential : PreferredRawSourceLeaf216
  literalCMP109GeneratedHistoryResponseProducer : PreferredRawSourceLeaf216
  literalCMP109BetaDifferenceDecomposition : PreferredRawSourceLeaf216
  literalPhysicalCompositeD1ChainRule : PreferredRawSourceLeaf216

data LeafState216 : Set where
  closed open blocked : LeafState216

preferredLeafState216 : PreferredRawSourceLeaf216 → LeafState216
preferredLeafState216 literalBetaDrivenCMP119RawSourceFamily = open
preferredLeafState216 rawRunningCouplingSameBetaHistory = closed
preferredLeafState216 activeSection2PredicatesFromCMP122 = closed
preferredLeafState216 literalCMP119RegularESectorRealization = blocked
preferredLeafState216 cmp119RegularEToCMP109116Continuation = closed
preferredLeafState216 cmp119RegularEToBC1Potential = closed
preferredLeafState216 literalCMP109GeneratedHistoryResponseProducer = open
preferredLeafState216 literalCMP109BetaDifferenceDecomposition = blocked
preferredLeafState216 literalPhysicalCompositeD1ChainRule = blocked

preferredFirstMissingCoordinate216 : PreferredRawSourceLeaf216
preferredFirstMissingCoordinate216 = literalBetaDrivenCMP119RawSourceFamily

preferredFirstMissingCoordinate216IsOpen :
  preferredLeafState216 preferredFirstMissingCoordinate216 ≡ open
preferredFirstMissingCoordinate216IsOpen = refl

rawCouplingSameObjectClosed :
  preferredLeafState216 rawRunningCouplingSameBetaHistory ≡ closed
rawCouplingSameObjectClosed = refl

activeSection2CompilerClosed :
  preferredLeafState216 activeSection2PredicatesFromCMP122 ≡ closed
activeSection2CompilerClosed = refl

regularContinuationSameObjectClosed :
  preferredLeafState216 cmp119RegularEToCMP109116Continuation ≡ closed
regularContinuationSameObjectClosed = refl

bc1RegularPotentialSameObjectClosed :
  preferredLeafState216 cmp119RegularEToBC1Potential ≡ closed
bc1RegularPotentialSameObjectClosed = refl

betaDrivenRawStateCompilerLevel : ProofLevel
betaDrivenRawStateCompilerLevel = Raw.betaDrivenCMP119RawStateCompilerLevel

betaDrivenRawCouplingSameObjectLevel : ProofLevel
betaDrivenRawCouplingSameObjectLevel = Raw.betaDrivenCMP119CouplingSameObjectLevel

cmp122ActiveSection2CompilerLevel : ProofLevel
cmp122ActiveSection2CompilerLevel = T1.cmp122Theorem1ProducesActiveSection2Level

cmp119RegularSectorContinuationLevel : ProofLevel
cmp119RegularSectorContinuationLevel = Regular.cmp119RegularSectorContinuationCompilerLevel

cmp119RegularSectorBC1Level : ProofLevel
cmp119RegularSectorBC1Level = BC1.cmp119RegularSectorBC1CompilerLevel

literalBetaDrivenCMP119RawSourceFamilyLevel : ProofLevel
literalBetaDrivenCMP119RawSourceFamilyLevel = Raw.literalBetaDrivenCMP119RawSourceInputsLevel

literalCMP119RegularESectorRealizationLevel : ProofLevel
literalCMP119RegularESectorRealizationLevel = Regular.literalCMP119RegularSectorRealizationLevel

literalCMP109GeneratedHistoryResponseProducerLevel : ProofLevel
literalCMP109GeneratedHistoryResponseProducerLevel =
  R212.literalCMP109GeneratedHistoryResponseProducerLevel

literalCMP109BetaDifferenceDecompositionLevel : ProofLevel
literalCMP109BetaDifferenceDecompositionLevel =
  R212.literalCMP109BetaDifferenceDecompositionLevel

literalPhysicalCompositeD1ChainRuleLevel : ProofLevel
literalPhysicalCompositeD1ChainRuleLevel =
  R212.literalPhysicalCompositeD1ChainRuleLevel

round216PhysicalSourceClosure : Bool
round216PhysicalSourceClosure = false

round216ClayPromotion : Bool
round216ClayPromotion = false

round216PhysicalSourceClosureIsFalse : round216PhysicalSourceClosure ≡ false
round216PhysicalSourceClosureIsFalse = refl

round216ClayPromotionIsFalse : round216ClayPromotion ≡ false
round216ClayPromotionIsFalse = refl
