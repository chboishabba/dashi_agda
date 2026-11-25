module DASHI.Wikimedia.ShemSourcePairPredictionObstructionExact where

-- H23: two actual pinned WLC Exodus 14:19-21 Shem columns (0-based 1,43).
-- Glyphs: yod-lamed-yod and yod-lamed-he. H20 gematria chart codes:
-- 13=(1,1,1), 10=(1,0,1), 12=(0,1,1).
-- This uses the original signed field point carrier. The three positions
-- of this payload are letter roles, NOT Base369 appraisal semantics.
-- Source-written, not Agda kernel accepted.
open import DASHI.Core.Prelude
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Foundations.SSPTritCarrier as S
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as C

Point : Set
Point = C.Ternary27Point

yod lamed he : Point
yod = C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne
lamed = C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne
he = C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne

yodNotHe : yod ≡ he → ⊥
yodNotHe ()

data SourceColumn : Set where
  column2 column44 : SourceColumn

payload : SourceColumn → C.TernaryHyperformalPoint
payload column2 = C.ternaryHyperformalPoint yod lamed yod
payload column44 = C.ternaryHyperformalPoint yod lamed he

visiblePair : SourceColumn → Point × Point
visiblePair i = C.interactionVoxel (payload i) , C.appraisalAVoxel (payload i)

withheldThird : SourceColumn → Point
withheldThird i = C.appraisalBVoxel (payload i)

sameVisiblePair : visiblePair column2 ≡ visiblePair column44
sameVisiblePair = refl

pairNotSufficient : Descent.ConsumerSufficient visiblePair withheldThird → ⊥
pairNotSufficient h = yodNotHe (h column2 column44 sameVisiblePair)

pairCannotFactor : Descent.FactorsThrough visiblePair withheldThird → ⊥
pairCannotFactor h =
  pairNotSufficient (Descent.factorsThroughImpliesFibreConstant h)

-- Any genuinely sufficient refinement must separate these two source
-- observations, not simply relabel their common ordered pair.
refinementMustSeparate : {Surface : Set} (observe : SourceColumn → Surface) →
  Descent.ConsumerSufficient observe withheldThird →
  observe column2 ≡ observe column44 → ⊥
refinementMustSeparate observe h same = yodNotHe (h column2 column44 same)

-- Indexing separates the witness but does not supply an independently
-- predictive operator. A lookup of withheld letters is not prediction.
