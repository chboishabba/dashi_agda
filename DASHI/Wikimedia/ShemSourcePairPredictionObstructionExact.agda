module DASHI.Wikimedia.ShemSourcePairPredictionObstructionExact where

-- H23: two actual pinned WLC Exodus 14:19-21 Shem columns (0-based 1,43).
-- Glyphs: yod-lamed-yod and yod-lamed-he. H20 gematria chart codes:
-- 13=(1,1,1), 10=(1,0,1), 12=(0,1,1).
-- This uses the original signed field point carrier. The three positions
-- of this payload are letter roles, NOT Base369 appraisal semantics.
-- Source-written, not Agda kernel accepted.
open import DASHI.Core.Prelude
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Foundations.SSPTritCarrier as S
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as C
import DASHI.Wikimedia.KeyShoeNativeFieldIncidenceExact as Field
import DASHI.Wikimedia.KeyShoeFieldLawMovingFrameExact as Laws

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

-- Attach the source witness to the canonical repair constructor.
sourceCollision : Descent.ConsumerNonDescentWitness visiblePair withheldThird
sourceCollision =
  Descent.consumerNonDescentWitness column2 column44 sameVisiblePair yodNotHe

contextRepairMustSeparate : {Context : Set} (context : SourceColumn → Context) →
  Repair.RefinementRepairs visiblePair context withheldThird →
  context column2 ≡ context column44 → ⊥
contextRepairMustSeparate context repaired same =
  Repair.refinementRepairSeparatesWitness sourceCollision repaired same


-- H32: chart-independent affine F3-line obstruction.
-- Actual source columns 4 and 23 (one-based): ayin-lamed-mem,
-- mem-lamed-he. Reorder each unordered incidence triple to lamed,mem,third.
-- These original glyph identifiers use the existing gematria point chart;
-- the tested candidate chart may be ANY injective map on these identifiers.
mem ayin : Point
mem = C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne
ayin = C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero

ayinNotHe : ayin ≡ he → ⊥
ayinNotHe ()

affineSharedPairForcesThird : (a b c d : Point) →
  Field.add (Field.add a b) c ≡ Field.add (Field.add a b) d →
  c ≡ d
affineSharedPairForcesThird a b c d same =
  trans (sym (Laws.subAdd (Field.add a b) c))
    (trans (cong (λ v → Field.sub v (Field.add a b)) same)
      (Laws.subAdd (Field.add a b) d))

sourceLineChartObstruction : (chart : Point → Point) →
  (∀ {x y} → chart x ≡ chart y → x ≡ y) →
  Field.add (Field.add (chart lamed) (chart mem)) (chart ayin) ≡ C.origin →
  Field.add (Field.add (chart lamed) (chart mem)) (chart he) ≡ C.origin →
  ⊥
sourceLineChartObstruction chart injective line4 line23 =
  ayinNotHe (injective
    (affineSharedPairForcesThird (chart lamed) (chart mem)
      (chart ayin) (chart he) (trans line4 (sym line23))))


-- H34: a selector equivariant under Frobenius on a normalized visible pair
-- must return a Frobenius-fixed point. This is a conditional obstruction,
-- not a requirement that the original creator law be equivariant.
frobeniusPairFixed : (select : Point → Point → Point) →
  ((a b : Point) →
    select (Laws.cube a) (Laws.cube b) ≡ Laws.cube (select a b)) →
  Laws.cube (select C.origin Field.one) ≡ select C.origin Field.one
frobeniusPairFixed select equivariant = sym (equivariant C.origin Field.one)

-- Exact closed finite field arithmetic on the existing signed point carrier.
-- Fixed points of x -> x^3 are precisely the prime subfield.
frobeniusFixedBase : (x : Point) → Laws.cube x ≡ x →
  (x ≡ C.origin) ⊎ ((x ≡ Field.one) ⊎ (x ≡ Field.negative Field.one))
frobeniusFixedBase (C.ternary27Point S.sspZero S.sspZero S.sspZero) eq = inj₁ refl
frobeniusFixedBase (C.ternary27Point S.sspZero S.sspZero S.sspPosOne) ()
frobeniusFixedBase (C.ternary27Point S.sspZero S.sspZero S.sspNegOne) ()
frobeniusFixedBase (C.ternary27Point S.sspZero S.sspPosOne S.sspZero) ()
frobeniusFixedBase (C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne) ()
frobeniusFixedBase (C.ternary27Point S.sspZero S.sspPosOne S.sspNegOne) ()
frobeniusFixedBase (C.ternary27Point S.sspZero S.sspNegOne S.sspZero) ()
frobeniusFixedBase (C.ternary27Point S.sspZero S.sspNegOne S.sspPosOne) ()
frobeniusFixedBase (C.ternary27Point S.sspZero S.sspNegOne S.sspNegOne) ()
frobeniusFixedBase (C.ternary27Point S.sspPosOne S.sspZero S.sspZero) eq = inj₂ (inj₁ refl)
frobeniusFixedBase (C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne) ()
frobeniusFixedBase (C.ternary27Point S.sspPosOne S.sspZero S.sspNegOne) ()
frobeniusFixedBase (C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero) ()
frobeniusFixedBase (C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne) ()
frobeniusFixedBase (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne) ()
frobeniusFixedBase (C.ternary27Point S.sspPosOne S.sspNegOne S.sspZero) ()
frobeniusFixedBase (C.ternary27Point S.sspPosOne S.sspNegOne S.sspPosOne) ()
frobeniusFixedBase (C.ternary27Point S.sspPosOne S.sspNegOne S.sspNegOne) ()
frobeniusFixedBase (C.ternary27Point S.sspNegOne S.sspZero S.sspZero) eq = inj₂ (inj₂ refl)
frobeniusFixedBase (C.ternary27Point S.sspNegOne S.sspZero S.sspPosOne) ()
frobeniusFixedBase (C.ternary27Point S.sspNegOne S.sspZero S.sspNegOne) ()
frobeniusFixedBase (C.ternary27Point S.sspNegOne S.sspPosOne S.sspZero) ()
frobeniusFixedBase (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne) ()
frobeniusFixedBase (C.ternary27Point S.sspNegOne S.sspPosOne S.sspNegOne) ()
frobeniusFixedBase (C.ternary27Point S.sspNegOne S.sspNegOne S.sspZero) ()
frobeniusFixedBase (C.ternary27Point S.sspNegOne S.sspNegOne S.sspPosOne) ()
frobeniusFixedBase (C.ternary27Point S.sspNegOne S.sspNegOne S.sspNegOne) ()

frobeniusPairSelectorBase : (select : Point → Point → Point) →
  ((a b : Point) →
    select (Laws.cube a) (Laws.cube b) ≡ Laws.cube (select a b)) →
  let x = select C.origin Field.one in
  (x ≡ C.origin) ⊎ ((x ≡ Field.one) ⊎ (x ≡ Field.negative Field.one))
frobeniusPairSelectorBase select equivariant =
  frobeniusFixedBase (select C.origin Field.one)
    (frobeniusPairFixed select equivariant)
