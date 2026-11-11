module DASHI.Foundations.TernaryThirteenOriginalHeisenbergGroupCarrierExact where

------------------------------------------------------------------------
-- H1.01: REAL original finite Heisenberg central extension ↔ 13 trits.
--
-- The SOURCE is the independently existing Monster3BFiniteHeisenberg
-- central-extension multiplication with six translation, six dual
-- modulation and one central F3 coordinate. Its associativity,
-- identity and inverse are owned by the existing original modules.
--
-- This file proves BOTH finite carrier round trips and transports the
-- original, NONABELIAN group law onto a canonical 13-word.
-- It does not infer that relational appraisal, an actual Monster
-- subgroup, or an ITIR semantic world is this group.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Algebra.Trit as F3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergAssociativityExact as Assoc
import DASHI.Moonshine.Monster3BFiniteHeisenbergInverseExact as Inv
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact as Codec
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel

toWordTrit : F3.Trit → Word.Trit
toWordTrit F3.neg = Word.negative
toWordTrit F3.zer = Word.neutral
toWordTrit F3.pos = Word.positive

fromWordTrit : Word.Trit → F3.Trit
fromWordTrit Word.negative = F3.neg
fromWordTrit Word.neutral = F3.zer
fromWordTrit Word.positive = F3.pos

wordTritAfterOriginal :
  (value : F3.Trit) → fromWordTrit (toWordTrit value) ≡ value
wordTritAfterOriginal F3.neg = refl
wordTritAfterOriginal F3.zer = refl
wordTritAfterOriginal F3.pos = refl

originalTritAfterWord :
  (value : Word.Trit) → toWordTrit (fromWordTrit value) ≡ value
originalTritAfterWord Word.negative = refl
originalTritAfterWord Word.neutral = refl
originalTritAfterWord Word.positive = refl

x6ToWord : G.X6 → Word.TritWord 6
x6ToWord (G.x6 a b c d e f) =
  toWordTrit a , (toWordTrit b , (toWordTrit c ,
    (toWordTrit d , (toWordTrit e , (toWordTrit f , tt)))))

wordToX6 : Word.TritWord 6 → G.X6
wordToX6 (a , (b , (c , (d , (e , (f , tt)))))) =
  G.x6 (fromWordTrit a) (fromWordTrit b) (fromWordTrit c)
       (fromWordTrit d) (fromWordTrit e) (fromWordTrit f)

x6OriginalRoundTrip :
  (x : G.X6) → wordToX6 (x6ToWord x) ≡ x
x6OriginalRoundTrip (G.x6 a b c d e f)
  rewrite wordTritAfterOriginal a | wordTritAfterOriginal b
        | wordTritAfterOriginal c | wordTritAfterOriginal d
        | wordTritAfterOriginal e | wordTritAfterOriginal f = refl

x6WordRoundTrip :
  (x : Word.TritWord 6) → x6ToWord (wordToX6 x) ≡ x
x6WordRoundTrip (a , (b , (c , (d , (e , (f , tt))))))
  rewrite originalTritAfterWord a | originalTritAfterWord b
        | originalTritAfterWord c | originalTritAfterWord d
        | originalTritAfterWord e | originalTritAfterWord f = refl

-- The actual source H_6 carrier maps to exactly six + six + one
-- trits, with the source's central cocycle coordinate preserved.
originalGroupToWord :
  H.Heisenberg6 → Word.TritWord 13
originalGroupToWord (H.heisenberg6 (H.symplectic12 x y) c) =
  Word.joinTriple 6 6 1
    (x6ToWord x , (x6ToWord y , (toWordTrit c , tt)))

wordToOriginalGroup :
  Word.TritWord 13 → H.Heisenberg6
wordToOriginalGroup code with Word.splitTriple 6 6 1 code
... | x , (y , (c , tt)) =
  H.heisenberg6
    (H.symplectic12 (wordToX6 x) (wordToX6 y))
    (fromWordTrit c)

originalGroupRoundTrip :
  (g : H.Heisenberg6) →
  wordToOriginalGroup (originalGroupToWord g) ≡ g
originalGroupRoundTrip
  (H.heisenberg6 (H.symplectic12 x y) c)
  rewrite Word.splitTripleAfterJoin 6 6 1
    (x6ToWord x) (x6ToWord y) (toWordTrit c , tt)
        | x6OriginalRoundTrip x
        | x6OriginalRoundTrip y
        | wordTritAfterOriginal c = refl

originalWordRoundTrip :
  (code : Word.TritWord 13) →
  originalGroupToWord (wordToOriginalGroup code) ≡ code
originalWordRoundTrip code with Word.splitTriple 6 6 1 code
... | x , (y , (c , tt))
  rewrite x6WordRoundTrip x
        | x6WordRoundTrip y
        | originalTritAfterWord c =
  Word.joinTripleAfterSplit 6 6 1 code

-- Nonabelian multiplication is transported from the ORIGINAL
-- cocycle-bearing source, not independently defined by componentwise
-- trit addition (which would lose the Heisenberg commutator).
wordCompose :
  Word.TritWord 13 → Word.TritWord 13 → Word.TritWord 13
wordCompose x y =
  originalGroupToWord
    (H.compose (wordToOriginalGroup x) (wordToOriginalGroup y))

wordIdentity : Word.TritWord 13
wordIdentity = originalGroupToWord H.identityH

wordInverse : Word.TritWord 13 → Word.TritWord 13
wordInverse code =
  originalGroupToWord (Inv.inverseH (wordToOriginalGroup code))

originalMultiplicationRespected :
  (g h : H.Heisenberg6) →
  wordCompose (originalGroupToWord g) (originalGroupToWord h)
  ≡ originalGroupToWord (H.compose g h)
originalMultiplicationRespected g h
  rewrite originalGroupRoundTrip g | originalGroupRoundTrip h =
  refl

wordMultiplicationDecoded :
  (x y : Word.TritWord 13) →
  wordToOriginalGroup (wordCompose x y)
  ≡ H.compose (wordToOriginalGroup x) (wordToOriginalGroup y)
wordMultiplicationDecoded x y =
  originalGroupRoundTrip
    (H.compose (wordToOriginalGroup x) (wordToOriginalGroup y))

originalIdentityRespected :
  wordToOriginalGroup wordIdentity ≡ H.identityH
originalIdentityRespected = originalGroupRoundTrip H.identityH

originalInverseRespected :
  (g : H.Heisenberg6) →
  wordInverse (originalGroupToWord g)
  ≡ originalGroupToWord (Inv.inverseH g)
originalInverseRespected g
  rewrite originalGroupRoundTrip g = refl

originalAssociativityRespected :
  (g h k : H.Heisenberg6) →
  originalGroupToWord (H.compose (H.compose g h) k)
  ≡ originalGroupToWord (H.compose g (H.compose h k))
originalAssociativityRespected g h k =
  cong originalGroupToWord (Assoc.composeAssociative g h k)

-- An actual original source noncommuting generator pair.
sourceTranslation : H.Heisenberg6
sourceTranslation = H.translationGenerator G.axis0

sourceModulation : H.Heisenberg6
sourceModulation = H.modulationGenerator G.axis0

sourceTranslationModulationPhase :
  H.centralPhase (H.compose sourceTranslation sourceModulation)
  ≡ F3.zer
sourceTranslationModulationPhase = refl

sourceModulationTranslationPhase :
  H.centralPhase (H.compose sourceModulation sourceTranslation)
  ≡ F3.pos
sourceModulationTranslationPhase = refl

originalGeneratorOrderMatters :
  H.compose sourceTranslation sourceModulation
  ≡ H.compose sourceModulation sourceTranslation → ⊥
originalGeneratorOrderMatters equal =
  zeroNotPositive
    (cong H.centralPhase equal)
  where
    zeroNotPositive : F3.zer ≡ F3.pos → ⊥
    zeroNotPositive ()

wordGeneratorOrderMatters :
  wordCompose
    (originalGroupToWord sourceTranslation)
    (originalGroupToWord sourceModulation)
  ≡
  wordCompose
    (originalGroupToWord sourceModulation)
    (originalGroupToWord sourceTranslation) → ⊥
wordGeneratorOrderMatters equality =
  originalGeneratorOrderMatters
    (trans
      (sym (originalGroupRoundTrip
        (H.compose sourceTranslation sourceModulation)))
      (trans
        (cong wordToOriginalGroup equality)
        (originalGroupRoundTrip
          (H.compose sourceModulation sourceTranslation))))

-- Keep the exact boundary: this SOURCE GROUP is not automatically
-- the separately intended relational/group/world semantic completion.

------------------------------------------------------------------------
-- Exact ORIGINAL relational 12-axis-plus-centre source carrier.
-- This is an actual transport to the existing source valuation
-- type; equality of functions is avoided, not assumed.
------------------------------------------------------------------------

originalGroupToSource :
  H.Heisenberg6 → Rel.SourceCentralCompletionCarrier
originalGroupToSource g =
  Codec.thirteenToSourceCentral (originalGroupToWord g)

sourceToOriginalGroup :
  Rel.SourceCentralCompletionCarrier → H.Heisenberg6
sourceToOriginalGroup state =
  wordToOriginalGroup (Codec.sourceCentralToThirteen state)

originalGroupSourceRoundTrip :
  (g : H.Heisenberg6) →
  sourceToOriginalGroup (originalGroupToSource g) ≡ g
originalGroupSourceRoundTrip g =
  trans
    (cong wordToOriginalGroup
      (Codec.thirteenSourceRoundTrip (originalGroupToWord g)))
    (originalGroupRoundTrip g)

sourceOriginalGroupRoundTripAxis :
  (state : Rel.SourceCentralCompletionCarrier)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁ (originalGroupToSource (sourceToOriginalGroup state)) axis
  ≡ proj₁ state axis
sourceOriginalGroupRoundTripAxis state axis =
  trans
    (cong
      (λ code → proj₁ (Codec.thirteenToSourceCentral code) axis)
      (originalWordRoundTrip (Codec.sourceCentralToThirteen state)))
    (Codec.sourceCentralRoundTripOnAxis state axis)

sourceOriginalGroupRoundTripCentre :
  (state : Rel.SourceCentralCompletionCarrier) →
  proj₂ (originalGroupToSource (sourceToOriginalGroup state))
  ≡ proj₂ state
sourceOriginalGroupRoundTripCentre state =
  trans
    (cong
      (λ code → proj₂ (Codec.thirteenToSourceCentral code))
      (originalWordRoundTrip (Codec.sourceCentralToThirteen state)))
    (Codec.sourceCentralRoundTripOnCentre state)

-- Noncommutative ORIGINAL group operation pulled back to the
-- chosen relational 12+central coordinate model. This is NOT
-- coordinatewise ternary addition.
sourceCentralCompose :
  Rel.SourceCentralCompletionCarrier →
  Rel.SourceCentralCompletionCarrier →
  Rel.SourceCentralCompletionCarrier
sourceCentralCompose x y =
  originalGroupToSource
    (H.compose (sourceToOriginalGroup x) (sourceToOriginalGroup y))

sourceCentralGroupCompositionOnAxes :
  (g h : H.Heisenberg6)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁
    (sourceCentralCompose (originalGroupToSource g)
                          (originalGroupToSource h)) axis
  ≡ proj₁ (originalGroupToSource (H.compose g h)) axis
sourceCentralGroupCompositionOnAxes g h axis
  rewrite originalGroupSourceRoundTrip g
        | originalGroupSourceRoundTrip h = refl

sourceCentralGroupCompositionOnCentre :
  (g h : H.Heisenberg6) →
  proj₂
    (sourceCentralCompose (originalGroupToSource g)
                          (originalGroupToSource h))
  ≡ proj₂ (originalGroupToSource (H.compose g h))
sourceCentralGroupCompositionOnCentre g h
  rewrite originalGroupSourceRoundTrip g
        | originalGroupSourceRoundTrip h = refl

-- The finite Heisenberg group is an independently existing
-- group owner with genuine cocycle/commutator. What is NOT paid
-- is an identification of arbitrary 144-cell relations, ITIR
-- world nodes, or an actual Monster group representation with it.
