module DASHI.Statistics.ZipfABC6OrderHeapsQuotientExact where

------------------------------------------------------------------------
-- Six-permutation ABC/Heaps cross-carrier information-loss adapter.
--
-- SOURCE OWNERS REUSED, NOT REPLACED:
--   SSSPThreeFrontierLinearExtensionQuotientBidiExact.LinearOrder3
--   SSSPThreeFrontierMinimumOrbitQuotientExact.minimumOf
--   SSSPThreeFrontierBinaryTernaryFactorExact.encodeOrder/decodeOrder
--   ZipfFullHeapsCurveIdentityNoGoExact.fullHeapsCurve/histogram
--   ZipfNoveltyCurveInjectiveExact.curveFromZero
--
-- For a corpus with one EACH of three named types A,B,C, all six temporal
-- orders have exact full Heaps curve (0,1,2,3). The complete curve does NOT
-- identify even the first named type. The minimum+tail codec DOES identify
-- the order, by an existing source-owned round-trip proof.
--
-- S3-sized six-order carrier != cyclic C6, HexTruth, or Monster identity.
-- No Zipf exponent, empirical time-dependence or fluid-phase theorem.
--
-- Mathematical ancestry: classical S3 permutation counting and Heaps
-- prefix vocabulary statistic. Original existing repository SSSP and
-- ternary-codec proofs retain ownership. New narrow source adaptation:
-- Johl Brown-directed with OpenAI ChatGPT assistance, 2026-10-28.
-- Agda source-written; not kernel-verified in this environment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Computation.SSSPThreeFrontierLinearExtensionQuotientBidiExact as F3
import DASHI.Computation.SSSPThreeFrontierMinimumOrbitQuotientExact as Min
import DASHI.Computation.SSSPThreeFrontierBinaryTernaryFactorExact as Code
import DASHI.Statistics.ZipfFullHeapsCurveIdentityNoGoExact as Hist
import DASHI.Statistics.ZipfNoveltyCurveInjectiveExact as Flag

------------------------------------------------------------------------
-- Typed representation map, NOT an identification of graph vertices with
-- corpus tokens. This interpretation is the only new cross-domain map.
------------------------------------------------------------------------

vertexAsLetter : F3.Frontier3 → Hist.Letter
vertexAsLetter F3.a = Hist.A
vertexAsLetter F3.b = Hist.B
vertexAsLetter F3.c = Hist.C

orderAsWord : F3.LinearOrder3 → List Hist.Letter
orderAsWord F3.abc = Hist.A ∷ Hist.B ∷ Hist.C ∷ []
orderAsWord F3.acb = Hist.A ∷ Hist.C ∷ Hist.B ∷ []
orderAsWord F3.bac = Hist.B ∷ Hist.A ∷ Hist.C ∷ []
orderAsWord F3.bca = Hist.B ∷ Hist.C ∷ Hist.A ∷ []
orderAsWord F3.cab = Hist.C ∷ Hist.A ∷ Hist.B ∷ []
orderAsWord F3.cba = Hist.C ∷ Hist.B ∷ Hist.A ∷ []

------------------------------------------------------------------------
-- ALL SIX full-prefix Heaps histories are identical.
------------------------------------------------------------------------

threeTypeCurve : List Nat
threeTypeCurve =
  zero ∷ suc zero ∷ suc (suc zero) ∷
  suc (suc (suc zero)) ∷ []

allSixFullHeapsCurvesCoincide :
  (o : F3.LinearOrder3) →
  Hist.fullHeapsCurve (orderAsWord o) ≡ threeTypeCurve
allSixFullHeapsCurvesCoincide F3.abc = refl
allSixFullHeapsCurvesCoincide F3.acb = refl
allSixFullHeapsCurvesCoincide F3.bac = refl
allSixFullHeapsCurvesCoincide F3.bca = refl
allSixFullHeapsCurvesCoincide F3.cab = refl
allSixFullHeapsCurvesCoincide F3.cba = refl

threeTypeHistogram : Hist.ThreeTypeHistogram
threeTypeHistogram =
  Hist.frequencies (suc zero) (suc zero) (suc zero)

allSixTerminalHistogramsCoincide :
  (o : F3.LinearOrder3) →
  Hist.observedHistogram (orderAsWord o) ≡ threeTypeHistogram
allSixTerminalHistogramsCoincide F3.abc = refl
allSixTerminalHistogramsCoincide F3.acb = refl
allSixTerminalHistogramsCoincide F3.bac = refl
allSixTerminalHistogramsCoincide F3.bca = refl
allSixTerminalHistogramsCoincide F3.cab = refl
allSixTerminalHistogramsCoincide F3.cba = refl

threeNoveltyFlags : List Bool
threeNoveltyFlags = true ∷ true ∷ true ∷ []

allSixAreSameFlagCurve :
  (o : F3.LinearOrder3) →
  Hist.fullHeapsCurve (orderAsWord o) ≡
    Flag.curveFromZero threeNoveltyFlags
allSixAreSameFlagCurve o =
  allSixFullHeapsCurvesCoincide o

------------------------------------------------------------------------
-- The first observed token is the source-owned minimum consumer.
-- Unlike the full Heaps curve, that observation preserves 3 outcomes.
------------------------------------------------------------------------

firstLetter : List Hist.Letter → Hist.Letter
firstLetter (x ∷ xs) = x
firstLetter [] = Hist.A

firstMatchesSSSPMinimum :
  (o : F3.LinearOrder3) →
  firstLetter (orderAsWord o) ≡ vertexAsLetter (Min.minimumOf o)
firstMatchesSSSPMinimum F3.abc = refl
firstMatchesSSSPMinimum F3.acb = refl
firstMatchesSSSPMinimum F3.bac = refl
firstMatchesSSSPMinimum F3.bca = refl
firstMatchesSSSPMinimum F3.cab = refl
firstMatchesSSSPMinimum F3.cba = refl

abcVsBacSameCurve :
  Hist.fullHeapsCurve (orderAsWord F3.abc) ≡
  Hist.fullHeapsCurve (orderAsWord F3.bac)
abcVsBacSameCurve = refl

abcVsAcbSameCurve :
  Hist.fullHeapsCurve (orderAsWord F3.abc) ≡
  Hist.fullHeapsCurve (orderAsWord F3.acb)
abcVsAcbSameCurve = refl

-- Universal recovery of first-token LABEL from full Heaps curve alone
-- would identify the distinct A and B constructors. Impossible.
noFirstLabelRecoveryFromFullHeapsCurve :
  (recover : List Nat → Hist.Letter) →
  ((o : F3.LinearOrder3) →
    recover (Hist.fullHeapsCurve (orderAsWord o))
    ≡ firstLetter (orderAsWord o)) →
  Hist.⊥
noFirstLabelRecoveryFromFullHeapsCurve recover correct =
  Hist.A≢B
    (trans (sym (correct F3.abc))
      (trans (cong recover abcVsBacSameCurve)
        (correct F3.bac)))

------------------------------------------------------------------------
-- The existing 6 <-> (minimum trit, tail bit) codec keeps all six.
-- Reuse BOTH source-owned roundtrips; do not build a parallel S3.
------------------------------------------------------------------------

orderRecoveredFromExistingCodec :
  (o : F3.LinearOrder3) →
  Code.decodeOrder (Code.encodeOrder o) ≡ o
orderRecoveredFromExistingCodec = Code.orderRoundTrip

codeRecoveredFromExistingOrder :
  (c : Code.MinTailCode) →
  Code.encodeOrder (Code.decodeOrder c) ≡ c
codeRecoveredFromExistingOrder = Code.codeRoundTrip

encodedMinimumIsExistingConsumer :
  (o : F3.LinearOrder3) →
  Code.minimumClass (Code.encodeOrder o) ≡ Min.pullOneObservation o
encodedMinimumIsExistingConsumer = Code.minimumFactorAgreesWithPull

-- The two A-first permutations have the same full curve and same
-- minimum consumer, but different unresolved tail orientation.
sameAMinimumDifferentTail :
  Min.minimumOf F3.abc ≡ Min.minimumOf F3.acb
sameAMinimumDifferentTail = Min.minA-fibre

aFirstDifferentTailCodes :
  Code.tailOrientation (Code.encodeOrder F3.abc) ≡ Code.forwardTail
aFirstDifferentTailCodes = refl

aFirstReverseTailCode :
  Code.tailOrientation (Code.encodeOrder F3.acb) ≡ Code.reverseTail
aFirstReverseTailCode = refl

forwardNotReverse : Code.forwardTail ≡ Code.reverseTail → Hist.⊥
forwardNotReverse ()

noTailRecoveryFromFullHeapsCurve :
  (recover : List Nat → Code.TailBit) →
  ((o : F3.LinearOrder3) →
    recover (Hist.fullHeapsCurve (orderAsWord o))
      ≡ Code.tailOrientation (Code.encodeOrder o)) →
  Hist.⊥
noTailRecoveryFromFullHeapsCurve recover correct =
  forwardNotReverse
    (trans (sym (correct F3.abc))
      (trans (cong recover abcVsAcbSameCurve)
        (correct F3.acb)))

-- Boundary: source codec chart has 6 outcomes; minimum-only has
-- 3 two-element fibres; full Heaps event curve has 1 six-element fibre.
-- These are different observation maps, NOT isomorphic consumer theories.


------------------------------------------------------------------------
-- The smallest positive-count repeated-token cut (2,1,1).
-- The first three symbols still use the already-owned A/B/C labels.
-- This is a literal H08 *finite witness*, not a general all-count proof.
------------------------------------------------------------------------

aRepeatedEarly : List Hist.Letter
aRepeatedEarly = Hist.A ∷ Hist.A ∷ Hist.B ∷ Hist.C ∷ []

aRepeatedLate : List Hist.Letter
aRepeatedLate = Hist.A ∷ Hist.B ∷ Hist.C ∷ Hist.A ∷ []

repeatedHistogram : Hist.ThreeTypeHistogram
repeatedHistogram =
  Hist.frequencies (suc (suc zero)) (suc zero) (suc zero)

earlySameHistogram :
  Hist.observedHistogram aRepeatedEarly ≡ repeatedHistogram
earlySameHistogram = refl

lateSameHistogram :
  Hist.observedHistogram aRepeatedLate ≡ repeatedHistogram
lateSameHistogram = refl

earlyMinimalProfile :
  Hist.fullHeapsCurve aRepeatedEarly ≡
    (zero ∷ suc zero ∷ suc zero ∷ suc (suc zero) ∷
     suc (suc (suc zero)) ∷ [])
earlyMinimalProfile = refl

lateMaximalProfile :
  Hist.fullHeapsCurve aRepeatedLate ≡
    (zero ∷ suc zero ∷ suc (suc zero) ∷
     suc (suc (suc zero)) ∷ suc (suc (suc zero)) ∷ [])
lateMaximalProfile = refl

-- The same histogram does NOT force identical full curves if there
-- is a repeated type. This strengthens the six-order all-novelty case.
earlyAndLateCurvesDistinct :
  Hist.fullHeapsCurve aRepeatedEarly ≡
  Hist.fullHeapsCurve aRepeatedLate → Hist.⊥
earlyAndLateCurvesDistinct ()
