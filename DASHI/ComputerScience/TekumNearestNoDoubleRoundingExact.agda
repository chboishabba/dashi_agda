module DASHI.ComputerScience.TekumNearestNoDoubleRoundingExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (just)
open import Data.Rational.Base using (ℚ)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

source12 : Vec Trit.Trit 12
source12 =
  Trit.neg ∷ Trit.zer ∷ Trit.pos ∷ Trit.zer ∷ Trit.zer ∷ Trit.neg ∷
  Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ []

intermediate10 : Vec Trit.Trit 10
intermediate10 =
  Trit.pos ∷ Trit.zer ∷ Trit.zer ∷ Trit.neg ∷ Trit.neg ∷
  Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ []

twoStageFinal8 : Vec Trit.Trit 8
twoStageFinal8 =
  Trit.zer ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷
  Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ []

directFinal8 : Vec Trit.Trit 8
directFinal8 =
  Trit.pos ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷
  Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ []

sourceOrdinary : Sem.OrdinaryTekum
sourceOrdinary =
  Sem.ordinaryTekum Anchor.negativeSign (Sem.nonnegative 182) (Sem.negative 28) 4

intermediateOrdinary : Sem.OrdinaryTekum
intermediateOrdinary =
  Sem.ordinaryTekum Anchor.negativeSign (Sem.nonnegative 182) (Sem.negative 3) 2

twoStageOrdinary : Sem.OrdinaryTekum
twoStageOrdinary =
  Sem.ordinaryTekum Anchor.negativeSign (Sem.nonnegative 182) (Sem.nonnegative 0) 0

directOrdinary : Sem.OrdinaryTekum
directOrdinary =
  Sem.ordinaryTekum Anchor.negativeSign (Sem.nonnegative 181) (Sem.nonnegative 0) 0

sourceDecoderSameObject :
  Source.parseTekumWord source12 ≡ just (Sem.ordinary sourceOrdinary)
sourceDecoderSameObject = refl

intermediateDecoderSameObject :
  Source.parseTekumWord intermediate10 ≡ just (Sem.ordinary intermediateOrdinary)
intermediateDecoderSameObject = refl

twoStageDecoderSameObject :
  Source.parseTekumWord twoStageFinal8 ≡ just (Sem.ordinary twoStageOrdinary)
twoStageDecoderSameObject = refl

directDecoderSameObject :
  Source.parseTekumWord directFinal8 ≡ just (Sem.ordinary directOrdinary)
directDecoderSameObject = refl

sourceValue : ℚ
sourceValue = Exact.ordinaryRational sourceOrdinary

intermediateValue : ℚ
intermediateValue = Exact.ordinaryRational intermediateOrdinary

twoStageValue : ℚ
twoStageValue = Exact.ordinaryRational twoStageOrdinary

directValue : ℚ
directValue = Exact.ordinaryRational directOrdinary

twoStageAndDirectDiffer : ¬ (twoStageFinal8 ≡ directFinal8)
twoStageAndDirectDiffer ()

record DashiNearestNoDoubleRoundingCounterexample : Set where
  constructor dashiNearestNoDoubleRoundingCounterexample
  field
    sourceSameObject :
      Source.parseTekumWord source12 ≡ just (Sem.ordinary sourceOrdinary)
    intermediateSameObject :
      Source.parseTekumWord intermediate10 ≡ just (Sem.ordinary intermediateOrdinary)
    twoStageSameObject :
      Source.parseTekumWord twoStageFinal8 ≡ just (Sem.ordinary twoStageOrdinary)
    directSameObject :
      Source.parseTekumWord directFinal8 ≡ just (Sem.ordinary directOrdinary)
    finalWordsDiffer : ¬ (twoStageFinal8 ≡ directFinal8)
open DashiNearestNoDoubleRoundingCounterexample public

dashiNearestNoDoubleRoundingCounterexample :
  DashiNearestNoDoubleRoundingCounterexample
dashiNearestNoDoubleRoundingCounterexample =
  dashiNearestNoDoubleRoundingCounterexample
    sourceDecoderSameObject
    intermediateDecoderSameObject
    twoStageDecoderSameObject
    directDecoderSameObject
    twoStageAndDirectDiffer

universalNoDoubleRoundingRefuted :
  ¬ (twoStageFinal8 ≡ directFinal8)
universalNoDoubleRoundingRefuted = twoStageAndDirectDiffer

------------------------------------------------------------------------
-- Exact executable receipt values:
-- source      = -448599938492324310442483952132513863641390497147438380708009220498080919908972335004317
-- intermediate= -457064088275198354035738366323693370502548808414371180344009394469742824058198228117606
-- two-stage   = -685596132412797531053607549485540055753823212621556770516014091704614236087297342176409
-- direct      = -228532044137599177017869183161846685251274404207185590172004697234871412029099114058803
-- Stage two is an exact tie at source codes -3279/-3278; lower-code DASHI
-- policy chooses -3279. Direct 12→8 exact-nearest is unique at -3278.
------------------------------------------------------------------------
