module DASHI.Mathematics.Complexity.PNPDecisionDerivedGainFailureExact where

-- Same actual Cook decision candidate, existing indexed restriction,
-- and existing finite SAT truth producer. The candidate's search does
-- NOT use the exhaustive finite truth producer; that producer is only
-- used to exhibit a genuine error in its actual query path.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (sym; trans)
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.BooleanFormulaFiniteSATDecisionExact as Finite
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct

Candidate : PR.PolynomialCostModel Cook.BooleanFormula → Set₁
Candidate = Direct.PolynomialSATDeciderCandidate

query : ∀ {cost n} → Candidate cost → SAT.BooleanFormula (suc n) → Bool
query c f = Direct.decide c (Bridge.indexedToCook (SAT.restrictHead false f))

assignment : ∀ {cost n} → Candidate cost → SAT.BooleanFormula n → SAT.Assignment n
assignment {n = zero} c f = Finite.emptyAssignment
assignment {n = suc n} c f with query c f
... | true = SAT.extendAssignment false (assignment c (SAT.restrictHead false f))
... | false = SAT.extendAssignment true (assignment c (SAT.restrictHead true f))

data TraceFailure {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  (c : Candidate cost) : ∀ {n} → SAT.BooleanFormula n → Set₁ where
  positive : ∀ {n} {f : SAT.BooleanFormula (suc n)} →
    query c f ≡ true →
    (SAT.Satisfying (SAT.restrictHead false f) → ⊥) → TraceFailure c f
  negative : ∀ {n} {f : SAT.BooleanFormula (suc n)} →
    query c f ≡ false →
    SAT.Satisfying (SAT.restrictHead false f) → TraceFailure c f
  deeperFalse : ∀ {n} {f : SAT.BooleanFormula (suc n)} →
    query c f ≡ true → TraceFailure c (SAT.restrictHead false f) → TraceFailure c f
  deeperTrue : ∀ {n} {f : SAT.BooleanFormula (suc n)} →
    query c f ≡ false → TraceFailure c (SAT.restrictHead true f) → TraceFailure c f

toDirectFailure : ∀ {cost n} {c : Candidate cost} {f : SAT.BooleanFormula n} →
  TraceFailure c f → Direct.SATDecisionFailure c
toDirectFailure {c = c} (positive {f = f} answer impossible) =
  Direct.falsePositive (Bridge.indexedToCook (SAT.restrictHead false f)) answer
    (λ sat → impossible (Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
      (SAT.restrictHead false f) sat))
toDirectFailure {c = c} (negative {f = f} answer sat) =
  Direct.falseNegative (Bridge.indexedToCook (SAT.restrictHead false f))
    (Bridge.indexedSatisfyingGivesCookSatisfiable (SAT.restrictHead false f) sat) answer
toDirectFailure (deeperFalse answer rest) = toDirectFailure rest
toDirectFailure (deeperTrue answer rest) = toDirectFailure rest

-- Follow one actual candidate query per variable; starting from a
-- genuine original witness, either the computed assignment verifies
-- or a queried formula has the wrong answer. No exact oracle assumed.
verifiedOrFailure : ∀ {cost n} (c : Candidate cost) (f : SAT.BooleanFormula n) →
  SAT.Satisfying f →
  (SAT.evaluate f (assignment c f) ≡ true) ⊎ TraceFailure c f
verifiedOrFailure {n = zero} c f sat =
  inj₁ (trans (SAT.evaluateExtensional f (λ ())) (SAT.evaluatesTrue sat))
verifiedOrFailure {n = suc n} c f sat with query c f in answer
... | true with Finite.decideFiniteSAT (SAT.restrictHead false f)
...   | inj₂ impossible = inj₂ (positive answer impossible)
...   | inj₁ child with verifiedOrFailure c (SAT.restrictHead false f) child
...     | inj₂ wrong = inj₂ (deeperFalse answer wrong)
...     | inj₁ ok = inj₁ (trans (sym (SAT.restrictionEvaluation false f
          (assignment c (SAT.restrictHead false f)))) ok)
verifiedOrFailure {n = suc n} c f sat | false with SAT.satisfiableSplits f sat
...   | inj₁ child = inj₂ (negative answer child)
...   | inj₂ child with verifiedOrFailure c (SAT.restrictHead true f) child
...     | inj₂ wrong = inj₂ (deeperTrue answer wrong)
...     | inj₁ ok = inj₁ (trans (sym (SAT.restrictionEvaluation true f
          (assignment c (SAT.restrictHead true f)))) ok)

missGivesActualDecisionFailure : ∀ {cost n} (c : Candidate cost)
  (f : SAT.BooleanFormula n) → SAT.Satisfying f →
  SAT.evaluate f (assignment c f) ≡ false → Direct.SATDecisionFailure c
missGivesActualDecisionFailure c f sat miss with verifiedOrFailure c f sat
... | inj₂ wrong = toDirectFailure wrong
... | inj₁ ok = ⊥-elim (Direct.falseNotTrue (trans (sym miss) ok))

pin : ∀ {n} → SAT.BooleanFormula n → Fin n → Bool → SAT.BooleanFormula n
pin f i true = SAT.conjunction f (SAT.formulaVar i)
pin f i false = SAT.conjunction f (SAT.negate (SAT.formulaVar i))

andTrueLeft : ∀ a b → SAT.andBool a b ≡ true → a ≡ true
andTrueLeft true b h = refl
andTrueLeft false b ()

pinWitnessParent : ∀ {n} (f : SAT.BooleanFormula n) (i : Fin n) (b : Bool) →
  SAT.Satisfying (pin f i b) → SAT.Satisfying f
pinWitnessParent f i true (SAT.satisfying x ok) =
  SAT.satisfying x (andTrueLeft (SAT.evaluate f x) (x i) ok)
pinWitnessParent f i false (SAT.satisfying x ok) =
  SAT.satisfying x (andTrueLeft (SAT.evaluate f x) (SAT.notBool (x i)) ok)

-- An original verified unit child supplies the missed-parent
-- inhabitedness, whether found by the same code or another verifier.
gainGivesActualDecisionFailure : ∀ {cost n} (c : Candidate cost)
  (f : SAT.BooleanFormula n) (i : Fin n) (b : Bool) →
  SAT.Satisfying (pin f i b) →
  SAT.evaluate f (assignment c f) ≡ false → Direct.SATDecisionFailure c
gainGivesActualDecisionFailure c f i b sat miss =
  missGivesActualDecisionFailure c f (pinWitnessParent f i b sat) miss

-- The exact decision-to-search query bound and size transport are
-- already owned by SATDecisionToWitnessSelfReductionExact and
-- PNotEqualsNPSATSelfReductionQueryVolumeExact. This error extractor
-- may use exponential finite SAT verification: it is NOT the
-- candidate's clock, nor a universal producer of missed sources.
