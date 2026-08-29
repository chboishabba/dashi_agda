module DASHI.Physics.YangMills.BalabanTerminalTransferKatoGapStabilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Martin Luescher,
-- "Construction of a Selfadjoint, Strictly Positive Transfer Matrix for
-- Euclidean Lattice Gauge Theories", Communications in Mathematical Physics
-- 54 (1977), 283--292. DOI: 10.1007/BF01614090.
--
-- DASHI CONTRIBUTION
--
-- On the SAME vacuum-orthogonal carrier, if a reference quadratic form has gap
-- m0 and the terminal physical form is bounded below by the reference form
-- minus epsilon ||v||^2, then
--
--   H_terminal[v] >= (m0-epsilon) ||v||^2.
--
-- A strict epsilon < m0 therefore gives a strict terminal gap. Positivity of
-- the transfer operator itself is never substituted for this spectral theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record TerminalGapPerturbationData (Vector : Set) : Set₁ where
  field
    normSq : Vector → ℚ
    ReferenceExcited TerminalExcited : Vector → Set

    referenceForm terminalForm : Vector → ℚ
    referenceGap perturbationLoss : ℚ

    normNonnegative : ∀ vector → 0ℚ ≤ normSq vector
    referenceGapNonnegative : 0ℚ ≤ referenceGap
    perturbationLossNonnegative : 0ℚ ≤ perturbationLoss

    sameExcitedCarrier : ∀ vector →
      ReferenceExcited vector → TerminalExcited vector

    referenceGapLower : ∀ vector →
      ReferenceExcited vector →
      referenceGap * normSq vector ≤ referenceForm vector

    terminalAboveReferenceMinusLoss : ∀ vector →
      ReferenceExcited vector →
      referenceForm vector - perturbationLoss * normSq vector
      ≤ terminalForm vector

open TerminalGapPerturbationData public

terminalGapCandidate : ∀ {Vector} → TerminalGapPerturbationData Vector → ℚ
terminalGapCandidate dataSet = referenceGap dataSet - perturbationLoss dataSet

referenceMinusLossReassociate : ∀ reference loss normValue →
  reference * normValue - loss * normValue
  ≡ (reference - loss) * normValue
referenceMinusLossReassociate = ℚRing.solve-∀

terminalGapLower :
  ∀ {Vector}
    (dataSet : TerminalGapPerturbationData Vector)
    vector → ReferenceExcited dataSet vector →
  terminalGapCandidate dataSet * normSq dataSet vector
  ≤ terminalForm dataSet vector
terminalGapLower dataSet vector excited =
  let
    n = normSq dataSet vector
    ref = referenceGap dataSet
    loss = perturbationLoss dataSet

    subtractLoss :
      ref * n - loss * n
      ≤ referenceForm dataSet vector - loss * n
    subtractLoss =
      let
        translated = ℚP.+-monoˡ-≤ (- (loss * n))
          (referenceGapLower dataSet vector excited)
      in
      subst
        (λ lower → lower ≤ referenceForm dataSet vector - loss * n)
        (sym (ℚRing.solve-∀ ref loss n))
        (subst
          (λ upper → ref * n + (- (loss * n)) ≤ upper)
          (ℚRing.solve-∀ (referenceForm dataSet vector) loss n)
          translated)

    physical = ℚP.≤-trans subtractLoss
      (terminalAboveReferenceMinusLoss dataSet vector excited)
  in
  subst
    (λ lower → lower ≤ terminalForm dataSet vector)
    (sym (referenceMinusLossReassociate ref loss n))
    physical

differencePositive : ∀ larger smaller →
  smaller < larger → 0ℚ < larger - smaller
differencePositive larger smaller smaller<larger =
  let
    left : ℚ
    left = - larger + larger
    right : ℚ
    right = - smaller + larger
    step : left < right
    step = ℚP.+-monoˡ-< larger
      (ℚP.neg-antimono-< smaller<larger)
    leftExact : left ≡ 0ℚ
    leftExact = ℚRing.solve-∀ larger
    rightExact : right ≡ larger - smaller
    rightExact = ℚRing.solve-∀ larger smaller
  in
  subst (λ selectedLeft → selectedLeft < larger - smaller)
    leftExact
    (subst (λ selectedRight → left < selectedRight)
      rightExact step)

strictLossLeavesPositiveGap :
  ∀ {Vector}
    (dataSet : TerminalGapPerturbationData Vector) →
  perturbationLoss dataSet < referenceGap dataSet →
  0ℚ < terminalGapCandidate dataSet
strictLossLeavesPositiveGap dataSet strictLoss =
  differencePositive
    (referenceGap dataSet) (perturbationLoss dataSet) strictLoss

record StrictTerminalGapWitness (Vector : Set) : Set₁ where
  field
    dataSet : TerminalGapPerturbationData Vector
    perturbationStrict :
      perturbationLoss dataSet < referenceGap dataSet
open StrictTerminalGapWitness public

strictTerminalGapPositive :
  ∀ {Vector} (witness : StrictTerminalGapWitness Vector) →
  0ℚ < terminalGapCandidate (dataSet witness)
strictTerminalGapPositive witness =
  strictLossLeavesPositiveGap (dataSet witness) (perturbationStrict witness)

strictTerminalGapQuadraticLower :
  ∀ {Vector} (witness : StrictTerminalGapWitness Vector)
    vector → ReferenceExcited (dataSet witness) vector →
  terminalGapCandidate (dataSet witness)
    * normSq (dataSet witness) vector
  ≤ terminalForm (dataSet witness) vector
strictTerminalGapQuadraticLower witness = terminalGapLower (dataSet witness)

terminalKatoQuadraticGapStabilityLevel : ProofLevel
terminalKatoQuadraticGapStabilityLevel = machineChecked

terminalKatoStrictGapAssemblyLevel : ProofLevel
terminalKatoStrictGapAssemblyLevel = machineChecked

-- Remaining physical terminal theorem: choose the reference form on the SAME
-- terminal Wilson/Luescher Hilbert carrier, prove its isolated-vacuum gap, and
-- bound the actual terminal RG form perturbation by epsilon < m0. Kato-style
-- stability then supplies the terminal gap consumed by the existing Feshbach
-- pullback recursion.
physicalTerminalReferenceGapAndPerturbationLevel : ProofLevel
physicalTerminalReferenceGapAndPerturbationLevel = conditional
