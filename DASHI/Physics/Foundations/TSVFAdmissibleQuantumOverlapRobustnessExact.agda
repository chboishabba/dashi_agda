{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFAdmissibleQuantumOverlapRobustnessExact where

-- MAX-CUT: BIDIRECTIONALLY ADMISSIBLE HISTORIES -> SELECTED TSVF AMPLITUDES
-- -> EXACT FINITE TENSOR INNER PRODUCTS -> NORMALIZED RATIONAL ODDS.
--
-- Reuse ORIGINAL owners:
--  * DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact
--  * DASHI.Quantum.TSVF (Aharonov/Bergmann/Lebowitz and Aharonov/Vaidman)
--  * DASHI.Foundations.TwoBoundarySystem
--  * DASHI.Crypto.ShorFiniteVectorBornNormalizationExact (separate earlier
--    common-denominator normalization; no duplicate Shor theorem asserted)
--
-- Original physics: Aharonov, Cohen, Gruss, Landsberger (2014);
-- Aharonov, Cohen, Landsberger, Entropy 19(3):111 (2017), Eq.25.
--
-- The ORIGINAL bidirectional admissibility predicate proves that a history
-- satisfies both boundaries. It does NOT prove a nonzero complex amplitude.
-- The ORIGINAL TSVF quantum surface provides the projector-dependent
-- <post|P_h|pre> amplitude, normSquared, and ABL quotient interface.
--
-- This module does TWO distinct jobs:
-- (a) structural, but source-accurate, connection of the two original
--     interfaces plus actual two-outcome ABL denominator normalization laws;
-- (b) concrete *nontrivial* rational real two-level tensor amplitudes, exact
--     overlap and Born-normalized two-outcome mass, for ALL surviving k.
--
-- The finite environmental model is the rational real subspace of a qubit:
--    e_right = (5,0)/5, e_wrong = (3,4)/5,
--    <e_right|e_wrong> = 3/5, norm(e_i)=1,
--    |<e_right^tensor k|e_wrong^tensor k>|^2 = (9/25)^k.
-- Right/wrong unnormalized masses are 25^k and 9^k over one common
-- nonzero denominator 25^k+9^k. This is a genuinely normalized binary
-- rational distribution represented by its exact numerator/denominator.
--
-- This is NOT the full interacting 2017 pointer/environment physical source;
-- their disturbed gamma_1/gamma_2 factors, non-factorized environments,
-- exact postselected Born amplitudes, physical Hilbert and continuum 3+1/
-- OS time require further same-source construction. N-n is k below.
-- No ad hoc global time reversal, many-worlds ontology or Clay mass gap.
--
-- No postulates, metas, unsafes or termination bypasses locally.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Vec.Base using (Vec; []; _∷_)
open import Agda.Builtin.List using (List; []; _∷_) renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Data.Nat.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact as Bidi
import DASHI.Quantum.TSVF as TSVF

------------------------------------------------------------------------
-- SOURCE-AWARE BRIDGE. The original admissibleFromBoth predicate gives
-- which histories inhabit the selected boundary pair, BEFORE amplitudes.
-- Operators for those histories must be physically selected projectors.
------------------------------------------------------------------------

record AdmissibleTSVFQuantumSource
    (F : Bidi.BidirectionallyAdmissibleHistoryFibre)
    (Q : TSVF.QuantumSurface)
    (E : TSVF.TSVFEnsemble Q) : Set₁ where
  field
    initial : Bidi.InitialBoundary F
    final : Bidi.FinalBoundary F

    rightHistory wrongHistory : Bidi.History F
    rightAllowed :
      Bidi.admissibleFromBoth F initial final rightHistory
    wrongAllowed :
      Bidi.admissibleFromBoth F initial final wrongHistory

    -- A real projector construction must independently justify the map.
    projectorOf :
      (h : Bidi.History F) →
      Bidi.admissibleFromBoth F initial final h →
      TSVF.QuantumSurface.Operator Q

    -- Same actual ensemble E is used for both alternatives.
    -- Physical projectors/completeness and postselection are independently
    -- tested at the chosen source; no placeholder Set fields manufacture them.

open AdmissibleTSVFQuantumSource public

rightAmplitude :
  ∀ {F Q E} →
  AdmissibleTSVFQuantumSource F Q E →
  TSVF.QuantumSurface.Scalar Q
rightAmplitude {E = E} source =
  TSVF.transitionAmplitude E
    (projectorOf source (rightHistory source) (rightAllowed source))

wrongAmplitude :
  ∀ {F Q E} →
  AdmissibleTSVFQuantumSource F Q E →
  TSVF.QuantumSurface.Scalar Q
wrongAmplitude {E = E} source =
  TSVF.transitionAmplitude E
    (projectorOf source (wrongHistory source) (wrongAllowed source))

rightBornWeight :
  ∀ {F Q E} →
  AdmissibleTSVFQuantumSource F Q E →
  TSVF.QuantumSurface.Weight Q
rightBornWeight {Q = Q} source =
  TSVF.QuantumSurface.normSquared Q (rightAmplitude source)

wrongBornWeight :
  ∀ {F Q E} →
  AdmissibleTSVFQuantumSource F Q E →
  TSVF.QuantumSurface.Weight Q
wrongBornWeight {Q = Q} source =
  TSVF.QuantumSurface.normSquared Q (wrongAmplitude source)

-- ABL normalization: supply ONLY the operational scalar algebra and
-- genuinely positive denominator, not the desired normalized conclusion.
record TwoOutcomeABLAlgebra
    {F Q E}
    (source : AdmissibleTSVFQuantumSource F Q E) : Set₁ where
  field
    add : TSVF.QuantumSurface.Weight Q →
          TSVF.QuantumSurface.Weight Q →
          TSVF.QuantumSurface.Weight Q
    one : TSVF.QuantumSurface.Weight Q
    total : TSVF.QuantumSurface.Weight Q
    totalFromSource :
      total ≡ add (rightBornWeight source) (wrongBornWeight source)
    positiveTotal : TSVF.QuantumSurface.Positive Q total

    quotientAdditive :
      TSVF.QuantumSurface.divideWeight Q
        (add (rightBornWeight source) (wrongBornWeight source)) total
      ≡ add
          (TSVF.QuantumSurface.divideWeight Q
            (rightBornWeight source) total)
          (TSVF.QuantumSurface.divideWeight Q
            (wrongBornWeight source) total)
    quotientUnit :
      TSVF.QuantumSurface.divideWeight Q total total ≡ one

open TwoOutcomeABLAlgebra public

-- The normalized ABL/Born binary sum follows: not assumed as a field.
twoOutcomeABLNormalizes :
  ∀ {F Q E}
    (source : AdmissibleTSVFQuantumSource F Q E) →
    (laws : TwoOutcomeABLAlgebra source) →
  add laws
    (TSVF.QuantumSurface.divideWeight Q
      (rightBornWeight source) (total laws))
    (TSVF.QuantumSurface.divideWeight Q
      (wrongBornWeight source) (total laws))
  ≡ one laws
twoOutcomeABLNormalizes {Q = Q} source laws =
  trans
    (sym (quotientAdditive laws))
    (trans
      (cong (λ x → TSVF.QuantumSurface.divideWeight Q x (total laws))
        (sym (totalFromSource laws)))
      (quotientUnit laws))

------------------------------------------------------------------------
-- ACTUAL ORIGINAL TSVF ABL INTERFACE, NOT AN UNRELATED NEW PROBABILITY.
-- Projection and total are source-matched to the original measurement.
------------------------------------------------------------------------

record SourceMatchedABLMeasurement
    {F Q E}
    (source : AdmissibleTSVFQuantumSource F Q E)
    (laws : TwoOutcomeABLAlgebra source) : Set₁ where
  field
    measurement : TSVF.ProjectiveMeasurement Q
    rightOutcome wrongOutcome :
      TSVF.ProjectiveMeasurement.Outcome measurement

    rightProjectorMatches :
      TSVF.ProjectiveMeasurement.projector measurement rightOutcome
      ≡ projectorOf source (rightHistory source) (rightAllowed source)
    wrongProjectorMatches :
      TSVF.ProjectiveMeasurement.projector measurement wrongOutcome
      ≡ projectorOf source (wrongHistory source) (wrongAllowed source)

    measurementTotalMatches :
      TSVF.ProjectiveMeasurement.totalPathWeight measurement E
      ≡ total laws
    measurementPositive :
      TSVF.QuantumSurface.Positive Q
        (TSVF.ProjectiveMeasurement.totalPathWeight measurement E)

open SourceMatchedABLMeasurement public

selectedABLContext :
  ∀ {F Q E} {source : AdmissibleTSVFQuantumSource F Q E}
    {laws : TwoOutcomeABLAlgebra source} →
  (M : SourceMatchedABLMeasurement source laws) →
  TSVF.ABLContext Q (measurement M) E
selectedABLContext M =
  TSVF.ablContext (measurementPositive M)

rightABLEqualsOriginalSourceWeight :
  ∀ {F Q E}
    {source : AdmissibleTSVFQuantumSource F Q E}
    {laws : TwoOutcomeABLAlgebra source} →
  (M : SourceMatchedABLMeasurement source laws) →
  TSVF.ablProbability (selectedABLContext M) (rightOutcome M)
  ≡ TSVF.QuantumSurface.divideWeight Q
      (rightBornWeight source) (total laws)
rightABLEqualsOriginalSourceWeight {Q = Q} {E = E} M =
  cong₂ (TSVF.QuantumSurface.divideWeight Q)
    (cong (TSVF.transitionWeight E) (rightProjectorMatches M))
    (measurementTotalMatches M)

wrongABLEqualsOriginalSourceWeight :
  ∀ {F Q E}
    {source : AdmissibleTSVFQuantumSource F Q E}
    {laws : TwoOutcomeABLAlgebra source} →
  (M : SourceMatchedABLMeasurement source laws) →
  TSVF.ablProbability (selectedABLContext M) (wrongOutcome M)
  ≡ TSVF.QuantumSurface.divideWeight Q
      (wrongBornWeight source) (total laws)
wrongABLEqualsOriginalSourceWeight {Q = Q} {E = E} M =
  cong₂ (TSVF.QuantumSurface.divideWeight Q)
    (cong (TSVF.transitionWeight E) (wrongProjectorMatches M))
    (measurementTotalMatches M)

-- Normalization is now proved for the ORIGINAL TSVF.ablProbability path,
-- not a second ad hoc branch probability interface.
sourceMatchedOriginalABLNormalizes :
  ∀ {F Q E}
    {source : AdmissibleTSVFQuantumSource F Q E}
    {laws : TwoOutcomeABLAlgebra source} →
  (M : SourceMatchedABLMeasurement source laws) →
  add laws
    (TSVF.ablProbability (selectedABLContext M) (rightOutcome M))
    (TSVF.ablProbability (selectedABLContext M) (wrongOutcome M))
  ≡ one laws
sourceMatchedOriginalABLNormalizes {source = source} {laws = laws} M =
  trans
    (cong₂ (add laws)
      (rightABLEqualsOriginalSourceWeight M)
      (wrongABLEqualsOriginalSourceWeight M))
    (twoOutcomeABLNormalizes source laws)

------------------------------------------------------------------------
-- EXACT NONTRIVIAL 2-LEVEL REAL HILBERT SUBSPACE.
-- Coordinates are integer numerators over the common denominator 5;
-- this models a genuine rational 2-dimensional inner-product sector.
------------------------------------------------------------------------

record QubitNumerator : Set where
  constructor ket₂
  field
    x y : Nat

open QubitNumerator public

dot₂ : QubitNumerator → QubitNumerator → Nat
dot₂ a b = x a * x b + y a * y b

norm₂ : QubitNumerator → Nat
norm₂ a = dot₂ a a

epsRight epsWrong epsOrthogonal : QubitNumerator
epsRight = ket₂ 5 0
epsWrong = ket₂ 3 4
epsOrthogonal = ket₂ 0 5

rightNorm25 : norm₂ epsRight ≡ 25
rightNorm25 = refl

wrongNorm25 : norm₂ epsWrong ≡ 25
wrongNorm25 = refl

singleSiteDot15 : dot₂ epsRight epsWrong ≡ 15
singleSiteDot15 = refl

orthogonalDotZero : dot₂ epsRight epsOrthogonal ≡ zero
orthogonalDotZero = refl

-- Cross-multiplication of normalized single-site squared overlap:
-- (15/25)^2 = 9/25, no real-division axiom or unsolved meta.
singleSiteSquaredOverlapExactlyNineOverTwentyFive :
  (dot₂ epsRight epsWrong * dot₂ epsRight epsWrong) * 25
  ≡ 9 * (norm₂ epsRight * norm₂ epsWrong)
singleSiteSquaredOverlapExactlyNineOverTwentyFive = refl

-- A list of k independent environmental qubit factors is an actual
-- length-indexed tensor product. The dot product is multiplicative.
replicate : (q : QubitNumerator) (k : Nat) → Vec QubitNumerator k
replicate q zero = []
replicate q (suc k) = q ∷ replicate q k

tensorDot :
  ∀ {k} → Vec QubitNumerator k → Vec QubitNumerator k → Nat
tensorDot [] [] = 1
tensorDot (a ∷ as) (b ∷ bs) = dot₂ a b * tensorDot as bs

power : Nat → Nat → Nat
power base zero = 1
power base (suc k) = base * power base k

rightTensorNorm :
  (k : Nat) →
  tensorDot (replicate epsRight k) (replicate epsRight k)
  ≡ power 25 k
rightTensorNorm zero = refl
rightTensorNorm (suc k) =
  cong (λ z → 25 * z) (rightTensorNorm k)

wrongTensorNorm :
  (k : Nat) →
  tensorDot (replicate epsWrong k) (replicate epsWrong k)
  ≡ power 25 k
wrongTensorNorm zero = refl
wrongTensorNorm (suc k) =
  cong (λ z → 25 * z) (wrongTensorNorm k)

tensorOverlap :
  (k : Nat) →
  tensorDot (replicate epsRight k) (replicate epsWrong k)
  ≡ power 15 k
tensorOverlap zero = refl
tensorOverlap (suc k) =
  cong (λ z → 15 * z) (tensorOverlap k)

------------------------------------------------------------------------
-- THE NONTRIVIAL TENSOR QUANTUM OVERLAP IDENTITY.
-- Repeated inner products factor because the environmental state is a
-- tensor product. No "overlap" Boolean or arbitrary q parameter is used.
------------------------------------------------------------------------

tensorRearrange :
  ∀ (a b c d : Nat) →
    (a * b) * (c * d) ≡ (a * c) * (b * d)
tensorRearrange a b c d = solve (a ∷ₗ b ∷ₗ c ∷ₗ d ∷ₗ []ₗ)

tensorPowerMultiplicative :
  (a b k : Nat) →
  power a k * power b k ≡ power (a * b) k
tensorPowerMultiplicative a b zero = refl
tensorPowerMultiplicative a b (suc k) =
  trans
    (tensorRearrange a (power a k) b (power b k))
    (cong (λ v → (a * b) * v) (tensorPowerMultiplicative a b k))

-- (15/25)^(2k) = (9/25)^k. This is an exact cross-multiplication
-- identity between the unreduced and reduced rational squared overlaps.
tensorSquaredOverlapReduces :
  (k : Nat) →
  (power 15 k * power 15 k) * power 25 k
  ≡ power 9 k * (power 25 k * power 25 k)
tensorSquaredOverlapReduces k =
  trans
    (cong (λ v → v * power 25 k)
      (tensorPowerMultiplicative 15 15 k))
    (trans
      (tensorPowerMultiplicative 225 25 k)
      (trans
        (sym (tensorPowerMultiplicative 9 625 k))
        (cong (λ v → power 9 k * v)
          (sym (tensorPowerMultiplicative 25 25 k)))))

actualTensorSquaredOverlapIsNineOverTwentyFivePower :
  (k : Nat) →
  (tensorDot (replicate epsRight k) (replicate epsWrong k)
    * tensorDot (replicate epsRight k) (replicate epsWrong k))
    * power 25 k
  ≡ power 9 k *
      (tensorDot (replicate epsRight k) (replicate epsRight k)
        * tensorDot (replicate epsWrong k) (replicate epsWrong k))
actualTensorSquaredOverlapIsNineOverTwentyFivePower k
  rewrite tensorOverlap k
        | rightTensorNorm k
        | wrongTensorNorm k =
  tensorSquaredOverlapReduces k

------------------------------------------------------------------------
-- EXACT NORMALIZED FINITE BORN PROBABILITY (COMMON-DENOMINATOR FORM).
-- For k surviving registers and equal positive disturbed-factor prefactors:
--
--      odds(Right : Wrong) = 25^k : 9^k.
--      P_R = 25^k/(25^k+9^k), P_W = 9^k/(25^k+9^k).
--
-- The numerator sum equals the denominator by a *proof*; denominator
-- positivity and growing relative odds follow independently below.
------------------------------------------------------------------------

record BinaryRationalMass : Set where
  constructor binaryRationalMass
  field
    rightNumerator wrongNumerator denominator : Nat
    normalized :
      rightNumerator + wrongNumerator ≡ denominator
    denominatorPositive :
      suc zero ≤ denominator

open BinaryRationalMass public

rightRaw : Nat → Nat
rightRaw k = power 25 k

wrongRaw : Nat → Nat
wrongRaw k = power 9 k

rightTimes25 : (k : Nat) →
  rightRaw (suc k) ≡ 25 * rightRaw k
rightTimes25 k = refl

wrongTimes9 : (k : Nat) →
  wrongRaw (suc k) ≡ 9 * wrongRaw k
wrongTimes9 k = refl

oneAtMost25 : 1 ≤ 25
oneAtMost25 = s≤s z≤n

nineAtMost25 : 9 ≤ 25
nineAtMost25 = ℕₚ.m≤m+n 9 16

oneAtMostRightPower : (k : Nat) → 1 ≤ rightRaw k
oneAtMostRightPower zero = ℕₚ.≤-refl
oneAtMostRightPower (suc k) =
  ℕₚ.*-mono-≤ oneAtMost25 (oneAtMostRightPower k)

wrongAtMostRight : (k : Nat) → wrongRaw k ≤ rightRaw k
wrongAtMostRight zero = ℕₚ.≤-refl
wrongAtMostRight (suc k) =
  ℕₚ.*-mono-≤ nineAtMost25 (wrongAtMostRight k)

selectedBornMass : Nat → BinaryRationalMass
selectedBornMass k =
  binaryRationalMass
    (rightRaw k)
    (wrongRaw k)
    (rightRaw k + wrongRaw k)
    refl
    (ℕₚ.≤-trans (oneAtMostRightPower k)
      (ℕₚ.m≤m+n (rightRaw k) (wrongRaw k)))

selectedBornRightDominates :
  (k : Nat) →
  wrongNumerator (selectedBornMass k)
  ≤ rightNumerator (selectedBornMass k)
selectedBornRightDominates = wrongAtMostRight

selectedBornDenominatorIsSum :
  (k : Nat) →
  rightNumerator (selectedBornMass k)
    + wrongNumerator (selectedBornMass k)
  ≡ denominator (selectedBornMass k)
selectedBornDenominatorIsSum k = normalized (selectedBornMass k)

-- Explicit *strict* odds fixture, without assuming a gamma balance theorem
-- or calling this physical k an environment size from a real apparatus.
rightOddsAtZero : rightRaw 0 ≡ 1
rightOddsAtZero = refl

wrongOddsAtZero : wrongRaw 0 ≡ 1
wrongOddsAtZero = refl

rightOddsAtOne : rightRaw 1 ≡ 25
rightOddsAtOne = refl

wrongOddsAtOne : wrongRaw 1 ≡ 9
wrongOddsAtOne = refl

rightOddsAtTwo : rightRaw 2 ≡ 625
rightOddsAtTwo = refl

wrongOddsAtTwo : wrongRaw 2 ≡ 81
wrongOddsAtTwo = refl

rightOddsAtThree : rightRaw 3 ≡ 15625
rightOddsAtThree = refl

wrongOddsAtThree : wrongRaw 3 ≡ 729
wrongOddsAtThree = refl

-- Exact powers, nonzero denominator, source positivity and chosen Hilbert
-- overlap come from the SAME model, not a supplied desired robustness Bool.
-- Orthogonality is a distinct edge case (zero wrong branch) and does not
-- contradict logical admissibility of both histories.

------------------------------------------------------------------------
-- LARGE-BOUNDS VERSION WITH TWO INDEPENDENT DISTURBED-FACTOR WEIGHTS.
-- gammaRight/gammaWrong below are nonnegative BORN WEIGHTS, not
-- unspecified complex gamma amplitudes. Their physical derivation from
-- the original 2017 disturbed-environment states remains a separate leaf.
------------------------------------------------------------------------

weightedRightRaw : Nat → Nat → Nat
weightedRightRaw gammaRight k = gammaRight * rightRaw k

weightedWrongRaw : Nat → Nat → Nat
weightedWrongRaw gammaWrong k = gammaWrong * wrongRaw k

weightedBornMass :
  (gammaRight gammaWrong k : Nat) →
  1 ≤ gammaRight →
  BinaryRationalMass
weightedBornMass gammaRight gammaWrong k gammaRightPositive =
  binaryRationalMass
    (weightedRightRaw gammaRight k)
    (weightedWrongRaw gammaWrong k)
    (weightedRightRaw gammaRight k + weightedWrongRaw gammaWrong k)
    refl
    (ℕₚ.≤-trans
      (ℕₚ.*-mono-≤ gammaRightPositive (oneAtMostRightPower k))
      (ℕₚ.m≤m+n
        (weightedRightRaw gammaRight k)
        (weightedWrongRaw gammaWrong k)))

weightedBornNormalizes :
  (gammaRight gammaWrong k : Nat)
  (positive : 1 ≤ gammaRight) →
  rightNumerator (weightedBornMass gammaRight gammaWrong k positive)
    + wrongNumerator (weightedBornMass gammaRight gammaWrong k positive)
  ≡ denominator (weightedBornMass gammaRight gammaWrong k positive)
weightedBornNormalizes gammaRight gammaWrong k positive =
  normalized (weightedBornMass gammaRight gammaWrong k positive)

-- The cross-multiplication form of the wrong-branch upper bound
--   P_wrong <= (9/25)^k
-- after common positive denominators are cancelled.
-- No division under an unproved nonzero denominator is used.
wrongBornTailBoundCrossMultiplied :
  (k : Nat) →
  wrongRaw k * rightRaw k
  ≤ wrongRaw k * (rightRaw k + wrongRaw k)
wrongBornTailBoundCrossMultiplied k =
  ℕₚ.*-mono-≤ ℕₚ.≤-refl
    (ℕₚ.m≤m+n (rightRaw k) (wrongRaw k))

-- A zero wrong disturbance factor is an explicit infinite-odds branch,
-- not a division-by-zero theorem.
oneAtMostOne : 1 ≤ 1
oneAtMostOne = ℕₚ.≤-refl

zeroWrongFactorGivesZeroWrongMassCorrect :
  (k : Nat) →
  wrongNumerator (weightedBornMass 1 0 k oneAtMostOne)
  ≡ zero
zeroWrongFactorGivesZeroWrongMassCorrect k = refl

-- Disturbance factors can overwhelm any one finite redundancy regime.
-- At k=2 the selected right weight is 1*625 and wrong weight 100*81.
-- This concretely refutes the invalid conclusion "k positive => robust"
-- without a controlled gamma ratio.
adversarialWrongWeightAtTwo :
  weightedWrongRaw 100 2 ≡ 8100
adversarialWrongWeightAtTwo = refl

adversarialRightWeightAtTwo :
  weightedRightRaw 1 2 ≡ 625
adversarialRightWeightAtTwo = refl

adversarialWrongDominatesRightAtTwo :
  weightedRightRaw 1 2 ≤ weightedWrongRaw 100 2
adversarialWrongDominatesRightAtTwo =
  ℕₚ.m≤m+n 625 7475


-- One of the two original bidirectional toy histories can be compatible
-- and assigned *zero* quantum weight. Logical admissibility alone is
-- insufficient for nonzero postselection or finite division.
------------------------------------------------------------------------

zeroWeightCountermodel : Bidi.ToyHistory → Nat
zeroWeightCountermodel _ = zero

leftIsAllowedButZeroWeighted :
  Bidi.ToyBidiAdmissible
    Bidi.initialSource Bidi.detectorLeft Bidi.leftCompatibleHistory
  ×
  (zeroWeightCountermodel Bidi.leftCompatibleHistory ≡ zero)
leftIsAllowedButZeroWeighted = Bidi.leftHistoryAdmissible , refl

admissibleDoesNotForcePositiveWeight :
  (positiveFromAdmissible :
    Bidi.ToyBidiAdmissible
      Bidi.initialSource Bidi.detectorLeft Bidi.leftCompatibleHistory →
    Σ Nat (λ n →
      zeroWeightCountermodel Bidi.leftCompatibleHistory ≡ suc n)) →
  ⊥
admissibleDoesNotForcePositiveWeight positiveFromAdmissible
  with positiveFromAdmissible Bidi.leftHistoryAdmissible
... | n , ()
