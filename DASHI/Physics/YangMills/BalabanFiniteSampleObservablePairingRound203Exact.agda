{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteSampleObservablePairingRound203Exact where

------------------------------------------------------------------------
-- ROUND203 BIDI CORRECTION: FINITE SAMPLE != EXHAUSTIVE FINITE SELECTOR.
--
-- `BalabanP33PhysicalCoordinateBasisExact.FiniteSelector A` is intentionally
-- strong: `selectorExact` must recover `value target` for EVERY target : A.
-- It is therefore an exhaustive finite-coordinate presentation, not merely a
-- chosen finite ensemble.
--
-- R197 used that carrier for rooted gauge configurations while simultaneously
-- saying it was only a finite selected ensemble.  For a compact-group lattice
-- configuration space those meanings must stay separate.
--
-- This owner provides the weaker sample-local object actually justified by a
-- finite list.  No theorem here says the full configuration carrier is finite,
-- and zero sampled norm has no authority outside the sampled list.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis

record FiniteSample (A : Set) : Set where
  field
    elements : List A

open FiniteSample public

samplePairing :
  ∀ {A : Set} → FiniteSample A →
  (A → ℚ) → (A → ℚ) → ℚ
samplePairing sample left right =
  Sums.sumRational (elements sample)
    (λ state → left state * right state)

sampleNormSq :
  ∀ {A : Set} → FiniteSample A → (A → ℚ) → ℚ
sampleNormSq sample observable = samplePairing sample observable observable

samplePairingSymmetric :
  ∀ {A : Set} (sample : FiniteSample A) left right →
  samplePairing sample left right ≡ samplePairing sample right left
samplePairingSymmetric sample left right =
  Sums.sumRationalCong (elements sample) _ _
    (λ state → ℚRing.solve-∀ (left state) (right state))

sumRationalAdd :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  Sums.sumRational values (λ value → left value + right value)
  ≡ Sums.sumRational values left + Sums.sumRational values right
sumRationalAdd [] left right = refl
sumRationalAdd (value ∷ values) left right
  rewrite sumRationalAdd values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (Sums.sumRational values left)
    (Sums.sumRational values right)

samplePairingAdditiveLeft :
  ∀ {A : Set} (sample : FiniteSample A) left middle right →
  samplePairing sample (λ state → left state + middle state) right
  ≡ samplePairing sample left right + samplePairing sample middle right
samplePairingAdditiveLeft sample left middle right =
  trans
    (Sums.sumRationalCong (elements sample) _ _
      (λ state → ℚRing.solve-∀
        (left state) (middle state) (right state)))
    (sumRationalAdd (elements sample)
      (λ state → left state * right state)
      (λ state → middle state * right state))

-- One sound sample-local implication: if the observable vanishes on each listed
-- sample occurrence, then its sampled norm is zero.  The converse is not used
-- here to infer anything about unsampled configurations.
samplePointwiseZeroImpliesNormZero :
  ∀ {A : Set} (sample : FiniteSample A) (observable : A → ℚ) →
  (∀ state → observable state ≡ 0ℚ) →
  sampleNormSq sample observable ≡ 0ℚ
samplePointwiseZeroImpliesNormZero sample observable pointwise =
  trans
    (Sums.sumRationalCong (elements sample) _ (λ _ → 0ℚ)
      (λ state →
        cong (λ value → value * value) (pointwise state)))
    (zeroSum (elements sample))
  where
    zeroSum : ∀ {A : Set} (values : List A) →
      Sums.sumRational values (λ _ → 0ℚ) ≡ 0ℚ
    zeroSum [] = refl
    zeroSum (_ ∷ values) rewrite zeroSum values = refl

-- An exhaustive selector may of course be forgotten to a sample.  There is no
-- reverse constructor: a finite sample is intentionally weaker.
selectorAsSample :
  ∀ {A : Set} → Basis.FiniteSelector A → FiniteSample A
selectorAsSample selector = record
  { elements = Basis.elements selector }

finiteSampleObservablePairingRound203Level : ProofLevel
finiteSampleObservablePairingRound203Level = machineChecked

finiteSampleExhaustiveSelectorSeparationRound203Level : ProofLevel
finiteSampleExhaustiveSelectorSeparationRound203Level = machineChecked

-- Physical L2 remains an analytic measure/completion problem, not a finite-list
-- theorem.
literalPhysicalHaarGibbsL2FromFiniteSampleRound203Level : ProofLevel
literalPhysicalHaarGibbsL2FromFiniteSampleRound203Level = conditional
