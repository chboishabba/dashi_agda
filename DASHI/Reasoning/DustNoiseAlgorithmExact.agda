module DASHI.Reasoning.DustNoiseAlgorithmExact where

-- SOURCE-BOUNDED ALGORITHMIC SPECIFICATION
-- Original Dust: Dahal, Mandal, Gulbahar, Vegesna (2026), equations (1)-(4).
-- Noise challenge: Gulbahar, Mandal, Vegesna, Dahal + attributed contributors.
-- DASHI owns these typed definitions / structural derivations only.
-- This is not a kernel receipt or empirical reproduction.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.List using (List; []; _∷_)

-- Parametric scalar arithmetic preserves the declared exact equation
-- without equating scientific real-number numerics to natural arithmetic.
record ScalarOps : Set₁ where
  field
    S : Set
    zeroS : S
    add : S → S → S
    mul : S → S → S
    neg : S → S
    invNonzero : S → S
open ScalarOps

record ForwardOnlyTrace (A : ScalarOps) (Token Layer Draw : Set) : Set₁ where
  open ScalarOps A
  field
    -- Published Dust uses the MEAN PERTURBED loss at this token,
    -- not the clean/baseline loss.
    populationMeanPerturbedLoss : Token → S
    perturbedTokenLoss : Draw → Token → S
    populationCenteredTokenLoss : Draw → Token → S
    noise : Layer → Draw → Token → S
    creditDecay : Layer → S
    futureWeight : Layer → Token → Token → S
    futureReward : Layer → Draw → Token → S
    -- Finite sum and causal ordering are kept explicit rather than implicit.
    sumFuture : (Token → S) → Token → S
    sumDraws : (Draw → S) → S
    sumTokens : (Token → S) → S
    populationInverse : S
    sigmaInverse : S
    futureRewardEquation :
      (l : Layer) (k : Draw) (t : Token) →
      futureReward l k t ≡
        sumFuture
          (λ s → mul (futureWeight l t s)
            (populationCenteredTokenLoss k s)) t
    centeredRewardDefinition :
      (k : Draw) (t : Token) →
      populationCenteredTokenLoss k t ≡
        add (populationMeanPerturbedLoss t) (neg (perturbedTokenLoss k t))
    provenance : String
open ForwardOnlyTrace

-- Dust eq (2), with loss reduction convention explicitly negative:
-- ghat_t = - (1/(K*sigma)) sum_i r_t^i a_t^i
dustActivationCredit :
  {A : ScalarOps} {T L K : Set} →
  ForwardOnlyTrace A T L K → L → T → S A
dustActivationCredit {A} p l t =
  let open ScalarOps A in
  neg (mul
    (mul (populationInverse p) (sigmaInverse p))
    (sumDraws p (λ k → mul (futureReward p l k t) (noise p l k t))))

record WeightUpdate (A : ScalarOps) (Token Layer Draw : Set) : Set₁ where
  open ScalarOps A
  field
    forward : ForwardOnlyTrace A Token Layer Draw
    layerInput : Layer → Token → S
    -- Scalar coordinate of the outer product ghat_t * input_t.
    perTokenWeightCoordinate : Layer → Token → S
    weightCoordinate : Layer → S
    outerProductLaw :
      (l : Layer) (t : Token) →
      perTokenWeightCoordinate l t ≡
        mul (dustActivationCredit forward l t) (layerInput l t)
    aggregateLaw :
      (l : Layer) →
      weightCoordinate l ≡
        sumTokens forward (perTokenWeightCoordinate l)
    sumCongruence :
      (l : Layer) →
      sumTokens forward (perTokenWeightCoordinate l) ≡
        sumTokens forward
          (λ t → mul (dustActivationCredit forward l t) (layerInput l t))
    provenance : String
open WeightUpdate

-- Substitution yields the source equation (3); no gradient validity
-- is inferred from defining an estimator.
dustOuterProductEquation :
  {A : ScalarOps} {T L K : Set}
  (p : WeightUpdate A T L K) (l : L) →
  weightCoordinate p l ≡
    sumTokens (forward p)
      (λ t → mul (dustActivationCredit (forward p) l t)
                   (layerInput p l t))
dustOuterProductEquation p l =
  trans (aggregateLaw p l)
    (sumCongruence p l)

-- Separately typed attention-local surrogate: Dust eq (4).
record AttentionCredit (A : ScalarOps) (Token Layer Draw : Set) : Set₁ where
  open ScalarOps A
  field
    outputCredit : Layer → Token → S
    outputDisplacement : Layer → Draw → Token → S
    attentionScore : Layer → Draw → Token → S
    attentionScoreEquation :
      (l : Layer) (k : Draw) (t : Token) →
      attentionScore l k t ≡
        neg (mul (outputCredit l t)
                 (outputDisplacement l k t))
    -- Channel/heads and tokenwise causality cannot be erased by scalar notation.
    causalHeadScopeDeclared : Bool
    provenance : String
open AttentionCredit

-- Population mean is a separately supplied finite-sum contract; zero-sum
-- centering cannot be inferred merely from the name of a function.
-- The source permits different estimation paths for the head and for
-- 2L residual mixing scalars; these must not be called activation Dust.
data EstimatorPath : Set where
  directActivation : EstimatorPath
  attentionSurrogate : EstimatorPath
  cachedLogitHead : EstimatorPath
  residualScalarWeightES : EstimatorPath

record NoiseProbeSchedule (A : ScalarOps) (Direction Coordinate : Set) : Set₁ where
  open ScalarOps A
  field
    probe : Direction → Coordinate → S
    sumDirections : (Direction → S) → S
    dimension : S
    kronecker : Coordinate → Coordinate → S
    orthogonality :
      (i j : Coordinate) →
      sumDirections (λ k → mul (probe k i) (probe k j))
      ≡ mul dimension (kronecker i j)
    designProvenance : String
open NoiseProbeSchedule

-- An orthogonal direction set is a complete-frame certificate, NOT
-- a statement that all forward evaluations are independent or cheap.
record AlgorithmReceipt : Set where
  field
    usesForwardEvaluations : Bool
    usesReverseAD : Bool
    actualBenchmarkRun : Bool
    sameArchAndDataset : Bool
    sourceRevision : String
    contributionOwners : String
    timeBoundary : String
