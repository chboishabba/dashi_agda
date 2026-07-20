module DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Balanced-ternary stream spine.
--
-- This module deliberately separates:
--   * the exact, finite, constructively checked stream/truncation layer; and
--   * the analytic completion obligations required to interpret
--       Φ(d) = Σ dₖ λᵏ
--     as a continuous Euclidean envelope.
--
-- It extends the existing finite p-adic carrier and prefix-ultrametric bridges
-- without claiming that the repository has constructed ℝ, an analytic p-adic
-- field, an infinite sum, or a smooth manifold.

------------------------------------------------------------------------
-- Primitive balanced ternary carrier

data Trit : Set where
  neg : Trit
  zer : Trit
  pos : Trit

involution : Trit → Trit
involution neg = pos
involution zer = zer
involution pos = neg

involution-involutive : (t : Trit) → involution (involution t) ≡ t
involution-involutive neg = refl
involution-involutive zer = refl
involution-involutive pos = refl

Stream : Set
Stream = Nat → Trit

tail : Stream → Stream
tail d k = d (suc k)

------------------------------------------------------------------------
-- Cylinder agreement: equality through a finite digit depth.

data PrefixAgreement : Nat → Stream → Stream → Set where
  prefix-zero :
    ∀ {x y : Stream} →
    PrefixAgreement zero x y

  prefix-suc :
    ∀ {n : Nat} {x y : Stream} →
    x zero ≡ y zero →
    PrefixAgreement n (tail x) (tail y) →
    PrefixAgreement (suc n) x y

prefix-refl :
  ∀ (n : Nat) (x : Stream) →
  PrefixAgreement n x x
prefix-refl zero x = prefix-zero
prefix-refl (suc n) x = prefix-suc refl (prefix-refl n (tail x))

------------------------------------------------------------------------
-- Exact finite prefixes and truncation.

data TritPrefix : Nat → Set where
  [] : TritPrefix zero
  _∷_ : ∀ {n : Nat} → Trit → TritPrefix n → TritPrefix (suc n)

infixr 5 _∷_

take : (n : Nat) → Stream → TritPrefix n
take zero d = []
take (suc n) d = d zero ∷ take n (tail d)

prefixAgreement→takeEquality :
  ∀ {n : Nat} {x y : Stream} →
  PrefixAgreement n x y →
  take n x ≡ take n y
prefixAgreement→takeEquality prefix-zero = refl
prefixAgreement→takeEquality (prefix-suc refl rest)
  rewrite prefixAgreement→takeEquality rest = refl

------------------------------------------------------------------------
-- A syntax-level finite envelope.
--
-- digit-at t k denotes the finite term t · λᵏ. No analytic scalar is selected
-- here, so this layer is exact and does not smuggle in convergence.

data EnvelopeTerm : Set where
  envelope-zero : EnvelopeTerm
  digit-at : Trit → Nat → EnvelopeTerm
  _⊕_ : EnvelopeTerm → EnvelopeTerm → EnvelopeTerm

infixl 6 _⊕_

finiteEnvelope : Nat → Stream → EnvelopeTerm
finiteEnvelope zero d = envelope-zero
finiteEnvelope (suc n) d = finiteEnvelope n d ⊕ digit-at (d n) n

finiteEnvelope-zero :
  (d : Stream) →
  finiteEnvelope zero d ≡ envelope-zero
finiteEnvelope-zero d = refl

finiteEnvelope-step :
  (n : Nat) (d : Stream) →
  finiteEnvelope (suc n) d
  ≡ finiteEnvelope n d ⊕ digit-at (d n) n
finiteEnvelope-step n d = refl

------------------------------------------------------------------------
-- First-difference witness.
--
-- This finite combinatorial datum is shared by the p-adic norm and the
-- depth-weighted metric: streams agree through n digits and differ at n.

data ⊥ : Set where

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record FirstDifferenceAt (n : Nat) (x y : Stream) : Set where
  constructor first-difference-at
  field
    agreeBefore : PrefixAgreement n x y
    differAt : x n ≢ y n

open FirstDifferenceAt public

------------------------------------------------------------------------
-- Analytic carrier interface.
--
-- A model supplies scalar operations plus the exact propositions used to
-- state convergence, metric representation, cylinder control, first-difference
-- bounds, topology recovery, and weighted summability. This keeps λ < 1/3
-- explicit and prevents any analytic result from being promoted by naming it.

record DepthKernelModel : Set₁ where
  field
    Scalar : Set

    zeroˢ : Scalar
    oneˢ : Scalar
    thirdˢ : Scalar
    lambda : Scalar

    _+ˢ_ : Scalar → Scalar → Scalar
    _*ˢ_ : Scalar → Scalar → Scalar
    negateˢ : Scalar → Scalar

    tritValue : Trit → Scalar
    lambdaPower : Nat → Scalar
    tritDistance : Trit → Trit → Scalar

    Positive : Scalar → Set
    LessThan : Scalar → Scalar → Set
    AtMost : Scalar → Scalar → Set

    Converges : (Nat → Scalar) → Scalar → Set
    IsWeightedDigitMetric : Stream → Stream → Scalar → Set
    CylinderControlled :
      Nat → Stream → Stream → Scalar → Scalar → Set
    FirstDifferenceBound : Nat → Scalar → Set
    MetricRecoversCylinder : Nat → Stream → Stream → Scalar → Set
    WeightedL2Summable :
      {Axis : Set} →
      (Axis → Scalar) →
      (Axis → Scalar) →
      Set

    powerZero : lambdaPower zero ≡ oneˢ
    powerStep :
      (n : Nat) →
      lambdaPower (suc n) ≡ lambdaPower n *ˢ lambda

    negativeTritValue : tritValue neg ≡ negateˢ oneˢ
    zeroTritValue : tritValue zer ≡ zeroˢ
    positiveTritValue : tritValue pos ≡ oneˢ

open DepthKernelModel public

finiteEvaluation :
  (M : DepthKernelModel) →
  Nat →
  Stream →
  Scalar M
finiteEvaluation M zero d = zeroˢ M
finiteEvaluation M (suc n) d =
  _+ˢ_ M
    (finiteEvaluation M n d)
    (_*ˢ_ M (tritValue M (d n)) (lambdaPower M n))

finiteEvaluation-step :
  (M : DepthKernelModel) →
  (n : Nat) →
  (d : Stream) →
  finiteEvaluation M (suc n) d
  ≡ _+ˢ_ M
      (finiteEvaluation M n d)
      (_*ˢ_ M (tritValue M (d n)) (lambdaPower M n))
finiteEvaluation-step M n d = refl

------------------------------------------------------------------------
-- Paper-safe continuous-envelope receipt.
--
-- The fields correspond to:
--   Φ(d) = Σ dₖ λᵏ,
--   dλ(x,y) = Σ |xₖ-yₖ| λᵏ,
--   cylinder continuity,
--   first-difference control,
--   injectivity under λ < 1/3,
--   and agreement of metric and prefix/cylinder nearness.
--
-- They are proofs required from an analytic instance, not global postulates.

record ContinuousDepthEnvelope
  (M : DepthKernelModel) : Set₁ where
  field
    embed : Stream → Scalar M
    depthMetric : Stream → Stream → Scalar M

    lambdaPositive : Positive M (lambda M)
    lambdaBelowOne : LessThan M (lambda M) (oneˢ M)
    lambdaBelowThird : LessThan M (lambda M) (thirdˢ M)

    finiteApproximantsConvergeToEmbed :
      (d : Stream) →
      Converges M
        (λ n → finiteEvaluation M n d)
        (embed d)

    depthMetricIsWeightedDigitSum :
      (x y : Stream) →
      IsWeightedDigitMetric M x y (depthMetric x y)

    cylinderContinuity :
      (n : Nat) →
      (x y : Stream) →
      PrefixAgreement n x y →
      CylinderControlled M n x y (embed x) (embed y)

    firstDifferenceControlsMetric :
      (n : Nat) →
      (x y : Stream) →
      FirstDifferenceAt n x y →
      FirstDifferenceBound M n (depthMetric x y)

    injectiveBelowThird :
      (x y : Stream) →
      embed x ≡ embed y →
      x ≡ y

    metricCylinderRecovery :
      (n : Nat) →
      (x y : Stream) →
      MetricRecoversCylinder M n x y (depthMetric x y)

open ContinuousDepthEnvelope public

------------------------------------------------------------------------
-- Multi-axis / weighted signal boundary.
--
-- For an infinite axis Ω, summability belongs to the analytic instance. The
-- finite depth truncation remains constructive coordinate-by-coordinate.

record WeightedSignalEnvelope
  (M : DepthKernelModel)
  (E : ContinuousDepthEnvelope M) : Set₁ where
  field
    Axis : Set
    axisWeight : Axis → Scalar M
    signal : Axis → Stream
    coordinateEnvelope : Axis → Scalar M

    coordinateEnvelopeMatchesEmbed :
      (ω : Axis) →
      coordinateEnvelope ω ≡ embed E (signal ω)

    weightedL2Summable :
      WeightedL2Summable M axisWeight coordinateEnvelope

open WeightedSignalEnvelope public

------------------------------------------------------------------------
-- Depth-prior / MDL boundary.
--
-- Model class n sees exactly the first n trits. The selected-depth receipt
-- states that fit plus complexity is minimal under the supplied cost model.
-- This is the robust connection to MDL; no smooth-norm claim is needed.

record DepthPriorMDLModel : Set₁ where
  field
    Cost : Set
    _≤ᶜ_ : Cost → Cost → Set
    _+ᶜ_ : Cost → Cost → Cost

    fitCost : Nat → Cost
    complexityCost : Nat → Cost

open DepthPriorMDLModel public

totalCost :
  (M : DepthPriorMDLModel) →
  Nat →
  Cost M
totalCost M n = _+ᶜ_ M (fitCost M n) (complexityCost M n)

record MinimalEffectiveDepth
  (M : DepthPriorMDLModel) : Set where
  constructor minimal-effective-depth
  field
    selectedDepth : Nat
    selectedIsMinimal :
      (candidateDepth : Nat) →
      _≤ᶜ_ M
        (totalCost M selectedDepth)
        (totalCost M candidateDepth)

open MinimalEffectiveDepth public

------------------------------------------------------------------------
-- Explicit governance / claim boundary

formalStatus : String
formalStatus =
  "finite balanced-ternary stream, prefix, truncation, involution, and finite depth-evaluation spine checked; analytic completion supplied only through typed proof obligations"

continuousEnvelopeStatement : String
continuousEnvelopeStatement =
  "Microstates are balanced-ternary streams. A continuous depth envelope uses Φ(d)=Σ d_k λ^k with 0<λ<1 and λ<1/3 for faithful separation; first-difference depth controls the weighted metric, coarse-graining truncates depth, and MDL selects minimal effective depth under a depth prior."

nonPromotionBoundary : String
nonPromotionBoundary =
  "This module does not claim that Z_3 is a smooth manifold, does not construct real infinite sums or an analytic p-adic field, and does not derive injectivity, topology equivalence, weighted l2 summability, or MDL optimality without an explicit ContinuousDepthEnvelope or related receipt."
