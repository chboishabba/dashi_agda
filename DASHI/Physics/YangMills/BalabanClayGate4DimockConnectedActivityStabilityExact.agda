module DASHI.Physics.YangMills.BalabanClayGate4DimockConnectedActivityStabilityExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Connected-polymer activity bound to volume-uniform stability.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - III. Convergence",
-- arXiv:1304.0705v1 [math-ph]. No DOI recorded.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Field Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Dimock's final theorem has the form
--
--   Z/Z0 = exp(sum_X H(X)),
--   |H(X)| <= g exp(-kappa d_M(X)),
--
-- followed by the rooted polymer summation that bounds the decay weights by
-- volume.  The finite algebra below proves this last passage exactly.  The
-- physical cluster expansion only has to supply the connected activities,
-- pointwise decay and rooted decay-sum estimate.
------------------------------------------------------------------------

record StabilityAlgebra (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    negate absolute exponential : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

    multiplyMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (multiply left right) (multiply lower upper)

    absoluteZero : absolute zero ≡ zero
    absoluteTriangle : ∀ left right →
      LessEqual (absolute (add left right))
        (add (absolute left) (absolute right))

    zeroRight : ∀ value → multiply value zero ≡ zero
    leftDistributive : ∀ factor left right →
      multiply factor (add left right)
      ≡ add (multiply factor left) (multiply factor right)

    valueBelowAbsolute : ∀ value → LessEqual value (absolute value)
    negativeAbsoluteBelowValue : ∀ value →
      LessEqual (negate (absolute value)) value

    negateAntitone : ∀ {left right} →
      LessEqual left right → LessEqual (negate right) (negate left)

    exponentialMonotone : ∀ {left right} →
      LessEqual left right →
      LessEqual (exponential left) (exponential right)

open StabilityAlgebra public

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

finiteSum :
  ∀ {Scalar} → StabilityAlgebra Scalar → List Scalar → Scalar
finiteSum algebra [] = zero algebra
finiteSum algebra (value ∷ values) =
  add algebra value (finiteSum algebra values)

absoluteFiniteSumBelowSumAbsolute :
  ∀ {Scalar}
    (algebra : StabilityAlgebra Scalar)
    values →
  LessEqual algebra
    (absolute algebra (finiteSum algebra values))
    (finiteSum algebra (mapList (absolute algebra) values))
absoluteFiniteSumBelowSumAbsolute algebra [] =
  subst
    (λ lower → LessEqual algebra lower (zero algebra))
    (sym (absoluteZero algebra))
    (reflexive algebra (zero algebra))
absoluteFiniteSumBelowSumAbsolute algebra (value ∷ values) =
  transitive algebra
    (absoluteTriangle algebra value (finiteSum algebra values))
    (addMonotone algebra
      (reflexive algebra (absolute algebra value))
      (absoluteFiniteSumBelowSumAbsolute algebra values))

finiteSumPointwiseMonotone :
  ∀ {A Scalar}
    (algebra : StabilityAlgebra Scalar)
    (lower upper : A → Scalar)
    values →
  (∀ value → LessEqual algebra (lower value) (upper value)) →
  LessEqual algebra
    (finiteSum algebra (mapList lower values))
    (finiteSum algebra (mapList upper values))
finiteSumPointwiseMonotone algebra lower upper [] estimate =
  reflexive algebra (zero algebra)
finiteSumPointwiseMonotone algebra lower upper (value ∷ values) estimate =
  addMonotone algebra
    (estimate value)
    (finiteSumPointwiseMonotone algebra lower upper values estimate)

leftMultiplyFiniteSum :
  ∀ {Scalar}
    (algebra : StabilityAlgebra Scalar)
    factor values →
  multiply algebra factor (finiteSum algebra values)
  ≡ finiteSum algebra (mapList (multiply algebra factor) values)
leftMultiplyFiniteSum algebra factor [] = zeroRight algebra factor
leftMultiplyFiniteSum algebra factor (value ∷ values) =
  trans
    (leftDistributive algebra factor value (finiteSum algebra values))
    (cong
      (add algebra (multiply algebra factor value))
      (leftMultiplyFiniteSum algebra factor values))

record ConnectedActivityStabilityData
    (Polymer Scalar : Set) : Set₁ where
  field
    algebra : StabilityAlgebra Scalar
    polymers : List Polymer

    activity decayWeight : Polymer → Scalar
    coupling volume : Scalar

    activityDecay : ∀ polymer →
      LessEqual algebra
        (absolute algebra (activity polymer))
        (multiply algebra coupling (decayWeight polymer))

    decaySumBelowVolume :
      LessEqual algebra
        (finiteSum algebra (mapList decayWeight polymers))
        volume

  totalActivity : Scalar
  totalActivity = finiteSum algebra (mapList activity polymers)

open ConnectedActivityStabilityData public

connectedActivityBelowCouplingVolume :
  ∀ {Polymer Scalar}
    (dataSet : ConnectedActivityStabilityData Polymer Scalar) →
  LessEqual (algebra dataSet)
    (absolute (algebra dataSet) (totalActivity dataSet))
    (multiply (algebra dataSet)
      (coupling dataSet) (volume dataSet))
connectedActivityBelowCouplingVolume dataSet =
  transitive (algebra dataSet)
    (absoluteFiniteSumBelowSumAbsolute
      (algebra dataSet)
      (mapList (activity dataSet) (polymers dataSet)))
    (transitive (algebra dataSet)
      (finiteSumPointwiseMonotone
        (algebra dataSet)
        (λ polymer → absolute (algebra dataSet) (activity dataSet polymer))
        (λ polymer →
          multiply (algebra dataSet)
            (coupling dataSet) (decayWeight dataSet polymer))
        (polymers dataSet)
        (activityDecay dataSet))
      (subst
        (λ lower → LessEqual (algebra dataSet) lower
          (multiply (algebra dataSet)
            (coupling dataSet) (volume dataSet)))
        (leftMultiplyFiniteSum
          (algebra dataSet)
          (coupling dataSet)
          (mapList (decayWeight dataSet) (polymers dataSet)))
        (multiplyMonotone (algebra dataSet)
          (reflexive (algebra dataSet) (coupling dataSet))
          (decaySumBelowVolume dataSet))))

record ExponentiatedStabilityData
    {Polymer Scalar : Set}
    (connected : ConnectedActivityStabilityData Polymer Scalar) : Set₁ where
  field
    partitionRatio : Scalar
    partitionRatioMeaning :
      partitionRatio
      ≡ exponential (algebra connected) (totalActivity connected)

open ExponentiatedStabilityData public

partitionRatioUpperStability :
  ∀ {Polymer Scalar}
    {connected : ConnectedActivityStabilityData Polymer Scalar} →
  (dataSet : ExponentiatedStabilityData connected) →
  LessEqual (algebra connected)
    (partitionRatio dataSet)
    (exponential (algebra connected)
      (multiply (algebra connected)
        (coupling connected) (volume connected)))
partitionRatioUpperStability {connected = connected} dataSet =
  subst
    (λ lower → LessEqual (algebra connected) lower
      (exponential (algebra connected)
        (multiply (algebra connected)
          (coupling connected) (volume connected))))
    (sym (partitionRatioMeaning dataSet))
    (exponentialMonotone (algebra connected)
      (transitive (algebra connected)
        (valueBelowAbsolute (algebra connected)
          (totalActivity connected))
        (connectedActivityBelowCouplingVolume connected)))

partitionRatioLowerStability :
  ∀ {Polymer Scalar}
    {connected : ConnectedActivityStabilityData Polymer Scalar} →
  (dataSet : ExponentiatedStabilityData connected) →
  LessEqual (algebra connected)
    (exponential (algebra connected)
      (negate (algebra connected)
        (multiply (algebra connected)
          (coupling connected) (volume connected))))
    (partitionRatio dataSet)
partitionRatioLowerStability {connected = connected} dataSet =
  subst
    (λ upper → LessEqual (algebra connected)
      (exponential (algebra connected)
        (negate (algebra connected)
          (multiply (algebra connected)
            (coupling connected) (volume connected))))
      upper)
    (sym (partitionRatioMeaning dataSet))
    (exponentialMonotone (algebra connected)
      (transitive (algebra connected)
        (negateAntitone (algebra connected)
          (connectedActivityBelowCouplingVolume connected))
        (negativeAbsoluteBelowValue (algebra connected)
          (totalActivity connected))))

dimockConnectedActivityVolumeBoundLevel : ProofLevel
dimockConnectedActivityVolumeBoundLevel = machineChecked

dimockExponentiatedStabilityAssemblyLevel : ProofLevel
dimockExponentiatedStabilityAssemblyLevel = machineChecked

dimockConvergenceAndStabilitySourceLevel : ProofLevel
dimockConvergenceAndStabilitySourceLevel = standardImported

physicalYangMillsConnectedActivityDecayInputsLevel : ProofLevel
physicalYangMillsConnectedActivityDecayInputsLevel = conditional

physicalYangMillsRootedDecaySumInputsLevel : ProofLevel
physicalYangMillsRootedDecaySumInputsLevel = conditional
