module DASHI.Physics.YangMills.BalabanAllScaleThermodynamicCutset where

------------------------------------------------------------------------
-- Exact theorem-facing cutset for J10--J11 and K1--K6.
--
-- The module is deliberately proof-relevant and fail-closed.  It does not
-- represent mathematical evidence by String values and it introduces no
-- postulates.  Every assembled conclusion below is obtained by applying a
-- named producer theorem carried by one coherent data record.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record AllScaleEffectiveActionData
    (Scale State Bound Operator : Set) : Set₁ where
  field
    state : Scale → State
    effectiveActionBound relevantCouplingBound polymerTailBound
      vacuumEnergyTailBound : Scale → Bound

    LessEqual : Bound → Bound → Set
    transitive : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c

    uniformEffectiveActionBound : Bound
    uniformRelevantCouplingBound : Bound
    totalIrrelevantPolymerBound : Bound
    totalVacuumEnergyVariation : Bound

    effectiveActionAtScale : ∀ scale →
      LessEqual (effectiveActionBound scale) uniformEffectiveActionBound
    relevantCouplingAtScale : ∀ scale →
      LessEqual (relevantCouplingBound scale) uniformRelevantCouplingBound
    irrelevantPolymerPartialTail : Nat → Bound
    irrelevantPolymerPartialBound : ∀ cutoff →
      LessEqual (irrelevantPolymerPartialTail cutoff) totalIrrelevantPolymerBound
    vacuumEnergyPartialTail : Nat → Bound
    vacuumEnergyPartialBound : ∀ cutoff →
      LessEqual (vacuumEnergyPartialTail cutoff) totalVacuumEnergyVariation

    Local GaugeInvariant Relevant Irrelevant : Operator → Set
    VacuumOperator GaugeCouplingOperator GaugeMassOperator : Operator

    localGaugeInvariantOperatorClassificationInput :
      ∀ operator → Local operator → GaugeInvariant operator →
      Relevant operator →
      (operator ≡ VacuumOperator) ⊎ (operator ≡ GaugeCouplingOperator)
    vacuumRelevant : Relevant VacuumOperator
    gaugeCouplingRelevant : Relevant GaugeCouplingOperator
    nonRelevantImpliesIrrelevant : ∀ operator →
      Local operator → GaugeInvariant operator →
      (Relevant operator → (operator ≡ VacuumOperator) ⊎
                            (operator ≡ GaugeCouplingOperator)) →
      Irrelevant operator
    wardIdentityExcludesGaugeMass :
      Relevant GaugeMassOperator →
      (GaugeMassOperator ≡ VacuumOperator) ⊎
      (GaugeMassOperator ≡ GaugeCouplingOperator) → ⊥

open AllScaleEffectiveActionData public

-- J10

effectiveActionUniformAtEveryScale :
  ∀ {Scale State Bound Operator : Set} →
  (dataSet : AllScaleEffectiveActionData Scale State Bound Operator) →
  ∀ scale → LessEqual dataSet (effectiveActionBound dataSet scale)
                              (uniformEffectiveActionBound dataSet)
effectiveActionUniformAtEveryScale = effectiveActionAtScale

relevantCouplingsUniformlyControlled :
  ∀ {Scale State Bound Operator : Set} →
  (dataSet : AllScaleEffectiveActionData Scale State Bound Operator) →
  ∀ scale → LessEqual dataSet (relevantCouplingBound dataSet scale)
                              (uniformRelevantCouplingBound dataSet)
relevantCouplingsUniformlyControlled = relevantCouplingAtScale

irrelevantPolymerNormSummable :
  ∀ {Scale State Bound Operator : Set} →
  (dataSet : AllScaleEffectiveActionData Scale State Bound Operator) →
  Σ Bound (λ total → ∀ cutoff →
    LessEqual dataSet (irrelevantPolymerPartialTail dataSet cutoff) total)
irrelevantPolymerNormSummable dataSet =
  totalIrrelevantPolymerBound dataSet , irrelevantPolymerPartialBound dataSet

vacuumEnergyRenormalizationConverges :
  ∀ {Scale State Bound Operator : Set} →
  (dataSet : AllScaleEffectiveActionData Scale State Bound Operator) →
  Σ Bound (λ total → ∀ cutoff →
    LessEqual dataSet (vacuumEnergyPartialTail dataSet cutoff) total)
vacuumEnergyRenormalizationConverges dataSet =
  totalVacuumEnergyVariation dataSet , vacuumEnergyPartialBound dataSet

-- J11

localGaugeInvariantOperatorClassification :
  ∀ {Scale State Bound Operator : Set} →
  (dataSet : AllScaleEffectiveActionData Scale State Bound Operator) →
  ∀ operator → Local dataSet operator → GaugeInvariant dataSet operator →
  Relevant dataSet operator →
  (operator ≡ VacuumOperator dataSet) ⊎
  (operator ≡ GaugeCouplingOperator dataSet)
localGaugeInvariantOperatorClassification =
  localGaugeInvariantOperatorClassificationInput

onlyVacuumAndGaugeCouplingRelevant :
  ∀ {Scale State Bound Operator : Set} →
  (dataSet : AllScaleEffectiveActionData Scale State Bound Operator) →
  ∀ operator → Local dataSet operator → GaugeInvariant dataSet operator →
  Relevant dataSet operator →
  (operator ≡ VacuumOperator dataSet) ⊎
  (operator ≡ GaugeCouplingOperator dataSet)
onlyVacuumAndGaugeCouplingRelevant =
  localGaugeInvariantOperatorClassification

allOtherLocalOperatorsIrrelevant :
  ∀ {Scale State Bound Operator : Set} →
  (dataSet : AllScaleEffectiveActionData Scale State Bound Operator) →
  ∀ operator → Local dataSet operator → GaugeInvariant dataSet operator →
  (Relevant dataSet operator →
    (operator ≡ VacuumOperator dataSet) ⊎
    (operator ≡ GaugeCouplingOperator dataSet)) →
  Irrelevant dataSet operator
allOtherLocalOperatorsIrrelevant = nonRelevantImpliesIrrelevant

wardIdentitiesExcludeGaugeMassTerm :
  ∀ {Scale State Bound Operator : Set} →
  (dataSet : AllScaleEffectiveActionData Scale State Bound Operator) →
  Relevant dataSet (GaugeMassOperator dataSet) →
  (GaugeMassOperator dataSet ≡ VacuumOperator dataSet) ⊎
  (GaugeMassOperator dataSet ≡ GaugeCouplingOperator dataSet) → ⊥
wardIdentitiesExcludeGaugeMassTerm = wardIdentityExcludesGaugeMass

record ThermodynamicLimitData
    (Volume Boundary TestTuple Value LimitPoint : Set) : Set₁ where
  field
    partitionFunction : Volume → Boundary → Value
    schwinger connectedSchwinger : Volume → Boundary → TestTuple → Value
    limitingSchwinger : TestTuple → Value

    Positive Finite : Value → Set
    Bound : Value → Value → Set
    transitive : ∀ {a b c} → Bound a b → Bound b c → Bound a c

    normalizationBound momentBound connectedBound distributionOrderBound : Value

    finiteVolumePartitionFunctionPositiveInput :
      ∀ volume boundary → Positive (partitionFunction volume boundary)
    finiteVolumePartitionFunctionFiniteInput :
      ∀ volume boundary → Finite (partitionFunction volume boundary)
    uniformFiniteVolumeNormalizationInput :
      ∀ volume boundary → Bound (partitionFunction volume boundary) normalizationBound
    normalizationIndependentOfVolumeInput :
      ∀ volume₁ volume₂ boundary →
      Bound (partitionFunction volume₁ boundary)
            (partitionFunction volume₂ boundary)

    uniformSchwingerMomentBoundInput :
      ∀ volume boundary tests → Bound (schwinger volume boundary tests) momentBound
    uniformConnectedSchwingerBoundInput :
      ∀ volume boundary tests →
      Bound (connectedSchwinger volume boundary tests) connectedBound
    uniformDistributionOrderInput :
      ∀ volume boundary tests → Bound (schwinger volume boundary tests) distributionOrderBound

    Equicontinuous Precompact : (Volume → Value) → Set
    finiteVolumeSchwingerEquicontinuousInput :
      ∀ boundary tests → Equicontinuous (λ volume → schwinger volume boundary tests)
    finiteVolumeSchwingerPrecompactInput :
      ∀ boundary tests → Precompact (λ volume → schwinger volume boundary tests)

    subsequence : Nat → Volume
    VolumesTendToInfinity : (Nat → Volume) → Set
    Converges : (Nat → Value) → Value → Set
    volumesTendToInfinityInput : VolumesTendToInfinity subsequence
    subsequenceSchwingerConvergesInput :
      ∀ boundary tests →
      Converges (λ n → schwinger (subsequence n) boundary tests)
                (limitingSchwinger tests)

    ClusterExpansionUnique : LimitPoint → Set
    realizesLimit : LimitPoint → (TestTuple → Value) → Set
    clusterExpansionInfiniteVolumeUniqueInput :
      ∀ point₁ point₂ → ClusterExpansionUnique point₁ →
      ClusterExpansionUnique point₂ → point₁ ≡ point₂
    compatibleThermodynamicLimitsCoincideInput :
      ∀ point₁ point₂ → realizesLimit point₁ limitingSchwinger →
      realizesLimit point₂ limitingSchwinger → point₁ ≡ point₂

    boundaryInfluence : Volume → Boundary → Boundary → TestTuple → Value
    boundaryDecayBound : Value
    boundaryInfluenceExponentiallySmallInput :
      ∀ volume boundary₁ boundary₂ tests →
      Bound (boundaryInfluence volume boundary₁ boundary₂ tests) boundaryDecayBound
    boundaryConditionComparisonBoundInput :
      ∀ volume boundary₁ boundary₂ tests →
      Bound (schwinger volume boundary₁ tests)
            (boundaryInfluence volume boundary₁ boundary₂ tests)

open ThermodynamicLimitData public

-- K1
finiteVolumePartitionFunctionPositive = finiteVolumePartitionFunctionPositiveInput
finiteVolumePartitionFunctionFinite = finiteVolumePartitionFunctionFiniteInput
uniformFiniteVolumeNormalization = uniformFiniteVolumeNormalizationInput
normalizationIndependentOfVolume = normalizationIndependentOfVolumeInput

-- K2
uniformSchwingerMomentBound = uniformSchwingerMomentBoundInput
uniformConnectedSchwingerBound = uniformConnectedSchwingerBoundInput
uniformDistributionOrder = uniformDistributionOrderInput

-- K3
finiteVolumeSchwingerEquicontinuous = finiteVolumeSchwingerEquicontinuousInput
finiteVolumeSchwingerPrecompact = finiteVolumeSchwingerPrecompactInput

-- K4
thermodynamicDiagonalSubsequence :
  ∀ {Volume Boundary TestTuple Value LimitPoint : Set} →
  (dataSet : ThermodynamicLimitData Volume Boundary TestTuple Value LimitPoint) →
  Nat → Volume
thermodynamicDiagonalSubsequence = subsequence

infiniteVolumeSubsequenceExists :
  ∀ {Volume Boundary TestTuple Value LimitPoint : Set} →
  (dataSet : ThermodynamicLimitData Volume Boundary TestTuple Value LimitPoint) →
  Σ (Nat → Volume) (λ selected → VolumesTendToInfinity dataSet selected)
infiniteVolumeSubsequenceExists dataSet =
  subsequence dataSet , volumesTendToInfinityInput dataSet

volumesTendToInfinity = volumesTendToInfinityInput
subsequenceSchwingerConverges = subsequenceSchwingerConvergesInput

-- K5
clusterExpansionInfiniteVolumeUnique = clusterExpansionInfiniteVolumeUniqueInput
compatibleThermodynamicLimitsCoincide = compatibleThermodynamicLimitsCoincideInput

infiniteVolumeLimitUnique :
  ∀ {Volume Boundary TestTuple Value LimitPoint : Set} →
  (dataSet : ThermodynamicLimitData Volume Boundary TestTuple Value LimitPoint) →
  ∀ point₁ point₂ → realizesLimit dataSet point₁ (limitingSchwinger dataSet) →
  realizesLimit dataSet point₂ (limitingSchwinger dataSet) → point₁ ≡ point₂
infiniteVolumeLimitUnique = compatibleThermodynamicLimitsCoincideInput

-- K6
boundaryInfluenceExponentiallySmall = boundaryInfluenceExponentiallySmallInput
boundaryConditionComparisonBound = boundaryConditionComparisonBoundInput

infiniteVolumeIndependentOfBoundaryConditions :
  ∀ {Volume Boundary TestTuple Value LimitPoint : Set} →
  (dataSet : ThermodynamicLimitData Volume Boundary TestTuple Value LimitPoint) →
  ∀ volume boundary₁ boundary₂ tests →
  Bound dataSet (schwinger dataSet volume boundary₁ tests)
                (boundaryDecayBound dataSet)
infiniteVolumeIndependentOfBoundaryConditions dataSet volume boundary₁ boundary₂ tests =
  transitive dataSet
    (boundaryConditionComparisonBoundInput dataSet volume boundary₁ boundary₂ tests)
    (boundaryInfluenceExponentiallySmallInput dataSet volume boundary₁ boundary₂ tests)

record AllScaleThermodynamicCertificate
    (Scale State Bound₁ Operator Volume Boundary TestTuple Value LimitPoint : Set)
    : Set₁ where
  field
    allScaleData : AllScaleEffectiveActionData Scale State Bound₁ Operator
    thermodynamicData : ThermodynamicLimitData Volume Boundary TestTuple Value LimitPoint
    effectiveActionUniform : ∀ scale →
      LessEqual allScaleData (effectiveActionBound allScaleData scale)
                            (uniformEffectiveActionBound allScaleData)
    polymerTailSummable : Σ Bound₁ (λ total → ∀ cutoff →
      LessEqual allScaleData (irrelevantPolymerPartialTail allScaleData cutoff) total)
    uniqueInfiniteVolume : ∀ point₁ point₂ →
      realizesLimit thermodynamicData point₁ (limitingSchwinger thermodynamicData) →
      realizesLimit thermodynamicData point₂ (limitingSchwinger thermodynamicData) →
      point₁ ≡ point₂

assembleAllScaleThermodynamicCertificate :
  ∀ {Scale State Bound₁ Operator Volume Boundary TestTuple Value LimitPoint : Set} →
  (allScaleData : AllScaleEffectiveActionData Scale State Bound₁ Operator) →
  (thermodynamicData : ThermodynamicLimitData Volume Boundary TestTuple Value LimitPoint) →
  AllScaleThermodynamicCertificate
    Scale State Bound₁ Operator Volume Boundary TestTuple Value LimitPoint
assembleAllScaleThermodynamicCertificate allScaleData thermodynamicData = record
  { allScaleData = allScaleData
  ; thermodynamicData = thermodynamicData
  ; effectiveActionUniform = effectiveActionUniformAtEveryScale allScaleData
  ; polymerTailSummable = irrelevantPolymerNormSummable allScaleData
  ; uniqueInfiniteVolume = infiniteVolumeLimitUnique thermodynamicData
  }

allScaleThermodynamicAssemblyLevel : ProofLevel
allScaleThermodynamicAssemblyLevel = machineChecked

allScaleThermodynamicAnalyticLeavesLevel : ProofLevel
allScaleThermodynamicAnalyticLeavesLevel = conditional
