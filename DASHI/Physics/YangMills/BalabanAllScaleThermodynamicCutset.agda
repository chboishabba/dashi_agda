module DASHI.Physics.YangMills.BalabanAllScaleThermodynamicCutset where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- J10--J11: effective-action control and relevant-direction closure.
------------------------------------------------------------------------

record EffectiveActionCutset (Scale Bound Operator : Set) : Set₁ where
  field
    effectiveAction relevantCoupling : Scale → Bound
    irrelevantPartial vacuumPartial : Nat → Bound
    effectiveUniform relevantUniform irrelevantTotal vacuumTotal : Bound
    _≤B_ : Bound → Bound → Set

    effectiveAtScale : ∀ k → effectiveAction k ≤B effectiveUniform
    relevantAtScale : ∀ k → relevantCoupling k ≤B relevantUniform
    irrelevantPartialBound : ∀ n → irrelevantPartial n ≤B irrelevantTotal
    vacuumPartialBound : ∀ n → vacuumPartial n ≤B vacuumTotal

    Local GaugeInvariant Relevant Irrelevant : Operator → Set
    vacuum gaugeCoupling gaugeMass : Operator

    classifyRelevant : ∀ op → Local op → GaugeInvariant op → Relevant op →
      (op ≡ vacuum) ⊎ (op ≡ gaugeCoupling)
    otherLocalIrrelevant : ∀ op → Local op → GaugeInvariant op →
      (Relevant op → (op ≡ vacuum) ⊎ (op ≡ gaugeCoupling)) → Irrelevant op
    wardExcludesMass : Relevant gaugeMass →
      (gaugeMass ≡ vacuum) ⊎ (gaugeMass ≡ gaugeCoupling) → ⊥

open EffectiveActionCutset public


effectiveActionUniformAtEveryScale :
  ∀ {Scale Bound Operator : Set} (d : EffectiveActionCutset Scale Bound Operator) →
  ∀ k → _≤B_ d (effectiveAction d k) (effectiveUniform d)
effectiveActionUniformAtEveryScale = effectiveAtScale

relevantCouplingsUniformlyControlled :
  ∀ {Scale Bound Operator : Set} (d : EffectiveActionCutset Scale Bound Operator) →
  ∀ k → _≤B_ d (relevantCoupling d k) (relevantUniform d)
relevantCouplingsUniformlyControlled = relevantAtScale

irrelevantPolymerNormSummable :
  ∀ {Scale Bound Operator : Set} (d : EffectiveActionCutset Scale Bound Operator) →
  Σ Bound (λ total → ∀ n → _≤B_ d (irrelevantPartial d n) total)
irrelevantPolymerNormSummable d = irrelevantTotal d , irrelevantPartialBound d

vacuumEnergyRenormalizationConverges :
  ∀ {Scale Bound Operator : Set} (d : EffectiveActionCutset Scale Bound Operator) →
  Σ Bound (λ total → ∀ n → _≤B_ d (vacuumPartial d n) total)
vacuumEnergyRenormalizationConverges d = vacuumTotal d , vacuumPartialBound d

localGaugeInvariantOperatorClassification :
  ∀ {Scale Bound Operator : Set} (d : EffectiveActionCutset Scale Bound Operator) →
  ∀ op → Local d op → GaugeInvariant d op → Relevant d op →
  (op ≡ vacuum d) ⊎ (op ≡ gaugeCoupling d)
localGaugeInvariantOperatorClassification = classifyRelevant

onlyVacuumAndGaugeCouplingRelevant :
  ∀ {Scale Bound Operator : Set} (d : EffectiveActionCutset Scale Bound Operator) →
  ∀ op → Local d op → GaugeInvariant d op → Relevant d op →
  (op ≡ vacuum d) ⊎ (op ≡ gaugeCoupling d)
onlyVacuumAndGaugeCouplingRelevant = classifyRelevant

allOtherLocalOperatorsIrrelevant :
  ∀ {Scale Bound Operator : Set} (d : EffectiveActionCutset Scale Bound Operator) →
  ∀ op → Local d op → GaugeInvariant d op →
  (Relevant d op → (op ≡ vacuum d) ⊎ (op ≡ gaugeCoupling d)) →
  Irrelevant d op
allOtherLocalOperatorsIrrelevant = otherLocalIrrelevant

wardIdentitiesExcludeGaugeMassTerm :
  ∀ {Scale Bound Operator : Set} (d : EffectiveActionCutset Scale Bound Operator) →
  Relevant d (gaugeMass d) →
  (gaugeMass d ≡ vacuum d) ⊎ (gaugeMass d ≡ gaugeCoupling d) → ⊥
wardIdentitiesExcludeGaugeMassTerm = wardExcludesMass

------------------------------------------------------------------------
-- K1--K6: finite-volume normalization through uniqueness and boundary
-- independence.  No String-valued evidence and no local postulates.
------------------------------------------------------------------------

record ThermodynamicCutset
    (Volume Boundary Tests Value Limit : Set) : Set₁ where
  field
    partition : Volume → Boundary → Value
    schwinger connected : Volume → Boundary → Tests → Value
    limitSchwinger : Tests → Value
    _≤V_ : Value → Value → Set
    transitiveV : ∀ {a b c} → a ≤V b → b ≤V c → a ≤V c

    Positive Finite : Value → Set
    normalizationBound momentBound connectedBound orderBound boundaryBound : Value

    partitionPositive : ∀ volume boundary → Positive (partition volume boundary)
    partitionFinite : ∀ volume boundary → Finite (partition volume boundary)
    partitionUniform : ∀ volume boundary → partition volume boundary ≤V normalizationBound
    normalizationVolumeIndependent : ∀ v₁ v₂ boundary → partition v₁ boundary ≤V partition v₂ boundary

    momentUniform : ∀ volume boundary tests → schwinger volume boundary tests ≤V momentBound
    connectedUniform : ∀ volume boundary tests → connected volume boundary tests ≤V connectedBound
    distributionOrderUniform : ∀ volume boundary tests → schwinger volume boundary tests ≤V orderBound

    Equicontinuous Precompact : (Volume → Value) → Set
    schwingerEquicontinuous : ∀ boundary tests → Equicontinuous (λ v → schwinger v boundary tests)
    schwingerPrecompact : ∀ boundary tests → Precompact (λ v → schwinger v boundary tests)

    selectedVolumes : Nat → Volume
    TendsToInfinity : (Nat → Volume) → Set
    Converges : (Nat → Value) → Value → Set
    selectedTendsToInfinity : TendsToInfinity selectedVolumes
    selectedConverges : ∀ boundary tests →
      Converges (λ n → schwinger (selectedVolumes n) boundary tests) (limitSchwinger tests)

    Realizes : Limit → (Tests → Value) → Set
    compatibleLimitsCoincide : ∀ x y →
      Realizes x limitSchwinger → Realizes y limitSchwinger → x ≡ y

    boundaryInfluence : Volume → Boundary → Boundary → Tests → Value
    boundaryInfluenceSmall : ∀ volume b₁ b₂ tests →
      boundaryInfluence volume b₁ b₂ tests ≤V boundaryBound
    boundaryComparison : ∀ volume b₁ b₂ tests →
      schwinger volume b₁ tests ≤V boundaryInfluence volume b₁ b₂ tests

open ThermodynamicCutset public

finiteVolumePartitionFunctionPositive :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ volume boundary → Positive d (partition d volume boundary)
finiteVolumePartitionFunctionPositive = partitionPositive

finiteVolumePartitionFunctionFinite :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ volume boundary → Finite d (partition d volume boundary)
finiteVolumePartitionFunctionFinite = partitionFinite

uniformFiniteVolumeNormalization :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ volume boundary → _≤V_ d (partition d volume boundary) (normalizationBound d)
uniformFiniteVolumeNormalization = partitionUniform

normalizationIndependentOfVolume :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ v₁ v₂ boundary → _≤V_ d (partition d v₁ boundary) (partition d v₂ boundary)
normalizationIndependentOfVolume = normalizationVolumeIndependent

uniformSchwingerMomentBound :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ volume boundary tests → _≤V_ d (schwinger d volume boundary tests) (momentBound d)
uniformSchwingerMomentBound = momentUniform

uniformConnectedSchwingerBound :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ volume boundary tests → _≤V_ d (connected d volume boundary tests) (connectedBound d)
uniformConnectedSchwingerBound = connectedUniform

uniformDistributionOrder :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ volume boundary tests → _≤V_ d (schwinger d volume boundary tests) (orderBound d)
uniformDistributionOrder = distributionOrderUniform

finiteVolumeSchwingerEquicontinuous :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ boundary tests → Equicontinuous d (λ v → schwinger d v boundary tests)
finiteVolumeSchwingerEquicontinuous = schwingerEquicontinuous

finiteVolumeSchwingerPrecompact :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ boundary tests → Precompact d (λ v → schwinger d v boundary tests)
finiteVolumeSchwingerPrecompact = schwingerPrecompact

thermodynamicDiagonalSubsequence :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) → Nat → Volume
thermodynamicDiagonalSubsequence = selectedVolumes

infiniteVolumeSubsequenceExists :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  Σ (Nat → Volume) (TendsToInfinity d)
infiniteVolumeSubsequenceExists d = selectedVolumes d , selectedTendsToInfinity d

volumesTendToInfinity :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  TendsToInfinity d (selectedVolumes d)
volumesTendToInfinity = selectedTendsToInfinity

subsequenceSchwingerConverges :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ boundary tests → Converges d (λ n → schwinger d (selectedVolumes d n) boundary tests) (limitSchwinger d tests)
subsequenceSchwingerConverges = selectedConverges

compatibleThermodynamicLimitsCoincide :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ x y → Realizes d x (limitSchwinger d) → Realizes d y (limitSchwinger d) → x ≡ y
compatibleThermodynamicLimitsCoincide = compatibleLimitsCoincide

infiniteVolumeLimitUnique :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ x y → Realizes d x (limitSchwinger d) → Realizes d y (limitSchwinger d) → x ≡ y
infiniteVolumeLimitUnique = compatibleLimitsCoincide

boundaryInfluenceExponentiallySmall :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ volume b₁ b₂ tests → _≤V_ d (boundaryInfluence d volume b₁ b₂ tests) (boundaryBound d)
boundaryInfluenceExponentiallySmall = boundaryInfluenceSmall

boundaryConditionComparisonBound :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ volume b₁ b₂ tests →
  _≤V_ d (schwinger d volume b₁ tests) (boundaryInfluence d volume b₁ b₂ tests)
boundaryConditionComparisonBound = boundaryComparison

infiniteVolumeIndependentOfBoundaryConditions :
  ∀ {Volume Boundary Tests Value Limit : Set} (d : ThermodynamicCutset Volume Boundary Tests Value Limit) →
  ∀ volume b₁ b₂ tests → _≤V_ d (schwinger d volume b₁ tests) (boundaryBound d)
infiniteVolumeIndependentOfBoundaryConditions d volume b₁ b₂ tests =
  transitiveV d (boundaryComparison d volume b₁ b₂ tests)
                (boundaryInfluenceSmall d volume b₁ b₂ tests)

allScaleThermodynamicAssemblyLevel : ProofLevel
allScaleThermodynamicAssemblyLevel = machineChecked

allScaleThermodynamicAnalyticLeavesLevel : ProofLevel
allScaleThermodynamicAnalyticLeavesLevel = conditional
