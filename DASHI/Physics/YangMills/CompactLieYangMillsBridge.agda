module DASHI.Physics.YangMills.CompactLieYangMillsBridge where

-- Generic group-dependent inputs for the Balaban/Yang--Mills lane.  This file
-- states the exact promotion boundary from an SU(2) carrier to an arbitrary
-- compact simple Lie group without claiming the analytic obligations are solved.

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieGroupGeometry
open import DASHI.Physics.YangMills.CompactLieRepresentationData

record CompactLieGaugeTheoryData
    {g a s r : Level}
    {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    (K : CompactSimpleLieGroup G 𝔤)
    (S : OrderedScalar Scalar) : Set (lsuc (g ⊔ a ⊔ s ⊔ r)) where
  field
    metric : InvariantLieMetric K S
    chart : UniformLieChart K S metric
    roots : RootStructureData K S
    haarData : HaarMeasureData K S
    characters : CharacterEstimateData {r = r} K S

    Lattice Field GaugeTransformation Block Scale : Set
    gaugeAction : GaugeTransformation → Field → Field
    blockAverage : Block → Field → Field

    GaugeActionLaw : Set
    GaugeFixingSlice : Set
    FaddeevPopovCoercivity : Set
    BlockAverageEquivariance : Set
    SmallFieldChartCompatibility : Set
    LargeFieldSuppression : Set
    PolymerDiameterEntropy : Set
    ReflectionPositivity : Set
    ClusterDecomposition : Set

    gaugeActionLaw : GaugeActionLaw
    gaugeFixingSlice : GaugeFixingSlice
    faddeevPopovCoercivity : FaddeevPopovCoercivity
    blockAverageEquivariance : BlockAverageEquivariance
    smallFieldChartCompatibility : SmallFieldChartCompatibility
    largeFieldSuppression : LargeFieldSuppression
    polymerDiameterEntropy : PolymerDiameterEntropy
    reflectionPositivity : ReflectionPositivity
    clusterDecomposition : ClusterDecomposition

open CompactLieGaugeTheoryData public

record ScaleUniformCompactLieRG
    {g a s r : Level}
    {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    (K : CompactSimpleLieGroup G 𝔤)
    (S : OrderedScalar Scalar)
    (D : CompactLieGaugeTheoryData {r = r} K S) : Set (lsuc (g ⊔ a ⊔ s ⊔ r)) where
  field
    GapConstant : Set s
    massGap : GapConstant

    PositiveGap : GapConstant → Set s
    gapPositive : PositiveGap massGap

    ScaleUniform VolumeUniform BackgroundUniform : Set
    scaleUniform : ScaleUniform
    volumeUniform : VolumeUniform
    backgroundUniform : BackgroundUniform

    OneStepRenormalizationGroup : Set
    IteratedRenormalizationGroup : Set
    InfiniteVolumeLimit : Set
    ExponentialClustering : Set

    oneStepRG : OneStepRenormalizationGroup
    iteratedRG : IteratedRenormalizationGroup
    infiniteVolumeLimit : InfiniteVolumeLimit
    exponentialClustering : ExponentialClustering

open ScaleUniformCompactLieRG public

record SU2SpecializationBoundary : Set₁ where
  field
    QuaternionCarrier : Set
    GenericCarrier : Set
    QuaternionRealizesGenericGroup : Set
    QuaternionAdjointMatchesGenericAd : Set
    SU2ConstantsInstantiateGroupConstants : Set

    quaternionCarrier : QuaternionCarrier
    genericCarrier : GenericCarrier
    quaternionRealizesGenericGroup : QuaternionRealizesGenericGroup
    quaternionAdjointMatchesGenericAd : QuaternionAdjointMatchesGenericAd
    su2ConstantsInstantiateGroupConstants : SU2ConstantsInstantiateGroupConstants

open SU2SpecializationBoundary public

record CompactLiePromotionBoundary : Set₁ where
  field
    su2ProofsAreOneInstantiation : Set
    quaternionPolynomialIdentitiesAreNotGenericProofs : Set
    groupDependentConstantsAreAllowed : Set
    scaleVolumeBackgroundUniformityStillRequired : Set
    genericMassGapRequiresAllAnalyticFields : Set

open CompactLiePromotionBoundary public
