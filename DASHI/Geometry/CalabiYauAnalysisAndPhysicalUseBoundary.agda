module DASHI.Geometry.CalabiYauAnalysisAndPhysicalUseBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.CalabiYau using (CalabiYauAuthority)

------------------------------------------------------------------------
-- Downstream analysis authority.  Structural Calabi-Yau data does not by
-- itself provide compactness, a Ricci-flat metric, Hodge theory, or physics.

record RicciFlatMetricAuthority
    (Point Metric : Set)
    : Set₁ where
  field
    metric : Metric
    positiveDefinite : Set
    kahlerCompatible : Set
    ricciTensorVanishes : Set
    completeness : Set

record CompactnessAuthority (Point : Set) : Set₁ where
  field
    OpenCover : Set
    finiteSubcoverExists : OpenCover → Set

record HodgeTheoryAuthority
    (Form Cohomology : Set)
    : Set₁ where
  field
    harmonicRepresentative : Cohomology → Form
    representativeClosed : Set
    representativeCoclosed : Set
    hodgeDecomposition : Set
    finiteDimensionalOnCompactCarrier : Set

record YauExistenceAuthority
    (Point Metric KahlerClass : Set)
    : Set₁ where
  field
    selectedKahlerClass : KahlerClass
    existenceMetric : Metric
    uniquenessInClass : Set
    solvesCalabiEquation : Set
    analyticHypothesesSatisfied : Set

record PhysicalCompactificationAuthority
    (InternalSpace EffectiveTheory : Set)
    : Set₁ where
  field
    internalSpace : InternalSpace
    effectiveTheory : EffectiveTheory
    dimensionalReductionDefined : Set
    spectrumComputed : Set
    moduliStabilised : Set
    anomalyCancellationChecked : Set
    lowEnergyObservablesMatched : Set
    falsifiablePrediction : Set

record WormPantsToCalabiYauBridge
    (WormState ComplexPoint : Set)
    : Set₁ where
  field
    mapWormStateToPoint : WormState → ComplexPoint
    respectsPantsComposition : Set
    respectsClopenRefinement : Set
    suppliesHolomorphicCharts : Set
    suppliesKahlerData : Set
    suppliesChernAndVolumeData : Set
    notMerelyDimensionCounting : Set

record CalabiYauAnalysisCutset
    (Point Coordinate RealScalar : Set)
    (Tangent : Point → Set)
    (IntegralCohomology2 TopForm Metric Form Cohomology KahlerClass : Set)
    : Set₁ where
  field
    structuralAuthority :
      CalabiYauAuthority
        Point Coordinate RealScalar Tangent IntegralCohomology2 TopForm
    compactness : CompactnessAuthority Point
    yauExistence : YauExistenceAuthority Point Metric KahlerClass
    ricciFlatMetric : RicciFlatMetricAuthority Point Metric
    hodgeTheory : HodgeTheoryAuthority Form Cohomology

record CalabiYauAnalysisPhysicalBoundary : Set where
  constructor calabiYauAnalysisPhysicalBoundary
  field
    structuralAuthorityAvailable : Bool
    yauTheoremDerivedFromStructureAlone : Bool
    yauTheoremDerivedFromStructureAloneIsFalse :
      yauTheoremDerivedFromStructureAlone ≡ false
    ricciFlatMetricConstructedCanonically : Bool
    ricciFlatMetricConstructedCanonicallyIsFalse :
      ricciFlatMetricConstructedCanonically ≡ false
    compactnessAutomatic : Bool
    compactnessAutomaticIsFalse : compactnessAutomatic ≡ false
    hodgeTheoryAutomatic : Bool
    hodgeTheoryAutomaticIsFalse : hodgeTheoryAutomatic ≡ false
    physicalCompactificationAutomatic : Bool
    physicalCompactificationAutomaticIsFalse :
      physicalCompactificationAutomatic ≡ false
    wormPantsAutomaticallyCalabiYau : Bool
    wormPantsAutomaticallyCalabiYauIsFalse :
      wormPantsAutomaticallyCalabiYau ≡ false
    interpretation : String

canonicalCalabiYauAnalysisPhysicalBoundary :
  CalabiYauAnalysisPhysicalBoundary
canonicalCalabiYauAnalysisPhysicalBoundary =
  calabiYauAnalysisPhysicalBoundary
    true
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "the merged structural Calabi-Yau authority is reusable, while Yau existence, Ricci-flat analysis, compactness, Hodge theory, physical compactification and any worm/pants bridge require independent proof-carrying cutsets"
