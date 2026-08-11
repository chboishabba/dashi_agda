module DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Assemble the Round-40 algebra into the existing physical selector reducer
-- without accepting an independently supplied scalar residual equality.
-- The literal raw-localization atoms and the pair-indexed Moore--Penrose Green
-- contraction generate the correlated residual definitionally through
-- CorrelatedResidualAuthority.  The projected variation has the unique sign
--
--   dS(Pw) = Singleton + RawLocalization - <Lg,K+Lw>.
--
-- Exact cancellation is removed before the four surviving owner estimates
-- close 55/18874368.  The resulting witness reuses the already physical
-- pair/deep channel to obtain the correlated Wilson lower bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonCorrelatedDeepPartitionExact as Split
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Radius
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority

literalRawExtractor :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  KKT.StateVector
literalRawExtractor = Boundary.rawPlaquetteSingletonExtractor

record CorrelatedSingletonExtractionData
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    Multiplier : Set
    pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationCovector : KKT.StateVector

    residualAuthority : Authority.CorrelatedResidualAuthority
      pseudoData firstVariationCovector
      (literalRawExtractor bondField plaquette)

    FineVariation : Set
    variation : FineVariation

    GaugeAdmissible : FineVariation → Set
    ConstraintTangent : FineVariation → Set
    SupportedNearPlaquette : FineVariation → Set

    gaugeAdmissible : GaugeAdmissible variation
    constraintTangent : ConstraintTangent variation
    localSupport : SupportedNearPlaquette variation

    variationNormSq : FineVariation → ℚ
    selectorConstant : ℚ
    selectorConstantNonnegative : 0ℚ ≤ selectorConstant
    variationChargeBound :
      variationNormSq variation
      ≤ selectorConstant * Wilson.plaquetteCrossCharge bondField plaquette

    firstVariation : FineVariation → ℚ

    selectedEulerLagrangeStationary :
      firstVariation variation ≡ 0ℚ

    projectedVariationExact :
      firstVariation variation
      ≡ Partition.physicalPlaquetteWilsonLinearPart
          background bondField plaquette
        + Sign.canonicalProjectedSpillover
            (Authority.rawLocalization residualAuthority)
            (Authority.canonicalMultiplierGreenPairing
              pseudoData firstVariationCovector
              (literalRawExtractor bondField plaquette))

    exactCancellation :
      Ownership.ExactCorrelatedCancellation
        (Authority.canonicalCorrelatedResidualFamily residualAuthority)

    ownerBudgets :
      Ownership.CorrelatedOwnerBudgets
        (Authority.canonicalCorrelatedResidualFamily residualAuthority)
        (Wilson.plaquetteCrossCharge bondField plaquette)

open CorrelatedSingletonExtractionData public

selectedSingletonResidualBudgetExact :
  ∀ {background bondField plaquette} →
  (dataSet : CorrelatedSingletonExtractionData
    background bondField plaquette) →
  Sign.canonicalProjectedSpillover
    (Authority.rawLocalization (residualAuthority dataSet))
    (Authority.canonicalMultiplierGreenPairing
      (pseudoData dataSet)
      (firstVariationCovector dataSet)
      (literalRawExtractor bondField plaquette))
  ≤ Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge bondField plaquette
selectedSingletonResidualBudgetExact
    {bondField = bondField} {plaquette = plaquette} dataSet =
  subst
    (λ lower →
      lower
      ≤ Selector.remainingSingletonCoefficient
          * Wilson.plaquetteCrossCharge bondField plaquette)
    (Authority.canonicalCorrelatedResidualIsProjectedSpillover
      (residualAuthority dataSet))
    (Ownership.correlatedResidualClosesSingletonBudget
      (exactCancellation dataSet)
      (ownerBudgets dataSet))

correlatedSingletonExtractionWitness :
  ∀ {background bondField plaquette} →
  CorrelatedSingletonExtractionData background bondField plaquette →
  Selector.SingletonExtractionWitness background bondField plaquette
correlatedSingletonExtractionWitness
    {bondField = bondField} {plaquette = plaquette} dataSet = record
  { Selector.SingletonExtractionWitness.FineVariation =
      FineVariation dataSet
  ; Selector.SingletonExtractionWitness.variation = variation dataSet
  ; Selector.SingletonExtractionWitness.GaugeAdmissible =
      GaugeAdmissible dataSet
  ; Selector.SingletonExtractionWitness.ConstraintTangent =
      ConstraintTangent dataSet
  ; Selector.SingletonExtractionWitness.SupportedNearPlaquette =
      SupportedNearPlaquette dataSet
  ; Selector.SingletonExtractionWitness.gaugeAdmissible =
      gaugeAdmissible dataSet
  ; Selector.SingletonExtractionWitness.constraintTangent =
      constraintTangent dataSet
  ; Selector.SingletonExtractionWitness.localSupport =
      localSupport dataSet
  ; Selector.SingletonExtractionWitness.variationNormSq =
      variationNormSq dataSet
  ; Selector.SingletonExtractionWitness.selectorConstant =
      selectorConstant dataSet
  ; Selector.SingletonExtractionWitness.selectorConstantNonnegative =
      selectorConstantNonnegative dataSet
  ; Selector.SingletonExtractionWitness.variationChargeBound =
      variationChargeBound dataSet
  ; Selector.SingletonExtractionWitness.firstVariation =
      firstVariation dataSet
  ; Selector.SingletonExtractionWitness.extractionSpillover =
      Sign.canonicalProjectedSpillover
        (Authority.rawLocalization (residualAuthority dataSet))
        (Authority.canonicalMultiplierGreenPairing
          (pseudoData dataSet)
          (firstVariationCovector dataSet)
          (literalRawExtractor bondField plaquette))
  ; Selector.SingletonExtractionWitness.selectedEulerLagrangeStationary =
      selectedEulerLagrangeStationary dataSet
  ; Selector.SingletonExtractionWitness.extractsLiteralSingleton =
      projectedVariationExact dataSet
  ; Selector.SingletonExtractionWitness.spilloverUpper =
      selectedSingletonResidualBudgetExact dataSet }

selectedBackgroundSingletonLowerFromCorrelatedResidual :
  ∀ {background bondField plaquette} →
  (dataSet : CorrelatedSingletonExtractionData
    background bondField plaquette) →
  - (Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge bondField plaquette)
  ≤ Partition.physicalPlaquetteWilsonLinearPart
      background bondField plaquette
selectedBackgroundSingletonLowerFromCorrelatedResidual dataSet =
  Selector.selectedBackgroundSingletonCurvatureLower
    (correlatedSingletonExtractionWitness dataSet)

selectedBackgroundCorrelatedWilsonLower :
  ∀ {background bondField plaquette} →
  Radius.RelaxedInverseLinkRadius background →
  CorrelatedSingletonExtractionData background bondField plaquette →
  - (Wilson.rhoOverThirtySix
      * Wilson.plaquetteCrossCharge bondField plaquette)
  ≤ Split.physicalPlaquetteCorrelatedWilsonPart
      background bondField plaquette
selectedBackgroundCorrelatedWilsonLower radius dataSet =
  Selector.selectedBackgroundCorrelatedWilsonLower
    radius (correlatedSingletonExtractionWitness dataSet)

record SelectedCorrelatedSingletonSelector
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4) : Set₂ where
  field
    selectCorrelated : ∀ plaquette →
      CorrelatedSingletonExtractionData background bondField plaquette
open SelectedCorrelatedSingletonSelector public

correlatedSelectorToPhysicalSelector :
  ∀ {background bondField} →
  SelectedCorrelatedSingletonSelector background bondField →
  Selector.SelectedBackgroundVariationSelector background bondField
correlatedSelectorToPhysicalSelector selected = record
  { Selector.SelectedBackgroundVariationSelector.select = λ plaquette →
      correlatedSingletonExtractionWitness
        (selectCorrelated selected plaquette) }

selectedSingletonResidualBudgetLevel : ProofLevel
selectedSingletonResidualBudgetLevel = machineChecked

selectedCorrelatedWilsonLowerLevel : ProofLevel
selectedCorrelatedWilsonLowerLevel = machineChecked

selectedPhysicalCorrelatedSingletonDataProducerLevel : ProofLevel
selectedPhysicalCorrelatedSingletonDataProducerLevel = conditional
