module DASHI.Physics.YangMills.BalabanSelectedCorrelatedPairSingletonClosureExact where

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
-- Alternative G2 closure that preserves cancellation inside the two signed
-- physical owner groups all the way to the selector boundary.  The previous
-- literal-family lane asks for four separate owner upper bounds.  This lane
-- asks only for
--
--   localization + transport <= c_LT * charge,
--   nearGreen + farGreen <= c_G * charge,
--   c_LT + c_G <= 55/18874368.
--
-- It therefore cannot lose a useful sign cancellation between localization
-- and transport or between near and far Green pieces.  The same raw extractor,
-- Moore--Penrose solve, stationarity, projected variation and exact-cancellation
-- authority remain vertically tied to the witness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedPairBudgetExact as Pair

literalRawExtractor :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → KKT.StateVector
literalRawExtractor = Boundary.rawPlaquetteSingletonExtractor

record PairedCorrelatedSingletonExtractionData
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
    selectedEulerLagrangeStationary : firstVariation variation ≡ 0ℚ

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

    pairBudgets :
      Pair.CorrelatedPairBudgets
        (Authority.canonicalCorrelatedResidualFamily residualAuthority)
        (Wilson.plaquetteCrossCharge bondField plaquette)

open PairedCorrelatedSingletonExtractionData public

selectedSingletonResidualBudgetPairedExact :
  ∀ {background bondField plaquette} →
  (dataSet : PairedCorrelatedSingletonExtractionData
    background bondField plaquette) →
  Sign.canonicalProjectedSpillover
    (Authority.rawLocalization (residualAuthority dataSet))
    (Authority.canonicalMultiplierGreenPairing
      (pseudoData dataSet)
      (firstVariationCovector dataSet)
      (literalRawExtractor bondField plaquette))
  ≤ Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge bondField plaquette
selectedSingletonResidualBudgetPairedExact
    {bondField = bondField} {plaquette = plaquette} dataSet =
  subst
    (λ lower →
      lower
      ≤ Selector.remainingSingletonCoefficient
          * Wilson.plaquetteCrossCharge bondField plaquette)
    (Authority.canonicalCorrelatedResidualIsProjectedSpillover
      (residualAuthority dataSet))
    (Pair.correlatedPairBudgetsCloseResidual
      (exactCancellation dataSet)
      (pairBudgets dataSet))

pairedCorrelatedSingletonExtractionWitness :
  ∀ {background bondField plaquette} →
  PairedCorrelatedSingletonExtractionData background bondField plaquette →
  Selector.SingletonExtractionWitness background bondField plaquette
pairedCorrelatedSingletonExtractionWitness
    {bondField = bondField} {plaquette = plaquette} dataSet = record
  { Selector.SingletonExtractionWitness.FineVariation = FineVariation dataSet
  ; Selector.SingletonExtractionWitness.variation = variation dataSet
  ; Selector.SingletonExtractionWitness.GaugeAdmissible = GaugeAdmissible dataSet
  ; Selector.SingletonExtractionWitness.ConstraintTangent = ConstraintTangent dataSet
  ; Selector.SingletonExtractionWitness.SupportedNearPlaquette =
      SupportedNearPlaquette dataSet
  ; Selector.SingletonExtractionWitness.gaugeAdmissible = gaugeAdmissible dataSet
  ; Selector.SingletonExtractionWitness.constraintTangent = constraintTangent dataSet
  ; Selector.SingletonExtractionWitness.localSupport = localSupport dataSet
  ; Selector.SingletonExtractionWitness.variationNormSq = variationNormSq dataSet
  ; Selector.SingletonExtractionWitness.selectorConstant = selectorConstant dataSet
  ; Selector.SingletonExtractionWitness.selectorConstantNonnegative =
      selectorConstantNonnegative dataSet
  ; Selector.SingletonExtractionWitness.variationChargeBound =
      variationChargeBound dataSet
  ; Selector.SingletonExtractionWitness.firstVariation = firstVariation dataSet
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
      selectedSingletonResidualBudgetPairedExact dataSet
  }

record PairedCorrelatedSingletonSelector
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4) : Set₂ where
  field
    selectCorrelated : ∀ plaquette →
      PairedCorrelatedSingletonExtractionData background bondField plaquette

open PairedCorrelatedSingletonSelector public

pairedCorrelatedSelectorToPhysicalSelector :
  ∀ {background bondField} →
  PairedCorrelatedSingletonSelector background bondField →
  Selector.SelectedBackgroundVariationSelector background bondField
pairedCorrelatedSelectorToPhysicalSelector selected = record
  { Selector.SelectedBackgroundVariationSelector.select = λ plaquette →
      pairedCorrelatedSingletonExtractionWitness
        (selectCorrelated selected plaquette) }

selectedPairedSingletonResidualBudgetLevel : ProofLevel
selectedPairedSingletonResidualBudgetLevel = machineChecked

selectedPairedCorrelatedSelectorLevel : ProofLevel
selectedPairedCorrelatedSelectorLevel = machineChecked
