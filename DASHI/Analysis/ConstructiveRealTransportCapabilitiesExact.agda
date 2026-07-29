module DASHI.Analysis.ConstructiveRealTransportCapabilitiesExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.ConstructiveRealCapabilityHierarchyExact as Capability
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Effective order and layered analysis transport.
--
-- Rocq/Coq standard-library precedent:
--   Coq.Reals.Abstract.ConstructiveReals
--   Coq.Reals.ConstructiveRealsMorphisms
-- Software documentation; no DOI.
--
-- Herman Geuvers and Milad Niqui,
-- "Constructive Reals in Coq: Axioms and Categoricity",
-- Types for Proofs and Programs, LNCS 2277 (2002), 79--95.
-- DOI: 10.1007/3-540-45842-5_6.
--
-- The backend strict order already lives in Set and may carry computational
-- evidence.  The first record therefore does not replace it: it adds a logical
-- view and an explicit epsilon-witness recovery seam.  The remaining records
-- layer limit, series and elementary-function transport over the minimal
-- strongly-extensional/order/add/multiply homomorphism.
------------------------------------------------------------------------

record EffectiveLogicalOrderView
    (R : Spine.SetoidOrderedCompleteReal) : Set₁ where
  field
    LogicalLt : Spine.Carrier R → Spine.Carrier R → Set
    Precision : Set
    positivePrecision : Precision → Spine.Carrier R

    forgetEffectiveLt : ∀ {x y} → Spine._<_ R x y → LogicalLt x y

    logicalLtHasSeparationWitness : ∀ {x y} → LogicalLt x y →
      Σ Precision
        (λ precision →
          Spine._<_ R
            (Spine._+_ R x (positivePrecision precision))
            y)

    separationWitnessRecoversEffectiveLt : ∀ {x y} →
      Σ Precision
        (λ precision →
          Spine._<_ R
            (Spine._+_ R x (positivePrecision precision))
            y) →
      Spine._<_ R x y

    effectiveLogicalAgreement :
      (x y : Spine.Carrier R) → Set

open EffectiveLogicalOrderView public

record SequenceTransportCapability
    {Source Target : Spine.SetoidOrderedCompleteReal}
    {sourceField : Capability.ConstructiveOrderedFieldCapability Source}
    {targetField : Capability.ConstructiveOrderedFieldCapability Target}
    (hom : Capability.ConstructiveRealHomomorphism
      Source Target sourceField targetField) : Set₁ where
  field
    targetSequence : Spine.Sequence Source → Spine.Sequence Target
    pointwiseMap : ∀ sequence index →
      Spine._≈_ Target
        (Spine.sequenceAt Target (targetSequence sequence) index)
        (Capability.map hom (Spine.sequenceAt Source sequence index))

    cauchyPreserved : ∀ sequence →
      Spine.IsCauchy Source sequence →
      Spine.IsCauchy Target (targetSequence sequence)

    convergencePreserved : ∀ sequence limit →
      Spine.ConvergesTo Source sequence limit →
      Spine.ConvergesTo Target
        (targetSequence sequence)
        (Capability.map hom limit)

    limitPreserved : ∀ sequence cauchy →
      Spine._≈_ Target
        (Capability.map hom
          (fst (Spine.cauchyLimit Source sequence cauchy)))
        (fst
          (Spine.cauchyLimit Target (targetSequence sequence)
            (cauchyPreserved sequence cauchy)))

open SequenceTransportCapability public

record ModulusTransportCapability
    {Source Target : Spine.SetoidOrderedCompleteReal}
    {sourceField : Capability.ConstructiveOrderedFieldCapability Source}
    {targetField : Capability.ConstructiveOrderedFieldCapability Target}
    (hom : Capability.ConstructiveRealHomomorphism
      Source Target sourceField targetField)
    (sourceEffective : Capability.EffectiveConvergenceStructure Source)
    (targetEffective : Capability.EffectiveConvergenceStructure Target) : Set₁ where
  field
    translatePrecision :
      Capability.Precision targetEffective → Capability.Precision sourceEffective

    sourceCauchyModulusTransports :
      (sequence : Spine.Sequence Source) →
      Spine.IsCauchy Source sequence →
      (precision : Capability.Precision targetEffective) → Set

    sourceConvergenceModulusTransports :
      (sequence : Spine.Sequence Source) →
      (limit : Spine.Carrier Source) →
      Spine.ConvergesTo Source sequence limit →
      (precision : Capability.Precision targetEffective) → Set

    translatedRadiusIsSufficient :
      (precision : Capability.Precision targetEffective) → Set

open ModulusTransportCapability public

record SeriesTransportCapability
    {Source Target : Spine.SetoidOrderedCompleteReal}
    {sourceField : Capability.ConstructiveOrderedFieldCapability Source}
    {targetField : Capability.ConstructiveOrderedFieldCapability Target}
    (hom : Capability.ConstructiveRealHomomorphism
      Source Target sourceField targetField) : Set₁ where
  field
    SourceSeries TargetSeries : Set
    sourceTerm : SourceSeries → Nat → Spine.Carrier Source
    targetTerm : TargetSeries → Nat → Spine.Carrier Target
    mapSeries : SourceSeries → TargetSeries

    termwiseMap : ∀ series index →
      Spine._≈_ Target
        (targetTerm (mapSeries series) index)
        (Capability.map hom (sourceTerm series index))

    SourceConvergent : SourceSeries → Spine.Carrier Source → Set
    TargetConvergent : TargetSeries → Spine.Carrier Target → Set
    SourceAbsolutelyConvergent : SourceSeries → Set
    TargetAbsolutelyConvergent : TargetSeries → Set

    convergenceTransport : ∀ series sum →
      SourceConvergent series sum →
      TargetConvergent (mapSeries series) (Capability.map hom sum)

    absoluteConvergenceTransport : ∀ series →
      SourceAbsolutelyConvergent series →
      TargetAbsolutelyConvergent (mapSeries series)

    geometricSeriesTransport : Set
    comparisonTestTransport : Set
    ratioTestTransport : Set
    cauchyProductTransport : Set

open SeriesTransportCapability public

record ElementaryFunctionTransportCapability
    {Source Target : Spine.SetoidOrderedCompleteReal}
    {sourceField : Capability.ConstructiveOrderedFieldCapability Source}
    {targetField : Capability.ConstructiveOrderedFieldCapability Target}
    (hom : Capability.ConstructiveRealHomomorphism
      Source Target sourceField targetField) : Set₁ where
  field
    sourceSin sourceCos sourceExp sourceLog :
      Spine.Carrier Source → Spine.Carrier Source
    targetSin targetCos targetExp targetLog :
      Spine.Carrier Target → Spine.Carrier Target
    PositiveSource : Spine.Carrier Source → Set

    sinTransport : ∀ x →
      Spine._≈_ Target
        (Capability.map hom (sourceSin x))
        (targetSin (Capability.map hom x))
    cosTransport : ∀ x →
      Spine._≈_ Target
        (Capability.map hom (sourceCos x))
        (targetCos (Capability.map hom x))
    expTransport : ∀ x →
      Spine._≈_ Target
        (Capability.map hom (sourceExp x))
        (targetExp (Capability.map hom x))
    logTransportOnPositiveDomain : ∀ x → PositiveSource x →
      Spine._≈_ Target
        (Capability.map hom (sourceLog x))
        (targetLog (Capability.map hom x))

open ElementaryFunctionTransportCapability public

record MinimalHomomorphismTransportDerivation
    {Source Target : Spine.SetoidOrderedCompleteReal}
    {sourceField : Capability.ConstructiveOrderedFieldCapability Source}
    {targetField : Capability.ConstructiveOrderedFieldCapability Target}
    (hom : Capability.ConstructiveRealHomomorphism
      Source Target sourceField targetField) : Set₂ where
  field
    algebraAndOrder : Capability.DerivedHomomorphismLaws hom
    sequencesAndLimits : SequenceTransportCapability hom
    series : SeriesTransportCapability hom
    elementaryFunctions : ElementaryFunctionTransportCapability hom

    sequenceTransportDerivedFromMinimalCore : Set
    limitTransportDerivedFromMinimalCore : Set
    seriesTransportDerivedFromTermwiseMapAndLimitUniqueness : Set
    elementaryTransportDerivedFromSeriesOrUniqueness : Set

open MinimalHomomorphismTransportDerivation public

record RationalArchimedeanMorphism
    {Source Target : Spine.SetoidOrderedCompleteReal}
    (sourceQ : Capability.RationalEmbeddingStructure Source)
    (targetQ : Capability.RationalEmbeddingStructure Target)
    (CommonQ : Set)
    (decodeSource : CommonQ → Capability.Q sourceQ)
    (decodeTarget : CommonQ → Capability.Q targetQ)
    {sourceField : Capability.ConstructiveOrderedFieldCapability Source}
    {targetField : Capability.ConstructiveOrderedFieldCapability Target}
    (hom : Capability.ConstructiveRealHomomorphism
      Source Target sourceField targetField) : Set₁ where
  field
    rationalCompatibility :
      Capability.RationalHomomorphismCompatibility
        sourceQ targetQ CommonQ decodeSource decodeTarget hom
    densityTransport : Set
    naturalMajorizationTransport : Set

open RationalArchimedeanMorphism public

record CompleteRealMorphism
    {Source Target : Spine.SetoidOrderedCompleteReal}
    {sourceField : Capability.ConstructiveOrderedFieldCapability Source}
    {targetField : Capability.ConstructiveOrderedFieldCapability Target} : Set₂ where
  field
    minimal : Capability.ConstructiveRealHomomorphism
      Source Target sourceField targetField
    derived : MinimalHomomorphismTransportDerivation minimal

open CompleteRealMorphism public

effectiveLogicalOrderViewLevel : ProofLevel
effectiveLogicalOrderViewLevel = machineChecked

sequenceSeriesElementaryTransportLayerLevel : ProofLevel
sequenceSeriesElementaryTransportLayerLevel = machineChecked

minimalTransportDerivationInputsLevel : ProofLevel
minimalTransportDerivationInputsLevel = conditional
