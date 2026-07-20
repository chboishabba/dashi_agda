module DASHI.Moonshine.UmbralPenumbralComparisonBoundary where

-- Penumbral and umbral moonshine share half-integral-weight and finite-group
-- structures, but their analytic form classes must not be identified.
-- Umbral constructions typically involve mock modular forms with nonzero
-- shadows; the penumbral forms represented here are weakly holomorphic.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Unit using (⊤; tt)

record HarmonicMaassCarrier : Set₁ where
  field
    HarmonicMaassForm : Set
    HolomorphicPart : Set
    Shadow : Set

    holomorphicPart : HarmonicMaassForm → HolomorphicPart
    shadow : HarmonicMaassForm → Shadow

    ZeroShadow : Shadow → Set
    MockModular : HolomorphicPart → Set
    WeaklyHolomorphic : HolomorphicPart → Set

record MockWeakHolomorphicSeparation
  (carrier : HarmonicMaassCarrier) : Setω where
  field
    completion :
      HarmonicMaassCarrier.HolomorphicPart carrier →
      HarmonicMaassCarrier.HarmonicMaassForm carrier

    weaklyHolomorphicHasZeroShadow :
      (form : HarmonicMaassCarrier.HolomorphicPart carrier) →
      HarmonicMaassCarrier.WeaklyHolomorphic carrier form →
      HarmonicMaassCarrier.ZeroShadow carrier
        (HarmonicMaassCarrier.shadow carrier (completion form))

    NonzeroShadow : HarmonicMaassCarrier.Shadow carrier → Set

    nonzeroShadowBlocksWeakHolomorphy :
      (form : HarmonicMaassCarrier.HolomorphicPart carrier) →
      NonzeroShadow
        (HarmonicMaassCarrier.shadow carrier (completion form)) →
      (HarmonicMaassCarrier.WeaklyHolomorphic carrier form → Set)

record UmbralPenumbralStructuralComparison : Setω where
  field
    UmbralDatum PenumbralDatum : Set
    FiniteGroup : Set
    HalfIntegralWeightForm : Set

    umbralGroup : UmbralDatum → FiniteGroup
    penumbralGroup : PenumbralDatum → FiniteGroup
    umbralForm : UmbralDatum → HalfIntegralWeightForm
    penumbralForm : PenumbralDatum → HalfIntegralWeightForm

    SharedFeature : Set
    sharedFeatureWitness : SharedFeature

    UmbralIncludedInPenumbral : Set
    PenumbralIncludedInUmbral : Set

    noUmbralInclusionProof :
      UmbralIncludedInPenumbral → Set
    noPenumbralInclusionProof :
      PenumbralIncludedInUmbral → Set

record UmbralPenumbralBoundary : Set where
  field
    mockModularAndWeaklyHolomorphicAreDistinctClasses : ⊤
    shadowDataMustBeTracked : ⊤
    sharedHalfWeightStructureDoesNotImplyInclusion : ⊤
    k3RealizationIsNotPartOfGenericPenumbralData : ⊤
    noUmbralPenumbralEquivalenceClaim : ⊤

umbralPenumbralBoundary : UmbralPenumbralBoundary
umbralPenumbralBoundary = record
  { mockModularAndWeaklyHolomorphicAreDistinctClasses = tt
  ; shadowDataMustBeTracked = tt
  ; sharedHalfWeightStructureDoesNotImplyInclusion = tt
  ; k3RealizationIsNotPartOfGenericPenumbralData = tt
  ; noUmbralPenumbralEquivalenceClaim = tt
  }
