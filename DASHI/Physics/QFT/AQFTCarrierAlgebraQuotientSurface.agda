module DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface where

open import Agda.Primitive using (Level; Setω; lzero)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT
import DASHI.Physics.QFT.ModularTheoryReceiptSurface as Modular
import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as MassGap
import DASHI.Foundations.QuotientSetoidSurface as QS
import DASHI.Foundations.RealAnalysisAxioms as RA

------------------------------------------------------------------------
-- AQFT local algebra from carrier receipts: quotient target surface.
--
-- This module records the next construction target after the abstract
-- Haag-Kastler net socket:
--
--   A(O) = promoted receipts over the carrier restricted to O,
--          quotiented by transport equivalence.
--
-- It intentionally keeps the restricted carrier, promoted-receipt predicate,
-- quotient carrier, and algebra operations abstract.  It does not construct a
-- C*-algebra, GNS state, Born-rule adapter, interacting QFT, Standard Model
-- net, or GRQFT promotion receipt.

data AQFTCarrierAlgebraQuotientStatus : Set where
  quotientSurfaceOnlyNoAQFTPromotion :
    AQFTCarrierAlgebraQuotientStatus

data AQFTCarrierAlgebraQuotientOpenObligation : Set where
  missingRestrictedCarrier :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingTransportEquivalenceLaws :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingPromotedReceiptPredicate :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingQuotientConstruction :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingPreciseQuotientRelation :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingAlgebraOperationsOnQuotient :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingNormOperationLabel :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingIsotonyFromCarrierTransport :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingColimitUniversality :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingCausalReachability :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingCauchyEvolutionReceipt :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingDepthFilteredColimitAlgebra :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingFullTimeSliceTheorem :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingKTheoreticIntermediateTarget :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingCStarNormUniquenessEnvelope :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingNuclearityTheorem :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingMassGapEnergyPositivityBWTimeSliceDependency :
    AQFTCarrierAlgebraQuotientOpenObligation

data AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt : Set where
  transportEquivalenceLawsSetoidInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

  transportQuotientExtensionalitySetoidInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

  transportQuotientEliminatorsSetoidInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

canonicalAQFTCarrierAlgebraQuotientSetoidInhabitedReceipts :
  List AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt
canonicalAQFTCarrierAlgebraQuotientSetoidInhabitedReceipts =
  transportEquivalenceLawsSetoidInhabited
  ∷ transportQuotientExtensionalitySetoidInhabited
  ∷ transportQuotientEliminatorsSetoidInhabited
  ∷ []

data AQFTCarrierAlgebraPromotionAuthorityToken : Set where

data CauchyEvolutionStatus : Set where
  cauchyEvolutionTargetOnlyNoTimeSliceProof :
    CauchyEvolutionStatus

data CauchyEvolutionOpenObligation : Set where
  missingCarrierDataOnCauchySurface :
    CauchyEvolutionOpenObligation

  missingCarrierEvolutionMap :
    CauchyEvolutionOpenObligation

  missingEvolutionDeterminesRegion :
    CauchyEvolutionOpenObligation

  missingDomainOfDependenceForTargetRegion :
    CauchyEvolutionOpenObligation

  missingSpacetimeAlgebraRegionIsomorphism :
    CauchyEvolutionOpenObligation

  missingDescentColimitCaveatDischarge :
    CauchyEvolutionOpenObligation

canonicalCauchyEvolutionOpenObligations :
  List CauchyEvolutionOpenObligation
canonicalCauchyEvolutionOpenObligations =
  missingCarrierDataOnCauchySurface
  ∷ missingCarrierEvolutionMap
  ∷ missingEvolutionDeterminesRegion
  ∷ missingDomainOfDependenceForTargetRegion
  ∷ missingSpacetimeAlgebraRegionIsomorphism
  ∷ missingDescentColimitCaveatDischarge
  ∷ []

data CauchyEvolutionPromotionAuthorityToken : Set where

data TimeSliceTheoremStatus : Set where
  timeSliceTheoremTargetOnlyNoPromotion :
    TimeSliceTheoremStatus

data TimeSliceTheoremOpenObligation : Set where
  missingCauchySurfaceRegion :
    TimeSliceTheoremOpenObligation

  missingCauchySurfaceInclusion :
    TimeSliceTheoremOpenObligation

  missingRegionSpacetimeInclusion :
    TimeSliceTheoremOpenObligation

  missingDomainOfDependenceLaw :
    TimeSliceTheoremOpenObligation

  missingCauchyRegionSpacetimeAlgebraIsomorphismChain :
    TimeSliceTheoremOpenObligation

  missingDescentColimitCompatibility :
    TimeSliceTheoremOpenObligation

canonicalTimeSliceTheoremOpenObligations :
  List TimeSliceTheoremOpenObligation
canonicalTimeSliceTheoremOpenObligations =
  missingCauchySurfaceRegion
  ∷ missingCauchySurfaceInclusion
  ∷ missingRegionSpacetimeInclusion
  ∷ missingDomainOfDependenceLaw
  ∷ missingCauchyRegionSpacetimeAlgebraIsomorphismChain
  ∷ missingDescentColimitCompatibility
  ∷ []

data TimeSliceTheoremPromotionAuthorityToken : Set where

data DepthFilteredAlgebraStatus : Set where
  depthFilteredColimitTargetOnlyNoCStarConstruction :
    DepthFilteredAlgebraStatus

data DepthFilteredAlgebraOpenObligation : Set where
  missingDepthOrder :
    DepthFilteredAlgebraOpenObligation

  missingDepthIndexedLocalAlgebras :
    DepthFilteredAlgebraOpenObligation

  missingDepthRefinementMorphisms :
    DepthFilteredAlgebraOpenObligation

  missingDirectedDepthWitness :
    DepthFilteredAlgebraOpenObligation

  missingFilteredColimitConstruction :
    DepthFilteredAlgebraOpenObligation

  missingColimitAlgebraOperations :
    DepthFilteredAlgebraOpenObligation

  missingCStarCompletionBoundary :
    DepthFilteredAlgebraOpenObligation

  missingColimitMatchesAQFTLocalAlgebra :
    DepthFilteredAlgebraOpenObligation

  missingDescentCompatibilityForCovers :
    DepthFilteredAlgebraOpenObligation

  missingTimeSliceCompatibilityForColimit :
    DepthFilteredAlgebraOpenObligation

canonicalDepthFilteredAlgebraOpenObligations :
  List DepthFilteredAlgebraOpenObligation
canonicalDepthFilteredAlgebraOpenObligations =
  missingDepthOrder
  ∷ missingDepthIndexedLocalAlgebras
  ∷ missingDepthRefinementMorphisms
  ∷ missingDirectedDepthWitness
  ∷ missingFilteredColimitConstruction
  ∷ missingColimitAlgebraOperations
  ∷ missingCStarCompletionBoundary
  ∷ missingColimitMatchesAQFTLocalAlgebra
  ∷ missingDescentCompatibilityForCovers
  ∷ missingTimeSliceCompatibilityForColimit
  ∷ []

data DepthFilteredAlgebraPromotionAuthorityToken : Set where

record QuotientOperationLabelReceipt : Setω where
  field
    unitOperationLabel :
      String

    unitOperationLabel-v :
      unitOperationLabel
      ≡
      "quotient-unit-operation"

    multiplicationOperationLabel :
      String

    multiplicationOperationLabel-v :
      multiplicationOperationLabel
      ≡
      "quotient-multiplication-operation"

    starOperationLabel :
      String

    starOperationLabel-v :
      starOperationLabel
      ≡
      "quotient-star-operation"

    normOperationLabel :
      String

    normOperationLabel-v :
      normOperationLabel
      ≡
      "quotient-norm-operation-target"

    operationLabelsPromoted :
      Bool

    operationLabelsPromotedIsFalse :
      operationLabelsPromoted ≡ false

    operationBoundary :
      List String

open QuotientOperationLabelReceipt public

canonicalQuotientOperationLabelReceipt :
  QuotientOperationLabelReceipt
canonicalQuotientOperationLabelReceipt =
  record
    { unitOperationLabel =
        "quotient-unit-operation"
    ; unitOperationLabel-v =
        refl
    ; multiplicationOperationLabel =
        "quotient-multiplication-operation"
    ; multiplicationOperationLabel-v =
        refl
    ; starOperationLabel =
        "quotient-star-operation"
    ; starOperationLabel-v =
        refl
    ; normOperationLabel =
        "quotient-norm-operation-target"
    ; normOperationLabel-v =
        refl
    ; operationLabelsPromoted =
        false
    ; operationLabelsPromotedIsFalse =
        refl
    ; operationBoundary =
        "unit, multiplication, star, and norm are named operation targets on the quotient carrier"
        ∷ "the norm entry is a target label only; no C-star norm law, completion, or representation is constructed here"
        ∷ []
    }

record TransportEquivalenceRelation
  (Carrier : AQFT.Region → Set)
  (TransportEquivalent :
    {region : AQFT.Region} →
    Carrier region →
    Carrier region →
    Set) : Setω where
  field
    transportReflexive :
      {region : AQFT.Region} →
      (x : Carrier region) →
      TransportEquivalent x x

    transportSymmetric :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      TransportEquivalent y x

    transportTransitive :
      {region : AQFT.Region} →
      {x y z : Carrier region} →
      TransportEquivalent x y →
      TransportEquivalent y z →
      TransportEquivalent x z

open TransportEquivalenceRelation public

record QuotientTransportStability
  (Carrier : AQFT.Region → Set)
  (TransportEquivalent :
    {region : AQFT.Region} →
    Carrier region →
    Carrier region →
    Set)
  (QuotientCarrier : AQFT.Region → Set)
  (quotientClass :
    {region : AQFT.Region} →
    Carrier region →
    QuotientCarrier region) : Setω where
  field
    transportEquivalenceRelation :
      TransportEquivalenceRelation Carrier TransportEquivalent

    quotientStable :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      quotientClass x
      ≡
      quotientClass y

open QuotientTransportStability public

record TransportQuotientEquivalenceLawReceipt : Setω where
  field
    Carrier :
      AQFT.Region →
      Set

    TransportEquivalent :
      {region : AQFT.Region} →
      Carrier region →
      Carrier region →
      Set

    QuotientCarrier :
      AQFT.Region →
      Set

    quotientClass :
      {region : AQFT.Region} →
      Carrier region →
      QuotientCarrier region

    transportEquivalenceRecord :
      TransportEquivalenceRelation Carrier TransportEquivalent

    quotientTransportStabilityRecord :
      QuotientTransportStability
        Carrier
        TransportEquivalent
        QuotientCarrier
        quotientClass

    transportReflexiveTarget :
      {region : AQFT.Region} →
      (x : Carrier region) →
      TransportEquivalent x x

    transportSymmetricTarget :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      TransportEquivalent y x

    transportTransitiveTarget :
      {region : AQFT.Region} →
      {x y z : Carrier region} →
      TransportEquivalent x y →
      TransportEquivalent y z →
      TransportEquivalent x z

    quotientStableUnderTransport :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      quotientClass x
      ≡
      quotientClass y

    quotientEquivalencePromoted :
      Bool

    quotientEquivalencePromotedIsFalse :
      quotientEquivalencePromoted ≡ false

    quotientEquivalenceBoundary :
      List String

open TransportQuotientEquivalenceLawReceipt public

transportSetoidFromRelation :
  (Carrier : AQFT.Region → Set) →
  (TransportEquivalent :
    {region : AQFT.Region} →
    Carrier region →
    Carrier region →
    Set) →
  TransportEquivalenceRelation Carrier TransportEquivalent →
  AQFT.Region →
  QS.SetoidSurface lzero lzero
transportSetoidFromRelation Carrier TransportEquivalent laws region =
  record
    { Carrier =
        Carrier region
    ; _≈_ =
        TransportEquivalent {region}
    ; isEquivalence =
        record
          { refl≈ =
              TransportEquivalenceRelation.transportReflexive
                laws
                {region}
          ; sym≈ =
              TransportEquivalenceRelation.transportSymmetric
                laws
                {region}
          ; trans≈ =
              TransportEquivalenceRelation.transportTransitive
                laws
                {region}
          }
    }

record TransportSetoidQuotientReceipt
  (Carrier : AQFT.Region → Set)
  (TransportEquivalent :
    {region : AQFT.Region} →
    Carrier region →
    Carrier region →
    Set)
  (QuotientCarrier : AQFT.Region → Set)
  (quotientClass :
    {region : AQFT.Region} →
    Carrier region →
    QuotientCarrier region) : Setω where
  field
    transportEquivalenceRecord :
      TransportEquivalenceRelation Carrier TransportEquivalent

    setoidQuotientAt :
      (region : AQFT.Region) →
      QS.SetoidQuotientSurface
        (transportSetoidFromRelation
          Carrier
          TransportEquivalent
          transportEquivalenceRecord
          region)
        lzero

    quotientExtensionalityDischargesTransportStability :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      quotientClass x
      ≡
      quotientClass y

    quotientEliminatorBoundary :
      List String

open TransportSetoidQuotientReceipt public

record QuotientNormSurface
  (Carrier : AQFT.Region → Set)
  (TransportEquivalent :
    {region : AQFT.Region} →
    Carrier region →
    Carrier region →
    Set)
  (QuotientCarrier : AQFT.Region → Set)
  (quotientClass :
    {region : AQFT.Region} →
    Carrier region →
    QuotientCarrier region) : Setω where
  field
    carrierNormTarget :
      {region : AQFT.Region} →
      Carrier region →
      RA.ℝ

    quotientNorm :
      {region : AQFT.Region} →
      QuotientCarrier region →
      RA.ℝ

    carrierNormTransportInvariant :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      carrierNormTarget x
      ≡
      carrierNormTarget y

    quotientNormβ :
      {region : AQFT.Region} →
      (x : Carrier region) →
      quotientNorm (quotientClass x)
      ≡
      carrierNormTarget x

    quotientNormPromoted :
      Bool

    quotientNormPromotedIsFalse :
      quotientNormPromoted ≡ false

    quotientNormBoundary :
      List String

open QuotientNormSurface public

record QuotientAlgebraOperationsTransportWellDefined
  (Carrier : AQFT.Region → Set)
  (TransportEquivalent :
    {region : AQFT.Region} →
    Carrier region →
    Carrier region →
    Set)
  (QuotientCarrier : AQFT.Region → Set)
  (quotientClass :
    {region : AQFT.Region} →
    Carrier region →
    QuotientCarrier region)
  (quotientUnit :
    {region : AQFT.Region} →
    QuotientCarrier region)
  (quotientMul :
    {region : AQFT.Region} →
    QuotientCarrier region →
    QuotientCarrier region →
    QuotientCarrier region)
  (quotientStar :
    {region : AQFT.Region} →
    QuotientCarrier region →
    QuotientCarrier region)
  (quotientNorm :
    {region : AQFT.Region} →
    QuotientCarrier region →
    RA.ℝ) : Setω where
  field
    quotientClassTransportStable :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      quotientClass x
      ≡
      quotientClass y

    quotientUnitTransportInvariant :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      quotientUnit {region}
      ≡
      quotientUnit {region}

    quotientMulTransportWellDefined :
      {region : AQFT.Region} →
      {x x′ y y′ : Carrier region} →
      TransportEquivalent x x′ →
      TransportEquivalent y y′ →
      quotientMul (quotientClass x) (quotientClass y)
      ≡
      quotientMul (quotientClass x′) (quotientClass y′)

    quotientStarTransportWellDefined :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      quotientStar (quotientClass x)
      ≡
      quotientStar (quotientClass y)

    quotientNormTransportWellDefined :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      quotientNorm (quotientClass x)
      ≡
      quotientNorm (quotientClass y)

    operationTransportBoundary :
      List String

open QuotientAlgebraOperationsTransportWellDefined public

record UnitaryConjugationPreservesNormSocket
  (AQFTAlgebra : AQFT.Region → Set)
  (quotientNorm :
    {region : AQFT.Region} →
    AQFTAlgebra region →
    RA.ℝ) : Setω where
  field
    LocalUnitary :
      AQFT.Region →
      Set

    unitaryConjugate :
      {region : AQFT.Region} →
      LocalUnitary region →
      AQFTAlgebra region →
      AQFTAlgebra region

    unitaryNormAuthority :
      RA.RealAnalysisAuthority

    unitaryConjugationPreservesNorm :
      {region : AQFT.Region} →
      (U : LocalUnitary region) →
      (a : AQFTAlgebra region) →
      quotientNorm (unitaryConjugate U a)
      ≡
      quotientNorm a

    unitaryConjugationPromoted :
      Bool

    unitaryConjugationPromotedIsFalse :
      unitaryConjugationPromoted ≡ false

    unitaryConjugationBoundary :
      List String

open UnitaryConjugationPreservesNormSocket public

record FiniteDimensionalCStarIdentitySocket
  (AQFTAlgebra : AQFT.Region → Set)
  (quotientMul :
    {region : AQFT.Region} →
    AQFTAlgebra region →
    AQFTAlgebra region →
    AQFTAlgebra region)
  (quotientStar :
    {region : AQFT.Region} →
    AQFTAlgebra region →
    AQFTAlgebra region)
  (quotientNorm :
    {region : AQFT.Region} →
    AQFTAlgebra region →
    RA.ℝ) : Setω where
  field
    FiniteDimensionalWitness :
      AQFT.Region →
      Set

    finiteDimensionalCStarIdentityTarget :
      {region : AQFT.Region} →
      FiniteDimensionalWitness region →
      (a : AQFTAlgebra region) →
      quotientNorm (quotientMul (quotientStar a) a)
      ≡
      RA._*ℝ_ (quotientNorm a) (quotientNorm a)

    finiteDimensionalCStarAuthority :
      (region : AQFT.Region) →
      FiniteDimensionalWitness region →
      Set

    finiteDimensionalCStarPromoted :
      Bool

    finiteDimensionalCStarPromotedIsFalse :
      finiteDimensionalCStarPromoted ≡ false

    finiteDimensionalCStarBoundary :
      List String

open FiniteDimensionalCStarIdentitySocket public

record CStarCompletionUniversalPropertyAuthority
  (AlgebraicAlgebra : AQFT.Region → Set)
  (algebraicNorm :
    {region : AQFT.Region} →
    AlgebraicAlgebra region →
    RA.ℝ) : Setω where
  field
    CStarCompletion :
      AQFT.Region →
      Set

    completionEmbed :
      {region : AQFT.Region} →
      AlgebraicAlgebra region →
      CStarCompletion region

    completionNorm :
      {region : AQFT.Region} →
      CStarCompletion region →
      RA.ℝ

    completionEmbedPreservesNormTarget :
      {region : AQFT.Region} →
      (a : AlgebraicAlgebra region) →
      completionNorm (completionEmbed a)
      ≡
      algebraicNorm a

    CompletionCStarAlgebraWitness :
      AQFT.Region →
      Set

    universalPropertyTarget :
      {TargetCStarAlgebra : AQFT.Region → Set} →
      ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
      Set

    universalArrow :
      {TargetCStarAlgebra : AQFT.Region → Set} →
      ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
      ((region : AQFT.Region) →
        AlgebraicAlgebra region →
        TargetCStarAlgebra region) →
      (region : AQFT.Region) →
      CStarCompletion region →
      TargetCStarAlgebra region

    universalArrowExtendsEmbedding :
      {TargetCStarAlgebra : AQFT.Region → Set} →
      (targetNorm : (region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
      (algebraMap :
        (region : AQFT.Region) →
        AlgebraicAlgebra region →
        TargetCStarAlgebra region) →
      Set

    universalArrowUnique :
      {TargetCStarAlgebra : AQFT.Region → Set} →
      (targetNorm : (region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
      (algebraMap :
        (region : AQFT.Region) →
        AlgebraicAlgebra region →
        TargetCStarAlgebra region) →
      Set

    completionAuthority :
      RA.RealAnalysisAuthority

    cStarCompletionSafeAuthority :
      Bool

    cStarCompletionSafeAuthorityIsTrue :
      cStarCompletionSafeAuthority ≡ true

    cStarCompletionLocallyConstructed :
      Bool

    cStarCompletionLocallyConstructedIsFalse :
      cStarCompletionLocallyConstructed ≡ false

    cStarCompletionPromoted :
      Bool

    cStarCompletionPromotedIsFalse :
      cStarCompletionPromoted ≡ false

    cStarCompletionAuthorityBoundary :
      List String

open CStarCompletionUniversalPropertyAuthority public

data Gate4CStarNormEnvelopeStatus : Set where
  cstarNormEnvelopeNuclearityTargetsOnlyNoPromotion :
    Gate4CStarNormEnvelopeStatus

data Gate4CStarNormEnvelopeOpenObligation : Set where
  missingCStarNormUniquenessProof :
    Gate4CStarNormEnvelopeOpenObligation

  missingEnvelopingCStarAlgebraConstruction :
    Gate4CStarNormEnvelopeOpenObligation

  missingEnvelopeUniversalPropertyProof :
    Gate4CStarNormEnvelopeOpenObligation

  missingNuclearityProof :
    Gate4CStarNormEnvelopeOpenObligation

  missingNuclearityStabilityUnderIsotony :
    Gate4CStarNormEnvelopeOpenObligation

canonicalGate4CStarNormEnvelopeOpenObligations :
  List Gate4CStarNormEnvelopeOpenObligation
canonicalGate4CStarNormEnvelopeOpenObligations =
  missingCStarNormUniquenessProof
  ∷ missingEnvelopingCStarAlgebraConstruction
  ∷ missingEnvelopeUniversalPropertyProof
  ∷ missingNuclearityProof
  ∷ missingNuclearityStabilityUnderIsotony
  ∷ []

record CStarNormUniquenessEnvelopeNuclearitySurface
  (Algebra : AQFT.Region → Set)
  (quotientNorm :
    {region : AQFT.Region} →
    Algebra region →
    RA.ℝ) : Setω where
  field
    status :
      Gate4CStarNormEnvelopeStatus

    cstarNorm :
      {region : AQFT.Region} →
      Algebra region →
      RA.ℝ

    cstarNormMatchesQuotientNorm :
      {region : AQFT.Region} →
      (a : Algebra region) →
      cstarNorm a
      ≡
      quotientNorm a

    cstarNormUniquenessTarget :
      {region : AQFT.Region} →
      (otherNorm : Algebra region → RA.ℝ) →
      Set

    EnvelopingCStarAlgebra :
      AQFT.Region →
      Set

    envelopeEmbed :
      {region : AQFT.Region} →
      Algebra region →
      EnvelopingCStarAlgebra region

    envelopeNorm :
      {region : AQFT.Region} →
      EnvelopingCStarAlgebra region →
      RA.ℝ

    envelopeEmbedIsometricTarget :
      {region : AQFT.Region} →
      (a : Algebra region) →
      envelopeNorm (envelopeEmbed a)
      ≡
      cstarNorm a

    envelopeUniversalPropertyTarget :
      {TargetCStarAlgebra : AQFT.Region → Set} →
      ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
      ((region : AQFT.Region) → Algebra region → TargetCStarAlgebra region) →
      Set

    envelopeUniversalArrowTarget :
      {TargetCStarAlgebra : AQFT.Region → Set} →
      ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
      ((region : AQFT.Region) → Algebra region → TargetCStarAlgebra region) →
      (region : AQFT.Region) →
      EnvelopingCStarAlgebra region →
      TargetCStarAlgebra region

    envelopeUniversalArrowUniqueTarget :
      {TargetCStarAlgebra : AQFT.Region → Set} →
      (targetNorm : (region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
      (algebraMap :
        (region : AQFT.Region) →
        Algebra region →
        TargetCStarAlgebra region) →
      Set

    NuclearityTarget :
      AQFT.Region →
      Set

    nuclearityStableUnderIsotonyTarget :
      {small large : AQFT.Region} →
      small AQFT.⊆ large →
      NuclearityTarget small →
      NuclearityTarget large

    nuclearityPassesToEnvelopeTarget :
      (region : AQFT.Region) →
      NuclearityTarget region →
      Set

    analyticAuthority :
      RA.RealAnalysisAuthority

    openGate4Obligations :
      List Gate4CStarNormEnvelopeOpenObligation

    openGate4ObligationsAreCanonical :
      openGate4Obligations
      ≡
      canonicalGate4CStarNormEnvelopeOpenObligations

    gate4Promoted :
      Bool

    gate4PromotedIsFalse :
      gate4Promoted ≡ false

    gate4Boundary :
      List String

open CStarNormUniquenessEnvelopeNuclearitySurface public

record ColimitCoconeShape : Setω where
  field
    CoconeDepth :
      Set

    _≤CoconeDepth_ :
      CoconeDepth →
      CoconeDepth →
      Set

    CoconeDiagramAlgebra :
      CoconeDepth →
      AQFT.Region →
      Set

    coconeDiagramMap :
      {d e : CoconeDepth} →
      d ≤CoconeDepth e →
      {region : AQFT.Region} →
      CoconeDiagramAlgebra d region →
      CoconeDiagramAlgebra e region

    CoconeColimitAlgebra :
      AQFT.Region →
      Set

    coconeLeg :
      (d : CoconeDepth) →
      {region : AQFT.Region} →
      CoconeDiagramAlgebra d region →
      CoconeColimitAlgebra region

    coconeCommutes :
      {d e : CoconeDepth} →
      d ≤CoconeDepth e →
      {region : AQFT.Region} →
      Set

open ColimitCoconeShape public

record ColimitUniversalityReceiptTarget : Setω where
  field
    Depth :
      Set

    _≤Depth_ :
      Depth →
      Depth →
      Set

    DiagramAlgebra :
      Depth →
      AQFT.Region →
      Set

    diagramMap :
      {d e : Depth} →
      d ≤Depth e →
      {region : AQFT.Region} →
      DiagramAlgebra d region →
      DiagramAlgebra e region

    ColimitAlgebra :
      AQFT.Region →
      Set

    colimitCoconeShape :
      ColimitCoconeShape

    colimitCocone :
      (d : Depth) →
      {region : AQFT.Region} →
      DiagramAlgebra d region →
      ColimitAlgebra region

    colimitCoconeCommutes :
      {d e : Depth} →
      d ≤Depth e →
      {region : AQFT.Region} →
      Set

    universalMediatorTarget :
      {TargetAlgebra : AQFT.Region → Set} →
      ((d : Depth) →
        {region : AQFT.Region} →
        DiagramAlgebra d region →
        TargetAlgebra region) →
      (region : AQFT.Region) →
      ColimitAlgebra region →
      TargetAlgebra region

    universalMediatorUniqueTarget :
      {TargetAlgebra : AQFT.Region → Set} →
      (cocone :
        (d : Depth) →
        {region : AQFT.Region} →
        DiagramAlgebra d region →
        TargetAlgebra region) →
      Set

    colimitUniversalityPromoted :
      Bool

    colimitUniversalityPromotedIsFalse :
      colimitUniversalityPromoted ≡ false

    colimitBoundary :
      List String

open ColimitUniversalityReceiptTarget public

record IsotonyG6DescentFromTypedNet
  (typedNetSurface : AQFT.AQFTTypedNetSurface) : Setω where
  field
    typedNetIsotony :
      {small large : AQFT.Region} →
      small AQFT.⊆ large →
      AQFT.AlgebraMorphism small large

    typedNetIsotonyFunctoriality :
      {small middle large : AQFT.Region} →
      small AQFT.⊆ middle →
      middle AQFT.⊆ large →
      Set

    typedNetG6Causality :
      (left right : AQFT.Region) →
      AQFT.CausallySeparated left right →
      Set

    typedNetDescentCompatibility :
      (region : AQFT.Region) →
      AQFT.DescentCover region →
      Set

open IsotonyG6DescentFromTypedNet public

record IsotonyG6CausalityDescentReceiptTarget : Setω where
  field
    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    typedNetLawRecord :
      IsotonyG6DescentFromTypedNet typedNetSurface

    isotonyTarget :
      {small large : AQFT.Region} →
      small AQFT.⊆ large →
      AQFT.AlgebraMorphism small large

    isotonyFunctorialityTarget :
      {small middle large : AQFT.Region} →
      small AQFT.⊆ middle →
      middle AQFT.⊆ large →
      Set

    g6CausalityTarget :
      (left right : AQFT.Region) →
      AQFT.CausallySeparated left right →
      Set

    causalReachabilityTarget :
      AQFT.Region →
      AQFT.Region →
      Set

    descentBoundaryTarget :
      (region : AQFT.Region) →
      AQFT.DescentCover region →
      Set

    isotonyCausalityDescentPromoted :
      Bool

    isotonyCausalityDescentPromotedIsFalse :
      isotonyCausalityDescentPromoted ≡ false

    isotonyCausalityDescentBoundary :
      List String

open IsotonyG6CausalityDescentReceiptTarget public

typedNetIsotonyG6DescentRecord :
  (typedNetSurface : AQFT.AQFTTypedNetSurface) →
  IsotonyG6DescentFromTypedNet typedNetSurface
typedNetIsotonyG6DescentRecord typedNetSurface =
  record
    { typedNetIsotony =
        AQFT.AQFTTypedNetSurface.isotonyMorphism typedNetSurface
    ; typedNetIsotonyFunctoriality =
        AQFT.AQFTTypedNetSurface.isotonyFunctorialityLaw typedNetSurface
    ; typedNetG6Causality =
        AQFT.AQFTTypedNetSurface.causalityLaw typedNetSurface
    ; typedNetDescentCompatibility =
        AQFT.AQFTTypedNetSurface.descentCompatibilityLaw typedNetSurface
    }

record DepthFilteredLocalAlgebraSurface : Setω where
  field
    status :
      DepthFilteredAlgebraStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    Depth :
      Set

    _≤Depth_ :
      Depth →
      Depth →
      Set

    depthReflexive :
      (d : Depth) →
      d ≤Depth d

    depthTransitive :
      {d e f : Depth} →
      d ≤Depth e →
      e ≤Depth f →
      d ≤Depth f

    commonDepthRefinement :
      (d e : Depth) →
      Set

    A_d :
      Depth →
      AQFT.Region →
      Set

    depthMap :
      {d e : Depth} →
      d ≤Depth e →
      {region : AQFT.Region} →
      A_d d region →
      A_d e region

    A_colim :
      AQFT.Region →
      Set

    colimIntro :
      (d : Depth) →
      {region : AQFT.Region} →
      A_d d region →
      A_colim region

    colimIdentifiesDepthMap :
      {d e : Depth} →
      (d≤e : d ≤Depth e) →
      {region : AQFT.Region} →
      (x : A_d d region) →
      colimIntro e (depthMap d≤e x)
      ≡
      colimIntro d x

    colimMatchesLocalAlgebra :
      (region : AQFT.Region) →
      AQFT.AQFTTypedNetSurface.Algebra typedNetSurface region
      ≡
      A_colim region

    algebraicOperationsOnColimit :
      AQFT.Region →
      Set

    cstarCompletionTarget :
      AQFT.Region →
      Set

    colimitUniversalityReceipt :
      ColimitUniversalityReceiptTarget

    cstarCompletionBoundary :
      String

    cstarCompletionBoundary-v :
      cstarCompletionBoundary
      ≡
      "algebraic-colimit-operations-do-not-construct-C-star-completion-or-representation"

    openDepthFilteredAlgebraObligations :
      List DepthFilteredAlgebraOpenObligation

    openDepthFilteredAlgebraObligationsAreCanonical :
      openDepthFilteredAlgebraObligations
      ≡
      canonicalDepthFilteredAlgebraOpenObligations

    cstarConstructionPromoted :
      Bool

    cstarConstructionPromotedIsFalse :
      cstarConstructionPromoted ≡ false

    noDepthColimitPromotionWithoutAuthority :
      DepthFilteredAlgebraPromotionAuthorityToken →
      ⊥

    depthFilteredBoundary :
      List String

open DepthFilteredLocalAlgebraSurface public

record AQFTAlgebraColimitCompletionSurface : Setω where
  field
    depthFilteredLocalAlgebraSurface :
      DepthFilteredLocalAlgebraSurface

    AlgebraicColimitAlgebra :
      AQFT.Region →
      Set

    algebraicColimitMatchesDepthColimit :
      (region : AQFT.Region) →
      AlgebraicColimitAlgebra region
      ≡
      DepthFilteredLocalAlgebraSurface.A_colim
        depthFilteredLocalAlgebraSurface
        region

    algebraicColimitOperations :
      AQFT.Region →
      Set

    algebraicColimitNorm :
      {region : AQFT.Region} →
      AlgebraicColimitAlgebra region →
      RA.ℝ

    cStarCompletionAuthority :
      CStarCompletionUniversalPropertyAuthority
        AlgebraicColimitAlgebra
        algebraicColimitNorm

    CompletedAQFTAlgebra :
      AQFT.Region →
      Set

    completedAQFTAlgebraMatchesCompletion :
      (region : AQFT.Region) →
      CompletedAQFTAlgebra region
      ≡
      CStarCompletionUniversalPropertyAuthority.CStarCompletion
        cStarCompletionAuthority
        region

    completedAQFTAlgebraMatchesTypedNetTarget :
      (region : AQFT.Region) →
      AQFT.AQFTTypedNetSurface.Algebra
        (DepthFilteredLocalAlgebraSurface.typedNetSurface
          depthFilteredLocalAlgebraSurface)
        region
      ≡
      CompletedAQFTAlgebra region

    aqftAlgebraColimitCompletionPromoted :
      Bool

    aqftAlgebraColimitCompletionPromotedIsFalse :
      aqftAlgebraColimitCompletionPromoted ≡ false

    aqftAlgebraColimitCompletionBoundary :
      List String

open AQFTAlgebraColimitCompletionSurface public

record TimeSliceFromDomainOfDependence
  (typedNetSurface : AQFT.AQFTTypedNetSurface)
  (source target : AQFT.Region) : Setω where
  field
    domainWitness :
      AQFT.DomainOfDependence source target

    inducedTimeSliceCover :
      AQFT.TimeSliceCover source target

    inducedTimeSliceMorphism :
      AQFT.AlgebraMorphism source target

    inducedTimeSliceSurjectivity :
      AQFT.AlgebraMorphismSurjective inducedTimeSliceMorphism

    inducedTimeSliceIsomorphism :
      AQFT.AlgebraIsomorphism source target

open TimeSliceFromDomainOfDependence public

record TimeSliceTheoremSurface : Setω where
  field
    status :
      TimeSliceTheoremStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    cauchySurfaceRegion :
      AQFT.Region

    targetRegion :
      AQFT.Region

    spacetimeRegion :
      AQFT.Region

    cauchySurfaceIncludedInTarget :
      cauchySurfaceRegion AQFT.⊆ targetRegion

    targetIncludedInSpacetime :
      targetRegion AQFT.⊆ spacetimeRegion

    domainOfDependence :
      AQFT.DomainOfDependence cauchySurfaceRegion targetRegion

    cauchyDomainTimeSliceRecord :
      TimeSliceFromDomainOfDependence
        typedNetSurface
        cauchySurfaceRegion
        targetRegion

    cauchyToTargetTransport :
      AQFT.AlgebraMorphism cauchySurfaceRegion targetRegion

    cauchyToTargetSurjectivityTarget :
      AQFT.AlgebraMorphismSurjective cauchyToTargetTransport

    cauchyTargetAlgebraIso :
      AQFT.AlgebraIsomorphism cauchySurfaceRegion targetRegion

    targetSpacetimeAlgebraIso :
      AQFT.AlgebraIsomorphism targetRegion spacetimeRegion

    cauchySpacetimeAlgebraIso :
      AQFT.AlgebraIsomorphism cauchySurfaceRegion spacetimeRegion

    causalReachabilityTarget :
      AQFT.Region →
      AQFT.Region →
      Set

    algebraIsoChainLabel :
      String

    algebraIsoChainLabel-v :
      algebraIsoChainLabel
      ≡
      "A(Sigma)-iso-A(O)-iso-A(M)-target-only"

    openTimeSliceTheoremObligations :
      List TimeSliceTheoremOpenObligation

    openTimeSliceTheoremObligationsAreCanonical :
      openTimeSliceTheoremObligations
      ≡
      canonicalTimeSliceTheoremOpenObligations

    timeSliceTheoremPromoted :
      Bool

    timeSliceTheoremPromotedIsFalse :
      timeSliceTheoremPromoted ≡ false

    noTimeSliceTheoremPromotionWithoutAuthority :
      TimeSliceTheoremPromotionAuthorityToken →
      ⊥

    descentColimitCaveats :
      List String

    timeSliceTheoremBoundary :
      List String

open TimeSliceTheoremSurface public

record TimeSliceKTheoreticIntermediateTarget : Setω where
  field
    timeSliceSurface :
      TimeSliceTheoremSurface

    causalReachability :
      AQFT.Region →
      AQFT.Region →
      Set

    sigmaToOIsomorphismTarget :
      AQFT.AlgebraIsomorphism
        (TimeSliceTheoremSurface.cauchySurfaceRegion timeSliceSurface)
        (TimeSliceTheoremSurface.targetRegion timeSliceSurface)

    oToSpacetimeIsomorphismTarget :
      AQFT.AlgebraIsomorphism
        (TimeSliceTheoremSurface.targetRegion timeSliceSurface)
        (TimeSliceTheoremSurface.spacetimeRegion timeSliceSurface)

    kTheoreticIntermediate :
      AQFT.Region →
      Set

    kTheoreticFunctorialityTarget :
      {source target : AQFT.Region} →
      causalReachability source target →
      kTheoreticIntermediate source →
      kTheoreticIntermediate target

    kTheoreticIntermediatePromoted :
      Bool

    kTheoreticIntermediatePromotedIsFalse :
      kTheoreticIntermediatePromoted ≡ false

    kTheoreticBoundary :
      List String

open TimeSliceKTheoreticIntermediateTarget public

data Gate5TimeSliceDependencyStatus : Set where
  massGapEnergyPositivityBWTimeSliceTargetsOnlyNoPromotion :
    Gate5TimeSliceDependencyStatus

data Gate5TimeSliceDependencyStage : Set where
  massGapDependencyStage :
    Gate5TimeSliceDependencyStage

  energyPositivityDependencyStage :
    Gate5TimeSliceDependencyStage

  bisognanoWichmannDependencyStage :
    Gate5TimeSliceDependencyStage

  timeSliceSurjectivityIsomorphismStage :
    Gate5TimeSliceDependencyStage

canonicalGate5TimeSliceDependencyStages :
  List Gate5TimeSliceDependencyStage
canonicalGate5TimeSliceDependencyStages =
  massGapDependencyStage
  ∷ energyPositivityDependencyStage
  ∷ bisognanoWichmannDependencyStage
  ∷ timeSliceSurjectivityIsomorphismStage
  ∷ []

data Gate5TimeSliceDependencyOpenObligation : Set where
  missingMassGapAcceptanceForChain :
    Gate5TimeSliceDependencyOpenObligation

  missingMassGapToEnergyPositivityTheorem :
    Gate5TimeSliceDependencyOpenObligation

  missingEnergyPositivityToSpectrumConditionTheorem :
    Gate5TimeSliceDependencyOpenObligation

  missingBisognanoWichmannTheorem :
    Gate5TimeSliceDependencyOpenObligation

  missingBWToTimeSliceSurjectivityTheorem :
    Gate5TimeSliceDependencyOpenObligation

  missingTimeSliceIsomorphismTheorem :
    Gate5TimeSliceDependencyOpenObligation

canonicalGate5TimeSliceDependencyOpenObligations :
  List Gate5TimeSliceDependencyOpenObligation
canonicalGate5TimeSliceDependencyOpenObligations =
  missingMassGapAcceptanceForChain
  ∷ missingMassGapToEnergyPositivityTheorem
  ∷ missingEnergyPositivityToSpectrumConditionTheorem
  ∷ missingBisognanoWichmannTheorem
  ∷ missingBWToTimeSliceSurjectivityTheorem
  ∷ missingTimeSliceIsomorphismTheorem
  ∷ []

data Gate5TimeSliceDependencyPromotionAuthorityToken : Set where

data ReehSchliederForDASHIStatus : Set where
  reehSchliederClosedImmediateFromDASHIReceiptDependencies :
    ReehSchliederForDASHIStatus

data ReehSchliederProofRouteStage : Set where
  positiveEnergyToHolomorphicWightmanForwardTube :
    ReehSchliederProofRouteStage

  edgeOfTheWedgeContinuation :
    ReehSchliederProofRouteStage

  timeSlicePoincareCovariancePropagation :
    ReehSchliederProofRouteStage

  irreducibilityHaagDualityVacuumCyclicity :
    ReehSchliederProofRouteStage

canonicalReehSchliederProofRouteStages :
  List ReehSchliederProofRouteStage
canonicalReehSchliederProofRouteStages =
  positiveEnergyToHolomorphicWightmanForwardTube
  ∷ edgeOfTheWedgeContinuation
  ∷ timeSlicePoincareCovariancePropagation
  ∷ irreducibilityHaagDualityVacuumCyclicity
  ∷ []

record EnergyPositivityFromMassGapTarget : Setω where
  field
    massGapReceipt :
      MassGap.BalabanRGMassGapReceiptSurface

    energyPositivityTarget :
      Set

    massGapImpliesEnergyPositivityTarget :
      MassGap.BalabanRGMassGapReceiptSurface.massGapPromotedByDASHI
        massGapReceipt
      ≡
      true →
      energyPositivityTarget

    spectrumConditionTarget :
      Set

    energyPositivitySuppliesSpectrumConditionTarget :
      energyPositivityTarget →
      spectrumConditionTarget

    energyPositivityBoundary :
      List String

open EnergyPositivityFromMassGapTarget public

record BisognanoWichmannFromEnergyPositivityTarget : Setω where
  field
    energyPositivityReceipt :
      EnergyPositivityFromMassGapTarget

    modularTheoryReceipt :
      Modular.ModularTheoryReceiptSurface

    bisognanoWichmannTarget :
      Modular.BisognanoWichmannReceiptTarget

    bisognanoWichmannAuthorityReceipt :
      Modular.BisognanoWichmannAuthorityReceipt

    spectrumConditionFeedsBWTarget :
      EnergyPositivityFromMassGapTarget.spectrumConditionTarget
        energyPositivityReceipt →
      Modular.BisognanoWichmannReceiptTarget.spectrumConditionTarget
        bisognanoWichmannTarget

    bwFeedsWedgeModularCovarianceTarget :
      Modular.BisognanoWichmannDependency
        (Modular.BisognanoWichmannReceiptTarget.wedgeRegion
          bisognanoWichmannTarget) →
      Set

    bwDependencyBoundary :
      List String

open BisognanoWichmannFromEnergyPositivityTarget public

record TimeSliceSurjectivityIsomorphismTarget
  (typedNetSurface : AQFT.AQFTTypedNetSurface)
  (source target : AQFT.Region) : Setω where
  field
    timeSliceCover :
      AQFT.TimeSliceCover source target

    timeSliceMorphism :
      AQFT.AlgebraMorphism source target

    timeSliceMorphismIsTypedNetMorphism :
      timeSliceMorphism
      ≡
      AQFT.AQFTTypedNetSurface.timeSliceLaw
        typedNetSurface
        timeSliceCover

    timeSliceSurjectivityTarget :
      AQFT.AlgebraMorphismSurjective timeSliceMorphism

    timeSliceIsomorphismTarget :
      AQFT.AlgebraIsomorphism source target

    timeSliceIsomorphismMatchesTypedNetTarget :
      timeSliceIsomorphismTarget
      ≡
      AQFT.AQFTTypedNetSurface.timeSliceIsomorphismTarget
        typedNetSurface
        timeSliceCover

    surjectivityIsomorphismBoundary :
      List String

open TimeSliceSurjectivityIsomorphismTarget public

record BisognanoWichmannToTimeSliceReceipt : Setω where
  field
    geometricBisognanoWichmannNetReceipt :
      Modular.GeometricBisognanoWichmannNetReceipt

    timeSliceSurface :
      TimeSliceTheoremSurface

    modularFlowEqualsBoostFlowTarget :
      Modular.GeometricBisognanoWichmannNetReceipt.haagDualityHypothesis
        geometricBisognanoWichmannNetReceipt →
      Modular.GeometricBisognanoWichmannNetReceipt.poincareCovarianceHypothesis
        geometricBisognanoWichmannNetReceipt →
      Modular.GeometricBisognanoWichmannNetReceipt.positiveEnergyHypothesis
        geometricBisognanoWichmannNetReceipt →
      Modular.GeometricBisognanoWichmannNetReceipt.cyclicSeparatingVacuumStandardnessHypothesis
        geometricBisognanoWichmannNetReceipt →
      Modular.GeometricBisognanoWichmannNetReceipt.wedgeModularFlow
        geometricBisognanoWichmannNetReceipt
      ≡
      Modular.GeometricBisognanoWichmannNetReceipt.wedgeBoostAutomorphismFlow
        geometricBisognanoWichmannNetReceipt

    tomitaConjugationWedgeComplementTarget :
      Set

    wedgeCoverIterationTarget :
      Set

    cauchySurfaceSpacetimeIsomorphismTarget :
      AQFT.AlgebraIsomorphism
        (TimeSliceTheoremSurface.cauchySurfaceRegion timeSliceSurface)
        (TimeSliceTheoremSurface.spacetimeRegion timeSliceSurface)

    cauchySurfaceSpacetimeTargetLabel :
      String

    cauchySurfaceSpacetimeTargetLabel-v :
      cauchySurfaceSpacetimeTargetLabel
      ≡
      "A(Sigma) ~= A(M)"

    bwToTimeSlicePromoted :
      Bool

    bwToTimeSlicePromotedIsFalse :
      bwToTimeSlicePromoted ≡ false

    bwToTimeSliceBoundary :
      List String

open BisognanoWichmannToTimeSliceReceipt public

record TimeSliceClosureModuloBisognanoWichmannReceipt : Setω where
  field
    bisognanoWichmannAuthorityReceipt :
      Modular.BisognanoWichmannAuthorityReceipt

    geometricBisognanoWichmannNetReceipt :
      Modular.GeometricBisognanoWichmannNetReceipt

    timeSliceSurface :
      TimeSliceTheoremSurface

    timeSliceSurjectivityIsomorphism :
      TimeSliceSurjectivityIsomorphismTarget
        (TimeSliceTheoremSurface.typedNetSurface timeSliceSurface)
        (TimeSliceTheoremSurface.cauchySurfaceRegion timeSliceSurface)
        (TimeSliceTheoremSurface.targetRegion timeSliceSurface)

    bwToTimeSliceReceipt :
      BisognanoWichmannToTimeSliceReceipt

    closureModulusLabel :
      String

    closureModulusLabel-v :
      closureModulusLabel
      ≡
      "BisognanoWichmann"

    timeSliceClosureModuloBisognanoWichmannTarget :
      Set

    timeSliceClosureModuloBWPromoted :
      Bool

    timeSliceClosureModuloBWPromotedIsFalse :
      timeSliceClosureModuloBWPromoted ≡ false

    closureModuloBWBoundary :
      List String

open TimeSliceClosureModuloBisognanoWichmannReceipt public

record MassGapEnergyPositivityBWTimeSliceDependencySurface : Setω where
  field
    status :
      Gate5TimeSliceDependencyStatus

    dependencyStages :
      List Gate5TimeSliceDependencyStage

    dependencyStagesAreCanonical :
      dependencyStages
      ≡
      canonicalGate5TimeSliceDependencyStages

    massGapReceipt :
      MassGap.BalabanRGMassGapReceiptSurface

    energyPositivityFromMassGap :
      EnergyPositivityFromMassGapTarget

    bwFromEnergyPositivity :
      BisognanoWichmannFromEnergyPositivityTarget

    timeSliceSurface :
      TimeSliceTheoremSurface

    timeSliceSurjectivityIsomorphism :
      TimeSliceSurjectivityIsomorphismTarget
        (TimeSliceTheoremSurface.typedNetSurface timeSliceSurface)
        (TimeSliceTheoremSurface.cauchySurfaceRegion timeSliceSurface)
        (TimeSliceTheoremSurface.targetRegion timeSliceSurface)

    timeSliceClosureModuloBisognanoWichmann :
      TimeSliceClosureModuloBisognanoWichmannReceipt

    bwToTimeSliceReceipt :
      BisognanoWichmannToTimeSliceReceipt

    bwToTimeSliceBridgeTarget :
      Modular.BisognanoWichmannDependency
        (Modular.BisognanoWichmannReceiptTarget.wedgeRegion
          (BisognanoWichmannFromEnergyPositivityTarget.bisognanoWichmannTarget
            bwFromEnergyPositivity)) →
      Set

    openGate5Obligations :
      List Gate5TimeSliceDependencyOpenObligation

    openGate5ObligationsAreCanonical :
      openGate5Obligations
      ≡
      canonicalGate5TimeSliceDependencyOpenObligations

    gate5Promoted :
      Bool

    gate5PromotedIsFalse :
      gate5Promoted ≡ false

    noGate5PromotionWithoutAuthority :
      Gate5TimeSliceDependencyPromotionAuthorityToken →
      ⊥

    dependencyBoundary :
      List String

open MassGapEnergyPositivityBWTimeSliceDependencySurface public

data TierBPaper3Delta3aCompletionStatus : Set where
  cstarCompletionConstructivityOneSprintTargetOnly :
    TierBPaper3Delta3aCompletionStatus

record TierBPaper3Delta3aCStarCompletionConstructivity
  (AlgebraicQuotient : AQFT.Region → Set)
  (algebraicNorm :
    {region : AQFT.Region} →
    AlgebraicQuotient region →
    RA.ℝ) : Setω where
  field
    status :
      TierBPaper3Delta3aCompletionStatus

    completionAuthority :
      CStarCompletionUniversalPropertyAuthority
        AlgebraicQuotient
        algebraicNorm

    algebraicPrequotientLabel :
      String

    algebraicPrequotientLabel-v :
      algebraicPrequotientLabel
      ≡
      "A0(O)"

    nullIdealLabel :
      String

    nullIdealLabel-v :
      nullIdealLabel
      ≡
      "I_null"

    quotientLabel :
      String

    quotientLabel-v :
      quotientLabel
      ≡
      "A0(O)/I_null"

    cubicalHITSetQuotientTarget :
      AQFT.Region →
      Set

    standardMetricCompletionAdaptationTarget :
      Set

    standardCStarCompletionAdaptationTarget :
      Set

    sprintEstimate :
      String

    sprintEstimate-v :
      sprintEstimate
      ≡
      "roughly-one-sprint-target-not-currently-inhabited"

    cubicalSetQuotientRouteRecorded :
      Bool

    cubicalSetQuotientRouteRecordedIsTrue :
      cubicalSetQuotientRouteRecorded ≡ true

    constructivityCurrentlyInhabited :
      Bool

    constructivityCurrentlyInhabitedIsFalse :
      constructivityCurrentlyInhabited ≡ false

    cstarCompletionPromoted :
      Bool

    cstarCompletionPromotedIsFalse :
      cstarCompletionPromoted ≡ false

    delta3aBoundary :
      List String

open TierBPaper3Delta3aCStarCompletionConstructivity public

data TierBPaper3Delta3bBWAuthorityCitation : Set where
  borchers1992CMP143315332 :
    TierBPaper3Delta3bBWAuthorityCitation

  brunettiGuidoLongo1993RevMathPhys4pp483to513 :
    TierBPaper3Delta3bBWAuthorityCitation

canonicalTierBPaper3Delta3bBWAuthorityCitations :
  List TierBPaper3Delta3bBWAuthorityCitation
canonicalTierBPaper3Delta3bBWAuthorityCitations =
  borchers1992CMP143315332
  ∷ brunettiGuidoLongo1993RevMathPhys4pp483to513
  ∷ []

record TierBPaper3Delta3bBWAuthorityAnchors : Setω where
  field
    gate5DependencySurface :
      MassGapEnergyPositivityBWTimeSliceDependencySurface

    bisognanoWichmannAuthorityReceipt :
      Modular.BisognanoWichmannAuthorityReceipt

    borchersCitation :
      String

    borchersCitation-v :
      borchersCitation
      ≡
      "Borchers-1992-Communications-in-Mathematical-Physics-143-315-332"

    brunettiGuidoLongoCitation :
      String

    brunettiGuidoLongoCitation-v :
      brunettiGuidoLongoCitation
      ≡
      "Brunetti-Guido-Longo-Rev-Math-Phys-4-1993-483-513"

    citationTokens :
      List TierBPaper3Delta3bBWAuthorityCitation

    citationTokensAreCanonical :
      citationTokens
      ≡
      canonicalTierBPaper3Delta3bBWAuthorityCitations

    citationAuthorityOnly :
      Bool

    citationAuthorityOnlyIsTrue :
      citationAuthorityOnly ≡ true

    localBWProofSupplied :
      Bool

    localBWProofSuppliedIsFalse :
      localBWProofSupplied ≡ false

    timeSlicePromotedByBWAnchors :
      Bool

    timeSlicePromotedByBWAnchorsIsFalse :
      timeSlicePromotedByBWAnchors ≡ false

    delta3bBoundary :
      List String

open TierBPaper3Delta3bBWAuthorityAnchors public

record ReehSchliederForDASHIReceipt : Setω where
  field
    status :
      ReehSchliederForDASHIStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    localAlgebraSurface :
      TimeSliceClosureModuloBisognanoWichmannReceipt

    gate5DependencySurface :
      MassGapEnergyPositivityBWTimeSliceDependencySurface

    geometricBisognanoWichmannNetReceipt :
      Modular.GeometricBisognanoWichmannNetReceipt

    boundedRegion :
      AQFT.Region →
      Set

    nonEmptyRegion :
      AQFT.Region →
      Set

    vacuumHilbertSpaceTarget :
      Set

    vacuumVectorOmegaTarget :
      Set

    localAlgebraOmegaDenseTarget :
      (O : AQFT.Region) →
      nonEmptyRegion O →
      boundedRegion O →
      Set

    localAlgebraOmegaDenseLabel :
      String

    localAlgebraOmegaDenseLabel-v :
      localAlgebraOmegaDenseLabel
      ≡
      "for-non-empty-bounded-O-A(O)-Omega-is-dense-in-H"

    dashiReehSchliederCyclicityTarget :
      Set

    proofRouteStages :
      List ReehSchliederProofRouteStage

    proofRouteStagesAreCanonical :
      proofRouteStages
      ≡
      canonicalReehSchliederProofRouteStages

    holomorphicWightmanForwardTubeTarget :
      Set

    edgeOfTheWedgeTarget :
      Set

    timeSlicePoincareCovarianceTarget :
      Set

    irreducibilityHaagDualityTarget :
      Set

    dependenciesPresentAsReceipts :
      Bool

    dependenciesPresentAsReceiptsIsTrue :
      dependenciesPresentAsReceipts ≡ true

    closedImmediateInDASHIReceipts :
      Bool

    closedImmediateInDASHIReceiptsIsTrue :
      closedImmediateInDASHIReceipts ≡ true

    independentNewTheoremClaimed :
      Bool

    independentNewTheoremClaimedIsFalse :
      independentNewTheoremClaimed ≡ false

    bwAuthorityPromotedHere :
      Bool

    bwAuthorityPromotedHereIsFalse :
      bwAuthorityPromotedHere ≡ false

    drAuthorityPromotedHere :
      Bool

    drAuthorityPromotedHereIsFalse :
      drAuthorityPromotedHere ≡ false

    reehSchliederBoundary :
      List String

open ReehSchliederForDASHIReceipt public

record CauchyEvolutionReceiptTarget : Setω where
  field
    status :
      CauchyEvolutionStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    CauchyCarrierData :
      AQFT.Region →
      Set

    cauchyEvolution :
      {source target : AQFT.Region} →
      AQFT.TimeSliceCover source target →
      CauchyCarrierData source →
      CauchyCarrierData target

    evolutionDeterminesTarget :
      {source target : AQFT.Region} →
      AQFT.TimeSliceCover source target →
      CauchyCarrierData source →
      Set

    timeSliceMorphismFromEvolution :
      {source target : AQFT.Region} →
      AQFT.TimeSliceCover source target →
      AQFT.AlgebraMorphism source target

    timeSliceTheoremSurface :
      TimeSliceTheoremSurface

    openCauchyEvolutionObligations :
      List CauchyEvolutionOpenObligation

    openCauchyEvolutionObligationsAreCanonical :
      openCauchyEvolutionObligations
      ≡
      canonicalCauchyEvolutionOpenObligations

    timeSlicePromoted :
      Bool

    timeSlicePromotedIsFalse :
      timeSlicePromoted ≡ false

    noTimeSlicePromotionWithoutAuthority :
      CauchyEvolutionPromotionAuthorityToken →
      ⊥

    cauchyEvolutionBoundary :
      List String

open CauchyEvolutionReceiptTarget public

record AQFTCarrierAlgebraQuotientSurface : Setω where
  field
    status :
      AQFTCarrierAlgebraQuotientStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    RestrictedCarrier :
      AQFT.Region →
      Set

    TransportEquivalent :
      {region : AQFT.Region} →
      RestrictedCarrier region →
      RestrictedCarrier region →
      Set

    transportRefl :
      {region : AQFT.Region} →
      (x : RestrictedCarrier region) →
      TransportEquivalent x x

    transportSym :
      {region : AQFT.Region} →
      {x y : RestrictedCarrier region} →
      TransportEquivalent x y →
      TransportEquivalent y x

    transportTrans :
      {region : AQFT.Region} →
      {x y z : RestrictedCarrier region} →
      TransportEquivalent x y →
      TransportEquivalent y z →
      TransportEquivalent x z

    PromotedReceipt :
      {region : AQFT.Region} →
      RestrictedCarrier region →
      Set

    promotedReceiptTransport :
      {region : AQFT.Region} →
      {x y : RestrictedCarrier region} →
      TransportEquivalent x y →
      PromotedReceipt x →
      PromotedReceipt y

    PromotedReceiptQuotient :
      AQFT.Region →
      Set

    QuotientRelation :
      {region : AQFT.Region} →
      PromotedReceiptQuotient region →
      PromotedReceiptQuotient region →
      Set

    quotientIntro :
      {region : AQFT.Region} →
      (x : RestrictedCarrier region) →
      PromotedReceipt x →
      PromotedReceiptQuotient region

    transportQuotientClass :
      {region : AQFT.Region} →
      RestrictedCarrier region →
      PromotedReceiptQuotient region

    quotientTransportStable :
      {region : AQFT.Region} →
      {x y : RestrictedCarrier region} →
      (eq : TransportEquivalent x y) →
      (receipt : PromotedReceipt x) →
      quotientIntro x receipt
      ≡
      quotientIntro y (promotedReceiptTransport eq receipt)

    quotientRelationIntro :
      {region : AQFT.Region} →
      {x y : RestrictedCarrier region} →
      (eq : TransportEquivalent x y) →
      (receipt : PromotedReceipt x) →
      QuotientRelation
        (quotientIntro x receipt)
        (quotientIntro y (promotedReceiptTransport eq receipt))

    quotientUnit :
      {region : AQFT.Region} →
      PromotedReceiptQuotient region

    quotientMul :
      {region : AQFT.Region} →
      PromotedReceiptQuotient region →
      PromotedReceiptQuotient region →
      PromotedReceiptQuotient region

    quotientStar :
      {region : AQFT.Region} →
      PromotedReceiptQuotient region →
      PromotedReceiptQuotient region

    quotientNorm :
      {region : AQFT.Region} →
      PromotedReceiptQuotient region →
      RA.ℝ

    operationLabelReceipt :
      QuotientOperationLabelReceipt

    quotientNormSurface :
      QuotientNormSurface
        RestrictedCarrier
        TransportEquivalent
        PromotedReceiptQuotient
        transportQuotientClass

    operationTransportWellDefinedReceipt :
      QuotientAlgebraOperationsTransportWellDefined
        RestrictedCarrier
        TransportEquivalent
        PromotedReceiptQuotient
        transportQuotientClass
        quotientUnit
        quotientMul
        quotientStar
        quotientNorm

    unitaryConjugationNormSocket :
      UnitaryConjugationPreservesNormSocket
        PromotedReceiptQuotient
        quotientNorm

    finiteDimensionalCStarIdentitySocket :
      FiniteDimensionalCStarIdentitySocket
        PromotedReceiptQuotient
        quotientMul
        quotientStar
        quotientNorm

    transportQuotientEquivalenceLawReceipt :
      TransportQuotientEquivalenceLawReceipt

    transportSetoidQuotientReceipt :
      TransportSetoidQuotientReceipt
        RestrictedCarrier
        TransportEquivalent
        PromotedReceiptQuotient
        transportQuotientClass

    setoidInhabitedReceipts :
      List AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

    setoidInhabitedReceiptsAreCanonical :
      setoidInhabitedReceipts
      ≡
      canonicalAQFTCarrierAlgebraQuotientSetoidInhabitedReceipts

    colimitUniversalityReceipt :
      ColimitUniversalityReceiptTarget

    cStarCompletionUniversalPropertyAuthority :
      CStarCompletionUniversalPropertyAuthority
        PromotedReceiptQuotient
        quotientNorm

    cStarNormUniquenessEnvelopeNuclearitySurface :
      CStarNormUniquenessEnvelopeNuclearitySurface
        PromotedReceiptQuotient
        quotientNorm

    aqftAlgebraColimitCompletionSurface :
      AQFTAlgebraColimitCompletionSurface

    isotonyG6CausalityDescentReceipt :
      IsotonyG6CausalityDescentReceiptTarget

    timeSliceKTheoreticIntermediateTarget :
      TimeSliceKTheoreticIntermediateTarget

    massGapEnergyPositivityBWTimeSliceDependencySurface :
      MassGapEnergyPositivityBWTimeSliceDependencySurface

    tierBPaper3Delta3aCompletionConstructivity :
      TierBPaper3Delta3aCStarCompletionConstructivity
        PromotedReceiptQuotient
        quotientNorm

    tierBPaper3Delta3bBWAuthorityAnchors :
      TierBPaper3Delta3bBWAuthorityAnchors

    quotientAlgebraWellDefinedTarget :
      String

    quotientAlgebraWellDefinedTarget-v :
      quotientAlgebraWellDefinedTarget
      ≡
      "target-only-transport-equivalence-respects-unit-product-star-and-receipt-composition"

    cstarCompletionBoundary :
      String

    cstarCompletionBoundary-v :
      cstarCompletionBoundary
      ≡
      "algebraic-star-structure-is-staged-before-any-C-star-completion-GNS-state-or-Born-rule-adapter"

    localAlgebraIsPromotedReceiptQuotient :
      (region : AQFT.Region) →
      AQFT.AQFTTypedNetSurface.Algebra typedNetSurface region
      ≡
      PromotedReceiptQuotient region

    openObligations :
      List AQFTCarrierAlgebraQuotientOpenObligation

    aqftPromoted :
      Bool

    aqftPromotedIsFalse :
      aqftPromoted ≡ false

    noPromotionWithoutAuthority :
      AQFTCarrierAlgebraPromotionAuthorityToken →
      ⊥

    quotientBoundary :
      List String

open AQFTCarrierAlgebraQuotientSurface public

postulate
  abstractRestrictedCarrier :
    AQFT.Region →
    Set

  abstractTransportEquivalent :
    {region : AQFT.Region} →
    abstractRestrictedCarrier region →
    abstractRestrictedCarrier region →
    Set

  abstractTransportRefl :
    {region : AQFT.Region} →
    (x : abstractRestrictedCarrier region) →
    abstractTransportEquivalent x x

  abstractTransportSym :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractTransportEquivalent y x

  abstractTransportTrans :
    {region : AQFT.Region} →
    {x y z : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractTransportEquivalent y z →
    abstractTransportEquivalent x z

  abstractPromotedReceipt :
    {region : AQFT.Region} →
    abstractRestrictedCarrier region →
    Set

  abstractPromotedReceiptTransport :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractPromotedReceipt x →
    abstractPromotedReceipt y

  abstractPromotedReceiptQuotient :
    AQFT.Region →
    Set

  abstractQuotientIntro :
    {region : AQFT.Region} →
    (x : abstractRestrictedCarrier region) →
    abstractPromotedReceipt x →
    abstractPromotedReceiptQuotient region

  abstractQuotientTransportStable :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    (eq : abstractTransportEquivalent x y) →
    (receipt : abstractPromotedReceipt x) →
    abstractQuotientIntro x receipt
    ≡
    abstractQuotientIntro
      y
      (abstractPromotedReceiptTransport eq receipt)

  abstractQuotientRelation :
    {region : AQFT.Region} →
    abstractPromotedReceiptQuotient region →
    abstractPromotedReceiptQuotient region →
    Set

  abstractQuotientRelationIntro :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    (eq : abstractTransportEquivalent x y) →
    (receipt : abstractPromotedReceipt x) →
    abstractQuotientRelation
      (abstractQuotientIntro x receipt)
      (abstractQuotientIntro
        y
        (abstractPromotedReceiptTransport eq receipt))

  abstractQuotientUnit :
    {region : AQFT.Region} →
    abstractPromotedReceiptQuotient region

  abstractQuotientMul :
    {region : AQFT.Region} →
    abstractPromotedReceiptQuotient region →
    abstractPromotedReceiptQuotient region →
    abstractPromotedReceiptQuotient region

  abstractQuotientStar :
    {region : AQFT.Region} →
    abstractPromotedReceiptQuotient region →
    abstractPromotedReceiptQuotient region

  abstractTransportQuotientClass :
    {region : AQFT.Region} →
    abstractRestrictedCarrier region →
    abstractPromotedReceiptQuotient region

  abstractTransportQuotientClassStable :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractTransportQuotientClass x
    ≡
    abstractTransportQuotientClass y

  abstractRestrictedCarrierNorm :
    {region : AQFT.Region} →
    abstractRestrictedCarrier region →
    RA.ℝ

  abstractQuotientNorm :
    {region : AQFT.Region} →
    abstractPromotedReceiptQuotient region →
    RA.ℝ

  abstractRestrictedCarrierNormTransportInvariant :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractRestrictedCarrierNorm x
    ≡
    abstractRestrictedCarrierNorm y

  abstractQuotientNormβ :
    {region : AQFT.Region} →
    (x : abstractRestrictedCarrier region) →
    abstractQuotientNorm (abstractTransportQuotientClass x)
    ≡
    abstractRestrictedCarrierNorm x

  abstractQuotientMulTransportWellDefined :
    {region : AQFT.Region} →
    {x x′ y y′ : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x x′ →
    abstractTransportEquivalent y y′ →
    abstractQuotientMul
      (abstractTransportQuotientClass x)
      (abstractTransportQuotientClass y)
    ≡
    abstractQuotientMul
      (abstractTransportQuotientClass x′)
      (abstractTransportQuotientClass y′)

  abstractQuotientStarTransportWellDefined :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractQuotientStar (abstractTransportQuotientClass x)
    ≡
    abstractQuotientStar (abstractTransportQuotientClass y)

  abstractQuotientNormTransportWellDefined :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractQuotientNorm (abstractTransportQuotientClass x)
    ≡
    abstractQuotientNorm (abstractTransportQuotientClass y)

  abstractLocalUnitary :
    AQFT.Region →
    Set

  abstractUnitaryConjugate :
    {region : AQFT.Region} →
    abstractLocalUnitary region →
    abstractPromotedReceiptQuotient region →
    abstractPromotedReceiptQuotient region

  abstractUnitaryConjugationPreservesNorm :
    {region : AQFT.Region} →
    (U : abstractLocalUnitary region) →
    (a : abstractPromotedReceiptQuotient region) →
    abstractQuotientNorm (abstractUnitaryConjugate U a)
    ≡
    abstractQuotientNorm a

  abstractFiniteDimensionalWitness :
    AQFT.Region →
    Set

  abstractFiniteDimensionalCStarIdentityTarget :
    {region : AQFT.Region} →
    abstractFiniteDimensionalWitness region →
    (a : abstractPromotedReceiptQuotient region) →
    abstractQuotientNorm
      (abstractQuotientMul (abstractQuotientStar a) a)
    ≡
    RA._*ℝ_ (abstractQuotientNorm a) (abstractQuotientNorm a)

  abstractFiniteDimensionalCStarAuthority :
    (region : AQFT.Region) →
    abstractFiniteDimensionalWitness region →
    Set

  abstractQuotientCStarCompletion :
    AQFT.Region →
    Set

  abstractQuotientCompletionEmbed :
    {region : AQFT.Region} →
    abstractPromotedReceiptQuotient region →
    abstractQuotientCStarCompletion region

  abstractQuotientCompletionNorm :
    {region : AQFT.Region} →
    abstractQuotientCStarCompletion region →
    RA.ℝ

  abstractQuotientCompletionEmbedPreservesNormTarget :
    {region : AQFT.Region} →
    (a : abstractPromotedReceiptQuotient region) →
    abstractQuotientCompletionNorm (abstractQuotientCompletionEmbed a)
    ≡
    abstractQuotientNorm a

  abstractQuotientCompletionCStarAlgebraWitness :
    AQFT.Region →
    Set

  abstractQuotientCompletionUniversalPropertyTarget :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    Set

  abstractQuotientCompletionUniversalArrow :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    ((region : AQFT.Region) →
      abstractPromotedReceiptQuotient region →
      TargetCStarAlgebra region) →
    (region : AQFT.Region) →
    abstractQuotientCStarCompletion region →
    TargetCStarAlgebra region

  abstractQuotientCompletionUniversalArrowExtendsEmbedding :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    (targetNorm : (region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    (algebraMap :
      (region : AQFT.Region) →
      abstractPromotedReceiptQuotient region →
      TargetCStarAlgebra region) →
    Set

  abstractQuotientCompletionUniversalArrowUnique :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    (targetNorm : (region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    (algebraMap :
      (region : AQFT.Region) →
      abstractPromotedReceiptQuotient region →
      TargetCStarAlgebra region) →
    Set

  abstractQuotientCStarNormUniquenessTarget :
    {region : AQFT.Region} →
    (otherNorm : abstractPromotedReceiptQuotient region → RA.ℝ) →
    Set

  abstractQuotientEnvelopingCStarAlgebra :
    AQFT.Region →
    Set

  abstractQuotientEnvelopeEmbed :
    {region : AQFT.Region} →
    abstractPromotedReceiptQuotient region →
    abstractQuotientEnvelopingCStarAlgebra region

  abstractQuotientEnvelopeNorm :
    {region : AQFT.Region} →
    abstractQuotientEnvelopingCStarAlgebra region →
    RA.ℝ

  abstractQuotientEnvelopeEmbedIsometricTarget :
    {region : AQFT.Region} →
    (a : abstractPromotedReceiptQuotient region) →
    abstractQuotientEnvelopeNorm (abstractQuotientEnvelopeEmbed a)
    ≡
    abstractQuotientNorm a

  abstractQuotientEnvelopeUniversalPropertyTarget :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    ((region : AQFT.Region) →
      abstractPromotedReceiptQuotient region →
      TargetCStarAlgebra region) →
    Set

  abstractQuotientEnvelopeUniversalArrowTarget :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    ((region : AQFT.Region) →
      abstractPromotedReceiptQuotient region →
      TargetCStarAlgebra region) →
    (region : AQFT.Region) →
    abstractQuotientEnvelopingCStarAlgebra region →
    TargetCStarAlgebra region

  abstractQuotientEnvelopeUniversalArrowUniqueTarget :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    (targetNorm : (region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    (algebraMap :
      (region : AQFT.Region) →
      abstractPromotedReceiptQuotient region →
      TargetCStarAlgebra region) →
    Set

  abstractQuotientNuclearityTarget :
    AQFT.Region →
    Set

  abstractQuotientNuclearityStableUnderIsotonyTarget :
    {small large : AQFT.Region} →
    small AQFT.⊆ large →
    abstractQuotientNuclearityTarget small →
    abstractQuotientNuclearityTarget large

  abstractQuotientNuclearityPassesToEnvelopeTarget :
    (region : AQFT.Region) →
    abstractQuotientNuclearityTarget region →
    Set

  abstractTransportQuotientRec :
    (region : AQFT.Region) →
    {ℓb : Level} →
    (B : Set ℓb) →
    (f : abstractRestrictedCarrier region → B) →
    ((x y : abstractRestrictedCarrier region) →
      abstractTransportEquivalent x y →
      f x ≡ f y) →
    abstractPromotedReceiptQuotient region →
    B

  abstractTransportQuotientRec-β :
    (region : AQFT.Region) →
    {ℓb : Level} →
    (B : Set ℓb) →
    (f : abstractRestrictedCarrier region → B) →
    (resp :
      (x y : abstractRestrictedCarrier region) →
      abstractTransportEquivalent x y →
      f x ≡ f y) →
    (x : abstractRestrictedCarrier region) →
    abstractTransportQuotientRec region B f resp
      (abstractTransportQuotientClass x)
    ≡
    f x

  abstractTransportQuotientElim :
    (region : AQFT.Region) →
    {ℓp : Level} →
    (P : abstractPromotedReceiptQuotient region → Set ℓp) →
    (f :
      (x : abstractRestrictedCarrier region) →
      P (abstractTransportQuotientClass x)) →
    ((x y : abstractRestrictedCarrier region) →
      (eq : abstractTransportEquivalent x y) →
      QS.subst P (abstractTransportQuotientClassStable eq) (f x)
      ≡
      f y) →
    (q : abstractPromotedReceiptQuotient region) →
    P q

  abstractTransportQuotientElim-β :
    (region : AQFT.Region) →
    {ℓp : Level} →
    (P : abstractPromotedReceiptQuotient region → Set ℓp) →
    (f :
      (x : abstractRestrictedCarrier region) →
      P (abstractTransportQuotientClass x)) →
    (resp :
      (x y : abstractRestrictedCarrier region) →
      (eq : abstractTransportEquivalent x y) →
      QS.subst P (abstractTransportQuotientClassStable eq) (f x)
      ≡
      f y) →
    (x : abstractRestrictedCarrier region) →
    abstractTransportQuotientElim region P f resp
      (abstractTransportQuotientClass x)
    ≡
    f x

  abstractLocalAlgebraIsPromotedReceiptQuotient :
    (region : AQFT.Region) →
    AQFT.AQFTTypedNetSurface.Algebra
      AQFT.canonicalAQFTTypedNetSurface
      region
    ≡
    abstractPromotedReceiptQuotient region

  abstractDepth :
    Set

  abstractDepthOrder :
    abstractDepth →
    abstractDepth →
    Set

  abstractDepthReflexive :
    (d : abstractDepth) →
    abstractDepthOrder d d

  abstractDepthTransitive :
    {d e f : abstractDepth} →
    abstractDepthOrder d e →
    abstractDepthOrder e f →
    abstractDepthOrder d f

  abstractCommonDepthRefinement :
    (d e : abstractDepth) →
    Set

  abstractDepthLocalAlgebra :
    abstractDepth →
    AQFT.Region →
    Set

  abstractDepthMap :
    {d e : abstractDepth} →
    abstractDepthOrder d e →
    {region : AQFT.Region} →
    abstractDepthLocalAlgebra d region →
    abstractDepthLocalAlgebra e region

  abstractDepthColimit :
    AQFT.Region →
    Set

  abstractDepthColimitIntro :
    (d : abstractDepth) →
    {region : AQFT.Region} →
    abstractDepthLocalAlgebra d region →
    abstractDepthColimit region

  abstractDepthColimitIdentifiesDepthMap :
    {d e : abstractDepth} →
    (d≤e : abstractDepthOrder d e) →
    {region : AQFT.Region} →
    (x : abstractDepthLocalAlgebra d region) →
    abstractDepthColimitIntro e (abstractDepthMap d≤e x)
    ≡
    abstractDepthColimitIntro d x

  abstractDepthColimitMatchesLocalAlgebra :
    (region : AQFT.Region) →
    AQFT.AQFTTypedNetSurface.Algebra
      AQFT.canonicalAQFTTypedNetSurface
      region
    ≡
    abstractDepthColimit region

  abstractAlgebraicOperationsOnColimit :
    AQFT.Region →
    Set

  abstractCStarCompletionTarget :
    AQFT.Region →
    Set

  abstractDepthColimitNorm :
    {region : AQFT.Region} →
    abstractDepthColimit region →
    RA.ℝ

  abstractDepthCompletionEmbed :
    {region : AQFT.Region} →
    abstractDepthColimit region →
    abstractCStarCompletionTarget region

  abstractDepthCompletionNorm :
    {region : AQFT.Region} →
    abstractCStarCompletionTarget region →
    RA.ℝ

  abstractDepthCompletionEmbedPreservesNormTarget :
    {region : AQFT.Region} →
    (a : abstractDepthColimit region) →
    abstractDepthCompletionNorm (abstractDepthCompletionEmbed a)
    ≡
    abstractDepthColimitNorm a

  abstractDepthCompletionCStarAlgebraWitness :
    AQFT.Region →
    Set

  abstractDepthCompletionUniversalPropertyTarget :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    Set

  abstractDepthCompletionUniversalArrow :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    ((region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    ((region : AQFT.Region) →
      abstractDepthColimit region →
      TargetCStarAlgebra region) →
    (region : AQFT.Region) →
    abstractCStarCompletionTarget region →
    TargetCStarAlgebra region

  abstractDepthCompletionUniversalArrowExtendsEmbedding :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    (targetNorm : (region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    (algebraMap :
      (region : AQFT.Region) →
      abstractDepthColimit region →
      TargetCStarAlgebra region) →
    Set

  abstractDepthCompletionUniversalArrowUnique :
    {TargetCStarAlgebra : AQFT.Region → Set} →
    (targetNorm : (region : AQFT.Region) → TargetCStarAlgebra region → RA.ℝ) →
    (algebraMap :
      (region : AQFT.Region) →
      abstractDepthColimit region →
      TargetCStarAlgebra region) →
    Set

  abstractCompletedAQFTAlgebraMatchesTypedNetTarget :
    (region : AQFT.Region) →
    AQFT.AQFTTypedNetSurface.Algebra
      AQFT.canonicalAQFTTypedNetSurface
      region
    ≡
    abstractCStarCompletionTarget region

  abstractColimitCoconeCommutes :
    {d e : abstractDepth} →
    abstractDepthOrder d e →
    {region : AQFT.Region} →
    Set

  abstractColimitUniversalMediator :
    {TargetAlgebra : AQFT.Region → Set} →
    ((d : abstractDepth) →
      {region : AQFT.Region} →
      abstractDepthLocalAlgebra d region →
      TargetAlgebra region) →
    (region : AQFT.Region) →
    abstractDepthColimit region →
    TargetAlgebra region

  abstractColimitUniversalMediatorUnique :
    {TargetAlgebra : AQFT.Region → Set} →
    (cocone :
      (d : abstractDepth) →
      {region : AQFT.Region} →
      abstractDepthLocalAlgebra d region →
      TargetAlgebra region) →
    Set

  abstractCauchyCarrierData :
    AQFT.Region →
    Set

  abstractCauchyEvolution :
    {source target : AQFT.Region} →
    AQFT.TimeSliceCover source target →
    abstractCauchyCarrierData source →
    abstractCauchyCarrierData target

  abstractEvolutionDeterminesTarget :
    {source target : AQFT.Region} →
    AQFT.TimeSliceCover source target →
    abstractCauchyCarrierData source →
    Set

  abstractCauchySurfaceRegion :
    AQFT.Region

  abstractTargetRegion :
    AQFT.Region

  abstractSpacetimeRegion :
    AQFT.Region

  abstractCauchySurfaceIncludedInTarget :
    abstractCauchySurfaceRegion AQFT.⊆ abstractTargetRegion

  abstractTargetIncludedInSpacetime :
    abstractTargetRegion AQFT.⊆ abstractSpacetimeRegion

  abstractDomainOfDependence :
    AQFT.DomainOfDependence
      abstractCauchySurfaceRegion
      abstractTargetRegion

  abstractTargetSpacetimeAlgebraIso :
    AQFT.AlgebraIsomorphism
      abstractTargetRegion
      abstractSpacetimeRegion

  abstractCauchySpacetimeAlgebraIso :
    AQFT.AlgebraIsomorphism
      abstractCauchySurfaceRegion
      abstractSpacetimeRegion

  abstractCausalReachability :
    AQFT.Region →
    AQFT.Region →
    Set

  abstractKTheoreticIntermediate :
    AQFT.Region →
    Set

  abstractKTheoreticFunctorialityTarget :
    {source target : AQFT.Region} →
    abstractCausalReachability source target →
    abstractKTheoreticIntermediate source →
    abstractKTheoreticIntermediate target

  abstractEnergyPositivityTarget :
    Set

  abstractMassGapImpliesEnergyPositivityTarget :
    MassGap.BalabanRGMassGapReceiptSurface.massGapPromotedByDASHI
      MassGap.canonicalBalabanRGMassGapReceiptSurface
    ≡
    true →
    abstractEnergyPositivityTarget

  abstractSpectrumConditionFromEnergyTarget :
    Set

  abstractEnergyPositivitySuppliesSpectrumConditionTarget :
    abstractEnergyPositivityTarget →
    abstractSpectrumConditionFromEnergyTarget

  abstractSpectrumConditionFeedsBWTarget :
    abstractSpectrumConditionFromEnergyTarget →
    Modular.BisognanoWichmannReceiptTarget.spectrumConditionTarget
      Modular.canonicalBisognanoWichmannReceiptTarget

  abstractBWFeedsWedgeModularCovarianceTarget :
    Modular.BisognanoWichmannDependency
      (Modular.BisognanoWichmannReceiptTarget.wedgeRegion
        Modular.canonicalBisognanoWichmannReceiptTarget) →
    Set

  abstractBWToTimeSliceBridgeTarget :
    Modular.BisognanoWichmannDependency
      (Modular.BisognanoWichmannReceiptTarget.wedgeRegion
        Modular.canonicalBisognanoWichmannReceiptTarget) →
    Set

  abstractBWTimeSliceWedgeCoverIterationTarget :
    Set

  abstractTimeSliceClosureModuloBisognanoWichmannTarget :
    Set

  abstractDelta3aCubicalHITSetQuotientTarget :
    AQFT.Region →
    Set

  abstractDelta3aStandardMetricCompletionAdaptationTarget :
    Set

  abstractDelta3aStandardCStarCompletionAdaptationTarget :
    Set

canonicalTransportEquivalenceRelation :
  TransportEquivalenceRelation
    abstractRestrictedCarrier
    abstractTransportEquivalent
canonicalTransportEquivalenceRelation =
  record
    { transportReflexive =
        abstractTransportRefl
    ; transportSymmetric =
        abstractTransportSym
    ; transportTransitive =
        abstractTransportTrans
    }

canonicalTransportSetoidQuotientAt :
  (region : AQFT.Region) →
  QS.SetoidQuotientSurface
    (transportSetoidFromRelation
      abstractRestrictedCarrier
      abstractTransportEquivalent
      canonicalTransportEquivalenceRelation
      region)
    lzero
canonicalTransportSetoidQuotientAt region =
  record
    { QuotientCarrier =
        abstractPromotedReceiptQuotient region
    ; quotientClass =
        λ x →
          abstractTransportQuotientClass {region} x
    ; quotientSound =
        λ {x} {y} eq →
          abstractTransportQuotientClassStable {region} {x} {y} eq
    ; quotientRec =
        λ B f resp q →
          abstractTransportQuotientRec region B f resp q
    ; quotientRec-β =
        λ B f resp x →
          abstractTransportQuotientRec-β region B f resp x
    ; quotientElim =
        λ P f resp q →
          abstractTransportQuotientElim region P f resp q
    ; quotientElim-β =
        λ P f resp x →
          abstractTransportQuotientElim-β region P f resp x
    }

canonicalTransportSetoidQuotientReceipt :
  TransportSetoidQuotientReceipt
    abstractRestrictedCarrier
    abstractTransportEquivalent
    abstractPromotedReceiptQuotient
    abstractTransportQuotientClass
canonicalTransportSetoidQuotientReceipt =
  record
    { transportEquivalenceRecord =
        canonicalTransportEquivalenceRelation
    ; setoidQuotientAt =
        canonicalTransportSetoidQuotientAt
    ; quotientExtensionalityDischargesTransportStability =
        λ {region} {x} {y} eq →
          QS.quotientStable
            (canonicalTransportSetoidQuotientAt region)
            {x}
            {y}
            eq
    ; quotientEliminatorBoundary =
        "transport equivalence is exposed as a non-cubical setoid for each AQFT region"
        ∷ "quotientSound discharges carrier-class stability under transport equivalence"
        ∷ "quotientRec and quotientElim are authority fields for maps and dependent predicates that respect transport"
        ∷ "this is an eliminator surface only; it does not construct a HIT quotient or C-star completion"
        ∷ []
    }

canonicalQuotientTransportStability :
  QuotientTransportStability
    abstractRestrictedCarrier
    abstractTransportEquivalent
    abstractPromotedReceiptQuotient
    abstractTransportQuotientClass
canonicalQuotientTransportStability =
  record
    { transportEquivalenceRelation =
        canonicalTransportEquivalenceRelation
    ; quotientStable =
        TransportSetoidQuotientReceipt.quotientExtensionalityDischargesTransportStability
          canonicalTransportSetoidQuotientReceipt
    }

canonicalQuotientNormSurface :
  QuotientNormSurface
    abstractRestrictedCarrier
    abstractTransportEquivalent
    abstractPromotedReceiptQuotient
    abstractTransportQuotientClass
canonicalQuotientNormSurface =
  record
    { carrierNormTarget =
        abstractRestrictedCarrierNorm
    ; quotientNorm =
        abstractQuotientNorm
    ; carrierNormTransportInvariant =
        abstractRestrictedCarrierNormTransportInvariant
    ; quotientNormβ =
        abstractQuotientNormβ
    ; quotientNormPromoted =
        false
    ; quotientNormPromotedIsFalse =
        refl
    ; quotientNormBoundary =
        "quotientNorm is the descended norm socket for transport classes"
        ∷ "carrier norm invariance under transport and the quotient beta law are abstract authority fields"
        ∷ "no C*-identity, completeness theorem, or representation is proved by this norm surface"
        ∷ []
    }

canonicalQuotientAlgebraOperationsTransportWellDefined :
  QuotientAlgebraOperationsTransportWellDefined
    abstractRestrictedCarrier
    abstractTransportEquivalent
    abstractPromotedReceiptQuotient
    abstractTransportQuotientClass
    abstractQuotientUnit
    abstractQuotientMul
    abstractQuotientStar
    abstractQuotientNorm
canonicalQuotientAlgebraOperationsTransportWellDefined =
  record
    { quotientClassTransportStable =
        abstractTransportQuotientClassStable
    ; quotientUnitTransportInvariant =
        λ _ → refl
    ; quotientMulTransportWellDefined =
        abstractQuotientMulTransportWellDefined
    ; quotientStarTransportWellDefined =
        abstractQuotientStarTransportWellDefined
    ; quotientNormTransportWellDefined =
        abstractQuotientNormTransportWellDefined
    ; operationTransportBoundary =
        "unit, multiplication, star, and norm are exposed with transport-well-defined sockets"
        ∷ "the product, star, and norm compatibility proofs are abstract obligations over quotient classes"
        ∷ "this receipt does not add associativity, unit laws, C*-identity, or completion"
        ∷ []
    }

canonicalUnitaryConjugationPreservesNormSocket :
  UnitaryConjugationPreservesNormSocket
    abstractPromotedReceiptQuotient
    abstractQuotientNorm
canonicalUnitaryConjugationPreservesNormSocket =
  record
    { LocalUnitary =
        abstractLocalUnitary
    ; unitaryConjugate =
        abstractUnitaryConjugate
    ; unitaryNormAuthority =
        RA.postulatedRealAnalysisAuthority
    ; unitaryConjugationPreservesNorm =
        abstractUnitaryConjugationPreservesNorm
    ; unitaryConjugationPromoted =
        false
    ; unitaryConjugationPromotedIsFalse =
        refl
    ; unitaryConjugationBoundary =
        "unitary conjugation is present only as a norm-preservation socket"
        ∷ "the analytic authority is routed through RealAnalysisAxioms, not proved here"
        ∷ "no Hilbert representation, GNS state, or automorphism group is constructed"
        ∷ []
    }

canonicalFiniteDimensionalCStarIdentitySocket :
  FiniteDimensionalCStarIdentitySocket
    abstractPromotedReceiptQuotient
    abstractQuotientMul
    abstractQuotientStar
    abstractQuotientNorm
canonicalFiniteDimensionalCStarIdentitySocket =
  record
    { FiniteDimensionalWitness =
        abstractFiniteDimensionalWitness
    ; finiteDimensionalCStarIdentityTarget =
        abstractFiniteDimensionalCStarIdentityTarget
    ; finiteDimensionalCStarAuthority =
        abstractFiniteDimensionalCStarAuthority
    ; finiteDimensionalCStarPromoted =
        false
    ; finiteDimensionalCStarPromotedIsFalse =
        refl
    ; finiteDimensionalCStarBoundary =
        "the finite-dimensional C*-identity is a socket guarded by a finite-dimensional witness"
        ∷ "the identity ||a* a|| = ||a|| * ||a|| is not globally promoted for quotient algebras"
        ∷ "no infinite-dimensional completion or representation theorem follows from this socket"
        ∷ []
    }

canonicalQuotientCStarCompletionUniversalPropertyAuthority :
  CStarCompletionUniversalPropertyAuthority
    abstractPromotedReceiptQuotient
    abstractQuotientNorm
canonicalQuotientCStarCompletionUniversalPropertyAuthority =
  record
    { CStarCompletion =
        abstractQuotientCStarCompletion
    ; completionEmbed =
        abstractQuotientCompletionEmbed
    ; completionNorm =
        abstractQuotientCompletionNorm
    ; completionEmbedPreservesNormTarget =
        abstractQuotientCompletionEmbedPreservesNormTarget
    ; CompletionCStarAlgebraWitness =
        abstractQuotientCompletionCStarAlgebraWitness
    ; universalPropertyTarget =
        abstractQuotientCompletionUniversalPropertyTarget
    ; universalArrow =
        abstractQuotientCompletionUniversalArrow
    ; universalArrowExtendsEmbedding =
        abstractQuotientCompletionUniversalArrowExtendsEmbedding
    ; universalArrowUnique =
        abstractQuotientCompletionUniversalArrowUnique
    ; completionAuthority =
        RA.postulatedRealAnalysisAuthority
    ; cStarCompletionSafeAuthority =
        true
    ; cStarCompletionSafeAuthorityIsTrue =
        refl
    ; cStarCompletionLocallyConstructed =
        false
    ; cStarCompletionLocallyConstructedIsFalse =
        refl
    ; cStarCompletionPromoted =
        false
    ; cStarCompletionPromotedIsFalse =
        refl
    ; cStarCompletionAuthorityBoundary =
        "C*-completion is exposed as a safe authority surface with embedding, norm, mediator, and uniqueness targets"
        ∷ "the completion carrier is postulated as an authority target and is not locally constructed"
        ∷ "the universal property is named but not proved or promoted"
        ∷ "completion remains separate from GNS, Born-rule adapters, and interacting AQFT promotion"
        ∷ []
    }

canonicalTierBPaper3Delta3aCStarCompletionConstructivity :
  TierBPaper3Delta3aCStarCompletionConstructivity
    abstractPromotedReceiptQuotient
    abstractQuotientNorm
canonicalTierBPaper3Delta3aCStarCompletionConstructivity =
  record
    { status =
        cstarCompletionConstructivityOneSprintTargetOnly
    ; completionAuthority =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; algebraicPrequotientLabel =
        "A0(O)"
    ; algebraicPrequotientLabel-v =
        refl
    ; nullIdealLabel =
        "I_null"
    ; nullIdealLabel-v =
        refl
    ; quotientLabel =
        "A0(O)/I_null"
    ; quotientLabel-v =
        refl
    ; cubicalHITSetQuotientTarget =
        abstractDelta3aCubicalHITSetQuotientTarget
    ; standardMetricCompletionAdaptationTarget =
        abstractDelta3aStandardMetricCompletionAdaptationTarget
    ; standardCStarCompletionAdaptationTarget =
        abstractDelta3aStandardCStarCompletionAdaptationTarget
    ; sprintEstimate =
        "roughly-one-sprint-target-not-currently-inhabited"
    ; sprintEstimate-v =
        refl
    ; cubicalSetQuotientRouteRecorded =
        true
    ; cubicalSetQuotientRouteRecordedIsTrue =
        refl
    ; constructivityCurrentlyInhabited =
        false
    ; constructivityCurrentlyInhabitedIsFalse =
        refl
    ; cstarCompletionPromoted =
        false
    ; cstarCompletionPromotedIsFalse =
        refl
    ; delta3aBoundary =
        "Delta 3a records the constructivity route A0(O)/I_null via Cubical HIT or set quotient"
        ∷ "The standard metric completion and standard C*-completion arguments are adaptation targets, not local inhabitants"
        ∷ "The expected implementation size is roughly one sprint, but this surface records it as not currently inhabited"
        ∷ "No C*-completion, GNS state, Born-rule adapter, or promoted AQFT net follows from this accounting item"
        ∷ []
    }

canonicalCStarNormUniquenessEnvelopeNuclearitySurface :
  CStarNormUniquenessEnvelopeNuclearitySurface
    abstractPromotedReceiptQuotient
    abstractQuotientNorm
canonicalCStarNormUniquenessEnvelopeNuclearitySurface =
  record
    { status =
        cstarNormEnvelopeNuclearityTargetsOnlyNoPromotion
    ; cstarNorm =
        abstractQuotientNorm
    ; cstarNormMatchesQuotientNorm =
        λ _ → refl
    ; cstarNormUniquenessTarget =
        abstractQuotientCStarNormUniquenessTarget
    ; EnvelopingCStarAlgebra =
        abstractQuotientEnvelopingCStarAlgebra
    ; envelopeEmbed =
        abstractQuotientEnvelopeEmbed
    ; envelopeNorm =
        abstractQuotientEnvelopeNorm
    ; envelopeEmbedIsometricTarget =
        abstractQuotientEnvelopeEmbedIsometricTarget
    ; envelopeUniversalPropertyTarget =
        abstractQuotientEnvelopeUniversalPropertyTarget
    ; envelopeUniversalArrowTarget =
        abstractQuotientEnvelopeUniversalArrowTarget
    ; envelopeUniversalArrowUniqueTarget =
        abstractQuotientEnvelopeUniversalArrowUniqueTarget
    ; NuclearityTarget =
        abstractQuotientNuclearityTarget
    ; nuclearityStableUnderIsotonyTarget =
        abstractQuotientNuclearityStableUnderIsotonyTarget
    ; nuclearityPassesToEnvelopeTarget =
        abstractQuotientNuclearityPassesToEnvelopeTarget
    ; analyticAuthority =
        RA.postulatedRealAnalysisAuthority
    ; openGate4Obligations =
        canonicalGate4CStarNormEnvelopeOpenObligations
    ; openGate4ObligationsAreCanonical =
        refl
    ; gate4Promoted =
        false
    ; gate4PromotedIsFalse =
        refl
    ; gate4Boundary =
        "Gate 4 records C*-norm uniqueness, enveloping C*-algebra, and nuclearity as typed targets"
        ∷ "the quotient norm is reused as the candidate C*-norm, but uniqueness is an external target"
        ∷ "the envelope exposes embed, isometry, mediator, and uniqueness targets without constructing the C*-envelope"
        ∷ "nuclearity and stability under isotony remain analytic authority obligations"
        ∷ "no GNS representation, Born-rule adapter, interacting net, or AQFT promotion follows here"
        ∷ []
    }

canonicalColimitCoconeShape :
  ColimitCoconeShape
canonicalColimitCoconeShape =
  record
    { CoconeDepth =
        abstractDepth
    ; _≤CoconeDepth_ =
        abstractDepthOrder
    ; CoconeDiagramAlgebra =
        abstractDepthLocalAlgebra
    ; coconeDiagramMap =
        λ {d} {e} d≤e {region} x →
          abstractDepthMap {d} {e} d≤e {region} x
    ; CoconeColimitAlgebra =
        abstractDepthColimit
    ; coconeLeg =
        λ d {region} x →
          abstractDepthColimitIntro d {region} x
    ; coconeCommutes =
        λ {d} {e} d≤e {region} →
          abstractColimitCoconeCommutes {d} {e} d≤e {region}
    }

canonicalCauchyDomainTimeSliceRecord :
  TimeSliceFromDomainOfDependence
    AQFT.canonicalAQFTTypedNetSurface
    abstractCauchySurfaceRegion
    abstractTargetRegion
canonicalCauchyDomainTimeSliceRecord =
  record
    { domainWitness =
        abstractDomainOfDependence
    ; inducedTimeSliceCover =
        AQFT.AQFTTypedNetSurface.domainOfDependenceGivesTimeSlice
          AQFT.canonicalAQFTTypedNetSurface
          abstractDomainOfDependence
    ; inducedTimeSliceMorphism =
        AQFT.AQFTTypedNetSurface.timeSliceLaw
          AQFT.canonicalAQFTTypedNetSurface
          (AQFT.AQFTTypedNetSurface.domainOfDependenceGivesTimeSlice
            AQFT.canonicalAQFTTypedNetSurface
            abstractDomainOfDependence)
    ; inducedTimeSliceSurjectivity =
        AQFT.AQFTTypedNetSurface.timeSliceSurjectivityTarget
          AQFT.canonicalAQFTTypedNetSurface
          (AQFT.AQFTTypedNetSurface.domainOfDependenceGivesTimeSlice
            AQFT.canonicalAQFTTypedNetSurface
            abstractDomainOfDependence)
    ; inducedTimeSliceIsomorphism =
        AQFT.AQFTTypedNetSurface.timeSliceIsomorphismTarget
          AQFT.canonicalAQFTTypedNetSurface
          (AQFT.AQFTTypedNetSurface.domainOfDependenceGivesTimeSlice
            AQFT.canonicalAQFTTypedNetSurface
            abstractDomainOfDependence)
    }

canonicalTransportQuotientEquivalenceLawReceipt :
  TransportQuotientEquivalenceLawReceipt
canonicalTransportQuotientEquivalenceLawReceipt =
  record
    { Carrier =
        abstractRestrictedCarrier
    ; TransportEquivalent =
        abstractTransportEquivalent
    ; QuotientCarrier =
        abstractPromotedReceiptQuotient
    ; quotientClass =
        abstractTransportQuotientClass
    ; transportEquivalenceRecord =
        canonicalTransportEquivalenceRelation
    ; quotientTransportStabilityRecord =
        canonicalQuotientTransportStability
    ; transportReflexiveTarget =
        abstractTransportRefl
    ; transportSymmetricTarget =
        abstractTransportSym
    ; transportTransitiveTarget =
        abstractTransportTrans
    ; quotientStableUnderTransport =
        TransportSetoidQuotientReceipt.quotientExtensionalityDischargesTransportStability
          canonicalTransportSetoidQuotientReceipt
    ; quotientEquivalencePromoted =
        false
    ; quotientEquivalencePromotedIsFalse =
        refl
    ; quotientEquivalenceBoundary =
        "transport equivalence is packaged as a reflexive, symmetric, transitive relation record"
        ∷ "quotient stability under transport is discharged through the setoid quotient soundness field"
        ∷ "the eliminator is an authority surface for respectful maps; it does not prove C-star completion or full AQFT promotion"
        ∷ []
    }

canonicalColimitUniversalityReceiptTarget :
  ColimitUniversalityReceiptTarget
canonicalColimitUniversalityReceiptTarget =
  record
    { Depth =
        abstractDepth
    ; _≤Depth_ =
        abstractDepthOrder
    ; DiagramAlgebra =
        abstractDepthLocalAlgebra
    ; diagramMap =
        λ {d} {e} d≤e {region} x →
          abstractDepthMap {d} {e} d≤e {region} x
    ; ColimitAlgebra =
        abstractDepthColimit
    ; colimitCoconeShape =
        canonicalColimitCoconeShape
    ; colimitCocone =
        λ d {region} x →
          abstractDepthColimitIntro d {region} x
    ; colimitCoconeCommutes =
        λ {d} {e} d≤e {region} →
          abstractColimitCoconeCommutes {d} {e} d≤e {region}
    ; universalMediatorTarget =
        abstractColimitUniversalMediator
    ; universalMediatorUniqueTarget =
        abstractColimitUniversalMediatorUnique
    ; colimitUniversalityPromoted =
        false
    ; colimitUniversalityPromotedIsFalse =
        refl
    ; colimitBoundary =
        "filtered-colimit universality is a typed target with cocone and mediator fields"
        ∷ "unique mediation and compatibility with quotient operations remain target obligations"
        ∷ "no C-star completion, representation, or full local-net theorem is promoted here"
        ∷ []
    }

canonicalDepthCStarCompletionUniversalPropertyAuthority :
  CStarCompletionUniversalPropertyAuthority
    abstractDepthColimit
    abstractDepthColimitNorm
canonicalDepthCStarCompletionUniversalPropertyAuthority =
  record
    { CStarCompletion =
        abstractCStarCompletionTarget
    ; completionEmbed =
        abstractDepthCompletionEmbed
    ; completionNorm =
        abstractDepthCompletionNorm
    ; completionEmbedPreservesNormTarget =
        abstractDepthCompletionEmbedPreservesNormTarget
    ; CompletionCStarAlgebraWitness =
        abstractDepthCompletionCStarAlgebraWitness
    ; universalPropertyTarget =
        abstractDepthCompletionUniversalPropertyTarget
    ; universalArrow =
        abstractDepthCompletionUniversalArrow
    ; universalArrowExtendsEmbedding =
        abstractDepthCompletionUniversalArrowExtendsEmbedding
    ; universalArrowUnique =
        abstractDepthCompletionUniversalArrowUnique
    ; completionAuthority =
        RA.postulatedRealAnalysisAuthority
    ; cStarCompletionSafeAuthority =
        true
    ; cStarCompletionSafeAuthorityIsTrue =
        refl
    ; cStarCompletionLocallyConstructed =
        false
    ; cStarCompletionLocallyConstructedIsFalse =
        refl
    ; cStarCompletionPromoted =
        false
    ; cStarCompletionPromotedIsFalse =
        refl
    ; cStarCompletionAuthorityBoundary =
        "the algebraic filtered colimit has a separate safe C*-completion authority surface"
        ∷ "the completion carrier is postulated as an authority target and is not locally constructed"
        ∷ "embedding, norm preservation, universal arrow, and uniqueness remain target fields"
        ∷ "this authority does not identify completion with a represented operator algebra"
        ∷ []
    }

canonicalIsotonyG6CausalityDescentReceiptTarget :
  IsotonyG6CausalityDescentReceiptTarget
canonicalIsotonyG6CausalityDescentReceiptTarget =
  record
    { typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; typedNetLawRecord =
        typedNetIsotonyG6DescentRecord AQFT.canonicalAQFTTypedNetSurface
    ; isotonyTarget =
        AQFT.AQFTTypedNetSurface.isotonyMorphism
          AQFT.canonicalAQFTTypedNetSurface
    ; isotonyFunctorialityTarget =
        AQFT.AQFTTypedNetSurface.isotonyFunctorialityLaw
          AQFT.canonicalAQFTTypedNetSurface
    ; g6CausalityTarget =
        AQFT.AQFTTypedNetSurface.causalityLaw
          AQFT.canonicalAQFTTypedNetSurface
    ; causalReachabilityTarget =
        abstractCausalReachability
    ; descentBoundaryTarget =
        AQFT.AQFTTypedNetSurface.descentCompatibilityLaw
          AQFT.canonicalAQFTTypedNetSurface
    ; isotonyCausalityDescentPromoted =
        false
    ; isotonyCausalityDescentPromotedIsFalse =
        refl
    ; isotonyCausalityDescentBoundary =
        "isotony, G6 causality, and descent compatibility are read directly from the typed AQFT net fields"
        ∷ "causal reachability remains an extra target predicate and is not constructed from those fields"
        ∷ "G6 causality is consumed only as a typed law over causal separation, not as a discharged theorem"
        ∷ "descent compatibility remains a boundary before any full AQFT net promotion"
        ∷ []
    }

canonicalTimeSliceTheoremSurface :
  TimeSliceTheoremSurface
canonicalTimeSliceTheoremSurface =
  record
    { status =
        timeSliceTheoremTargetOnlyNoPromotion
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; cauchySurfaceRegion =
        abstractCauchySurfaceRegion
    ; targetRegion =
        abstractTargetRegion
    ; spacetimeRegion =
        abstractSpacetimeRegion
    ; cauchySurfaceIncludedInTarget =
        abstractCauchySurfaceIncludedInTarget
    ; targetIncludedInSpacetime =
        abstractTargetIncludedInSpacetime
    ; domainOfDependence =
        abstractDomainOfDependence
    ; cauchyDomainTimeSliceRecord =
        canonicalCauchyDomainTimeSliceRecord
    ; cauchyToTargetTransport =
        TimeSliceFromDomainOfDependence.inducedTimeSliceMorphism
          canonicalCauchyDomainTimeSliceRecord
    ; cauchyToTargetSurjectivityTarget =
        TimeSliceFromDomainOfDependence.inducedTimeSliceSurjectivity
          canonicalCauchyDomainTimeSliceRecord
    ; cauchyTargetAlgebraIso =
        TimeSliceFromDomainOfDependence.inducedTimeSliceIsomorphism
          canonicalCauchyDomainTimeSliceRecord
    ; targetSpacetimeAlgebraIso =
        abstractTargetSpacetimeAlgebraIso
    ; cauchySpacetimeAlgebraIso =
        abstractCauchySpacetimeAlgebraIso
    ; causalReachabilityTarget =
        abstractCausalReachability
    ; algebraIsoChainLabel =
        "A(Sigma)-iso-A(O)-iso-A(M)-target-only"
    ; algebraIsoChainLabel-v =
        refl
    ; openTimeSliceTheoremObligations =
        canonicalTimeSliceTheoremOpenObligations
    ; openTimeSliceTheoremObligationsAreCanonical =
        refl
    ; timeSliceTheoremPromoted =
        false
    ; timeSliceTheoremPromotedIsFalse =
        refl
    ; noTimeSliceTheoremPromotionWithoutAuthority =
        λ ()
    ; descentColimitCaveats =
        "A(Sigma) -> A(O) is induced from domain-of-dependence through the typed net time-slice fields"
        ∷ "surjectivity is explicitly represented for the induced morphism, but remains a typed target"
        ∷ "A(O) ~= A(M) and A(Sigma) ~= A(M) remain staged as isomorphism targets, not theorems"
        ∷ "domain-of-dependence is an abstract predicate and is not proved from carrier evolution"
        ∷ "descent and filtered-colimit compatibility remain caveats before AQFT promotion"
        ∷ []
    ; timeSliceTheoremBoundary =
        "TimeSliceTheoremSurface records the Cauchy surface inclusion and domain-of-dependence witness"
        ∷ "the Cauchy-to-target cover, morphism, surjectivity target, and isomorphism are constructed from AQFTTypedNetSurface fields"
        ∷ "causal reachability is present as a target predicate, not a constructed reachability theorem"
        ∷ "it does not prove the time-slice theorem, Cauchy evolution, spacetime algebra isomorphism chain, or descent theorem"
        ∷ "it does not construct interacting AQFT, Standard Model QFT, GRQFT, or full unification"
        ∷ []
    }

canonicalTimeSliceKTheoreticIntermediateTarget :
  TimeSliceKTheoreticIntermediateTarget
canonicalTimeSliceKTheoreticIntermediateTarget =
  record
    { timeSliceSurface =
        canonicalTimeSliceTheoremSurface
    ; causalReachability =
        abstractCausalReachability
    ; sigmaToOIsomorphismTarget =
        TimeSliceFromDomainOfDependence.inducedTimeSliceIsomorphism
          canonicalCauchyDomainTimeSliceRecord
    ; oToSpacetimeIsomorphismTarget =
        abstractTargetSpacetimeAlgebraIso
    ; kTheoreticIntermediate =
        abstractKTheoreticIntermediate
    ; kTheoreticFunctorialityTarget =
        abstractKTheoreticFunctorialityTarget
    ; kTheoreticIntermediatePromoted =
        false
    ; kTheoreticIntermediatePromotedIsFalse =
        refl
    ; kTheoreticBoundary =
        "A(Sigma) -> A(O) isomorphism and A(O) -> A(M) isomorphism are time-slice targets"
        ∷ "K-theoretic intermediate classification is staged after causal reachability and before any Standard Model or GRQFT promotion"
        ∷ "no K-theory functoriality theorem, charge classification, or time-slice theorem is proved here"
        ∷ []
    }

canonicalEnergyPositivityFromMassGapTarget :
  EnergyPositivityFromMassGapTarget
canonicalEnergyPositivityFromMassGapTarget =
  record
    { massGapReceipt =
        MassGap.canonicalBalabanRGMassGapReceiptSurface
    ; energyPositivityTarget =
        abstractEnergyPositivityTarget
    ; massGapImpliesEnergyPositivityTarget =
        abstractMassGapImpliesEnergyPositivityTarget
    ; spectrumConditionTarget =
        abstractSpectrumConditionFromEnergyTarget
    ; energyPositivitySuppliesSpectrumConditionTarget =
        abstractEnergyPositivitySuppliesSpectrumConditionTarget
    ; energyPositivityBoundary =
        "MassGap -> EnergyPositivity is represented as a dependency target"
        ∷ "the mass-gap receipt is the external Balaban/Odusanya intake surface and is not accepted or promoted here"
        ∷ "positive energy and spectrum condition are downstream targets, not derived theorems"
        ∷ []
    }

canonicalBisognanoWichmannFromEnergyPositivityTarget :
  BisognanoWichmannFromEnergyPositivityTarget
canonicalBisognanoWichmannFromEnergyPositivityTarget =
  record
    { energyPositivityReceipt =
        canonicalEnergyPositivityFromMassGapTarget
    ; modularTheoryReceipt =
        Modular.canonicalModularTheoryReceiptSurface
    ; bisognanoWichmannTarget =
        Modular.canonicalBisognanoWichmannReceiptTarget
    ; bisognanoWichmannAuthorityReceipt =
        Modular.canonicalBisognanoWichmannAuthorityReceipt
    ; spectrumConditionFeedsBWTarget =
        abstractSpectrumConditionFeedsBWTarget
    ; bwFeedsWedgeModularCovarianceTarget =
        abstractBWFeedsWedgeModularCovarianceTarget
    ; bwDependencyBoundary =
        "EnergyPositivity -> BisognanoWichmann is represented through the spectrum-condition target"
        ∷ "Bisognano-Wichmann data are imported from ModularTheoryReceiptSurface as targets and a non-promoting authority receipt"
        ∷ "the Borchers/BGL authority states wedge modular flow equals boost flow under positive energy, vacuum, and covariance hypotheses"
        ∷ "Poincare covariance, wedge duality, and local modular-flow identification remain external obligations"
        ∷ []
    }

canonicalTimeSliceSurjectivityIsomorphismTarget :
  TimeSliceSurjectivityIsomorphismTarget
    AQFT.canonicalAQFTTypedNetSurface
    abstractCauchySurfaceRegion
    abstractTargetRegion
canonicalTimeSliceSurjectivityIsomorphismTarget =
  record
    { timeSliceCover =
        TimeSliceFromDomainOfDependence.inducedTimeSliceCover
          canonicalCauchyDomainTimeSliceRecord
    ; timeSliceMorphism =
        TimeSliceFromDomainOfDependence.inducedTimeSliceMorphism
          canonicalCauchyDomainTimeSliceRecord
    ; timeSliceMorphismIsTypedNetMorphism =
        refl
    ; timeSliceSurjectivityTarget =
        TimeSliceFromDomainOfDependence.inducedTimeSliceSurjectivity
          canonicalCauchyDomainTimeSliceRecord
    ; timeSliceIsomorphismTarget =
        TimeSliceFromDomainOfDependence.inducedTimeSliceIsomorphism
          canonicalCauchyDomainTimeSliceRecord
    ; timeSliceIsomorphismMatchesTypedNetTarget =
        refl
    ; surjectivityIsomorphismBoundary =
        "the time-slice morphism is explicitly paired with a surjectivity target"
        ∷ "the same cover carries the typed-net algebra isomorphism target"
        ∷ "surjectivity and isomorphism are represented, not proved from BW or carrier evolution"
        ∷ []
    }

canonicalBisognanoWichmannToTimeSliceReceipt :
  BisognanoWichmannToTimeSliceReceipt
canonicalBisognanoWichmannToTimeSliceReceipt =
  record
    { geometricBisognanoWichmannNetReceipt =
        Modular.canonicalGeometricBisognanoWichmannNetReceipt
    ; timeSliceSurface =
        canonicalTimeSliceTheoremSurface
    ; modularFlowEqualsBoostFlowTarget =
        Modular.GeometricBisognanoWichmannNetReceipt.sigmaOmegaEqualsBoostAutomorphismTarget
          Modular.canonicalGeometricBisognanoWichmannNetReceipt
    ; tomitaConjugationWedgeComplementTarget =
        Modular.GeometricBisognanoWichmannNetReceipt.modularConjugationReflectsWedgeTarget
          Modular.canonicalGeometricBisognanoWichmannNetReceipt
    ; wedgeCoverIterationTarget =
        abstractBWTimeSliceWedgeCoverIterationTarget
    ; cauchySurfaceSpacetimeIsomorphismTarget =
        abstractCauchySpacetimeAlgebraIso
    ; cauchySurfaceSpacetimeTargetLabel =
        "A(Sigma) ~= A(M)"
    ; cauchySurfaceSpacetimeTargetLabel-v =
        refl
    ; bwToTimeSlicePromoted =
        false
    ; bwToTimeSlicePromotedIsFalse =
        refl
    ; bwToTimeSliceBoundary =
        "BW -> TimeSlice receipt consumes geometric BW for nets: sigma^omega_t equals the wedge boost automorphism"
        ∷ "Tomita conjugation targets J A(W) J = A(W)' = A(W') as the wedge-complement bridge"
        ∷ "wedge cover iteration records the step from wedge modular covariance to Cauchy evolution over the spacetime cover"
        ∷ "the receipt exposes A(Sigma) ~= A(M) as an isomorphism target and remains non-promoting"
        ∷ []
    }

canonicalTimeSliceClosureModuloBisognanoWichmannReceipt :
  TimeSliceClosureModuloBisognanoWichmannReceipt
canonicalTimeSliceClosureModuloBisognanoWichmannReceipt =
  record
    { bisognanoWichmannAuthorityReceipt =
        Modular.canonicalBisognanoWichmannAuthorityReceipt
    ; geometricBisognanoWichmannNetReceipt =
        Modular.canonicalGeometricBisognanoWichmannNetReceipt
    ; timeSliceSurface =
        canonicalTimeSliceTheoremSurface
    ; timeSliceSurjectivityIsomorphism =
        canonicalTimeSliceSurjectivityIsomorphismTarget
    ; bwToTimeSliceReceipt =
        canonicalBisognanoWichmannToTimeSliceReceipt
    ; closureModulusLabel =
        "BisognanoWichmann"
    ; closureModulusLabel-v =
        refl
    ; timeSliceClosureModuloBisognanoWichmannTarget =
        abstractTimeSliceClosureModuloBisognanoWichmannTarget
    ; timeSliceClosureModuloBWPromoted =
        false
    ; timeSliceClosureModuloBWPromotedIsFalse =
        refl
    ; closureModuloBWBoundary =
        "time-slice closure is recorded modulo BisognanoWichmann authority"
        ∷ "the modulo record consumes the non-promoting BW authority receipt, the geometric-net BW receipt, and typed time-slice surjectivity/isomorphism targets"
        ∷ "the BW -> TimeSlice bridge records modular-flow equality, Tomita wedge complement, wedge-cover iteration, and A(Sigma) ~= A(M)"
        ∷ "it does not prove BW, time-slice, Cauchy evolution, or a promoted Gate 5 theorem chain"
        ∷ []
    }

canonicalMassGapEnergyPositivityBWTimeSliceDependencySurface :
  MassGapEnergyPositivityBWTimeSliceDependencySurface
canonicalMassGapEnergyPositivityBWTimeSliceDependencySurface =
  record
    { status =
        massGapEnergyPositivityBWTimeSliceTargetsOnlyNoPromotion
    ; dependencyStages =
        canonicalGate5TimeSliceDependencyStages
    ; dependencyStagesAreCanonical =
        refl
    ; massGapReceipt =
        MassGap.canonicalBalabanRGMassGapReceiptSurface
    ; energyPositivityFromMassGap =
        canonicalEnergyPositivityFromMassGapTarget
    ; bwFromEnergyPositivity =
        canonicalBisognanoWichmannFromEnergyPositivityTarget
    ; timeSliceSurface =
        canonicalTimeSliceTheoremSurface
    ; timeSliceSurjectivityIsomorphism =
        canonicalTimeSliceSurjectivityIsomorphismTarget
    ; timeSliceClosureModuloBisognanoWichmann =
        canonicalTimeSliceClosureModuloBisognanoWichmannReceipt
    ; bwToTimeSliceReceipt =
        canonicalBisognanoWichmannToTimeSliceReceipt
    ; bwToTimeSliceBridgeTarget =
        abstractBWToTimeSliceBridgeTarget
    ; openGate5Obligations =
        canonicalGate5TimeSliceDependencyOpenObligations
    ; openGate5ObligationsAreCanonical =
        refl
    ; gate5Promoted =
        false
    ; gate5PromotedIsFalse =
        refl
    ; noGate5PromotionWithoutAuthority =
        λ ()
    ; dependencyBoundary =
        "Gate 5 dependency chain is MassGap -> EnergyPositivity -> BisognanoWichmann -> TimeSlice"
        ∷ "MassGap is an external intake receipt, EnergyPositivity and spectrum condition are explicit targets"
        ∷ "Bisognano-Wichmann is consumed from ModularTheoryReceiptSurface as a dependency target plus non-promoting Borchers/BGL authority receipt"
        ∷ "the detailed geometric-net BW receipt supplies W_R, boost flow, sigma^omega = boost, Tomita wedge-complement, wedge-cover iteration, and A(Sigma) ~= A(M) targets"
        ∷ "time-slice closure is recorded modulo BisognanoWichmann and remains unpromoted without a local Gate 5 authority token"
        ∷ "TimeSlice carries explicit surjectivity and isomorphism targets for A(Sigma) -> A(O)"
        ∷ "the chain is inhabited as a record of dependencies, not as a promoted theorem chain"
        ∷ []
    }

canonicalTierBPaper3Delta3bBWAuthorityAnchors :
  TierBPaper3Delta3bBWAuthorityAnchors
canonicalTierBPaper3Delta3bBWAuthorityAnchors =
  record
    { gate5DependencySurface =
        canonicalMassGapEnergyPositivityBWTimeSliceDependencySurface
    ; bisognanoWichmannAuthorityReceipt =
        Modular.canonicalBisognanoWichmannAuthorityReceipt
    ; borchersCitation =
        "Borchers-1992-Communications-in-Mathematical-Physics-143-315-332"
    ; borchersCitation-v =
        refl
    ; brunettiGuidoLongoCitation =
        "Brunetti-Guido-Longo-Rev-Math-Phys-4-1993-483-513"
    ; brunettiGuidoLongoCitation-v =
        refl
    ; citationTokens =
        canonicalTierBPaper3Delta3bBWAuthorityCitations
    ; citationTokensAreCanonical =
        refl
    ; citationAuthorityOnly =
        true
    ; citationAuthorityOnlyIsTrue =
        refl
    ; localBWProofSupplied =
        false
    ; localBWProofSuppliedIsFalse =
        refl
    ; timeSlicePromotedByBWAnchors =
        false
    ; timeSlicePromotedByBWAnchorsIsFalse =
        refl
    ; delta3bBoundary =
        "Delta 3b pins BW authority to Borchers 1992 CMP 143, 315-332 and Brunetti-Guido-Longo Rev. Math. Phys. 4 (1993), 483-513"
        ∷ "These entries are citation authority anchors for the imported BW receipt, not a DASHI-local proof"
        ∷ "The anchors do not promote BW-to-time-slice or discharge Gate 5 obligations"
        ∷ []
    }

canonicalCauchyEvolutionReceiptTarget :
  CauchyEvolutionReceiptTarget
canonicalCauchyEvolutionReceiptTarget =
  record
    { status =
        cauchyEvolutionTargetOnlyNoTimeSliceProof
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; CauchyCarrierData =
        abstractCauchyCarrierData
    ; cauchyEvolution =
        abstractCauchyEvolution
    ; evolutionDeterminesTarget =
        abstractEvolutionDeterminesTarget
    ; timeSliceMorphismFromEvolution =
        AQFT.AQFTTypedNetSurface.timeSliceLaw
          AQFT.canonicalAQFTTypedNetSurface
    ; timeSliceTheoremSurface =
        canonicalTimeSliceTheoremSurface
    ; openCauchyEvolutionObligations =
        canonicalCauchyEvolutionOpenObligations
    ; openCauchyEvolutionObligationsAreCanonical =
        refl
    ; timeSlicePromoted =
        false
    ; timeSlicePromotedIsFalse =
        refl
    ; noTimeSlicePromotionWithoutAuthority =
        λ ()
    ; cauchyEvolutionBoundary =
        "CauchyEvolutionReceiptTarget is the Paper 3a time-slice theorem target"
        ∷ "it must show carrier data on a Cauchy surface determines the target region"
        ∷ "A(Sigma) ~= A(O) ~= A(M), domain-of-dependence, and transport-from-Cauchy-surface isomorphism are recorded by TimeSliceTheoremSurface"
        ∷ "descent and filtered-colimit caveats remain open"
        ∷ "this target does not construct a time-slice proof, interacting AQFT net, or GRQFT receipt"
        ∷ []
    }

canonicalDepthFilteredLocalAlgebraSurface :
  DepthFilteredLocalAlgebraSurface
canonicalDepthFilteredLocalAlgebraSurface =
  record
    { status =
        depthFilteredColimitTargetOnlyNoCStarConstruction
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; Depth =
        abstractDepth
    ; _≤Depth_ =
        abstractDepthOrder
    ; depthReflexive =
        abstractDepthReflexive
    ; depthTransitive =
        abstractDepthTransitive
    ; commonDepthRefinement =
        abstractCommonDepthRefinement
    ; A_d =
        abstractDepthLocalAlgebra
    ; depthMap =
        λ {d} {e} d≤e {region} x →
          abstractDepthMap {d} {e} d≤e {region} x
    ; A_colim =
        abstractDepthColimit
    ; colimIntro =
        λ d {region} x →
          abstractDepthColimitIntro d {region} x
    ; colimIdentifiesDepthMap =
        λ {d} {e} d≤e {region} x →
          abstractDepthColimitIdentifiesDepthMap {d} {e} d≤e {region} x
    ; colimMatchesLocalAlgebra =
        abstractDepthColimitMatchesLocalAlgebra
    ; algebraicOperationsOnColimit =
        abstractAlgebraicOperationsOnColimit
    ; cstarCompletionTarget =
        abstractCStarCompletionTarget
    ; colimitUniversalityReceipt =
        canonicalColimitUniversalityReceiptTarget
    ; cstarCompletionBoundary =
        "algebraic-colimit-operations-do-not-construct-C-star-completion-or-representation"
    ; cstarCompletionBoundary-v =
        refl
    ; openDepthFilteredAlgebraObligations =
        canonicalDepthFilteredAlgebraOpenObligations
    ; openDepthFilteredAlgebraObligationsAreCanonical =
        refl
    ; cstarConstructionPromoted =
        false
    ; cstarConstructionPromotedIsFalse =
        refl
    ; noDepthColimitPromotionWithoutAuthority =
        λ ()
    ; depthFilteredBoundary =
        "A_d(O) and colim_d A_d(O) are staged as depth-filtered local algebra targets"
        ∷ "the directed depth witness, filtered colimit, colimit universality, algebra operations, C*-completion, and local-algebra equality are abstract here"
        ∷ "algebraic colimit operations are separated from the safe C*-completion authority and representation target"
        ∷ "this surface does not construct an AF algebra, interacting AQFT net, Standard Model, or GRQFT receipt"
        ∷ []
    }

canonicalAQFTAlgebraColimitCompletionSurface :
  AQFTAlgebraColimitCompletionSurface
canonicalAQFTAlgebraColimitCompletionSurface =
  record
    { depthFilteredLocalAlgebraSurface =
        canonicalDepthFilteredLocalAlgebraSurface
    ; AlgebraicColimitAlgebra =
        abstractDepthColimit
    ; algebraicColimitMatchesDepthColimit =
        λ _ → refl
    ; algebraicColimitOperations =
        abstractAlgebraicOperationsOnColimit
    ; algebraicColimitNorm =
        abstractDepthColimitNorm
    ; cStarCompletionAuthority =
        canonicalDepthCStarCompletionUniversalPropertyAuthority
    ; CompletedAQFTAlgebra =
        abstractCStarCompletionTarget
    ; completedAQFTAlgebraMatchesCompletion =
        λ _ → refl
    ; completedAQFTAlgebraMatchesTypedNetTarget =
        abstractCompletedAQFTAlgebraMatchesTypedNetTarget
    ; aqftAlgebraColimitCompletionPromoted =
        false
    ; aqftAlgebraColimitCompletionPromotedIsFalse =
        refl
    ; aqftAlgebraColimitCompletionBoundary =
        "AQFTAlgebra is staged as algebraic filtered colimit followed by a separate C*-completion authority"
        ∷ "the completion authority is safe to cite as a socket but is not a local construction of the completed C*-algebra"
        ∷ "the completed algebra-to-typed-net equality is a target socket, not a promoted theorem"
        ∷ "time-slice and descent/colimit compatibility remain outside this algebra completion surface"
        ∷ []
    }

canonicalAQFTCarrierAlgebraQuotientSurface :
  AQFTCarrierAlgebraQuotientSurface
canonicalAQFTCarrierAlgebraQuotientSurface =
  record
    { status =
        quotientSurfaceOnlyNoAQFTPromotion
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; RestrictedCarrier =
        abstractRestrictedCarrier
    ; TransportEquivalent =
        abstractTransportEquivalent
    ; transportRefl =
        abstractTransportRefl
    ; transportSym =
        abstractTransportSym
    ; transportTrans =
        abstractTransportTrans
    ; PromotedReceipt =
        abstractPromotedReceipt
    ; promotedReceiptTransport =
        abstractPromotedReceiptTransport
    ; PromotedReceiptQuotient =
        abstractPromotedReceiptQuotient
    ; QuotientRelation =
        abstractQuotientRelation
    ; quotientIntro =
        abstractQuotientIntro
    ; transportQuotientClass =
        abstractTransportQuotientClass
    ; quotientTransportStable =
        abstractQuotientTransportStable
    ; quotientRelationIntro =
        abstractQuotientRelationIntro
    ; quotientUnit =
        λ {region} →
          abstractQuotientUnit {region}
    ; quotientMul =
        λ {region} x y →
          abstractQuotientMul {region} x y
    ; quotientStar =
        λ {region} x →
          abstractQuotientStar {region} x
    ; quotientNorm =
        λ {region} x →
          abstractQuotientNorm {region} x
    ; operationLabelReceipt =
        canonicalQuotientOperationLabelReceipt
    ; quotientNormSurface =
        canonicalQuotientNormSurface
    ; operationTransportWellDefinedReceipt =
        canonicalQuotientAlgebraOperationsTransportWellDefined
    ; unitaryConjugationNormSocket =
        canonicalUnitaryConjugationPreservesNormSocket
    ; finiteDimensionalCStarIdentitySocket =
        canonicalFiniteDimensionalCStarIdentitySocket
    ; transportQuotientEquivalenceLawReceipt =
        canonicalTransportQuotientEquivalenceLawReceipt
    ; transportSetoidQuotientReceipt =
        canonicalTransportSetoidQuotientReceipt
    ; setoidInhabitedReceipts =
        canonicalAQFTCarrierAlgebraQuotientSetoidInhabitedReceipts
    ; setoidInhabitedReceiptsAreCanonical =
        refl
    ; colimitUniversalityReceipt =
        canonicalColimitUniversalityReceiptTarget
    ; cStarCompletionUniversalPropertyAuthority =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarNormUniquenessEnvelopeNuclearitySurface =
        canonicalCStarNormUniquenessEnvelopeNuclearitySurface
    ; aqftAlgebraColimitCompletionSurface =
        canonicalAQFTAlgebraColimitCompletionSurface
    ; isotonyG6CausalityDescentReceipt =
        canonicalIsotonyG6CausalityDescentReceiptTarget
    ; timeSliceKTheoreticIntermediateTarget =
        canonicalTimeSliceKTheoreticIntermediateTarget
    ; massGapEnergyPositivityBWTimeSliceDependencySurface =
        canonicalMassGapEnergyPositivityBWTimeSliceDependencySurface
    ; tierBPaper3Delta3aCompletionConstructivity =
        canonicalTierBPaper3Delta3aCStarCompletionConstructivity
    ; tierBPaper3Delta3bBWAuthorityAnchors =
        canonicalTierBPaper3Delta3bBWAuthorityAnchors
    ; quotientAlgebraWellDefinedTarget =
        "target-only-transport-equivalence-respects-unit-product-star-and-receipt-composition"
    ; quotientAlgebraWellDefinedTarget-v =
        refl
    ; cstarCompletionBoundary =
        "algebraic-star-structure-is-staged-before-any-C-star-completion-GNS-state-or-Born-rule-adapter"
    ; cstarCompletionBoundary-v =
        refl
    ; localAlgebraIsPromotedReceiptQuotient =
        abstractLocalAlgebraIsPromotedReceiptQuotient
    ; openObligations =
        missingRestrictedCarrier
        ∷ missingPromotedReceiptPredicate
        ∷ missingQuotientConstruction
        ∷ missingPreciseQuotientRelation
        ∷ missingAlgebraOperationsOnQuotient
        ∷ missingNormOperationLabel
        ∷ missingIsotonyFromCarrierTransport
        ∷ missingColimitUniversality
        ∷ missingCausalReachability
        ∷ missingCauchyEvolutionReceipt
        ∷ missingDepthFilteredColimitAlgebra
        ∷ missingFullTimeSliceTheorem
        ∷ missingKTheoreticIntermediateTarget
        ∷ missingCStarNormUniquenessEnvelope
        ∷ missingNuclearityTheorem
        ∷ missingMassGapEnergyPositivityBWTimeSliceDependency
        ∷ []
    ; aqftPromoted =
        false
    ; aqftPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; quotientBoundary =
        "A(O) is staged as promoted receipts over the carrier restricted to O, quotiented by transport equivalence"
        ∷ "restricted carriers, transport equivalence, quotient relation, promoted receipts, quotient operations, and norm target are abstract here"
        ∷ "transport equivalence laws, transport quotient extensionality, and transport quotient eliminators are reclassified as setoid-inhabited"
        ∷ "transport quotient equivalence laws are routed through a non-cubical setoid quotient eliminator surface"
        ∷ "colimit universality, isotony, G6 causality, and descent are explicit target receipts"
        ∷ "A_d(O) and colim_d A_d(O) remain blocked on DepthFilteredLocalAlgebraSurface and ColimitUniversalityReceiptTarget"
        ∷ "time-slice, causal reachability, Cauchy-surface inclusion, domain-of-dependence, and A(Sigma) ~= A(O) ~= A(M) remain blocked on TimeSliceTheoremSurface"
        ∷ "K-theoretic intermediate classification is a staged target and does not classify charges here"
        ∷ "C*-completion is a safe authority socket but not a local construction; C*-norm uniqueness, C*-envelope, and nuclearity are Gate 4 typed targets only"
        ∷ "Delta 3a accounts for the Cubical HIT/set-quotient route A0(O)/I_null plus standard metric/C*-completion adaptation as roughly one sprint, not currently inhabited"
        ∷ "MassGap -> EnergyPositivity -> BisognanoWichmann -> TimeSlice is a Gate 5 dependency record with explicit surjectivity/isomorphism targets and time-slice closure modulo BisognanoWichmann"
        ∷ "Delta 3b pins BW authority to Borchers 1992 CMP 143, 315-332 and Brunetti-Guido-Longo Rev. Math. Phys. 4 (1993), 483-513 without local BW proof or time-slice promotion"
        ∷ "descent/colimit caveats remain open and are not discharged by the quotient surface"
        ∷ "this surface does not construct a concrete C*-algebra, GNS state, Born-rule adapter, or interacting AQFT net"
        ∷ "this surface does not promote Standard Model, stress-energy, GRQFT, or full unification claims"
        ∷ []
    }
