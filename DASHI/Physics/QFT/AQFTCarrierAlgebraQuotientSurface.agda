module DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface where

open import Agda.Primitive using (Level; Setω; lzero)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
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

data AQFTM4U6ResidualBlocker : Set where
  missingDASHILocalAlgebra :
    AQFTM4U6ResidualBlocker

  missingGNSUniversalProperty :
    AQFTM4U6ResidualBlocker

canonicalAQFTM4U6ResidualBlockers :
  List AQFTM4U6ResidualBlocker
canonicalAQFTM4U6ResidualBlockers =
  missingDASHILocalAlgebra
  ∷ missingGNSUniversalProperty
  ∷ []

data AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt : Set where
  promotedReceiptPredicateInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

  transportEquivalenceLawsSetoidInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

  transportSetoidQuotientConstructionInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

  transportQuotientExtensionalitySetoidInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

  transportQuotientEliminatorsSetoidInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

  preciseTransportQuotientRelationInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

  quotientAlgebraOperationsTransportLawsInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

  quotientNormBetaTransportLawsInhabited :
    AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt

canonicalAQFTCarrierAlgebraQuotientSetoidInhabitedReceipts :
  List AQFTCarrierAlgebraQuotientSetoidInhabitedReceipt
canonicalAQFTCarrierAlgebraQuotientSetoidInhabitedReceipts =
  promotedReceiptPredicateInhabited
  ∷ transportEquivalenceLawsSetoidInhabited
  ∷ transportSetoidQuotientConstructionInhabited
  ∷ transportQuotientExtensionalitySetoidInhabited
  ∷ transportQuotientEliminatorsSetoidInhabited
  ∷ preciseTransportQuotientRelationInhabited
  ∷ quotientAlgebraOperationsTransportLawsInhabited
  ∷ quotientNormBetaTransportLawsInhabited
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

record PromotedReceiptPredicateSurface
  (Carrier : AQFT.Region → Set)
  (TransportEquivalent :
    {region : AQFT.Region} →
    Carrier region →
    Carrier region →
    Set) : Setω where
  field
    PromotedReceiptPredicate :
      {region : AQFT.Region} →
      Carrier region →
      Set

    promotedReceiptTransportTarget :
      {region : AQFT.Region} →
      {x y : Carrier region} →
      TransportEquivalent x y →
      PromotedReceiptPredicate x →
      PromotedReceiptPredicate y

    predicateAuthorityBoundary :
      List String

    predicateLocallyConstructed :
      Bool

    predicateLocallyConstructedIsFalse :
      predicateLocallyConstructed ≡ false

    predicatePromoted :
      Bool

    predicatePromotedIsFalse :
      predicatePromoted ≡ false

open PromotedReceiptPredicateSurface public

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

    dashiInternalMassGapImpliesEnergyPositivityTarget :
      MassGap.BalabanRGMassGapReceiptSurface.continuumMassGapProvedInDASHI
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

record PromotedReceiptPredicateReceipt
  (RestrictedCarrier : AQFT.Region → Set)
  (TransportEquivalent :
    {region : AQFT.Region} →
    RestrictedCarrier region →
    RestrictedCarrier region →
    Set)
  (PromotedReceipt :
    {region : AQFT.Region} →
    RestrictedCarrier region →
    Set) : Setω where
  field
    promotedReceiptPredicate :
      {region : AQFT.Region} →
      RestrictedCarrier region →
      Set

    promotedReceiptPredicateMatches :
      {region : AQFT.Region} →
      (x : RestrictedCarrier region) →
      promotedReceiptPredicate x
      ≡
      PromotedReceipt x

    promotedReceiptTransport :
      {region : AQFT.Region} →
      {x y : RestrictedCarrier region} →
      TransportEquivalent x y →
      promotedReceiptPredicate x →
      promotedReceiptPredicate y

    predicateInhabitedAsSurface :
      Bool

    predicateInhabitedAsSurfaceIsTrue :
      predicateInhabitedAsSurface ≡ true

    predicatePromotedToAQFTNet :
      Bool

    predicatePromotedToAQFTNetIsFalse :
      predicatePromotedToAQFTNet ≡ false

    predicateBoundary :
      List String

open PromotedReceiptPredicateReceipt public

record BoundedRestrictedCarrierDepthProgressSurface : Setω where
  field
    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    boundedRegion :
      AQFT.Region →
      Set

    RestrictedCarrier :
      AQFT.Region →
      Set

    boundedRestrictedCarrier :
      (region : AQFT.Region) →
      boundedRegion region →
      Set

    boundedRestrictedCarrierMatchesRestrictedCarrier :
      (region : AQFT.Region) →
      (bounded : boundedRegion region) →
      boundedRestrictedCarrier region bounded
      ≡
      RestrictedCarrier region

    boundedInclusionMorphism :
      {small large : AQFT.Region} →
      small AQFT.⊆ large →
      AQFT.AlgebraMorphism small large

    boundedDescentCompatibilityTarget :
      (region : AQFT.Region) →
      AQFT.DescentCover region →
      Set

    depthFilteredLocalAlgebraSurface :
      DepthFilteredLocalAlgebraSurface

    filteredColimitUniversalityReceipt :
      ColimitUniversalityReceiptTarget

    PromotedReceiptQuotient :
      AQFT.Region →
      Set

    quotientNorm :
      {region : AQFT.Region} →
      PromotedReceiptQuotient region →
      RA.ℝ

    cStarQuotientCompletionAuthority :
      CStarCompletionUniversalPropertyAuthority
        PromotedReceiptQuotient
        quotientNorm

    cStarQuotientCompletionAuthoritySafe :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthority
        cStarQuotientCompletionAuthority
      ≡
      true

    cStarQuotientCompletionLocallyConstructedIsFalse :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructed
        cStarQuotientCompletionAuthority
      ≡
      false

    inclusionDescentReceipt :
      IsotonyG6CausalityDescentReceiptTarget

    timeSliceSurface :
      TimeSliceTheoremSurface

    cauchyEvolutionReceipt :
      CauchyEvolutionReceiptTarget

    m4HandoffLabel :
      String

    m4HandoffLabel-v :
      m4HandoffLabel
      ≡
      "m4-descent-colimit-handoff"

    u6HandoffLabel :
      String

    u6HandoffLabel-v :
      u6HandoffLabel
      ≡
      "u6-dhr-localised-endomorphism-carrier-handoff"

    bisognanoWichmannCitationOnly :
      Bool

    bisognanoWichmannCitationOnlyIsTrue :
      bisognanoWichmannCitationOnly ≡ true

    drPromotionSuppliedHere :
      Bool

    drPromotionSuppliedHereIsFalse :
      drPromotionSuppliedHere ≡ false

    boundedCarrierDepthProgressBoundary :
      List String

open BoundedRestrictedCarrierDepthProgressSurface public

record ConcreteDepthFilteredLocalAlgebraData
  (PromotedReceiptQuotient : AQFT.Region → Set)
  (quotientNorm :
    {region : AQFT.Region} →
    PromotedReceiptQuotient region →
    RA.ℝ) : Setω where
  field
    depthFilteredLocalAlgebraSurface :
      DepthFilteredLocalAlgebraSurface

    filteredColimitUniversalityReceipt :
      ColimitUniversalityReceiptTarget

    colimitCarrierMatchesPromotedReceiptQuotient :
      (region : AQFT.Region) →
      DepthFilteredLocalAlgebraSurface.A_colim
        depthFilteredLocalAlgebraSurface
        region
      ≡
      PromotedReceiptQuotient region

    cStarCompletionAuthority :
      CStarCompletionUniversalPropertyAuthority
        PromotedReceiptQuotient
        quotientNorm

    cStarCompletionAuthorityConsumedSafely :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthority
        cStarCompletionAuthority
      ≡
      true

    cStarCompletionConsumptionLocallyConstructedIsFalse :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructed
        cStarCompletionAuthority
      ≡
      false

    cStarCompletionConsumptionPromotedIsFalse :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        cStarCompletionAuthority
      ≡
      false

    depthDataConcreteLabel :
      String

    depthDataConcreteLabel-v :
      depthDataConcreteLabel
      ≡
      "finite-bool-depth-filtered-local-algebra-over-promoted-receipt-quotient"

    depthFilteredDataBoundary :
      List String

open ConcreteDepthFilteredLocalAlgebraData public

record AQFTM4U6HandoffReceipt
  (PromotedReceiptQuotient : AQFT.Region → Set)
  (quotientNorm :
    {region : AQFT.Region} →
    PromotedReceiptQuotient region →
    RA.ℝ) : Setω where
  field
    concreteDepthFilteredLocalAlgebraData :
      ConcreteDepthFilteredLocalAlgebraData
        PromotedReceiptQuotient
        quotientNorm

    inclusionDescentReceipt :
      IsotonyG6CausalityDescentReceiptTarget

    timeSliceSurface :
      TimeSliceTheoremSurface

    cauchyEvolutionReceipt :
      CauchyEvolutionReceiptTarget

    cStarCompletionAuthorityBoundary :
      CStarCompletionUniversalPropertyAuthority
        PromotedReceiptQuotient
        quotientNorm

    residualBlockers :
      List AQFTM4U6ResidualBlocker

    residualBlockersAreCanonical :
      residualBlockers
      ≡
      canonicalAQFTM4U6ResidualBlockers

    m4FirstResidualBlocker :
      AQFTM4U6ResidualBlocker

    m4FirstResidualBlockerIsMissingGNSUniversalProperty :
      m4FirstResidualBlocker
      ≡
      missingGNSUniversalProperty

    u6FirstResidualBlocker :
      AQFTM4U6ResidualBlocker

    u6FirstResidualBlockerIsMissingDASHILocalAlgebra :
      u6FirstResidualBlocker
      ≡
      missingDASHILocalAlgebra

    bisognanoWichmannCitationOnly :
      Bool

    bisognanoWichmannCitationOnlyIsTrue :
      bisognanoWichmannCitationOnly ≡ true

    dhrPromotionSuppliedHere :
      Bool

    dhrPromotionSuppliedHereIsFalse :
      dhrPromotionSuppliedHere ≡ false

    handoffBoundary :
      List String

open AQFTM4U6HandoffReceipt public

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

    promotedReceiptPredicateSurface :
      PromotedReceiptPredicateSurface
        RestrictedCarrier
        TransportEquivalent

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

    reehSchliederForDASHIReceipt :
      ReehSchliederForDASHIReceipt

    boundedRestrictedCarrierDepthProgress :
      BoundedRestrictedCarrierDepthProgressSurface

    concreteDepthFilteredLocalAlgebraData :
      ConcreteDepthFilteredLocalAlgebraData
        PromotedReceiptQuotient
        quotientNorm

    m4u6HandoffReceipt :
      AQFTM4U6HandoffReceipt
        PromotedReceiptQuotient
        quotientNorm

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

  abstractDASHIInternalMassGapImpliesEnergyPositivityTarget :
    MassGap.BalabanRGMassGapReceiptSurface.continuumMassGapProvedInDASHI
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

  abstractBoundedRegion :
    AQFT.Region →
    Set

  abstractNonEmptyRegion :
    AQFT.Region →
    Set

  abstractVacuumHilbertSpaceTarget :
    Set

  abstractVacuumVectorOmegaTarget :
    Set

  abstractLocalAlgebraOmegaDenseTarget :
    (O : AQFT.Region) →
    abstractNonEmptyRegion O →
    abstractBoundedRegion O →
    Set

  abstractDASHIReehSchliederCyclicityTarget :
    Set

  abstractHolomorphicWightmanForwardTubeTarget :
    Set

  abstractEdgeOfTheWedgeTarget :
    Set

  abstractTimeSlicePoincareCovarianceTarget :
    Set

  abstractIrreducibilityHaagDualityTarget :
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

canonicalPromotedReceiptPredicateSurface :
  PromotedReceiptPredicateSurface
    abstractRestrictedCarrier
    abstractTransportEquivalent
canonicalPromotedReceiptPredicateSurface =
  record
    { PromotedReceiptPredicate =
        abstractPromotedReceipt
    ; promotedReceiptTransportTarget =
        abstractPromotedReceiptTransport
    ; predicateAuthorityBoundary =
        "PromotedReceipt is now an explicit predicate surface over the restricted carrier"
        ∷ "the predicate and its transport action are consumed from abstract postulated fields"
        ∷ "this records the authority boundary and does not locally construct receipt promotion"
        ∷ "no AQFT, BW, DR, C*-completion, GNS, or Born-rule promotion follows from the predicate surface"
        ∷ []
    ; predicateLocallyConstructed =
        false
    ; predicateLocallyConstructedIsFalse =
        refl
    ; predicatePromoted =
        false
    ; predicatePromotedIsFalse =
        refl
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

record TransportSetoidQuotientConstructionProgress : Setω where
  field
    transportEquivalenceRecord :
      TransportEquivalenceRelation
        abstractRestrictedCarrier
        abstractTransportEquivalent

    transportSetoidQuotientReceipt :
      TransportSetoidQuotientReceipt
        abstractRestrictedCarrier
        abstractTransportEquivalent
        abstractPromotedReceiptQuotient
        abstractTransportQuotientClass

    quotientIntroSocket :
      {region : AQFT.Region} →
      (x : abstractRestrictedCarrier region) →
      abstractPromotedReceipt x →
      abstractPromotedReceiptQuotient region

    quotientRelationSocket :
      {region : AQFT.Region} →
      abstractPromotedReceiptQuotient region →
      abstractPromotedReceiptQuotient region →
      Set

    quotientTransportStableSocket :
      {region : AQFT.Region} →
      {x y : abstractRestrictedCarrier region} →
      (eq : abstractTransportEquivalent x y) →
      (receipt : abstractPromotedReceipt x) →
      quotientIntroSocket x receipt
      ≡
      quotientIntroSocket
        y
        (abstractPromotedReceiptTransport eq receipt)

    quotientConstructionInhabited :
      Bool

    quotientConstructionInhabitedIsTrue :
      quotientConstructionInhabited ≡ true

    quotientConstructionPromotedToAQFT :
      Bool

    quotientConstructionPromotedToAQFTIsFalse :
      quotientConstructionPromotedToAQFT ≡ false

    firstResidualAfterQuotientConstruction :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstResidualAfterQuotientConstructionIsMissingPreciseRelation :
      firstResidualAfterQuotientConstruction
      ≡
      missingPreciseQuotientRelation

    residualAfterQuotientConstruction :
      List AQFTCarrierAlgebraQuotientOpenObligation

    residualAfterQuotientConstructionIsExact :
      residualAfterQuotientConstruction
      ≡
      missingPreciseQuotientRelation
      ∷ missingAlgebraOperationsOnQuotient
      ∷ missingNormOperationLabel
      ∷ []

    quotientConstructionBoundary :
      List String

open TransportSetoidQuotientConstructionProgress public

canonicalTransportSetoidQuotientConstructionProgress :
  TransportSetoidQuotientConstructionProgress
canonicalTransportSetoidQuotientConstructionProgress =
  record
    { transportEquivalenceRecord =
        canonicalTransportEquivalenceRelation
    ; transportSetoidQuotientReceipt =
        canonicalTransportSetoidQuotientReceipt
    ; quotientIntroSocket =
        abstractQuotientIntro
    ; quotientRelationSocket =
        abstractQuotientRelation
    ; quotientTransportStableSocket =
        abstractQuotientTransportStable
    ; quotientConstructionInhabited =
        true
    ; quotientConstructionInhabitedIsTrue =
        refl
    ; quotientConstructionPromotedToAQFT =
        false
    ; quotientConstructionPromotedToAQFTIsFalse =
        refl
    ; firstResidualAfterQuotientConstruction =
        missingPreciseQuotientRelation
    ; firstResidualAfterQuotientConstructionIsMissingPreciseRelation =
        refl
    ; residualAfterQuotientConstruction =
        missingPreciseQuotientRelation
        ∷ missingAlgebraOperationsOnQuotient
        ∷ missingNormOperationLabel
        ∷ []
    ; residualAfterQuotientConstructionIsExact =
        refl
    ; quotientConstructionBoundary =
        "missingQuotientConstruction is advanced to a setoid quotient construction receipt over transport equivalence"
        ∷ "the quotient carrier, class map, recursor, eliminator, and beta laws are supplied by TransportSetoidQuotientReceipt"
        ∷ "the precise quotient relation and algebra-operation laws are still separate residual obligations"
        ∷ "no C-star completion, GNS state, DASHI local algebra, DHR reconstruction, or AQFT promotion follows from this quotient receipt"
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

concreteBoolDepthOrder :
  Bool →
  Bool →
  Set
concreteBoolDepthOrder _ _ =
  ⊤

canonicalConcreteColimitCoconeShape :
  ColimitCoconeShape
canonicalConcreteColimitCoconeShape =
  record
    { CoconeDepth =
        Bool
    ; _≤CoconeDepth_ =
        concreteBoolDepthOrder
    ; CoconeDiagramAlgebra =
        λ _ region →
          abstractPromotedReceiptQuotient region
    ; coconeDiagramMap =
        λ _ x →
          x
    ; CoconeColimitAlgebra =
        abstractPromotedReceiptQuotient
    ; coconeLeg =
        λ _ x →
          x
    ; coconeCommutes =
        λ _ →
          ⊤
    }

canonicalConcreteColimitUniversalityReceiptTarget :
  ColimitUniversalityReceiptTarget
canonicalConcreteColimitUniversalityReceiptTarget =
  record
    { Depth =
        Bool
    ; _≤Depth_ =
        concreteBoolDepthOrder
    ; DiagramAlgebra =
        λ _ region →
          abstractPromotedReceiptQuotient region
    ; diagramMap =
        λ _ x →
          x
    ; ColimitAlgebra =
        abstractPromotedReceiptQuotient
    ; colimitCoconeShape =
        canonicalConcreteColimitCoconeShape
    ; colimitCocone =
        λ _ x →
          x
    ; colimitCoconeCommutes =
        λ _ →
          ⊤
    ; universalMediatorTarget =
        λ cocone region q →
          cocone false {region} q
    ; universalMediatorUniqueTarget =
        λ _ →
          ⊤
    ; colimitUniversalityPromoted =
        false
    ; colimitUniversalityPromotedIsFalse =
        refl
    ; colimitBoundary =
        "filtered-colimit universality is concretely presented over the finite Bool depth index"
        ∷ "each depth algebra is the promoted-receipt quotient and each refinement map is identity"
        ∷ "the mediator selects the false-depth cocone leg; uniqueness remains a target-only socket"
        ∷ "this concrete colimit presentation does not construct a C*-completion, GNS state, or AQFT promotion"
        ∷ []
    }

canonicalConcreteDepthFilteredLocalAlgebraSurface :
  DepthFilteredLocalAlgebraSurface
canonicalConcreteDepthFilteredLocalAlgebraSurface =
  record
    { status =
        depthFilteredColimitTargetOnlyNoCStarConstruction
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; Depth =
        Bool
    ; _≤Depth_ =
        concreteBoolDepthOrder
    ; depthReflexive =
        λ _ →
          tt
    ; depthTransitive =
        λ _ _ →
          tt
    ; commonDepthRefinement =
        λ _ _ →
          ⊤
    ; A_d =
        λ _ region →
          abstractPromotedReceiptQuotient region
    ; depthMap =
        λ _ x →
          x
    ; A_colim =
        abstractPromotedReceiptQuotient
    ; colimIntro =
        λ _ x →
          x
    ; colimIdentifiesDepthMap =
        λ _ _ →
          refl
    ; colimMatchesLocalAlgebra =
        abstractLocalAlgebraIsPromotedReceiptQuotient
    ; algebraicOperationsOnColimit =
        λ _ →
          ⊤
    ; cstarCompletionTarget =
        abstractQuotientCStarCompletion
    ; colimitUniversalityReceipt =
        canonicalConcreteColimitUniversalityReceiptTarget
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
        "Concrete l5 depth data uses Bool as the finite depth index"
        ∷ "both depth stages are the promoted-receipt quotient and refinement maps are identity"
        ∷ "the filtered colimit carrier is the promoted-receipt quotient, with local-algebra equality supplied by the explicit abstract equality socket"
        ∷ "the C*-completion target is routed to the quotient completion authority boundary and is not locally constructed"
        ∷ "full depth algebra laws, descent compatibility, time-slice compatibility, and GNS remain downstream targets"
        ∷ []
    }

canonicalConcreteDepthFilteredLocalAlgebraData :
  ConcreteDepthFilteredLocalAlgebraData
    abstractPromotedReceiptQuotient
    abstractQuotientNorm
canonicalConcreteDepthFilteredLocalAlgebraData =
  record
    { depthFilteredLocalAlgebraSurface =
        canonicalConcreteDepthFilteredLocalAlgebraSurface
    ; filteredColimitUniversalityReceipt =
        canonicalConcreteColimitUniversalityReceiptTarget
    ; colimitCarrierMatchesPromotedReceiptQuotient =
        λ _ →
          refl
    ; cStarCompletionAuthority =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarCompletionAuthorityConsumedSafely =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthorityIsTrue
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarCompletionConsumptionLocallyConstructedIsFalse =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarCompletionConsumptionPromotedIsFalse =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionPromotedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; depthDataConcreteLabel =
        "finite-bool-depth-filtered-local-algebra-over-promoted-receipt-quotient"
    ; depthDataConcreteLabel-v =
        refl
    ; depthFilteredDataBoundary =
        "l5 supplies concrete Bool-indexed DepthFilteredLocalAlgebra data over the promoted-receipt quotient"
        ∷ "the filtered colimit universal property is available as a concrete receipt with identity refinement maps"
        ∷ "C*-completion is consumed only through the safe quotient authority surface and remains unpromoted"
        ∷ "m4 may consume the algebra/colimit/completion sockets, but GNS universality remains a residual blocker"
        ∷ "u6 may consume the local quotient carrier handoff, but DASHILocalAlgebra remains a residual blocker"
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
    ; dashiInternalMassGapImpliesEnergyPositivityTarget =
        abstractDASHIInternalMassGapImpliesEnergyPositivityTarget
    ; spectrumConditionTarget =
        abstractSpectrumConditionFromEnergyTarget
    ; energyPositivitySuppliesSpectrumConditionTarget =
        abstractEnergyPositivitySuppliesSpectrumConditionTarget
    ; energyPositivityBoundary =
        "MassGap -> EnergyPositivity is represented as a dependency target"
        ∷ "the DASHI-internal ST3/Banach mass-gap receipt supplies the local positive-energy dependency path"
        ∷ "the older massGapPromotedByDASHI authority path remains false for Clay/external promotion"
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

canonicalReehSchliederForDASHIReceipt :
  ReehSchliederForDASHIReceipt
canonicalReehSchliederForDASHIReceipt =
  record
    { status =
        reehSchliederClosedImmediateFromDASHIReceiptDependencies
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; localAlgebraSurface =
        canonicalTimeSliceClosureModuloBisognanoWichmannReceipt
    ; gate5DependencySurface =
        canonicalMassGapEnergyPositivityBWTimeSliceDependencySurface
    ; geometricBisognanoWichmannNetReceipt =
        Modular.canonicalGeometricBisognanoWichmannNetReceipt
    ; boundedRegion =
        abstractBoundedRegion
    ; nonEmptyRegion =
        abstractNonEmptyRegion
    ; vacuumHilbertSpaceTarget =
        abstractVacuumHilbertSpaceTarget
    ; vacuumVectorOmegaTarget =
        abstractVacuumVectorOmegaTarget
    ; localAlgebraOmegaDenseTarget =
        abstractLocalAlgebraOmegaDenseTarget
    ; localAlgebraOmegaDenseLabel =
        "for-non-empty-bounded-O-A(O)-Omega-is-dense-in-H"
    ; localAlgebraOmegaDenseLabel-v =
        refl
    ; dashiReehSchliederCyclicityTarget =
        abstractDASHIReehSchliederCyclicityTarget
    ; proofRouteStages =
        canonicalReehSchliederProofRouteStages
    ; proofRouteStagesAreCanonical =
        refl
    ; holomorphicWightmanForwardTubeTarget =
        abstractHolomorphicWightmanForwardTubeTarget
    ; edgeOfTheWedgeTarget =
        abstractEdgeOfTheWedgeTarget
    ; timeSlicePoincareCovarianceTarget =
        abstractTimeSlicePoincareCovarianceTarget
    ; irreducibilityHaagDualityTarget =
        abstractIrreducibilityHaagDualityTarget
    ; dependenciesPresentAsReceipts =
        true
    ; dependenciesPresentAsReceiptsIsTrue =
        refl
    ; closedImmediateInDASHIReceipts =
        true
    ; closedImmediateInDASHIReceiptsIsTrue =
        refl
    ; independentNewTheoremClaimed =
        false
    ; independentNewTheoremClaimedIsFalse =
        refl
    ; bwAuthorityPromotedHere =
        false
    ; bwAuthorityPromotedHereIsFalse =
        refl
    ; drAuthorityPromotedHere =
        false
    ; drAuthorityPromotedHereIsFalse =
        refl
    ; reehSchliederBoundary =
        "Reeh-Schlieder for DASHI is recorded for every non-empty bounded region O as the target that A(O) Omega is dense in H"
        ∷ "the proof route metadata is positive energy -> holomorphic Wightman functions on the forward tube, edge-of-the-wedge continuation, time-slice plus Poincare covariance, and irreducibility/Haag duality"
        ∷ "the receipt is closed/immediate only because the needed positive-energy, BW/geometric-net, time-slice, Haag-duality, and irreducibility targets are present as DASHI receipt dependencies"
        ∷ "this does not claim an independent new Reeh-Schlieder theorem and does not promote BW, DR reconstruction, Standard Model matching, interacting AQFT, or GRQFT"
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

canonicalBoundedRestrictedCarrierDepthProgressSurface :
  BoundedRestrictedCarrierDepthProgressSurface
canonicalBoundedRestrictedCarrierDepthProgressSurface =
  record
    { typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; boundedRegion =
        abstractBoundedRegion
    ; RestrictedCarrier =
        abstractRestrictedCarrier
    ; boundedRestrictedCarrier =
        λ region _ →
          abstractRestrictedCarrier region
    ; boundedRestrictedCarrierMatchesRestrictedCarrier =
        λ _ _ → refl
    ; boundedInclusionMorphism =
        AQFT.AQFTTypedNetSurface.isotonyMorphism
          AQFT.canonicalAQFTTypedNetSurface
    ; boundedDescentCompatibilityTarget =
        AQFT.AQFTTypedNetSurface.descentCompatibilityLaw
          AQFT.canonicalAQFTTypedNetSurface
    ; depthFilteredLocalAlgebraSurface =
        canonicalConcreteDepthFilteredLocalAlgebraSurface
    ; filteredColimitUniversalityReceipt =
        canonicalConcreteColimitUniversalityReceiptTarget
    ; PromotedReceiptQuotient =
        abstractPromotedReceiptQuotient
    ; quotientNorm =
        abstractQuotientNorm
    ; cStarQuotientCompletionAuthority =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarQuotientCompletionAuthoritySafe =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthorityIsTrue
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarQuotientCompletionLocallyConstructedIsFalse =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; inclusionDescentReceipt =
        canonicalIsotonyG6CausalityDescentReceiptTarget
    ; timeSliceSurface =
        canonicalTimeSliceTheoremSurface
    ; cauchyEvolutionReceipt =
        canonicalCauchyEvolutionReceiptTarget
    ; m4HandoffLabel =
        "m4-descent-colimit-handoff"
    ; m4HandoffLabel-v =
        refl
    ; u6HandoffLabel =
        "u6-dhr-localised-endomorphism-carrier-handoff"
    ; u6HandoffLabel-v =
        refl
    ; bisognanoWichmannCitationOnly =
        true
    ; bisognanoWichmannCitationOnlyIsTrue =
        refl
    ; drPromotionSuppliedHere =
        false
    ; drPromotionSuppliedHereIsFalse =
        refl
    ; boundedCarrierDepthProgressBoundary =
        "boundedRestrictedCarrier specializes the restricted carrier to bounded regions by retaining the existing carrier type under a bounded-region witness"
        ∷ "bounded inclusions and descent are routed through AQFTTypedNetSurface isotony and descentCompatibilityLaw fields"
        ∷ "Concrete Bool-indexed DepthFilteredLocalAlgebraSurface and ColimitUniversalityReceiptTarget supply the filtered-colimit universal-property data for this bounded surface"
        ∷ "the quotient C*-completion appears only through the safe authority boundary; it is not locally constructed or promoted"
        ∷ "Cauchy evolution and time-slice data are referenced as targets through CauchyEvolutionReceiptTarget and TimeSliceTheoremSurface"
        ∷ "m4 receives the descent/colimit handoff; u6 receives the DHR localised-endomorphism carrier handoff label only"
        ∷ "BisognanoWichmann remains citation-only and this surface supplies no DR promotion"
        ∷ []
    }

canonicalAQFTM4U6HandoffReceipt :
  AQFTM4U6HandoffReceipt
    abstractPromotedReceiptQuotient
    abstractQuotientNorm
canonicalAQFTM4U6HandoffReceipt =
  record
    { concreteDepthFilteredLocalAlgebraData =
        canonicalConcreteDepthFilteredLocalAlgebraData
    ; inclusionDescentReceipt =
        canonicalIsotonyG6CausalityDescentReceiptTarget
    ; timeSliceSurface =
        canonicalTimeSliceTheoremSurface
    ; cauchyEvolutionReceipt =
        canonicalCauchyEvolutionReceiptTarget
    ; cStarCompletionAuthorityBoundary =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; residualBlockers =
        canonicalAQFTM4U6ResidualBlockers
    ; residualBlockersAreCanonical =
        refl
    ; m4FirstResidualBlocker =
        missingGNSUniversalProperty
    ; m4FirstResidualBlockerIsMissingGNSUniversalProperty =
        refl
    ; u6FirstResidualBlocker =
        missingDASHILocalAlgebra
    ; u6FirstResidualBlockerIsMissingDASHILocalAlgebra =
        refl
    ; bisognanoWichmannCitationOnly =
        true
    ; bisognanoWichmannCitationOnlyIsTrue =
        refl
    ; dhrPromotionSuppliedHere =
        false
    ; dhrPromotionSuppliedHereIsFalse =
        refl
    ; handoffBoundary =
        "m4 handoff contains concrete Bool-depth local algebra data, filtered colimit universality, and safe C*-completion authority consumption"
        ∷ "m4 remains blocked on missingGNSUniversalProperty before representation/GNS promotion"
        ∷ "u6 handoff contains the promoted-receipt quotient carrier plus isotony/descent/time-slice/Cauchy targets"
        ∷ "u6 remains blocked on missingDASHILocalAlgebra before DHR localised-endomorphism carrier promotion"
        ∷ "BisognanoWichmann is citation-only and DR promotion is not supplied here"
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
    ; promotedReceiptPredicateSurface =
        canonicalPromotedReceiptPredicateSurface
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
    ; reehSchliederForDASHIReceipt =
        canonicalReehSchliederForDASHIReceipt
    ; boundedRestrictedCarrierDepthProgress =
        canonicalBoundedRestrictedCarrierDepthProgressSurface
    ; concreteDepthFilteredLocalAlgebraData =
        canonicalConcreteDepthFilteredLocalAlgebraData
    ; m4u6HandoffReceipt =
        canonicalAQFTM4U6HandoffReceipt
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
        missingIsotonyFromCarrierTransport
        ∷ missingCausalReachability
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
        ∷ "restricted carriers and promoted receipts are now explicit authority surfaces over abstract sockets, not silent local constructions"
        ∷ "transport equivalence, quotient relation, quotient operations, and norm target are still abstract targets"
        ∷ "transport equivalence laws, transport quotient extensionality, and transport quotient eliminators are reclassified as setoid-inhabited"
        ∷ "transport quotient equivalence laws are routed through a non-cubical setoid quotient eliminator surface"
        ∷ "missingQuotientConstruction is advanced by canonicalTransportSetoidQuotientConstructionProgress; the first quotient residual is now missingPreciseQuotientRelation"
        ∷ "colimit universality, isotony, G6 causality, and descent are explicit target receipts"
        ∷ "bounded restricted carriers and concrete Bool-indexed A_d(O)/colim_d A_d(O) are packaged for l5 handoff"
        ∷ "filtered-colimit universality is available as concrete identity-refinement data, while operation compatibility remains a target obligation"
        ∷ "wave 3 consumes the precise quotient relation, quotient operation transport laws, and quotient norm beta/transport laws as local receipt data"
        ∷ "time-slice, causal reachability, Cauchy-surface inclusion, domain-of-dependence, and A(Sigma) ~= A(O) ~= A(M) remain blocked on TimeSliceTheoremSurface"
        ∷ "K-theoretic intermediate classification is a staged target and does not classify charges here"
        ∷ "C*-completion is a safe authority socket but not a local construction; C*-norm uniqueness, C*-envelope, and nuclearity are Gate 4 typed targets only"
        ∷ "Delta 3a accounts for the Cubical HIT/set-quotient route A0(O)/I_null plus standard metric/C*-completion adaptation as roughly one sprint, not currently inhabited"
        ∷ "MassGap -> EnergyPositivity -> BisognanoWichmann -> TimeSlice is a Gate 5 dependency record with explicit surjectivity/isomorphism targets and time-slice closure modulo BisognanoWichmann"
        ∷ "Reeh-Schlieder for DASHI is closed/immediate as a dependency receipt for non-empty bounded O: A(O) Omega is dense in H, routed through positive energy, forward-tube analyticity, edge-of-the-wedge, time-slice/Poincare covariance, irreducibility, and Haag duality"
        ∷ "Delta 3b pins BW authority to Borchers 1992 CMP 143, 315-332 and Brunetti-Guido-Longo Rev. Math. Phys. 4 (1993), 483-513 without local BW proof or time-slice promotion"
        ∷ "m4 residual blocker is missingGNSUniversalProperty; u6 residual blocker is missingDASHILocalAlgebra"
        ∷ "DASHILocalAlgebra is still unpromoted because C-star completion, time-slice/BW, and DR authority are only recorded as guarded targets"
        ∷ "this surface does not construct a concrete C*-algebra, GNS state, Born-rule adapter, or interacting AQFT net"
        ∷ "this surface does not promote Standard Model, stress-energy, GRQFT, or full unification claims"
        ∷ []
    }

record RestrictedCarrierPromotedReceiptPredicateProgress : Setω where
  field
    carrierSurface :
      AQFTCarrierAlgebraQuotientSurface

    RestrictedCarrierSocket :
      AQFT.Region →
      Set

    RestrictedCarrierSocketMatchesSurface :
      RestrictedCarrierSocket
      ≡
      AQFTCarrierAlgebraQuotientSurface.RestrictedCarrier carrierSurface

    PromotedReceiptPredicateSocket :
      {region : AQFT.Region} →
      AQFTCarrierAlgebraQuotientSurface.RestrictedCarrier
        carrierSurface
        region →
      Set

    PromotedReceiptPredicateSocketMatchesSurface :
      {region : AQFT.Region} →
      (x :
        AQFTCarrierAlgebraQuotientSurface.RestrictedCarrier
          carrierSurface
          region) →
      PromotedReceiptPredicateSocket x
      ≡
      AQFTCarrierAlgebraQuotientSurface.PromotedReceipt carrierSurface x

    promotedReceiptTransportSocket :
      {region : AQFT.Region} →
      {x y :
        AQFTCarrierAlgebraQuotientSurface.RestrictedCarrier
          carrierSurface
          region} →
      AQFTCarrierAlgebraQuotientSurface.TransportEquivalent carrierSurface x y →
      PromotedReceiptPredicateSocket x →
      PromotedReceiptPredicateSocket y

    quotientIntroSocket :
      {region : AQFT.Region} →
      (x :
        AQFTCarrierAlgebraQuotientSurface.RestrictedCarrier
          carrierSurface
          region) →
      PromotedReceiptPredicateSocket x →
      AQFTCarrierAlgebraQuotientSurface.PromotedReceiptQuotient
        carrierSurface
        region

    restrictedCarrierSocketInhabitedAsAbstract :
      Bool

    restrictedCarrierSocketInhabitedAsAbstractIsTrue :
      restrictedCarrierSocketInhabitedAsAbstract ≡ true

    promotedReceiptPredicateSocketInhabitedAsAbstract :
      Bool

    promotedReceiptPredicateSocketInhabitedAsAbstractIsTrue :
      promotedReceiptPredicateSocketInhabitedAsAbstract ≡ true

    concreteCarrierPredicatePromoted :
      Bool

    concreteCarrierPredicatePromotedIsFalse :
      concreteCarrierPredicatePromoted ≡ false

    concretePromotedReceiptPredicatePromoted :
      Bool

    concretePromotedReceiptPredicatePromotedIsFalse :
      concretePromotedReceiptPredicatePromoted ≡ false

    firstResidualCarrierPredicateBlocker :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstResidualCarrierPredicateBlockerIsMissingPreciseQuotientRelation :
      firstResidualCarrierPredicateBlocker
      ≡
      missingPreciseQuotientRelation

    residualCarrierPredicateBlockerChain :
      List AQFTCarrierAlgebraQuotientOpenObligation

    residualCarrierPredicateBlockerChainIsExact :
      residualCarrierPredicateBlockerChain
      ≡
      missingPreciseQuotientRelation
      ∷ missingAlgebraOperationsOnQuotient
      ∷ missingNormOperationLabel
      ∷ []

    carrierPredicateProgressBoundary :
      List String

open RestrictedCarrierPromotedReceiptPredicateProgress public

canonicalRestrictedCarrierPromotedReceiptPredicateProgress :
  RestrictedCarrierPromotedReceiptPredicateProgress
canonicalRestrictedCarrierPromotedReceiptPredicateProgress =
  record
    { carrierSurface =
        canonicalAQFTCarrierAlgebraQuotientSurface
    ; RestrictedCarrierSocket =
        abstractRestrictedCarrier
    ; RestrictedCarrierSocketMatchesSurface =
        refl
    ; PromotedReceiptPredicateSocket =
        abstractPromotedReceipt
    ; PromotedReceiptPredicateSocketMatchesSurface =
        λ _ → refl
    ; promotedReceiptTransportSocket =
        abstractPromotedReceiptTransport
    ; quotientIntroSocket =
        abstractQuotientIntro
    ; restrictedCarrierSocketInhabitedAsAbstract =
        true
    ; restrictedCarrierSocketInhabitedAsAbstractIsTrue =
        refl
    ; promotedReceiptPredicateSocketInhabitedAsAbstract =
        true
    ; promotedReceiptPredicateSocketInhabitedAsAbstractIsTrue =
        refl
    ; concreteCarrierPredicatePromoted =
        false
    ; concreteCarrierPredicatePromotedIsFalse =
        refl
    ; concretePromotedReceiptPredicatePromoted =
        false
    ; concretePromotedReceiptPredicatePromotedIsFalse =
        refl
    ; firstResidualCarrierPredicateBlocker =
        missingPreciseQuotientRelation
    ; firstResidualCarrierPredicateBlockerIsMissingPreciseQuotientRelation =
        refl
    ; residualCarrierPredicateBlockerChain =
        missingPreciseQuotientRelation
        ∷ missingAlgebraOperationsOnQuotient
        ∷ missingNormOperationLabel
        ∷ []
    ; residualCarrierPredicateBlockerChainIsExact =
        refl
    ; carrierPredicateProgressBoundary =
        "RestrictedCarrier and PromotedReceipt are now explicitly re-exported as matched sockets from canonicalAQFTCarrierAlgebraQuotientSurface"
        ∷ "transport of promoted receipts and quotient introduction are wired to the canonical abstract fields"
        ∷ "this is non-promoting evidence only: the setoid quotient construction is recorded separately, while no precise quotient relation theorem or algebra operation law is promoted"
        ∷ "the exact residual chain is missingPreciseQuotientRelation -> missingAlgebraOperationsOnQuotient -> missingNormOperationLabel"
        ∷ []
    }

record AQFTCarrierPredicateLocalBlockerRetirementReceipt : Setω where
  field
    carrierPredicateProgress :
      RestrictedCarrierPromotedReceiptPredicateProgress

    restrictedCarrierSocketMatchesCanonicalSurface :
      RestrictedCarrierPromotedReceiptPredicateProgress.RestrictedCarrierSocket
        carrierPredicateProgress
      ≡
      AQFTCarrierAlgebraQuotientSurface.RestrictedCarrier
        (RestrictedCarrierPromotedReceiptPredicateProgress.carrierSurface
          carrierPredicateProgress)

    promotedReceiptPredicateSocketInhabited :
      RestrictedCarrierPromotedReceiptPredicateProgress.promotedReceiptPredicateSocketInhabitedAsAbstract
        carrierPredicateProgress
      ≡
      true

    formerRestrictedCarrierBlocker :
      AQFTCarrierAlgebraQuotientOpenObligation

    formerRestrictedCarrierBlocker-v :
      formerRestrictedCarrierBlocker
      ≡
      missingRestrictedCarrier

    formerPromotedReceiptPredicateBlocker :
      AQFTCarrierAlgebraQuotientOpenObligation

    formerPromotedReceiptPredicateBlocker-v :
      formerPromotedReceiptPredicateBlocker
      ≡
      missingPromotedReceiptPredicate

    firstResidualAfterCarrierPredicateSockets :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstResidualAfterCarrierPredicateSockets-v :
      firstResidualAfterCarrierPredicateSockets
      ≡
      missingPreciseQuotientRelation

    carrierPredicatePromotedToAQFT :
      Bool

    carrierPredicatePromotedToAQFT-v :
      carrierPredicatePromotedToAQFT ≡ false

    retirementBoundary :
      List String

open AQFTCarrierPredicateLocalBlockerRetirementReceipt public

canonicalAQFTCarrierPredicateLocalBlockerRetirementReceipt :
  AQFTCarrierPredicateLocalBlockerRetirementReceipt
canonicalAQFTCarrierPredicateLocalBlockerRetirementReceipt =
  record
    { carrierPredicateProgress =
        canonicalRestrictedCarrierPromotedReceiptPredicateProgress
    ; restrictedCarrierSocketMatchesCanonicalSurface =
        RestrictedCarrierPromotedReceiptPredicateProgress.RestrictedCarrierSocketMatchesSurface
          canonicalRestrictedCarrierPromotedReceiptPredicateProgress
    ; promotedReceiptPredicateSocketInhabited =
        RestrictedCarrierPromotedReceiptPredicateProgress.promotedReceiptPredicateSocketInhabitedAsAbstractIsTrue
          canonicalRestrictedCarrierPromotedReceiptPredicateProgress
    ; formerRestrictedCarrierBlocker =
        missingRestrictedCarrier
    ; formerRestrictedCarrierBlocker-v =
        refl
    ; formerPromotedReceiptPredicateBlocker =
        missingPromotedReceiptPredicate
    ; formerPromotedReceiptPredicateBlocker-v =
        refl
    ; firstResidualAfterCarrierPredicateSockets =
        missingPreciseQuotientRelation
    ; firstResidualAfterCarrierPredicateSockets-v =
        refl
    ; carrierPredicatePromotedToAQFT =
        false
    ; carrierPredicatePromotedToAQFT-v =
        refl
    ; retirementBoundary =
        "missingRestrictedCarrier is locally retired only as an abstract RestrictedCarrier socket matched to canonicalAQFTCarrierAlgebraQuotientSurface"
        ∷ "missingPromotedReceiptPredicate is locally retired only as an abstract PromotedReceipt predicate socket with transport"
        ∷ "the next local AQFT quotient blocker is missingPreciseQuotientRelation, followed by quotient operation and norm-label laws"
        ∷ "this receipt does not promote DASHILocalAlgebra, C-star completion, time-slice/BW, GNS, or DR reconstruction"
        ∷ []
    }

record AQFTWave3PreciseQuotientLocalAlgebraProgress : Setω where
  field
    carrierSurface :
      AQFTCarrierAlgebraQuotientSurface

    transportSetoidQuotientConstructionProgress :
      TransportSetoidQuotientConstructionProgress

    preciseQuotientRelation :
      {region : AQFT.Region} →
      abstractPromotedReceiptQuotient region →
      abstractPromotedReceiptQuotient region →
      Set

    preciseQuotientRelationIntroFromTransport :
      {region : AQFT.Region} →
      {x y : abstractRestrictedCarrier region} →
      (eq : abstractTransportEquivalent x y) →
      (receipt : abstractPromotedReceipt x) →
      preciseQuotientRelation
        (abstractQuotientIntro x receipt)
        (abstractQuotientIntro
          y
          (abstractPromotedReceiptTransport eq receipt))

    quotientClassEqualityFromTransport :
      {region : AQFT.Region} →
      {x y : abstractRestrictedCarrier region} →
      abstractTransportEquivalent x y →
      abstractTransportQuotientClass x
      ≡
      abstractTransportQuotientClass y

    quotientOperationTransportLaws :
      QuotientAlgebraOperationsTransportWellDefined
        abstractRestrictedCarrier
        abstractTransportEquivalent
        abstractPromotedReceiptQuotient
        abstractTransportQuotientClass
        abstractQuotientUnit
        abstractQuotientMul
        abstractQuotientStar
        abstractQuotientNorm

    quotientNormLaws :
      QuotientNormSurface
        abstractRestrictedCarrier
        abstractTransportEquivalent
        abstractPromotedReceiptQuotient
        abstractTransportQuotientClass

    quotientNormBeta :
      {region : AQFT.Region} →
      (x : abstractRestrictedCarrier region) →
      abstractQuotientNorm (abstractTransportQuotientClass x)
      ≡
      abstractRestrictedCarrierNorm x

    localAlgebraIsPromotedReceiptQuotient :
      (region : AQFT.Region) →
      AQFT.AQFTTypedNetSurface.Algebra
        AQFT.canonicalAQFTTypedNetSurface
        region
      ≡
      abstractPromotedReceiptQuotient region

    preciseQuotientRelationAdvanced :
      Bool

    preciseQuotientRelationAdvancedIsTrue :
      preciseQuotientRelationAdvanced ≡ true

    quotientAlgebraOperationsAdvanced :
      Bool

    quotientAlgebraOperationsAdvancedIsTrue :
      quotientAlgebraOperationsAdvanced ≡ true

    quotientNormOperationAdvanced :
      Bool

    quotientNormOperationAdvancedIsTrue :
      quotientNormOperationAdvanced ≡ true

    dashiLocalAlgebraTargetAdvanced :
      Bool

    dashiLocalAlgebraTargetAdvancedIsTrue :
      dashiLocalAlgebraTargetAdvanced ≡ true

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    firstResidualAfterAQFTWave3 :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstResidualAfterAQFTWave3IsMissingIsotony :
      firstResidualAfterAQFTWave3
      ≡
      missingIsotonyFromCarrierTransport

    quotientResidualAfterAQFTWave3 :
      List AQFTCarrierAlgebraQuotientOpenObligation

    quotientResidualAfterAQFTWave3IsExact :
      quotientResidualAfterAQFTWave3
      ≡
      missingIsotonyFromCarrierTransport
      ∷ missingCausalReachability
      ∷ missingFullTimeSliceTheorem
      ∷ missingKTheoreticIntermediateTarget
      ∷ missingCStarNormUniquenessEnvelope
      ∷ missingNuclearityTheorem
      ∷ missingMassGapEnergyPositivityBWTimeSliceDependency
      ∷ []

    dashiLocalAlgebraResidualBlocker :
      AQFTM4U6ResidualBlocker

    dashiLocalAlgebraResidualBlockerIsMissingDASHILocalAlgebra :
      dashiLocalAlgebraResidualBlocker
      ≡
      missingDASHILocalAlgebra

    cstarCompletionHardHalt :
      String

    cstarCompletionHardHalt-v :
      cstarCompletionHardHalt
      ≡
      "cStarCompletion-authority-only-no-local-C-star-completion"

    bisognanoWichmannHardHalt :
      String

    bisognanoWichmannHardHalt-v :
      bisognanoWichmannHardHalt
      ≡
      "BisognanoWichmann-citation-only-no-local-time-slice-promotion"

    doplicherRobertsHardHalt :
      String

    doplicherRobertsHardHalt-v :
      doplicherRobertsHardHalt
      ≡
      "DoplicherRoberts-not-consumed-before-missingDASHILocalAlgebra"

    aqftWave3Boundary :
      List String

open AQFTWave3PreciseQuotientLocalAlgebraProgress public

canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress :
  AQFTWave3PreciseQuotientLocalAlgebraProgress
canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress =
  record
    { carrierSurface =
        canonicalAQFTCarrierAlgebraQuotientSurface
    ; transportSetoidQuotientConstructionProgress =
        canonicalTransportSetoidQuotientConstructionProgress
    ; preciseQuotientRelation =
        abstractQuotientRelation
    ; preciseQuotientRelationIntroFromTransport =
        abstractQuotientRelationIntro
    ; quotientClassEqualityFromTransport =
        abstractTransportQuotientClassStable
    ; quotientOperationTransportLaws =
        canonicalQuotientAlgebraOperationsTransportWellDefined
    ; quotientNormLaws =
        canonicalQuotientNormSurface
    ; quotientNormBeta =
        abstractQuotientNormβ
    ; localAlgebraIsPromotedReceiptQuotient =
        abstractLocalAlgebraIsPromotedReceiptQuotient
    ; preciseQuotientRelationAdvanced =
        true
    ; preciseQuotientRelationAdvancedIsTrue =
        refl
    ; quotientAlgebraOperationsAdvanced =
        true
    ; quotientAlgebraOperationsAdvancedIsTrue =
        refl
    ; quotientNormOperationAdvanced =
        true
    ; quotientNormOperationAdvancedIsTrue =
        refl
    ; dashiLocalAlgebraTargetAdvanced =
        true
    ; dashiLocalAlgebraTargetAdvancedIsTrue =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; firstResidualAfterAQFTWave3 =
        missingIsotonyFromCarrierTransport
    ; firstResidualAfterAQFTWave3IsMissingIsotony =
        refl
    ; quotientResidualAfterAQFTWave3 =
        missingIsotonyFromCarrierTransport
        ∷ missingCausalReachability
        ∷ missingFullTimeSliceTheorem
        ∷ missingKTheoreticIntermediateTarget
        ∷ missingCStarNormUniquenessEnvelope
        ∷ missingNuclearityTheorem
        ∷ missingMassGapEnergyPositivityBWTimeSliceDependency
        ∷ []
    ; quotientResidualAfterAQFTWave3IsExact =
        refl
    ; dashiLocalAlgebraResidualBlocker =
        missingDASHILocalAlgebra
    ; dashiLocalAlgebraResidualBlockerIsMissingDASHILocalAlgebra =
        refl
    ; cstarCompletionHardHalt =
        "cStarCompletion-authority-only-no-local-C-star-completion"
    ; cstarCompletionHardHalt-v =
        refl
    ; bisognanoWichmannHardHalt =
        "BisognanoWichmann-citation-only-no-local-time-slice-promotion"
    ; bisognanoWichmannHardHalt-v =
        refl
    ; doplicherRobertsHardHalt =
        "DoplicherRoberts-not-consumed-before-missingDASHILocalAlgebra"
    ; doplicherRobertsHardHalt-v =
        refl
    ; aqftWave3Boundary =
        "Wave 3 consumes abstractQuotientRelation as the precise transport quotient relation on promoted receipt classes"
        ∷ "transport quotient equality, quotient relation intro, product/star/norm well-definedness, and quotient norm beta are wired to existing sockets"
        ∷ "AQFT local algebra is identified with the promoted-receipt quotient by abstractLocalAlgebraIsPromotedReceiptQuotient"
        ∷ "missingDASHILocalAlgebra remains unpromoted because C*-completion is authority-only and time-slice/BW/DR data are not locally proved"
        ∷ []
    }

record AQFTL5CarrierIsotonyFrontierReceipt : Setω where
  field
    carrierSurface :
      AQFTCarrierAlgebraQuotientSurface

    wave3Progress :
      AQFTWave3PreciseQuotientLocalAlgebraProgress

    quotientConstructionProgress :
      TransportSetoidQuotientConstructionProgress

    quotientConstructionInhabited :
      TransportSetoidQuotientConstructionProgress.quotientConstructionInhabited
        quotientConstructionProgress
      ≡
      true

    preciseQuotientRelationInhabited :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvanced
        wave3Progress
      ≡
      true

    quotientOperationsInhabited :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientAlgebraOperationsAdvanced
        wave3Progress
      ≡
      true

    quotientNormInhabited :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientNormOperationAdvanced
        wave3Progress
      ≡
      true

    typedNetIsotonyReceipt :
      IsotonyG6CausalityDescentReceiptTarget

    typedNetIsotonyMorphism :
      {small large : AQFT.Region} →
      small AQFT.⊆ large →
      AQFT.AlgebraMorphism small large

    typedNetIsotonyMorphismMatchesReceipt :
      {small large : AQFT.Region} →
      (inclusion : small AQFT.⊆ large) →
      typedNetIsotonyMorphism inclusion
      ≡
      IsotonyG6CausalityDescentReceiptTarget.isotonyTarget
        typedNetIsotonyReceipt
        inclusion

    localAlgebraQuotientEquality :
      (region : AQFT.Region) →
      AQFT.AQFTTypedNetSurface.Algebra
        AQFT.canonicalAQFTTypedNetSurface
        region
      ≡
      abstractPromotedReceiptQuotient region

    exactMissingCarrierTransportLabel :
      String

    exactMissingCarrierTransportLabel-v :
      exactMissingCarrierTransportLabel
      ≡
      "missing-carrier-inclusion-transport-respecting-quotient-and-matching-typed-net-isotony"

    firstResidualAfterL5Inspection :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstResidualAfterL5InspectionIsMissingIsotonyFromCarrierTransport :
      firstResidualAfterL5Inspection
      ≡
      missingIsotonyFromCarrierTransport

    residualAfterL5Inspection :
      List AQFTCarrierAlgebraQuotientOpenObligation

    residualAfterL5InspectionIsExact :
      residualAfterL5Inspection
      ≡
      missingIsotonyFromCarrierTransport
      ∷ missingCausalReachability
      ∷ missingFullTimeSliceTheorem
      ∷ missingKTheoreticIntermediateTarget
      ∷ missingCStarNormUniquenessEnvelope
      ∷ missingNuclearityTheorem
      ∷ missingMassGapEnergyPositivityBWTimeSliceDependency
      ∷ []

    dashiLocalAlgebraResidualBlocker :
      AQFTM4U6ResidualBlocker

    dashiLocalAlgebraResidualBlockerIsMissingDASHILocalAlgebra :
      dashiLocalAlgebraResidualBlocker
      ≡
      missingDASHILocalAlgebra

    gnsResidualBlocker :
      AQFTM4U6ResidualBlocker

    gnsResidualBlockerIsMissingGNSUniversalProperty :
      gnsResidualBlocker
      ≡
      missingGNSUniversalProperty

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    gnsUniversalPropertyPromoted :
      Bool

    gnsUniversalPropertyPromotedIsFalse :
      gnsUniversalPropertyPromoted ≡ false

    noCarrierIsotonyPromotionClaim :
      String

    noCarrierIsotonyPromotionClaim-v :
      noCarrierIsotonyPromotionClaim
      ≡
      "typed-net-isotony-plus-local-algebra-equality-does-not-construct-carrier-transport"

    l5CarrierIsotonyFrontierBoundary :
      List String

open AQFTL5CarrierIsotonyFrontierReceipt public

canonicalAQFTL5CarrierIsotonyFrontierReceipt :
  AQFTL5CarrierIsotonyFrontierReceipt
canonicalAQFTL5CarrierIsotonyFrontierReceipt =
  record
    { carrierSurface =
        canonicalAQFTCarrierAlgebraQuotientSurface
    ; wave3Progress =
        canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; quotientConstructionProgress =
        canonicalTransportSetoidQuotientConstructionProgress
    ; quotientConstructionInhabited =
        TransportSetoidQuotientConstructionProgress.quotientConstructionInhabitedIsTrue
          canonicalTransportSetoidQuotientConstructionProgress
    ; preciseQuotientRelationInhabited =
        AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvancedIsTrue
          canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; quotientOperationsInhabited =
        AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientAlgebraOperationsAdvancedIsTrue
          canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; quotientNormInhabited =
        AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientNormOperationAdvancedIsTrue
          canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; typedNetIsotonyReceipt =
        canonicalIsotonyG6CausalityDescentReceiptTarget
    ; typedNetIsotonyMorphism =
        IsotonyG6CausalityDescentReceiptTarget.isotonyTarget
          canonicalIsotonyG6CausalityDescentReceiptTarget
    ; typedNetIsotonyMorphismMatchesReceipt =
        λ _ →
          refl
    ; localAlgebraQuotientEquality =
        abstractLocalAlgebraIsPromotedReceiptQuotient
    ; exactMissingCarrierTransportLabel =
        "missing-carrier-inclusion-transport-respecting-quotient-and-matching-typed-net-isotony"
    ; exactMissingCarrierTransportLabel-v =
        refl
    ; firstResidualAfterL5Inspection =
        missingIsotonyFromCarrierTransport
    ; firstResidualAfterL5InspectionIsMissingIsotonyFromCarrierTransport =
        refl
    ; residualAfterL5Inspection =
        missingIsotonyFromCarrierTransport
        ∷ missingCausalReachability
        ∷ missingFullTimeSliceTheorem
        ∷ missingKTheoreticIntermediateTarget
        ∷ missingCStarNormUniquenessEnvelope
        ∷ missingNuclearityTheorem
        ∷ missingMassGapEnergyPositivityBWTimeSliceDependency
        ∷ []
    ; residualAfterL5InspectionIsExact =
        refl
    ; dashiLocalAlgebraResidualBlocker =
        missingDASHILocalAlgebra
    ; dashiLocalAlgebraResidualBlockerIsMissingDASHILocalAlgebra =
        refl
    ; gnsResidualBlocker =
        missingGNSUniversalProperty
    ; gnsResidualBlockerIsMissingGNSUniversalProperty =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; gnsUniversalPropertyPromoted =
        false
    ; gnsUniversalPropertyPromotedIsFalse =
        refl
    ; noCarrierIsotonyPromotionClaim =
        "typed-net-isotony-plus-local-algebra-equality-does-not-construct-carrier-transport"
    ; noCarrierIsotonyPromotionClaim-v =
        refl
    ; l5CarrierIsotonyFrontierBoundary =
        "l5 inspection consumes the setoid quotient construction, precise quotient relation, quotient operation transport laws, and quotient norm beta law"
        ∷ "typed-net isotony is available from IsotonyG6CausalityDescentReceiptTarget"
        ∷ "local algebra equality identifies AQFTTypedNetSurface.Algebra with the promoted-receipt quotient"
        ∷ "the missing datum is a carrier-level inclusion transport that respects transport equivalence and induces the typed-net isotony morphism on quotient classes"
        ∷ "therefore missingIsotonyFromCarrierTransport remains the exact first residual, while missingQuotientConstruction and missingPreciseQuotientRelation are not l5 frontier blockers"
        ∷ "missingDASHILocalAlgebra remains blocked by authority-only C-star completion, BW/time-slice targets, and absent DR promotion"
        ∷ "missingGNSUniversalProperty remains blocked because no GNS state, representation, universal arrow proof, or Born-rule adapter is constructed here"
        ∷ []
    }

data AQFTL5FailClosedBlocker : Set where
  l5MissingCarrierInclusionTransport :
    AQFTL5FailClosedBlocker

  l5MissingCarrierTransportRespectsQuotient :
    AQFTL5FailClosedBlocker

  l5MissingCarrierTransportMatchesTypedNetIsotony :
    AQFTL5FailClosedBlocker

  l5MissingCausalReachabilityConstruction :
    AQFTL5FailClosedBlocker

  l5MissingTimeSliceTheoremProof :
    AQFTL5FailClosedBlocker

  l5MissingCauchyEvolutionDeterminationProof :
    AQFTL5FailClosedBlocker

  l5MissingDescentColimitCompatibilityProof :
    AQFTL5FailClosedBlocker

  l5CStarCompletionAuthorityOnly :
    AQFTL5FailClosedBlocker

  l5MissingDASHILocalAlgebraHandoff :
    AQFTL5FailClosedBlocker

  l5MissingGNSUniversalPropertyHandoff :
    AQFTL5FailClosedBlocker

  l5BisognanoWichmannCitationOnly :
    AQFTL5FailClosedBlocker

  l5DoplicherRobertsNotConsumed :
    AQFTL5FailClosedBlocker

canonicalAQFTL5FailClosedBlockers :
  List AQFTL5FailClosedBlocker
canonicalAQFTL5FailClosedBlockers =
  l5MissingCarrierInclusionTransport
  ∷ l5MissingCarrierTransportRespectsQuotient
  ∷ l5MissingCarrierTransportMatchesTypedNetIsotony
  ∷ l5MissingCausalReachabilityConstruction
  ∷ l5MissingTimeSliceTheoremProof
  ∷ l5MissingCauchyEvolutionDeterminationProof
  ∷ l5MissingDescentColimitCompatibilityProof
  ∷ l5CStarCompletionAuthorityOnly
  ∷ l5MissingDASHILocalAlgebraHandoff
  ∷ l5MissingGNSUniversalPropertyHandoff
  ∷ l5BisognanoWichmannCitationOnly
  ∷ l5DoplicherRobertsNotConsumed
  ∷ []

record AQFTL5FailClosedReceipt : Setω where
  field
    restrictedCarrierPredicateReceipt :
      AQFTCarrierPredicateLocalBlockerRetirementReceipt

    l5CarrierIsotonyFrontierReceipt :
      AQFTL5CarrierIsotonyFrontierReceipt

    boundedCarrierDepthProgress :
      BoundedRestrictedCarrierDepthProgressSurface

    concreteDepthFilteredLocalAlgebraData :
      ConcreteDepthFilteredLocalAlgebraData
        abstractPromotedReceiptQuotient
        abstractQuotientNorm

    m4u6HandoffReceipt :
      AQFTM4U6HandoffReceipt
        abstractPromotedReceiptQuotient
        abstractQuotientNorm

    cStarCompletionAuthorityBoundary :
      CStarCompletionUniversalPropertyAuthority
        abstractPromotedReceiptQuotient
        abstractQuotientNorm

    cStarCompletionAuthoritySafe :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthority
        cStarCompletionAuthorityBoundary
      ≡
      true

    cStarCompletionLocallyConstructedIsFalse :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructed
        cStarCompletionAuthorityBoundary
      ≡
      false

    cStarCompletionPromotedIsFalse :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        cStarCompletionAuthorityBoundary
      ≡
      false

    inclusionDescentReceipt :
      IsotonyG6CausalityDescentReceiptTarget

    inclusionDescentPromotedIsFalse :
      IsotonyG6CausalityDescentReceiptTarget.isotonyCausalityDescentPromoted
        inclusionDescentReceipt
      ≡
      false

    timeSliceSurface :
      TimeSliceTheoremSurface

    timeSliceOpenObligationsAreCanonical :
      TimeSliceTheoremSurface.openTimeSliceTheoremObligations
        timeSliceSurface
      ≡
      canonicalTimeSliceTheoremOpenObligations

    timeSlicePromotedIsFalse :
      TimeSliceTheoremSurface.timeSliceTheoremPromoted timeSliceSurface
      ≡
      false

    cauchyEvolutionReceipt :
      CauchyEvolutionReceiptTarget

    cauchyEvolutionOpenObligationsAreCanonical :
      CauchyEvolutionReceiptTarget.openCauchyEvolutionObligations
        cauchyEvolutionReceipt
      ≡
      canonicalCauchyEvolutionOpenObligations

    cauchyTimeSlicePromotedIsFalse :
      CauchyEvolutionReceiptTarget.timeSlicePromoted cauchyEvolutionReceipt
      ≡
      false

    quotientConstructionAdvanced :
      TransportSetoidQuotientConstructionProgress.quotientConstructionInhabited
        (AQFTL5CarrierIsotonyFrontierReceipt.quotientConstructionProgress
          l5CarrierIsotonyFrontierReceipt)
      ≡
      true

    preciseQuotientRelationAdvanced :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvanced
        (AQFTL5CarrierIsotonyFrontierReceipt.wave3Progress
          l5CarrierIsotonyFrontierReceipt)
      ≡
      true

    quotientOpenObligationTail :
      List AQFTCarrierAlgebraQuotientOpenObligation

    quotientOpenObligationTailIsExact :
      quotientOpenObligationTail
      ≡
      missingIsotonyFromCarrierTransport
      ∷ missingCausalReachability
      ∷ missingFullTimeSliceTheorem
      ∷ missingKTheoreticIntermediateTarget
      ∷ missingCStarNormUniquenessEnvelope
      ∷ missingNuclearityTheorem
      ∷ missingMassGapEnergyPositivityBWTimeSliceDependency
      ∷ []

    m4u6ResidualBlockers :
      List AQFTM4U6ResidualBlocker

    m4u6ResidualBlockersAreCanonical :
      m4u6ResidualBlockers
      ≡
      canonicalAQFTM4U6ResidualBlockers

    exactL5FailClosedBlockers :
      List AQFTL5FailClosedBlocker

    exactL5FailClosedBlockersAreCanonical :
      exactL5FailClosedBlockers
      ≡
      canonicalAQFTL5FailClosedBlockers

    fullAQFTNetInhabited :
      Bool

    fullAQFTNetInhabitedIsFalse :
      fullAQFTNetInhabited ≡ false

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    gnsUniversalPropertyPromoted :
      Bool

    gnsUniversalPropertyPromotedIsFalse :
      gnsUniversalPropertyPromoted ≡ false

    bisognanoWichmannCitationOnly :
      Bool

    bisognanoWichmannCitationOnlyIsTrue :
      bisognanoWichmannCitationOnly ≡ true

    doplicherRobertsConsumedHere :
      Bool

    doplicherRobertsConsumedHereIsFalse :
      doplicherRobertsConsumedHere ≡ false

    l5FailClosedBoundary :
      List String

open AQFTL5FailClosedReceipt public

canonicalAQFTL5FailClosedReceipt :
  AQFTL5FailClosedReceipt
canonicalAQFTL5FailClosedReceipt =
  record
    { restrictedCarrierPredicateReceipt =
        canonicalAQFTCarrierPredicateLocalBlockerRetirementReceipt
    ; l5CarrierIsotonyFrontierReceipt =
        canonicalAQFTL5CarrierIsotonyFrontierReceipt
    ; boundedCarrierDepthProgress =
        canonicalBoundedRestrictedCarrierDepthProgressSurface
    ; concreteDepthFilteredLocalAlgebraData =
        canonicalConcreteDepthFilteredLocalAlgebraData
    ; m4u6HandoffReceipt =
        canonicalAQFTM4U6HandoffReceipt
    ; cStarCompletionAuthorityBoundary =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarCompletionAuthoritySafe =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthorityIsTrue
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarCompletionLocallyConstructedIsFalse =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarCompletionPromotedIsFalse =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionPromotedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; inclusionDescentReceipt =
        canonicalIsotonyG6CausalityDescentReceiptTarget
    ; inclusionDescentPromotedIsFalse =
        IsotonyG6CausalityDescentReceiptTarget.isotonyCausalityDescentPromotedIsFalse
          canonicalIsotonyG6CausalityDescentReceiptTarget
    ; timeSliceSurface =
        canonicalTimeSliceTheoremSurface
    ; timeSliceOpenObligationsAreCanonical =
        TimeSliceTheoremSurface.openTimeSliceTheoremObligationsAreCanonical
          canonicalTimeSliceTheoremSurface
    ; timeSlicePromotedIsFalse =
        TimeSliceTheoremSurface.timeSliceTheoremPromotedIsFalse
          canonicalTimeSliceTheoremSurface
    ; cauchyEvolutionReceipt =
        canonicalCauchyEvolutionReceiptTarget
    ; cauchyEvolutionOpenObligationsAreCanonical =
        CauchyEvolutionReceiptTarget.openCauchyEvolutionObligationsAreCanonical
          canonicalCauchyEvolutionReceiptTarget
    ; cauchyTimeSlicePromotedIsFalse =
        CauchyEvolutionReceiptTarget.timeSlicePromotedIsFalse
          canonicalCauchyEvolutionReceiptTarget
    ; quotientConstructionAdvanced =
        AQFTL5CarrierIsotonyFrontierReceipt.quotientConstructionInhabited
          canonicalAQFTL5CarrierIsotonyFrontierReceipt
    ; preciseQuotientRelationAdvanced =
        AQFTL5CarrierIsotonyFrontierReceipt.preciseQuotientRelationInhabited
          canonicalAQFTL5CarrierIsotonyFrontierReceipt
    ; quotientOpenObligationTail =
        missingIsotonyFromCarrierTransport
        ∷ missingCausalReachability
        ∷ missingFullTimeSliceTheorem
        ∷ missingKTheoreticIntermediateTarget
        ∷ missingCStarNormUniquenessEnvelope
        ∷ missingNuclearityTheorem
        ∷ missingMassGapEnergyPositivityBWTimeSliceDependency
        ∷ []
    ; quotientOpenObligationTailIsExact =
        refl
    ; m4u6ResidualBlockers =
        canonicalAQFTM4U6ResidualBlockers
    ; m4u6ResidualBlockersAreCanonical =
        refl
    ; exactL5FailClosedBlockers =
        canonicalAQFTL5FailClosedBlockers
    ; exactL5FailClosedBlockersAreCanonical =
        refl
    ; fullAQFTNetInhabited =
        false
    ; fullAQFTNetInhabitedIsFalse =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; gnsUniversalPropertyPromoted =
        false
    ; gnsUniversalPropertyPromotedIsFalse =
        refl
    ; bisognanoWichmannCitationOnly =
        true
    ; bisognanoWichmannCitationOnlyIsTrue =
        refl
    ; doplicherRobertsConsumedHere =
        false
    ; doplicherRobertsConsumedHereIsFalse =
        refl
    ; l5FailClosedBoundary =
        "l5 fail-closed receipt consumes restricted carrier and promoted receipt predicate sockets"
        ∷ "setoid quotient construction, precise quotient relation, quotient operations, and norm beta are advanced through the Wave3/frontier receipts"
        ∷ "C-star completion is consumed only through the safe authority boundary and remains locally unconstructed and unpromoted"
        ∷ "typed-net isotony and descent are available, but no carrier-level inclusion transport is constructed to descend them from the restricted carrier quotient"
        ∷ "time-slice and Cauchy evolution are consumed as target surfaces with their canonical open obligations intact"
        ∷ "full AQFT net inhabitation fails closed at missingIsotonyFromCarrierTransport before DASHILocalAlgebra or GNS universality can be promoted"
        ∷ "BisognanoWichmann remains citation-only and DoplicherRoberts is not consumed here"
        ∷ []
    }

record AQFTL5PreciseQuotientRelationToConstructionShapeReceipt : Setω where
  field
    quotientConstructionProgress :
      TransportSetoidQuotientConstructionProgress

    wave3PreciseQuotientProgress :
      AQFTWave3PreciseQuotientLocalAlgebraProgress

    preciseRelation :
      {region : AQFT.Region} →
      abstractPromotedReceiptQuotient region →
      abstractPromotedReceiptQuotient region →
      Set

    quotientIntroShape :
      {region : AQFT.Region} →
      (x : abstractRestrictedCarrier region) →
      abstractPromotedReceipt x →
      abstractPromotedReceiptQuotient region

    relationIntroShape :
      {region : AQFT.Region} →
      {x y : abstractRestrictedCarrier region} →
      (eq : abstractTransportEquivalent x y) →
      (receipt : abstractPromotedReceipt x) →
      preciseRelation
        (quotientIntroShape x receipt)
        (quotientIntroShape
          y
          (abstractPromotedReceiptTransport eq receipt))

    quotientConstructionShapeAvailable :
      Bool

    quotientConstructionShapeAvailableIsTrue :
      quotientConstructionShapeAvailable ≡ true

    localDASHIAlgebraPromoted :
      Bool

    localDASHIAlgebraPromotedIsFalse :
      localDASHIAlgebraPromoted ≡ false

    firstResidualAfterShape :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstResidualAfterShapeIsMissingIsotony :
      firstResidualAfterShape
      ≡
      missingIsotonyFromCarrierTransport

    retainedM4U6ResidualBlockers :
      List AQFTM4U6ResidualBlocker

    retainedM4U6ResidualBlockersAreCanonical :
      retainedM4U6ResidualBlockers
      ≡
      canonicalAQFTM4U6ResidualBlockers

    l5ShapeBoundary :
      List String

open AQFTL5PreciseQuotientRelationToConstructionShapeReceipt public

canonicalAQFTL5PreciseQuotientRelationToConstructionShapeReceipt :
  AQFTL5PreciseQuotientRelationToConstructionShapeReceipt
canonicalAQFTL5PreciseQuotientRelationToConstructionShapeReceipt =
  record
    { quotientConstructionProgress =
        canonicalTransportSetoidQuotientConstructionProgress
    ; wave3PreciseQuotientProgress =
        canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; preciseRelation =
        abstractQuotientRelation
    ; quotientIntroShape =
        abstractQuotientIntro
    ; relationIntroShape =
        abstractQuotientRelationIntro
    ; quotientConstructionShapeAvailable =
        true
    ; quotientConstructionShapeAvailableIsTrue =
        refl
    ; localDASHIAlgebraPromoted =
        false
    ; localDASHIAlgebraPromotedIsFalse =
        refl
    ; firstResidualAfterShape =
        missingIsotonyFromCarrierTransport
    ; firstResidualAfterShapeIsMissingIsotony =
        refl
    ; retainedM4U6ResidualBlockers =
        canonicalAQFTM4U6ResidualBlockers
    ; retainedM4U6ResidualBlockersAreCanonical =
        refl
    ; l5ShapeBoundary =
        "l5 precise quotient relation is explicitly tied to the quotient construction intro shape"
        ∷ "transport-equivalent representatives yield a precise relation witness through abstractQuotientRelationIntro"
        ∷ "this advances only quotient shape wiring; carrier-level isotony and DASHI local algebra remain unpromoted"
        ∷ "m4/u6 residual blockers remain missingDASHILocalAlgebra and missingGNSUniversalProperty"
        ∷ []
    }

record AQFTL3FilteredColimitPreservationAttemptSurface : Setω where
  field
    depthFilteredSurface :
      DepthFilteredLocalAlgebraSurface

    colimitUniversality :
      ColimitUniversalityReceiptTarget

    typedNetIsotonyDescent :
      IsotonyG6CausalityDescentReceiptTarget

    depthColimitMatchesLocalAlgebra :
      (region : AQFT.Region) →
      DepthFilteredLocalAlgebraSurface.A_colim depthFilteredSurface region
      ≡
      abstractPromotedReceiptQuotient region

    filteredColimitPreservationTarget :
      {small large : AQFT.Region} →
      small AQFT.⊆ large →
      Set

    filteredColimitShapeThreaded :
      Bool

    filteredColimitShapeThreadedIsTrue :
      filteredColimitShapeThreaded ≡ true

    filteredColimitPreservationProved :
      Bool

    filteredColimitPreservationProvedIsFalse :
      filteredColimitPreservationProved ≡ false

    firstResidualAfterL3Attempt :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstResidualAfterL3AttemptIsMissingIsotony :
      firstResidualAfterL3Attempt
      ≡
      missingIsotonyFromCarrierTransport

    l3AttemptBoundary :
      List String

open AQFTL3FilteredColimitPreservationAttemptSurface public

canonicalAQFTL3FilteredColimitPreservationAttemptSurface :
  AQFTL3FilteredColimitPreservationAttemptSurface
canonicalAQFTL3FilteredColimitPreservationAttemptSurface =
  record
    { depthFilteredSurface =
        canonicalConcreteDepthFilteredLocalAlgebraSurface
    ; colimitUniversality =
        canonicalConcreteColimitUniversalityReceiptTarget
    ; typedNetIsotonyDescent =
        canonicalIsotonyG6CausalityDescentReceiptTarget
    ; depthColimitMatchesLocalAlgebra =
        λ _ →
          refl
    ; filteredColimitPreservationTarget =
        λ _ →
          ⊤
    ; filteredColimitShapeThreaded =
        true
    ; filteredColimitShapeThreadedIsTrue =
        refl
    ; filteredColimitPreservationProved =
        false
    ; filteredColimitPreservationProvedIsFalse =
        refl
    ; firstResidualAfterL3Attempt =
        missingIsotonyFromCarrierTransport
    ; firstResidualAfterL3AttemptIsMissingIsotony =
        refl
    ; l3AttemptBoundary =
        "l3 filtered-colimit-preservation attempt reuses the repo-native concrete Bool-depth colimit surface"
        ∷ "the colimit algebra shape is threaded to abstractPromotedReceiptQuotient by definitional equality"
        ∷ "the preservation theorem is left as a target because no carrier inclusion transport inducing typed-net isotony is constructed"
        ∷ []
    }

record AQFTFirstMissingChainReceipt : Setω where
  field
    quotientConstructionProgress :
      TransportSetoidQuotientConstructionProgress

    missingQuotientConstructionAdvanced :
      TransportSetoidQuotientConstructionProgress.quotientConstructionInhabited
        quotientConstructionProgress
      ≡
      true

    firstResidualAfterQuotientConstruction :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstResidualAfterQuotientConstruction-v :
      firstResidualAfterQuotientConstruction
      ≡
      missingPreciseQuotientRelation

    preciseQuotientProgress :
      AQFTWave3PreciseQuotientLocalAlgebraProgress

    preciseQuotientRelation :
      {region : AQFT.Region} →
      abstractPromotedReceiptQuotient region →
      abstractPromotedReceiptQuotient region →
      Set

    preciseQuotientRelationMatchesWave3 :
      {region : AQFT.Region} →
      (x y : abstractPromotedReceiptQuotient region) →
      preciseQuotientRelation x y
      ≡
      AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelation
        preciseQuotientProgress
        x
        y

    missingPreciseQuotientRelationAdvanced :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvanced
        preciseQuotientProgress
      ≡
      true

    localAlgebraQuotientEquality :
      (region : AQFT.Region) →
      AQFT.AQFTTypedNetSurface.Algebra
        AQFT.canonicalAQFTTypedNetSurface
        region
      ≡
      abstractPromotedReceiptQuotient region

    missingDASHILocalAlgebraBlocker :
      AQFTM4U6ResidualBlocker

    missingDASHILocalAlgebraBlocker-v :
      missingDASHILocalAlgebraBlocker
      ≡
      missingDASHILocalAlgebra

    m4u6Handoff :
      AQFTM4U6HandoffReceipt
        abstractPromotedReceiptQuotient
        abstractQuotientNorm

    u6HandoffFirstResidualIsMissingDASHILocalAlgebra :
      AQFTM4U6HandoffReceipt.u6FirstResidualBlocker m4u6Handoff
      ≡
      missingDASHILocalAlgebra

    cStarCompletionAuthority :
      CStarCompletionUniversalPropertyAuthority
        abstractPromotedReceiptQuotient
        abstractQuotientNorm

    cStarCompletionLocallyConstructedIsFalse :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructed
        cStarCompletionAuthority
      ≡
      false

    cStarCompletionPromotedIsFalse :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        cStarCompletionAuthority
      ≡
      false

    timeSliceSurface :
      TimeSliceTheoremSurface

    timeSlicePromotedIsFalse :
      TimeSliceTheoremSurface.timeSliceTheoremPromoted timeSliceSurface
      ≡
      false

    bisognanoWichmannCitationOnly :
      Bool

    bisognanoWichmannCitationOnlyIsTrue :
      bisognanoWichmannCitationOnly ≡ true

    terminalPromotionSuppliedHere :
      Bool

    terminalPromotionSuppliedHereIsFalse :
      terminalPromotionSuppliedHere ≡ false

    doplicherRobertsPromotionSuppliedHere :
      Bool

    doplicherRobertsPromotionSuppliedHereIsFalse :
      doplicherRobertsPromotionSuppliedHere ≡ false

    exactFirstMissingChain :
      List String

open AQFTFirstMissingChainReceipt public

canonicalAQFTFirstMissingChainReceipt :
  AQFTFirstMissingChainReceipt
canonicalAQFTFirstMissingChainReceipt =
  record
    { quotientConstructionProgress =
        canonicalTransportSetoidQuotientConstructionProgress
    ; missingQuotientConstructionAdvanced =
        TransportSetoidQuotientConstructionProgress.quotientConstructionInhabitedIsTrue
          canonicalTransportSetoidQuotientConstructionProgress
    ; firstResidualAfterQuotientConstruction =
        missingPreciseQuotientRelation
    ; firstResidualAfterQuotientConstruction-v =
        refl
    ; preciseQuotientProgress =
        canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; preciseQuotientRelation =
        abstractQuotientRelation
    ; preciseQuotientRelationMatchesWave3 =
        λ _ _ →
          refl
    ; missingPreciseQuotientRelationAdvanced =
        AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvancedIsTrue
          canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; localAlgebraQuotientEquality =
        abstractLocalAlgebraIsPromotedReceiptQuotient
    ; missingDASHILocalAlgebraBlocker =
        missingDASHILocalAlgebra
    ; missingDASHILocalAlgebraBlocker-v =
        refl
    ; m4u6Handoff =
        canonicalAQFTM4U6HandoffReceipt
    ; u6HandoffFirstResidualIsMissingDASHILocalAlgebra =
        AQFTM4U6HandoffReceipt.u6FirstResidualBlockerIsMissingDASHILocalAlgebra
          canonicalAQFTM4U6HandoffReceipt
    ; cStarCompletionAuthority =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarCompletionLocallyConstructedIsFalse =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarCompletionPromotedIsFalse =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionPromotedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; timeSliceSurface =
        canonicalTimeSliceTheoremSurface
    ; timeSlicePromotedIsFalse =
        TimeSliceTheoremSurface.timeSliceTheoremPromotedIsFalse
          canonicalTimeSliceTheoremSurface
    ; bisognanoWichmannCitationOnly =
        true
    ; bisognanoWichmannCitationOnlyIsTrue =
        refl
    ; terminalPromotionSuppliedHere =
        false
    ; terminalPromotionSuppliedHereIsFalse =
        refl
    ; doplicherRobertsPromotionSuppliedHere =
        false
    ; doplicherRobertsPromotionSuppliedHereIsFalse =
        refl
    ; exactFirstMissingChain =
        "missingQuotientConstruction is advanced by the setoid quotient construction receipt"
        ∷ "missingPreciseQuotientRelation is advanced by abstractQuotientRelation plus its Wave3 transport-intro socket"
        ∷ "missingDASHILocalAlgebra remains the u6 blocker because C-star completion is authority-only, TimeSliceTheoremSurface is unpromoted, BisognanoWichmann is citation-only, and DoplicherRoberts promotion is absent"
        ∷ "no terminal promotion or DR promotion is supplied by this chain receipt"
        ∷ []
    }

record AQFTNextWavePreciseQuotientLocalAlgebraAttemptReceipt : Setω where
  field
    firstMissingChain :
      AQFTFirstMissingChainReceipt

    preciseQuotientAttempt :
      AQFTL5PreciseQuotientRelationToConstructionShapeReceipt

    filteredColimitAttempt :
      AQFTL3FilteredColimitPreservationAttemptSurface

    carrierFunctorLeftAdjointAttempted :
      Bool

    carrierFunctorLeftAdjointAttemptedIsTrue :
      carrierFunctorLeftAdjointAttempted ≡ true

    carrierFunctorLeftAdjointConstructed :
      Bool

    carrierFunctorLeftAdjointConstructedIsFalse :
      carrierFunctorLeftAdjointConstructed ≡ false

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    preciseQuotientRelationAdvanced :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvanced
        (AQFTFirstMissingChainReceipt.preciseQuotientProgress firstMissingChain)
      ≡
      true

    quotientConstructionAdvanced :
      TransportSetoidQuotientConstructionProgress.quotientConstructionInhabited
        (AQFTFirstMissingChainReceipt.quotientConstructionProgress firstMissingChain)
      ≡
      true

    carrierLevelIsotonyStillMissing :
      AQFTCarrierAlgebraQuotientOpenObligation

    carrierLevelIsotonyStillMissing-v :
      carrierLevelIsotonyStillMissing
      ≡
      missingIsotonyFromCarrierTransport

    dashiLocalAlgebraBlocker :
      AQFTM4U6ResidualBlocker

    dashiLocalAlgebraBlocker-v :
      dashiLocalAlgebraBlocker
      ≡
      missingDASHILocalAlgebra

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    gnsUniversalPropertyPromoted :
      Bool

    gnsUniversalPropertyPromotedIsFalse :
      gnsUniversalPropertyPromoted ≡ false

    nextWaveAQFTBoundary :
      List String

open AQFTNextWavePreciseQuotientLocalAlgebraAttemptReceipt public

canonicalAQFTNextWavePreciseQuotientLocalAlgebraAttemptReceipt :
  AQFTNextWavePreciseQuotientLocalAlgebraAttemptReceipt
canonicalAQFTNextWavePreciseQuotientLocalAlgebraAttemptReceipt =
  record
    { firstMissingChain =
        canonicalAQFTFirstMissingChainReceipt
    ; preciseQuotientAttempt =
        canonicalAQFTL5PreciseQuotientRelationToConstructionShapeReceipt
    ; filteredColimitAttempt =
        canonicalAQFTL3FilteredColimitPreservationAttemptSurface
    ; carrierFunctorLeftAdjointAttempted =
        true
    ; carrierFunctorLeftAdjointAttemptedIsTrue =
        refl
    ; carrierFunctorLeftAdjointConstructed =
        false
    ; carrierFunctorLeftAdjointConstructedIsFalse =
        refl
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; preciseQuotientRelationAdvanced =
        AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvancedIsTrue
          canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; quotientConstructionAdvanced =
        TransportSetoidQuotientConstructionProgress.quotientConstructionInhabitedIsTrue
          canonicalTransportSetoidQuotientConstructionProgress
    ; carrierLevelIsotonyStillMissing =
        missingIsotonyFromCarrierTransport
    ; carrierLevelIsotonyStillMissing-v =
        refl
    ; dashiLocalAlgebraBlocker =
        missingDASHILocalAlgebra
    ; dashiLocalAlgebraBlocker-v =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; gnsUniversalPropertyPromoted =
        false
    ; gnsUniversalPropertyPromotedIsFalse =
        refl
    ; nextWaveAQFTBoundary =
        "l5 next-wave attempt consumes the existing transport quotient and precise quotient surfaces"
        ∷ "l3 next-wave attempt records the carrier-functor left-adjoint route as attempted but not constructed"
        ∷ "filtered-colimit preservation remains a target surface; no adjunction, local algebra, or GNS universal property is promoted"
        ∷ "the carrier-level local-net frontier remains missingIsotonyFromCarrierTransport before missingDASHILocalAlgebra can be consumed downstream"
        ∷ []
    }

record L5Gate5DASHILocalAlgebraResidualReceipt : Setω where
  field
    firstMissingChain :
      AQFTFirstMissingChainReceipt

    quotientConstructionAdvanced :
      TransportSetoidQuotientConstructionProgress.quotientConstructionInhabited
        (AQFTFirstMissingChainReceipt.quotientConstructionProgress
          firstMissingChain)
      ≡
      true

    preciseQuotientRelationAdvanced :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvanced
        (AQFTFirstMissingChainReceipt.preciseQuotientProgress
          firstMissingChain)
      ≡
      true

    localAlgebraCarrier :
      AQFT.Region →
      Set

    localAlgebraCarrierMatchesQuotient :
      (region : AQFT.Region) →
      localAlgebraCarrier region
      ≡
      abstractPromotedReceiptQuotient region

    typedNetLocalAlgebraMatchesCarrier :
      (region : AQFT.Region) →
      AQFT.AQFTTypedNetSurface.Algebra
        AQFT.canonicalAQFTTypedNetSurface
        region
      ≡
      localAlgebraCarrier region

    firstResidualBlocker :
      AQFTM4U6ResidualBlocker

    firstResidualBlockerIsMissingDASHILocalAlgebra :
      firstResidualBlocker
      ≡
      missingDASHILocalAlgebra

    cstarCompletionPromoted :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        (AQFTFirstMissingChainReceipt.cStarCompletionAuthority
          firstMissingChain)
      ≡
      false

    timeSlicePromoted :
      TimeSliceTheoremSurface.timeSliceTheoremPromoted
        (AQFTFirstMissingChainReceipt.timeSliceSurface firstMissingChain)
      ≡
      false

    bisognanoWichmannCitationOnly :
      AQFTFirstMissingChainReceipt.bisognanoWichmannCitationOnly
        firstMissingChain
      ≡
      true

    doplicherRobertsPromotionSuppliedHere :
      AQFTFirstMissingChainReceipt.doplicherRobertsPromotionSuppliedHere
        firstMissingChain
      ≡
      false

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    receiptBoundary :
      List String

open L5Gate5DASHILocalAlgebraResidualReceipt public

canonicalL5Gate5DASHILocalAlgebraResidualReceipt :
  L5Gate5DASHILocalAlgebraResidualReceipt
canonicalL5Gate5DASHILocalAlgebraResidualReceipt =
  record
    { firstMissingChain =
        canonicalAQFTFirstMissingChainReceipt
    ; quotientConstructionAdvanced =
        AQFTFirstMissingChainReceipt.missingQuotientConstructionAdvanced
          canonicalAQFTFirstMissingChainReceipt
    ; preciseQuotientRelationAdvanced =
        AQFTFirstMissingChainReceipt.missingPreciseQuotientRelationAdvanced
          canonicalAQFTFirstMissingChainReceipt
    ; localAlgebraCarrier =
        abstractPromotedReceiptQuotient
    ; localAlgebraCarrierMatchesQuotient =
        λ _ →
          refl
    ; typedNetLocalAlgebraMatchesCarrier =
        AQFTFirstMissingChainReceipt.localAlgebraQuotientEquality
          canonicalAQFTFirstMissingChainReceipt
    ; firstResidualBlocker =
        missingDASHILocalAlgebra
    ; firstResidualBlockerIsMissingDASHILocalAlgebra =
        refl
    ; cstarCompletionPromoted =
        AQFTFirstMissingChainReceipt.cStarCompletionPromotedIsFalse
          canonicalAQFTFirstMissingChainReceipt
    ; timeSlicePromoted =
        AQFTFirstMissingChainReceipt.timeSlicePromotedIsFalse
          canonicalAQFTFirstMissingChainReceipt
    ; bisognanoWichmannCitationOnly =
        AQFTFirstMissingChainReceipt.bisognanoWichmannCitationOnlyIsTrue
          canonicalAQFTFirstMissingChainReceipt
    ; doplicherRobertsPromotionSuppliedHere =
        AQFTFirstMissingChainReceipt.doplicherRobertsPromotionSuppliedHereIsFalse
          canonicalAQFTFirstMissingChainReceipt
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Gate5 first-missing is now recorded as a DASHI local-algebra residual over abstractPromotedReceiptQuotient"
        ∷ "the quotient construction and precise quotient relation are consumed as advanced receipts"
        ∷ "typed-net local algebra equality is only the canonical abstract quotient equality, not a C-star or DR promotion"
        ∷ "C-star completion, time-slice, Bisognano-Wichmann, and Doplicher-Roberts promotion remain fail-closed"
        ∷ []
    }

record Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt : Setω where
  field
    gate5LocalAlgebraResidual :
      L5Gate5DASHILocalAlgebraResidualReceipt

    nextWaveQuotientAttempt :
      AQFTNextWavePreciseQuotientLocalAlgebraAttemptReceipt

    quotientRelationAdvanced :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvanced
        (AQFTFirstMissingChainReceipt.preciseQuotientProgress
          (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
            gate5LocalAlgebraResidual))
      ≡
      true

    quotientConstructionAdvanced :
      TransportSetoidQuotientConstructionProgress.quotientConstructionInhabited
        (AQFTFirstMissingChainReceipt.quotientConstructionProgress
          (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
            gate5LocalAlgebraResidual))
      ≡
      true

    quotientOperationsAdvanced :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientAlgebraOperationsAdvanced
        (AQFTFirstMissingChainReceipt.preciseQuotientProgress
          (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
            gate5LocalAlgebraResidual))
      ≡
      true

    quotientNormWellDefinednessReceiptOnly :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientNormOperationAdvanced
        (AQFTFirstMissingChainReceipt.preciseQuotientProgress
          (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
            gate5LocalAlgebraResidual))
      ≡
      true

    cStarCompletionAuthorityBoundary :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        (AQFTFirstMissingChainReceipt.cStarCompletionAuthority
          (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
            gate5LocalAlgebraResidual))
      ≡
      false

    localNetIsotonyBlocker :
      AQFTCarrierAlgebraQuotientOpenObligation

    localNetIsotonyBlocker-v :
      localNetIsotonyBlocker
      ≡
      missingIsotonyFromCarrierTransport

    timeSliceBlocker :
      TimeSliceTheoremSurface.timeSliceTheoremPromoted
        (AQFTFirstMissingChainReceipt.timeSliceSurface
          (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
            gate5LocalAlgebraResidual))
      ≡
      false

    firstMiddle6AQFTResidual :
      AQFTM4U6ResidualBlocker

    firstMiddle6AQFTResidual-v :
      firstMiddle6AQFTResidual
      ≡
      missingDASHILocalAlgebra

    gnsUniversalPropertyResidual :
      AQFTM4U6ResidualBlocker

    gnsUniversalPropertyResidual-v :
      gnsUniversalPropertyResidual
      ≡
      missingGNSUniversalProperty

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    middle6Boundary :
      List String

open Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt public

canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt :
  Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt =
  record
    { gate5LocalAlgebraResidual =
        canonicalL5Gate5DASHILocalAlgebraResidualReceipt
    ; nextWaveQuotientAttempt =
        canonicalAQFTNextWavePreciseQuotientLocalAlgebraAttemptReceipt
    ; quotientRelationAdvanced =
        AQFTFirstMissingChainReceipt.missingPreciseQuotientRelationAdvanced
          canonicalAQFTFirstMissingChainReceipt
    ; quotientConstructionAdvanced =
        AQFTFirstMissingChainReceipt.missingQuotientConstructionAdvanced
          canonicalAQFTFirstMissingChainReceipt
    ; quotientOperationsAdvanced =
        AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientAlgebraOperationsAdvancedIsTrue
          canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; quotientNormWellDefinednessReceiptOnly =
        AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientNormOperationAdvancedIsTrue
          canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; cStarCompletionAuthorityBoundary =
        AQFTFirstMissingChainReceipt.cStarCompletionPromotedIsFalse
          canonicalAQFTFirstMissingChainReceipt
    ; localNetIsotonyBlocker =
        missingIsotonyFromCarrierTransport
    ; localNetIsotonyBlocker-v =
        refl
    ; timeSliceBlocker =
        AQFTFirstMissingChainReceipt.timeSlicePromotedIsFalse
          canonicalAQFTFirstMissingChainReceipt
    ; firstMiddle6AQFTResidual =
        missingDASHILocalAlgebra
    ; firstMiddle6AQFTResidual-v =
        refl
    ; gnsUniversalPropertyResidual =
        missingGNSUniversalProperty
    ; gnsUniversalPropertyResidual-v =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; middle6Boundary =
        "middle6 AQFT records quotient relation, quotient construction, quotient operations, and quotient norm well-definedness as advanced receipt surfaces"
        ∷ "norm well-definedness here is only the quotient norm transport/beta receipt, not a C-star norm uniqueness or completion theorem"
        ∷ "C-star completion is consumed only through the existing authority boundary and remains locally unconstructed"
        ∷ "local-net isotony still blocks at missingIsotonyFromCarrierTransport, and time-slice promotion remains false"
        ∷ "the first AQFT residual remains missingDASHILocalAlgebra; the downstream GNS residual remains missingGNSUniversalProperty"
        ∷ []
    }

record AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt : Setω where
  field
    gate5FailClosedReceipt :
      Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt

    quotientCarrier :
      AQFT.Region →
      Set

    quotientCarrierMatchesPromotedReceiptQuotient :
      (region : AQFT.Region) →
      quotientCarrier region
      ≡
      abstractPromotedReceiptQuotient region

    quotientRelation :
      {region : AQFT.Region} →
      abstractPromotedReceiptQuotient region →
      abstractPromotedReceiptQuotient region →
      Set

    quotientRelationMatchesTransportRelation :
      {region : AQFT.Region} →
      (x y : abstractPromotedReceiptQuotient region) →
      quotientRelation x y
      ≡
      abstractQuotientRelation x y

    quotientNorm :
      {region : AQFT.Region} →
      abstractPromotedReceiptQuotient region →
      RA.ℝ

    quotientNormMatchesAbstractNorm :
      {region : AQFT.Region} →
      (x : abstractPromotedReceiptQuotient region) →
      quotientNorm x
      ≡
      abstractQuotientNorm x

    quotientOperationsAdvanced :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientAlgebraOperationsAdvanced
        canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
      ≡
      true

    quotientNormTransportAdvanced :
      AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientNormOperationAdvanced
        canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
      ≡
      true

    spacelikeCommutativityAttempted :
      Bool

    spacelikeCommutativityAttemptedIsTrue :
      spacelikeCommutativityAttempted ≡ true

    spacelikeCommutativityProved :
      Bool

    spacelikeCommutativityProvedIsFalse :
      spacelikeCommutativityProved ≡ false

    causalPathAbsenceConstructed :
      Bool

    causalPathAbsenceConstructedIsFalse :
      causalPathAbsenceConstructed ≡ false

    firstSpacelikeCommutativityBlocker :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstSpacelikeCommutativityBlockerIsCausalReachability :
      firstSpacelikeCommutativityBlocker
      ≡
      missingCausalReachability

    carrierLevelIsotonyStillBlocks :
      AQFTCarrierAlgebraQuotientOpenObligation

    carrierLevelIsotonyStillBlocksIsExact :
      carrierLevelIsotonyStillBlocks
      ≡
      missingIsotonyFromCarrierTransport

    missingDASHILocalAlgebraNotConsumed :
      AQFTM4U6ResidualBlocker

    missingDASHILocalAlgebraNotConsumedIsExact :
      missingDASHILocalAlgebraNotConsumed
      ≡
      missingDASHILocalAlgebra

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    attemptBoundary :
      List String

open AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt public

canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt :
  AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt =
  record
    { gate5FailClosedReceipt =
        canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; quotientCarrier =
        abstractPromotedReceiptQuotient
    ; quotientCarrierMatchesPromotedReceiptQuotient =
        λ _ →
          refl
    ; quotientRelation =
        abstractQuotientRelation
    ; quotientRelationMatchesTransportRelation =
        λ _ _ →
          refl
    ; quotientNorm =
        abstractQuotientNorm
    ; quotientNormMatchesAbstractNorm =
        λ _ →
          refl
    ; quotientOperationsAdvanced =
        AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientAlgebraOperationsAdvancedIsTrue
          canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; quotientNormTransportAdvanced =
        AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientNormOperationAdvancedIsTrue
          canonicalAQFTWave3PreciseQuotientLocalAlgebraProgress
    ; spacelikeCommutativityAttempted =
        true
    ; spacelikeCommutativityAttemptedIsTrue =
        refl
    ; spacelikeCommutativityProved =
        false
    ; spacelikeCommutativityProvedIsFalse =
        refl
    ; causalPathAbsenceConstructed =
        false
    ; causalPathAbsenceConstructedIsFalse =
        refl
    ; firstSpacelikeCommutativityBlocker =
        missingCausalReachability
    ; firstSpacelikeCommutativityBlockerIsCausalReachability =
        refl
    ; carrierLevelIsotonyStillBlocks =
        missingIsotonyFromCarrierTransport
    ; carrierLevelIsotonyStillBlocksIsExact =
        refl
    ; missingDASHILocalAlgebraNotConsumed =
        missingDASHILocalAlgebra
    ; missingDASHILocalAlgebraNotConsumedIsExact =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; attemptBoundary =
        "l5 quotient operations are threaded through abstractPromotedReceiptQuotient, abstractQuotientRelation, and abstractQuotientNorm"
        ∷ "the algebra-operation and quotient-norm transport receipts are advanced, but only as quotient transport surfaces"
        ∷ "spacelike commutativity is attempted at the local-net level and stops at missingCausalReachability/causal-path absence"
        ∷ "carrier-level isotony still blocks at missingIsotonyFromCarrierTransport"
        ∷ "missingDASHILocalAlgebra is not consumed and DASHI local algebra promotion remains false"
        ∷ []
    }

data DASHILocalAlgebraClosureMissingConstructor : Set where
  missingCStarCompletionConstructor :
    DASHILocalAlgebraClosureMissingConstructor

  missingCompletionCStarAlgebraWitnessConstructor :
    DASHILocalAlgebraClosureMissingConstructor

  missingLocalOperatorCarrierConstructor :
    DASHILocalAlgebraClosureMissingConstructor

  missingLocalOperatorMultiplicationConstructor :
    DASHILocalAlgebraClosureMissingConstructor

  missingLocalOperatorStarConstructor :
    DASHILocalAlgebraClosureMissingConstructor

  missingSpacelikeCausalBFSPathAbsenceConstructor :
    DASHILocalAlgebraClosureMissingConstructor

canonicalDASHILocalAlgebraClosureMissingConstructors :
  List DASHILocalAlgebraClosureMissingConstructor
canonicalDASHILocalAlgebraClosureMissingConstructors =
  missingCStarCompletionConstructor
  ∷ missingCompletionCStarAlgebraWitnessConstructor
  ∷ missingLocalOperatorCarrierConstructor
  ∷ missingLocalOperatorMultiplicationConstructor
  ∷ missingLocalOperatorStarConstructor
  ∷ missingSpacelikeCausalBFSPathAbsenceConstructor
  ∷ []

Gate5QuotientConstructionAdvanced :
  Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt →
  Set
Gate5QuotientConstructionAdvanced receipt =
  TransportSetoidQuotientConstructionProgress.quotientConstructionInhabited
    (AQFTFirstMissingChainReceipt.quotientConstructionProgress
      (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
        (Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.gate5LocalAlgebraResidual
          receipt)))
  ≡
  true

Gate5QuotientRelationAdvanced :
  Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt →
  Set
Gate5QuotientRelationAdvanced receipt =
  AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvanced
    (AQFTFirstMissingChainReceipt.preciseQuotientProgress
      (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
        (Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.gate5LocalAlgebraResidual
          receipt)))
  ≡
  true

Gate5QuotientOperationsAdvanced :
  Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt →
  Set
Gate5QuotientOperationsAdvanced receipt =
  AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientAlgebraOperationsAdvanced
    (AQFTFirstMissingChainReceipt.preciseQuotientProgress
      (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
        (Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.gate5LocalAlgebraResidual
          receipt)))
  ≡
  true

Gate5QuotientNormTransportAdvanced :
  Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt →
  Set
Gate5QuotientNormTransportAdvanced receipt =
  AQFTWave3PreciseQuotientLocalAlgebraProgress.quotientNormOperationAdvanced
    (AQFTFirstMissingChainReceipt.preciseQuotientProgress
      (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
        (Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.gate5LocalAlgebraResidual
          receipt)))
  ≡
  true

Gate5CStarCompletionPromotedFalse :
  Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt →
  Set
Gate5CStarCompletionPromotedFalse receipt =
  CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
    (AQFTFirstMissingChainReceipt.cStarCompletionAuthority
      (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
        (Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.gate5LocalAlgebraResidual
          receipt)))
  ≡
  false

Gate5TimeSlicePromotedFalse :
  Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt →
  Set
Gate5TimeSlicePromotedFalse receipt =
  TimeSliceTheoremSurface.timeSliceTheoremPromoted
    (AQFTFirstMissingChainReceipt.timeSliceSurface
      (L5Gate5DASHILocalAlgebraResidualReceipt.firstMissingChain
        (Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.gate5LocalAlgebraResidual
          receipt)))
  ≡
  false

GNSHandoffUniversalPropertyReceiptInhabited :
  Modular.Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt →
  Set
GNSHandoffUniversalPropertyReceiptInhabited handoff =
  Modular.GNSUniversalPropertyReceipt.universalPropertyReceiptInhabited
    (Modular.M4GNSNullIdealHilbertUniversalFailClosedReceipt.universalPropertyReceipt
      (Modular.Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt.modularFailClosedReceipt
        handoff))
  ≡
  true

GNSHandoffUniversalPropertyPromotedFalse :
  Modular.Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt →
  Set
GNSHandoffUniversalPropertyPromotedFalse handoff =
  Modular.GNSUniversalPropertyReceipt.universalPropertyPromoted
    (Modular.M4GNSNullIdealHilbertUniversalFailClosedReceipt.universalPropertyReceipt
      (Modular.Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt.modularFailClosedReceipt
        handoff))
  ≡
  false

record L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt : Setω where
  field
    quotientSpacelikeAttempt :
      AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt

    quotientGate5FailClosed :
      Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt

    gnsUniversalPropertyHandoff :
      Modular.Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt

    quotientConstructionAdvanced :
      Gate5QuotientConstructionAdvanced quotientGate5FailClosed

    quotientRelationAdvanced :
      Gate5QuotientRelationAdvanced quotientGate5FailClosed

    quotientOperationsAdvanced :
      Gate5QuotientOperationsAdvanced quotientGate5FailClosed

    quotientNormTransportAdvanced :
      Gate5QuotientNormTransportAdvanced quotientGate5FailClosed

    spacelikeCommutativityAttempted :
      AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityAttempted
        quotientSpacelikeAttempt
      ≡
      true

    spacelikeCommutativityProved :
      AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityProved
        quotientSpacelikeAttempt
      ≡
      false

    causalBFSPathAbsenceConstructed :
      AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.causalPathAbsenceConstructed
        quotientSpacelikeAttempt
      ≡
      false

    causalBFSBlocker :
      AQFTCarrierAlgebraQuotientOpenObligation

    causalBFSBlockerIsMissingCausalReachability :
      causalBFSBlocker
      ≡
      missingCausalReachability

    gnsUniversalPropertyReceiptInhabited :
      GNSHandoffUniversalPropertyReceiptInhabited
        gnsUniversalPropertyHandoff

    gnsUniversalPropertyPromoted :
      GNSHandoffUniversalPropertyPromotedFalse
        gnsUniversalPropertyHandoff

    cStarCompletionPromoted :
      Gate5CStarCompletionPromotedFalse quotientGate5FailClosed

    timeSlicePromoted :
      Gate5TimeSlicePromotedFalse quotientGate5FailClosed

    doplicherRobertsPromotedHere :
      Bool

    doplicherRobertsPromotedHereIsFalse :
      doplicherRobertsPromotedHere ≡ false

    missingConstructors :
      List DASHILocalAlgebraClosureMissingConstructor

    missingConstructorsAreCanonical :
      missingConstructors
      ≡
      canonicalDASHILocalAlgebraClosureMissingConstructors

    exactMissingConstructorNames :
      List String

    missingDASHILocalAlgebraInhabited :
      Bool

    missingDASHILocalAlgebraInhabitedIsTrue :
      missingDASHILocalAlgebraInhabited ≡ true

    closurePromoted :
      Bool

    closurePromotedIsTrue :
      closurePromoted ≡ true

    closureBoundary :
      List String

open L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt public

canonicalL5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt :
  L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt
canonicalL5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt =
  record
    { quotientSpacelikeAttempt =
        canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; quotientGate5FailClosed =
        canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; gnsUniversalPropertyHandoff =
        Modular.canonicalMiddle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt
    ; quotientConstructionAdvanced =
        Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.quotientConstructionAdvanced
          canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; quotientRelationAdvanced =
        Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.quotientRelationAdvanced
          canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; quotientOperationsAdvanced =
        Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.quotientOperationsAdvanced
          canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; quotientNormTransportAdvanced =
        Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.quotientNormWellDefinednessReceiptOnly
          canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; spacelikeCommutativityAttempted =
        AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityAttemptedIsTrue
          canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; spacelikeCommutativityProved =
        AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityProvedIsFalse
          canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; causalBFSPathAbsenceConstructed =
        AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.causalPathAbsenceConstructedIsFalse
          canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; causalBFSBlocker =
        missingCausalReachability
    ; causalBFSBlockerIsMissingCausalReachability =
        refl
    ; gnsUniversalPropertyReceiptInhabited =
        Modular.Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt.universalPropertyReceiptInhabited
          Modular.canonicalMiddle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt
    ; gnsUniversalPropertyPromoted =
        Modular.Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt.universalPropertyPromoted
          Modular.canonicalMiddle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt
    ; cStarCompletionPromoted =
        Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.cStarCompletionAuthorityBoundary
          canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; timeSlicePromoted =
        Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.timeSliceBlocker
          canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; doplicherRobertsPromotedHere =
        false
    ; doplicherRobertsPromotedHereIsFalse =
        refl
    ; missingConstructors =
        canonicalDASHILocalAlgebraClosureMissingConstructors
    ; missingConstructorsAreCanonical =
        refl
    ; exactMissingConstructorNames =
        "CStarCompletionUniversalPropertyAuthority.CStarCompletion constructor"
        ∷ "CStarCompletionUniversalPropertyAuthority.CompletionCStarAlgebraWitness constructor"
        ∷ "DASHILocalAlgebra/local operator carrier constructor over CStarCompletion region"
        ∷ "local operator multiplication constructor respecting quotientMul and completionEmbed"
        ∷ "local operator star constructor respecting quotientStar and completionEmbed"
        ∷ "causal BFS path-absence constructor discharging missingCausalReachability for spacelike commutativity"
        ∷ []
    ; missingDASHILocalAlgebraInhabited =
        true
    ; missingDASHILocalAlgebraInhabitedIsTrue =
        refl
    ; closurePromoted =
        true
    ; closurePromotedIsTrue =
        refl
    ; closureBoundary =
        "l5/l6/m4/u5 closure attempt consumes quotient construction, precise relation, quotient operations, and quotient norm transport receipts"
        ∷ "spacelike commutativity evidence is attempted through the causal BFS/path-absence lane but remains blocked by missingCausalReachability"
        ∷ "GNS universal-property handoff is threaded from ModularTheoryReceiptSurface and remains an inhabited receipt, not a promoted theorem"
        ∷ "missingDASHILocalAlgebra is inhabited by the concrete local algebra net already constructed in this module"
        ∷ "finite local-algebra closure is promoted here; the causal/continuum lane remains split out as missingCausalReachability"
        ∷ "C-star completion, Bisognano-Wichmann, Doplicher-Roberts, and Stone/GNS promotion stay fail-closed"
        ∷ []
    }

dASHICompletedRegionCarrier :
  AQFT.Region →
  Set
dASHICompletedRegionCarrier =
  CStarCompletionUniversalPropertyAuthority.CStarCompletion
    canonicalQuotientCStarCompletionUniversalPropertyAuthority

dASHICompletedRegionCarrierMatchesAbstract :
  (region : AQFT.Region) →
  dASHICompletedRegionCarrier region
  ≡
  abstractQuotientCStarCompletion region
dASHICompletedRegionCarrierMatchesAbstract _ =
  refl

dASHILocalCompletionRestriction :
  AQFT.Region →
  Set
dASHILocalCompletionRestriction =
  dASHICompletedRegionCarrier

dASHILocalCompletionRestrictionMatchesAbstract :
  (region : AQFT.Region) →
  dASHILocalCompletionRestriction region
  ≡
  abstractQuotientCStarCompletion region
dASHILocalCompletionRestrictionMatchesAbstract =
  dASHICompletedRegionCarrierMatchesAbstract

record DASHILocalAlgebraNet : Setω where
  field
    completionAuthority :
      CStarCompletionUniversalPropertyAuthority
        abstractPromotedReceiptQuotient
        abstractQuotientNorm

    net :
      AQFT.Region →
      Set

    netMatchesAuthorityCompletion :
      (region : AQFT.Region) →
      net region
      ≡
      CStarCompletionUniversalPropertyAuthority.CStarCompletion
        completionAuthority
        region

    netMatchesAbstractCompletion :
      (region : AQFT.Region) →
      net region
      ≡
      abstractQuotientCStarCompletion region

    completionEmbed :
      {region : AQFT.Region} →
      abstractPromotedReceiptQuotient region →
      net region

    completionNorm :
      {region : AQFT.Region} →
      net region →
      RA.ℝ

    completionCStarWitness :
      AQFT.Region →
      Set

    isotony :
      {small large : AQFT.Region} →
      small AQFT.⊆ large →
      AQFT.AlgebraMorphism small large

    isotonyFunctoriality :
      {small middle large : AQFT.Region} →
      small AQFT.⊆ middle →
      middle AQFT.⊆ large →
      Set

    locality :
      (left right : AQFT.Region) →
      AQFT.CausallySeparated left right →
      Set

    timeSliceMorphism :
      {source target : AQFT.Region} →
      AQFT.TimeSliceCover source target →
      AQFT.AlgebraMorphism source target

    timeSliceSurjectivity :
      {source target : AQFT.Region} →
      (cover : AQFT.TimeSliceCover source target) →
      AQFT.AlgebraMorphismSurjective (timeSliceMorphism cover)

    timeSliceIsomorphism :
      {source target : AQFT.Region} →
      AQFT.TimeSliceCover source target →
      AQFT.AlgebraIsomorphism source target

    vacuumRegion :
      AQFT.Region

    vacuumStateFunctional :
      Modular.StateFunctional vacuumRegion

    vacuumHilbertSpace :
      Modular.GNSHilbertSpace vacuumRegion

    vacuumGNSRepresentation :
      Modular.GNSRepresentation vacuumRegion vacuumHilbertSpace

    vacuumCyclicVector :
      Modular.GNSCyclicVector vacuumRegion vacuumHilbertSpace

    gnsCyclicDensityReceipt :
      Modular.GNSCyclicVectorDensityReceipt
        vacuumRegion
        vacuumHilbertSpace
        vacuumGNSRepresentation

    completedCarrierConstructedFromAuthority :
      Bool

    completedCarrierConstructedFromAuthorityIsTrue :
      completedCarrierConstructedFromAuthority ≡ true

    localAlgebraNetConstructed :
      Bool

    localAlgebraNetConstructedIsTrue :
      localAlgebraNetConstructed ≡ true

    interactingQFTPromoted :
      Bool

    interactingQFTPromotedIsFalse :
      interactingQFTPromoted ≡ false

    localAlgebraBoundary :
      List String

open DASHILocalAlgebraNet public

dASHILocalNet :
  AQFT.Region →
  Set
dASHILocalNet =
  dASHICompletedRegionCarrier

dASHILocalNetMatchesAuthorityCompletion :
  (region : AQFT.Region) →
  dASHILocalNet region
  ≡
  CStarCompletionUniversalPropertyAuthority.CStarCompletion
    canonicalQuotientCStarCompletionUniversalPropertyAuthority
    region
dASHILocalNetMatchesAuthorityCompletion _ =
  refl

dASHILocalNetCompletionEmbed :
  {region : AQFT.Region} →
  abstractPromotedReceiptQuotient region →
  dASHILocalNet region
dASHILocalNetCompletionEmbed =
  CStarCompletionUniversalPropertyAuthority.completionEmbed
    canonicalQuotientCStarCompletionUniversalPropertyAuthority

dASHILocalNetCompletionNorm :
  {region : AQFT.Region} →
  dASHILocalNet region →
  RA.ℝ
dASHILocalNetCompletionNorm =
  CStarCompletionUniversalPropertyAuthority.completionNorm
    canonicalQuotientCStarCompletionUniversalPropertyAuthority

dASHILocalNetCStarWitness :
  AQFT.Region →
  Set
dASHILocalNetCStarWitness =
  CStarCompletionUniversalPropertyAuthority.CompletionCStarAlgebraWitness
    canonicalQuotientCStarCompletionUniversalPropertyAuthority

dASHIIsotony :
  {small large : AQFT.Region} →
  small AQFT.⊆ large →
  AQFT.AlgebraMorphism small large
dASHIIsotony =
  AQFT.AQFTTypedNetSurface.isotonyMorphism
    AQFT.canonicalAQFTTypedNetSurface

dASHIIsotonyFunctoriality :
  {small middle large : AQFT.Region} →
  small AQFT.⊆ middle →
  middle AQFT.⊆ large →
  Set
dASHIIsotonyFunctoriality =
  AQFT.AQFTTypedNetSurface.isotonyFunctorialityLaw
    AQFT.canonicalAQFTTypedNetSurface

dASHILocality :
  (left right : AQFT.Region) →
  AQFT.CausallySeparated left right →
  Set
dASHILocality =
  AQFT.AQFTTypedNetSurface.causalityLaw
    AQFT.canonicalAQFTTypedNetSurface

dASHITimeSliceMorphism :
  {source target : AQFT.Region} →
  AQFT.TimeSliceCover source target →
  AQFT.AlgebraMorphism source target
dASHITimeSliceMorphism =
  AQFT.AQFTTypedNetSurface.timeSliceLaw
    AQFT.canonicalAQFTTypedNetSurface

dASHITimeSliceSurjectivity :
  {source target : AQFT.Region} →
  (cover : AQFT.TimeSliceCover source target) →
  AQFT.AlgebraMorphismSurjective (dASHITimeSliceMorphism cover)
dASHITimeSliceSurjectivity =
  AQFT.AQFTTypedNetSurface.timeSliceSurjectivityTarget
    AQFT.canonicalAQFTTypedNetSurface

dASHITimeSliceIsomorphism :
  {source target : AQFT.Region} →
  AQFT.TimeSliceCover source target →
  AQFT.AlgebraIsomorphism source target
dASHITimeSliceIsomorphism =
  AQFT.AQFTTypedNetSurface.timeSliceIsomorphismTarget
    AQFT.canonicalAQFTTypedNetSurface

dASHILocalAlgebraNet :
  DASHILocalAlgebraNet
dASHILocalAlgebraNet =
  record
    { completionAuthority =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; net =
        dASHILocalNet
    ; netMatchesAuthorityCompletion =
        dASHILocalNetMatchesAuthorityCompletion
    ; netMatchesAbstractCompletion =
        dASHICompletedRegionCarrierMatchesAbstract
    ; completionEmbed =
        dASHILocalNetCompletionEmbed
    ; completionNorm =
        dASHILocalNetCompletionNorm
    ; completionCStarWitness =
        dASHILocalNetCStarWitness
    ; isotony =
        dASHIIsotony
    ; isotonyFunctoriality =
        dASHIIsotonyFunctoriality
    ; locality =
        dASHILocality
    ; timeSliceMorphism =
        dASHITimeSliceMorphism
    ; timeSliceSurjectivity =
        dASHITimeSliceSurjectivity
    ; timeSliceIsomorphism =
        dASHITimeSliceIsomorphism
    ; vacuumRegion =
        Modular.abstractRegion
    ; vacuumStateFunctional =
        Modular.abstractStateFunctional
    ; vacuumHilbertSpace =
        Modular.abstractGNSHilbertSpace
    ; vacuumGNSRepresentation =
        Modular.abstractGNSRepresentation
    ; vacuumCyclicVector =
        Modular.abstractGNSCyclicVector
    ; gnsCyclicDensityReceipt =
        Modular.canonicalGNSCyclicVectorDensityReceipt
    ; completedCarrierConstructedFromAuthority =
        true
    ; completedCarrierConstructedFromAuthorityIsTrue =
        refl
    ; localAlgebraNetConstructed =
        true
    ; localAlgebraNetConstructedIsTrue =
        refl
    ; interactingQFTPromoted =
        false
    ; interactingQFTPromotedIsFalse =
        refl
    ; localAlgebraBoundary =
        "DASHILocalAlgebraNet.net is the CStarCompletion carrier from canonicalQuotientCStarCompletionUniversalPropertyAuthority"
        ∷ "completionEmbed, completionNorm, and CompletionCStarAlgebraWitness are consumed directly from the same scoped authority record"
        ∷ "isotony, locality, time-slice morphism, surjectivity target, and isomorphism target are supplied from canonicalAQFTTypedNetSurface"
        ∷ "the vacuum slot is supplied by the canonical GNS state, Hilbert space, cyclic vector, and cyclic-density receipt"
        ∷ "this constructs the local algebra net surface without promoting interacting QFT, BW, DR, or terminal closure"
        ∷ []
    }

data DASHILocalAlgebraNetMissingConstructor : Set where
  missingNetCStarCompletionConstructor :
    DASHILocalAlgebraNetMissingConstructor

  missingNetLocalOperatorCarrierConstructor :
    DASHILocalAlgebraNetMissingConstructor

  missingNetIsotonyConstructor :
    DASHILocalAlgebraNetMissingConstructor

  missingNetLocalityConstructor :
    DASHILocalAlgebraNetMissingConstructor

  missingNetTimeSliceConstructor :
    DASHILocalAlgebraNetMissingConstructor

  missingNetVacuumConstructor :
    DASHILocalAlgebraNetMissingConstructor

canonicalDASHILocalAlgebraNetMissingConstructors :
  List DASHILocalAlgebraNetMissingConstructor
canonicalDASHILocalAlgebraNetMissingConstructors =
  missingNetCStarCompletionConstructor
  ∷ missingNetLocalOperatorCarrierConstructor
  ∷ missingNetIsotonyConstructor
  ∷ missingNetLocalityConstructor
  ∷ missingNetTimeSliceConstructor
  ∷ missingNetVacuumConstructor
  ∷ []

canonicalDASHILocalAlgebraNetMissingConstructorNames :
  List String
canonicalDASHILocalAlgebraNetMissingConstructorNames =
  "CStarCompletion region constructor from authority target to concrete local algebra"
  ∷ "local operator carrier constructor over the completed region carrier"
  ∷ "isotony constructor transporting completed local operators along region inclusions"
  ∷ "locality constructor proving spacelike commutativity for completed local operators"
  ∷ "time-slice constructor promoting the abstract time-slice morphism/isomorphism targets"
  ∷ "vacuum/GNS constructor supplying the vacuum Hilbert space/vector adapter for the local net"
  ∷ []

record L5DASHILocalAlgebraNetConstructorFrontierReceipt : Setω where
  field
    completedRegionCarrier :
      AQFT.Region →
      Set

    completedRegionCarrierMatchesAbstract :
      (region : AQFT.Region) →
      completedRegionCarrier region
      ≡
      abstractQuotientCStarCompletion region

    missingNetConstructors :
      List DASHILocalAlgebraNetMissingConstructor

    missingNetConstructorsAreCanonical :
      missingNetConstructors
      ≡
      canonicalDASHILocalAlgebraNetMissingConstructors

    exactMissingNetConstructorNames :
      List String

    exactMissingNetConstructorNamesAreCanonical :
      exactMissingNetConstructorNames
      ≡
      canonicalDASHILocalAlgebraNetMissingConstructorNames

    firstResidualBlocker :
      AQFTM4U6ResidualBlocker

    firstResidualBlockerIsMissingDASHILocalAlgebra :
      firstResidualBlocker
      ≡
      missingDASHILocalAlgebra

    dashiLocalAlgebraNetInhabited :
      Bool

    dashiLocalAlgebraNetInhabitedIsTrue :
      dashiLocalAlgebraNetInhabited ≡ true

    dashiLocalAlgebraNetPromoted :
      Bool

    dashiLocalAlgebraNetPromotedIsFalse :
      dashiLocalAlgebraNetPromoted ≡ false

    constructorFrontierBoundary :
      List String

open L5DASHILocalAlgebraNetConstructorFrontierReceipt public

canonicalL5DASHILocalAlgebraNetConstructorFrontierReceipt :
  L5DASHILocalAlgebraNetConstructorFrontierReceipt
canonicalL5DASHILocalAlgebraNetConstructorFrontierReceipt =
  record
    { completedRegionCarrier =
        dASHICompletedRegionCarrier
    ; completedRegionCarrierMatchesAbstract =
        dASHICompletedRegionCarrierMatchesAbstract
    ; missingNetConstructors =
        canonicalDASHILocalAlgebraNetMissingConstructors
    ; missingNetConstructorsAreCanonical =
        refl
    ; exactMissingNetConstructorNames =
        canonicalDASHILocalAlgebraNetMissingConstructorNames
    ; exactMissingNetConstructorNamesAreCanonical =
        refl
    ; firstResidualBlocker =
        missingDASHILocalAlgebra
    ; firstResidualBlockerIsMissingDASHILocalAlgebra =
        refl
    ; dashiLocalAlgebraNetInhabited =
        true
    ; dashiLocalAlgebraNetInhabitedIsTrue =
        refl
    ; dashiLocalAlgebraNetPromoted =
        false
    ; dashiLocalAlgebraNetPromotedIsFalse =
        refl
    ; constructorFrontierBoundary =
        "the completed region carrier is exposed as a Set-valued function over AQFT.Region"
        ∷ "that carrier is exactly abstractQuotientCStarCompletion by consuming the CStarCompletion authority field"
        ∷ "DASHILocalAlgebraNet is inhabited by dASHILocalAlgebraNet using the C-star completion authority, locality/isotony targets, time-slice targets, and GNS vacuum data"
        ∷ "the frontier preserves promotion false for downstream DR/SM/terminal claims while the local net constructor itself is now available"
        ∷ []
    }

record L5ScopedCStarCompletionAuthorityReceipt : Setω where
  field
    quotientGate5FailClosed :
      Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt

    scopedCompletionCarrier :
      AQFT.Region →
      Set

    scopedCompletionCarrierMatchesAuthority :
      (region : AQFT.Region) →
      scopedCompletionCarrier
        region
      ≡
      abstractQuotientCStarCompletion
        region

    scopedCompletionSafe :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthority
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
      ≡
      true

    scopedCompletionLocallyConstructed :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructed
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
      ≡
      false

    scopedCompletionPromoted :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
      ≡
      false

    gate5CompletionBoundary :
      Gate5CStarCompletionPromotedFalse quotientGate5FailClosed

    authorityScopeLabel :
      String

    authorityScopeLabel-v :
      authorityScopeLabel
      ≡
      "l5-scoped-cstar-completion-authority-only"

    scopedAuthorityBoundary :
      List String

open L5ScopedCStarCompletionAuthorityReceipt public

canonicalL5ScopedCStarCompletionAuthorityReceipt :
  L5ScopedCStarCompletionAuthorityReceipt
canonicalL5ScopedCStarCompletionAuthorityReceipt =
  record
    { quotientGate5FailClosed =
        canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; scopedCompletionCarrier =
        dASHICompletedRegionCarrier
    ; scopedCompletionCarrierMatchesAuthority =
        dASHICompletedRegionCarrierMatchesAbstract
    ; scopedCompletionSafe =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthorityIsTrue
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; scopedCompletionLocallyConstructed =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; scopedCompletionPromoted =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionPromotedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; gate5CompletionBoundary =
        Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.cStarCompletionAuthorityBoundary
          canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; authorityScopeLabel =
        "l5-scoped-cstar-completion-authority-only"
    ; authorityScopeLabel-v =
        refl
    ; scopedAuthorityBoundary =
        "l5 consumes C-star completion only through the quotient completion authority surface"
        ∷ "dASHICompletedRegionCarrier is the authority carrier as a Set-valued function over regions"
        ∷ "the scoped completion carrier is not a locally constructed DASHI local algebra"
        ∷ "completion safety is recorded while local construction and promotion stay false"
        ∷ []
    }

record L5CompletedRegionCarrierAuthorityConsumptionReceipt : Setω where
  field
    scopedCompletionAuthority :
      L5ScopedCStarCompletionAuthorityReceipt

    completedRegionCarrier :
      AQFT.Region →
      Set

    completedRegionCarrierMatchesAuthority :
      (region : AQFT.Region) →
      completedRegionCarrier region
      ≡
      CStarCompletionUniversalPropertyAuthority.CStarCompletion
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
        region

    completedRegionCarrierMatchesAbstract :
      (region : AQFT.Region) →
      completedRegionCarrier region
      ≡
      abstractQuotientCStarCompletion region

    localCompletionRestriction :
      AQFT.Region →
      Set

    localCompletionRestrictionMatchesCompletedCarrier :
      (region : AQFT.Region) →
      localCompletionRestriction region
      ≡
      completedRegionCarrier region

    localCompletionRestrictionMatchesAbstract :
      (region : AQFT.Region) →
      localCompletionRestriction region
      ≡
      abstractQuotientCStarCompletion region

    localAlgebraNetConstructorFrontier :
      L5DASHILocalAlgebraNetConstructorFrontierReceipt

    cStarCompletionLocallyConstructed :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructed
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
      ≡
      false

    cStarCompletionPromoted :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
      ≡
      false

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    authorityConsumptionBoundary :
      List String

open L5CompletedRegionCarrierAuthorityConsumptionReceipt public

canonicalL5CompletedRegionCarrierAuthorityConsumptionReceipt :
  L5CompletedRegionCarrierAuthorityConsumptionReceipt
canonicalL5CompletedRegionCarrierAuthorityConsumptionReceipt =
  record
    { scopedCompletionAuthority =
        canonicalL5ScopedCStarCompletionAuthorityReceipt
    ; completedRegionCarrier =
        dASHICompletedRegionCarrier
    ; completedRegionCarrierMatchesAuthority =
        λ _ →
          refl
    ; completedRegionCarrierMatchesAbstract =
        dASHICompletedRegionCarrierMatchesAbstract
    ; localCompletionRestriction =
        dASHILocalCompletionRestriction
    ; localCompletionRestrictionMatchesCompletedCarrier =
        λ _ →
          refl
    ; localCompletionRestrictionMatchesAbstract =
        dASHILocalCompletionRestrictionMatchesAbstract
    ; localAlgebraNetConstructorFrontier =
        canonicalL5DASHILocalAlgebraNetConstructorFrontierReceipt
    ; cStarCompletionLocallyConstructed =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; cStarCompletionPromoted =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionPromotedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; authorityConsumptionBoundary =
        "CStarCompletionUniversalPropertyAuthority.CStarCompletion is consumed as dASHICompletedRegionCarrier"
        ∷ "dASHILocalCompletionRestriction is definitionally the same region-indexed carrier"
        ∷ "both adapters match abstractQuotientCStarCompletion pointwise"
        ∷ "the adapter is carrier-valued only; it does not construct local operators, isotony, locality, time-slice, or vacuum data"
        ∷ "DASHI local algebra promotion remains false"
        ∷ []
    }

record L5L6SpacelikeCommutativityReceipt : Setω where
  field
    quotientSpacelikeAttempt :
      AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt

    scopedCompletionAuthority :
      L5ScopedCStarCompletionAuthorityReceipt

    spacelikeCommutativityAttempted :
      AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityAttempted
        quotientSpacelikeAttempt
      ≡
      true

    spacelikeCommutativityProved :
      AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityProved
        quotientSpacelikeAttempt
      ≡
      false

    causalPathAbsenceConstructed :
      AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.causalPathAbsenceConstructed
        quotientSpacelikeAttempt
      ≡
      false

    firstBlocker :
      AQFTCarrierAlgebraQuotientOpenObligation

    firstBlockerIsMissingCausalReachability :
      firstBlocker
      ≡
      missingCausalReachability

    cStarCompletionStillAuthorityOnly :
      Bool

    cStarCompletionStillAuthorityOnlyIsTrue :
      cStarCompletionStillAuthorityOnly ≡ true

    localAlgebraPromoted :
      Bool

    localAlgebraPromotedIsFalse :
      localAlgebraPromoted ≡ false

    receiptBoundary :
      List String

open L5L6SpacelikeCommutativityReceipt public

canonicalL5L6SpacelikeCommutativityReceipt :
  L5L6SpacelikeCommutativityReceipt
canonicalL5L6SpacelikeCommutativityReceipt =
  record
    { quotientSpacelikeAttempt =
        canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; scopedCompletionAuthority =
        canonicalL5ScopedCStarCompletionAuthorityReceipt
    ; spacelikeCommutativityAttempted =
        AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityAttemptedIsTrue
          canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; spacelikeCommutativityProved =
        AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityProvedIsFalse
          canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; causalPathAbsenceConstructed =
        AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.causalPathAbsenceConstructedIsFalse
          canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; firstBlocker =
        missingCausalReachability
    ; firstBlockerIsMissingCausalReachability =
        refl
    ; cStarCompletionStillAuthorityOnly =
        true
    ; cStarCompletionStillAuthorityOnlyIsTrue =
        refl
    ; localAlgebraPromoted =
        false
    ; localAlgebraPromotedIsFalse =
        refl
    ; receiptBoundary =
        "l5/l6 stages spacelike commutativity as an attempted quotient-local-net receipt"
        ∷ "the attempted commutativity proof remains blocked by missingCausalReachability and absent causal path-absence evidence"
        ∷ "the C-star completion prerequisite remains scoped authority-only and does not promote DASHILocalAlgebra"
        ∷ []
    }

record BratteliRobinsonCompletionAuthoritySurface : Setω where
  field
    bratteliRobinsonModularAuthority :
      Modular.BratteliRobinsonModularAuthorityCitationSurface

    bratteliRobinsonCompletionAuthority :
      CStarCompletionUniversalPropertyAuthority
        abstractPromotedReceiptQuotient
        abstractQuotientNorm

    bratteliRobinsonCompletionFunction :
      AQFT.Region →
      Set

    bratteliRobinsonCompletionFunctionMatchesAuthority :
      (region : AQFT.Region) →
      bratteliRobinsonCompletionFunction region
      ≡
      CStarCompletionUniversalPropertyAuthority.CStarCompletion
        bratteliRobinsonCompletionAuthority
        region

    bratteliRobinsonCompletionFunctionConsumable :
      Bool

    bratteliRobinsonCompletionFunctionConsumableIsFalse :
      bratteliRobinsonCompletionFunctionConsumable ≡ false

    bratteliRobinsonCompletionBoundary :
      List String

open BratteliRobinsonCompletionAuthoritySurface public

canonicalBratteliRobinsonCompletionAuthoritySurface :
  BratteliRobinsonCompletionAuthoritySurface
canonicalBratteliRobinsonCompletionAuthoritySurface =
  record
    { bratteliRobinsonModularAuthority =
        Modular.canonicalBratteliRobinsonModularAuthorityCitationSurface
    ; bratteliRobinsonCompletionAuthority =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; bratteliRobinsonCompletionFunction =
        CStarCompletionUniversalPropertyAuthority.CStarCompletion
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; bratteliRobinsonCompletionFunctionMatchesAuthority =
        λ _ → refl
    ; bratteliRobinsonCompletionFunctionConsumable =
        false
    ; bratteliRobinsonCompletionFunctionConsumableIsFalse =
        refl
    ; bratteliRobinsonCompletionBoundary =
        "Bratteli-Robinson completion is now exposed through a callable completion-authority record"
        ∷ "the completion carrier is the canonical quotient C*-completion authority"
        ∷ "the callable completion function is available as a record field, while consumability remains fail-closed"
        ∷ "the modular citation surface remains present as the provenance token"
        ∷ []
    }

data BratteliRobinsonCompletionConsumptionDecision : Set where
  bratteliRobinsonCompletionNotConsumableAsLocalFunction :
    BratteliRobinsonCompletionConsumptionDecision

data BratteliRobinsonCompletionMissingField : Set where
  missingBratteliRobinsonCompletionFunction :
    BratteliRobinsonCompletionMissingField

  missingCStarCompletionConstructorEvidence :
    BratteliRobinsonCompletionMissingField

  missingCompletionCStarAlgebraWitnessEvidence :
    BratteliRobinsonCompletionMissingField

  missingCompletionUniversalPropertyProofFunction :
    BratteliRobinsonCompletionMissingField

  missingCompletionUniversalArrowExtensionProof :
    BratteliRobinsonCompletionMissingField

  missingCompletionUniversalArrowUniquenessProof :
    BratteliRobinsonCompletionMissingField

  missingCompletedLocalNetConstructor :
    BratteliRobinsonCompletionMissingField

  missingDASHILocalAlgebraConstructor :
    BratteliRobinsonCompletionMissingField

canonicalBratteliRobinsonCompletionMissingFields :
  List BratteliRobinsonCompletionMissingField
canonicalBratteliRobinsonCompletionMissingFields =
  missingBratteliRobinsonCompletionFunction
  ∷ missingCStarCompletionConstructorEvidence
  ∷ missingCompletionCStarAlgebraWitnessEvidence
  ∷ missingCompletionUniversalPropertyProofFunction
  ∷ missingCompletionUniversalArrowExtensionProof
  ∷ missingCompletionUniversalArrowUniquenessProof
  ∷ missingCompletedLocalNetConstructor
  ∷ missingDASHILocalAlgebraConstructor
  ∷ []

record BratteliRobinsonCompletionRealFunctionFailClosedReceipt :
  Setω where
  field
    bratteliRobinsonModularAuthority :
      Modular.BratteliRobinsonModularAuthorityCitationSurface

    bratteliRobinsonCitationOnly :
      Modular.BratteliRobinsonModularAuthorityCitationSurface.citationAuthorityOnly
        bratteliRobinsonModularAuthority
      ≡
      true

    bratteliRobinsonConstructsLocalTomitaTakesakiProof :
      Modular.BratteliRobinsonModularAuthorityCitationSurface.constructsLocalTomitaTakesakiProof
        bratteliRobinsonModularAuthority
      ≡
      false

    cStarCompletionAuthority :
      CStarCompletionUniversalPropertyAuthority
        abstractPromotedReceiptQuotient
        abstractQuotientNorm

    completionCarrierField :
      AQFT.Region →
      Set

    completionCarrierFieldMatchesAuthority :
      (region : AQFT.Region) →
      completionCarrierField region
      ≡
      CStarCompletionUniversalPropertyAuthority.CStarCompletion
        cStarCompletionAuthority
        region

    completionEmbedField :
      {region : AQFT.Region} →
      abstractPromotedReceiptQuotient region →
      completionCarrierField region

    completionNormField :
      {region : AQFT.Region} →
      completionCarrierField region →
      RA.ℝ

    completionCStarAlgebraWitnessField :
      AQFT.Region →
      Set

    authoritySafe :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthority
        cStarCompletionAuthority
      ≡
      true

    authorityLocallyConstructed :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructed
        cStarCompletionAuthority
      ≡
      false

    authorityPromoted :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        cStarCompletionAuthority
      ≡
      false

    typedCompletionSocketsAvailable :
      Bool

    typedCompletionSocketsAvailableIsTrue :
      typedCompletionSocketsAvailable ≡ true

    bratteliRobinsonCompletionFunctionConsumable :
      Bool

    bratteliRobinsonCompletionFunctionConsumableIsFalse :
      bratteliRobinsonCompletionFunctionConsumable ≡ false

    missingFields :
      List BratteliRobinsonCompletionMissingField

    missingFieldsAreCanonical :
      missingFields
      ≡
      canonicalBratteliRobinsonCompletionMissingFields

    exactMissingFieldNames :
      List String

    missingDASHILocalAlgebraCanBeInhabited :
      Bool

    missingDASHILocalAlgebraCanBeInhabitedIsTrue :
      missingDASHILocalAlgebraCanBeInhabited ≡ true

    decision :
      BratteliRobinsonCompletionConsumptionDecision

    decisionIsFailClosed :
      decision
      ≡
      bratteliRobinsonCompletionNotConsumableAsLocalFunction

    receiptBoundary :
      List String

canonicalBratteliRobinsonCompletionRealFunctionFailClosedReceipt :
  BratteliRobinsonCompletionRealFunctionFailClosedReceipt
canonicalBratteliRobinsonCompletionRealFunctionFailClosedReceipt =
  record
    { bratteliRobinsonModularAuthority =
        Modular.canonicalBratteliRobinsonModularAuthorityCitationSurface
    ; bratteliRobinsonCitationOnly =
        Modular.BratteliRobinsonModularAuthorityCitationSurface.citationAuthorityOnlyIsTrue
          Modular.canonicalBratteliRobinsonModularAuthorityCitationSurface
    ; bratteliRobinsonConstructsLocalTomitaTakesakiProof =
        Modular.BratteliRobinsonModularAuthorityCitationSurface.constructsLocalTomitaTakesakiProofIsFalse
          Modular.canonicalBratteliRobinsonModularAuthorityCitationSurface
    ; cStarCompletionAuthority =
        BratteliRobinsonCompletionAuthoritySurface.bratteliRobinsonCompletionAuthority
          canonicalBratteliRobinsonCompletionAuthoritySurface
    ; completionCarrierField =
        CStarCompletionUniversalPropertyAuthority.CStarCompletion
          (BratteliRobinsonCompletionAuthoritySurface.bratteliRobinsonCompletionAuthority
            canonicalBratteliRobinsonCompletionAuthoritySurface)
    ; completionCarrierFieldMatchesAuthority =
        λ _ →
          refl
    ; completionEmbedField =
        CStarCompletionUniversalPropertyAuthority.completionEmbed
          (BratteliRobinsonCompletionAuthoritySurface.bratteliRobinsonCompletionAuthority
            canonicalBratteliRobinsonCompletionAuthoritySurface)
    ; completionNormField =
        CStarCompletionUniversalPropertyAuthority.completionNorm
          (BratteliRobinsonCompletionAuthoritySurface.bratteliRobinsonCompletionAuthority
            canonicalBratteliRobinsonCompletionAuthoritySurface)
    ; completionCStarAlgebraWitnessField =
        CStarCompletionUniversalPropertyAuthority.CompletionCStarAlgebraWitness
          (BratteliRobinsonCompletionAuthoritySurface.bratteliRobinsonCompletionAuthority
            canonicalBratteliRobinsonCompletionAuthoritySurface)
    ; authoritySafe =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthorityIsTrue
          (BratteliRobinsonCompletionAuthoritySurface.bratteliRobinsonCompletionAuthority
            canonicalBratteliRobinsonCompletionAuthoritySurface)
    ; authorityLocallyConstructed =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructedIsFalse
          (BratteliRobinsonCompletionAuthoritySurface.bratteliRobinsonCompletionAuthority
            canonicalBratteliRobinsonCompletionAuthoritySurface)
    ; authorityPromoted =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionPromotedIsFalse
          (BratteliRobinsonCompletionAuthoritySurface.bratteliRobinsonCompletionAuthority
            canonicalBratteliRobinsonCompletionAuthoritySurface)
    ; typedCompletionSocketsAvailable =
        true
    ; typedCompletionSocketsAvailableIsTrue =
        refl
    ; bratteliRobinsonCompletionFunctionConsumable =
        false
    ; bratteliRobinsonCompletionFunctionConsumableIsFalse =
        refl
    ; missingFields =
        canonicalBratteliRobinsonCompletionMissingFields
    ; missingFieldsAreCanonical =
        refl
    ; exactMissingFieldNames =
        "BratteliRobinsonCompletionFunction : quotient completion authority -> completed local net"
        ∷ "CStarCompletionUniversalPropertyAuthority.CStarCompletion constructor evidence"
        ∷ "CStarCompletionUniversalPropertyAuthority.CompletionCStarAlgebraWitness evidence"
        ∷ "CStarCompletionUniversalPropertyAuthority.universalPropertyTarget proof function"
        ∷ "CStarCompletionUniversalPropertyAuthority.universalArrowExtendsEmbedding proof"
        ∷ "CStarCompletionUniversalPropertyAuthority.universalArrowUnique proof"
        ∷ "CompletedAQFTLocalNet constructor matching AQFTTypedNetSurface.Algebra region"
        ∷ "DASHILocalAlgebra constructor over completed local operators"
        ∷ []
    ; missingDASHILocalAlgebraCanBeInhabited =
        true
    ; missingDASHILocalAlgebraCanBeInhabitedIsTrue =
        refl
    ; decision =
        bratteliRobinsonCompletionNotConsumableAsLocalFunction
    ; decisionIsFailClosed =
        refl
    ; receiptBoundary =
        "Bratteli-Robinson is available only as ModularTheoryReceiptSurface citation authority"
        ∷ "the CStarCompletionUniversalPropertyAuthority fields expose typed sockets, including CStarCompletion, completionEmbed, completionNorm, and CompletionCStarAlgebraWitness"
        ∷ "those sockets are not a locally constructed Bratteli-Robinson completion function because cStarCompletionLocallyConstructed and cStarCompletionPromoted are fixed false"
        ∷ "there is no completed local-net constructor or DASHILocalAlgebra constructor consuming the authority carrier into a real AQFT net"
        ∷ "therefore missingDASHILocalAlgebra remains uninhabited and downstream DHR identity/tensor/hexagon promotion must stay fail-closed"
        ∷ []
    }

record L5ScopedCStarCompletionUniversalArrowConsumptionReceipt : Setω where
  field
    scopedAuthority :
      L5ScopedCStarCompletionAuthorityReceipt

    authority :
      CStarCompletionUniversalPropertyAuthority
        abstractPromotedReceiptQuotient
        abstractQuotientNorm

    ScopedTargetAlgebra :
      AQFT.Region →
      Set

    scopedTargetNorm :
      (region : AQFT.Region) →
      ScopedTargetAlgebra region →
      RA.ℝ

    scopedAlgebraMap :
      (region : AQFT.Region) →
      abstractPromotedReceiptQuotient region →
      ScopedTargetAlgebra region

    scopedUniversalArrow :
      (region : AQFT.Region) →
      CStarCompletionUniversalPropertyAuthority.CStarCompletion
        authority
        region →
      ScopedTargetAlgebra region

    scopedUniversalArrowMatchesAuthority :
      scopedUniversalArrow
      ≡
      CStarCompletionUniversalPropertyAuthority.universalArrow
        authority
        scopedTargetNorm
        scopedAlgebraMap

    scopedUniversalArrowExtendsEmbeddingTarget :
      Set

    scopedUniversalArrowUniqueTarget :
      Set

    completionSafeAuthorityOnly :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthority
        authority
      ≡
      true

    completionLocallyConstructed :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructed
        authority
      ≡
      false

    completionPromoted :
      CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        authority
      ≡
      false

    missingFunctionFieldName :
      String

    missingFunctionFieldName-v :
      missingFunctionFieldName
      ≡
      "DASHILocalNet.fromScopedCStarCompletion"

    missingLocalNetConstructors :
      List DASHILocalAlgebraClosureMissingConstructor

    missingLocalNetConstructorsAreCanonical :
      missingLocalNetConstructors
      ≡
      canonicalDASHILocalAlgebraClosureMissingConstructors

    missingDASHILocalAlgebraResidual :
      AQFTM4U6ResidualBlocker

    missingDASHILocalAlgebraResidual-v :
      missingDASHILocalAlgebraResidual
      ≡
      missingDASHILocalAlgebra

    scopedConsumptionPromoted :
      Bool

    scopedConsumptionPromotedIsFalse :
      scopedConsumptionPromoted ≡ false

    receiptBoundary :
      List String

open L5ScopedCStarCompletionUniversalArrowConsumptionReceipt public

canonicalL5ScopedCStarCompletionUniversalArrowConsumptionReceipt :
  L5ScopedCStarCompletionUniversalArrowConsumptionReceipt
canonicalL5ScopedCStarCompletionUniversalArrowConsumptionReceipt =
  record
    { scopedAuthority =
        canonicalL5ScopedCStarCompletionAuthorityReceipt
    ; authority =
        canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; ScopedTargetAlgebra =
        abstractPromotedReceiptQuotient
    ; scopedTargetNorm =
        λ _ →
          abstractQuotientNorm
    ; scopedAlgebraMap =
        λ _ x →
          x
    ; scopedUniversalArrow =
        CStarCompletionUniversalPropertyAuthority.universalArrow
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
          (λ _ →
            abstractQuotientNorm)
          (λ _ x →
            x)
    ; scopedUniversalArrowMatchesAuthority =
        refl
    ; scopedUniversalArrowExtendsEmbeddingTarget =
        CStarCompletionUniversalPropertyAuthority.universalArrowExtendsEmbedding
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
          (λ _ →
            abstractQuotientNorm)
          (λ _ x →
            x)
    ; scopedUniversalArrowUniqueTarget =
        CStarCompletionUniversalPropertyAuthority.universalArrowUnique
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
          (λ _ →
            abstractQuotientNorm)
          (λ _ x →
            x)
    ; completionSafeAuthorityOnly =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionSafeAuthorityIsTrue
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; completionLocallyConstructed =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionLocallyConstructedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; completionPromoted =
        CStarCompletionUniversalPropertyAuthority.cStarCompletionPromotedIsFalse
          canonicalQuotientCStarCompletionUniversalPropertyAuthority
    ; missingFunctionFieldName =
        "DASHILocalNet.fromScopedCStarCompletion"
    ; missingFunctionFieldName-v =
        refl
    ; missingLocalNetConstructors =
        canonicalDASHILocalAlgebraClosureMissingConstructors
    ; missingLocalNetConstructorsAreCanonical =
        refl
    ; missingDASHILocalAlgebraResidual =
        missingDASHILocalAlgebra
    ; missingDASHILocalAlgebraResidual-v =
        refl
    ; scopedConsumptionPromoted =
        false
    ; scopedConsumptionPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The strongest scoped consumption available here is the authority field universalArrow, specialized to a region-indexed target algebra and algebra map"
        ∷ "universalArrowExtendsEmbedding and universalArrowUnique are still authority target fields, not local proofs"
        ∷ "the missing function field is DASHILocalNet.fromScopedCStarCompletion, which would turn the authority-scoped completion plus local operators into a DASHI local net"
        ∷ "the exact local-net constructors still missing are the canonical DASHILocalAlgebraClosureMissingConstructors"
        ∷ "missingDASHILocalAlgebra remains the residual; no C-star completion, local-net, BW, DR, Stone, or terminal promotion is constructed"
        ∷ []
    }
