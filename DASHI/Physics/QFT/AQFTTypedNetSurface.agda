module DASHI.Physics.QFT.AQFTTypedNetSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Typed AQFT net surface.
--
-- This module gives the bool/string AQFT receipts a small typed socket for a
-- Haag-Kastler-shaped net.  It keeps all algebraic and categorical content
-- abstract: local algebras, morphisms, causal separation, time-slice coverage,
-- and descent are predicates or postulated carriers.
--
-- It does not construct a C*-algebra, Hilbert representation, vacuum state,
-- Born-rule adapter, interacting QFT, or GR/QFT promotion receipt.

postulate
  Region :
    Set

  LocalAlgebra :
    Region →
    Set

  AlgebraMorphism :
    Region →
    Region →
    Set

  AlgebraIsomorphism :
    Region →
    Region →
    Set

  AlgebraMorphismSurjective :
    {source target : Region} →
    AlgebraMorphism source target →
    Set

  _⊆_ :
    Region →
    Region →
    Set

  CausallySeparated :
    Region →
    Region →
    Set

  TimeSliceCover :
    Region →
    Region →
    Set

  DomainOfDependence :
    Region →
    Region →
    Set

  DescentCover :
    Region →
    Set

  DescentObject :
    Region →
    Set

data AQFTFoundationalSocket : Set where
  regionCarrierSocket :
    AQFTFoundationalSocket

  localAlgebraFamilySocket :
    AQFTFoundationalSocket

  algebraMorphismFamilySocket :
    AQFTFoundationalSocket

  algebraIsomorphismFamilySocket :
    AQFTFoundationalSocket

  algebraMorphismSurjectivitySocket :
    AQFTFoundationalSocket

  regionInclusionRelationSocket :
    AQFTFoundationalSocket

  causalSeparationRelationSocket :
    AQFTFoundationalSocket

  timeSliceCoverRelationSocket :
    AQFTFoundationalSocket

  domainOfDependenceRelationSocket :
    AQFTFoundationalSocket

  descentCoverFamilySocket :
    AQFTFoundationalSocket

  descentObjectFamilySocket :
    AQFTFoundationalSocket

canonicalAQFTFoundationalSockets :
  List AQFTFoundationalSocket
canonicalAQFTFoundationalSockets =
  regionCarrierSocket
  ∷ localAlgebraFamilySocket
  ∷ algebraMorphismFamilySocket
  ∷ algebraIsomorphismFamilySocket
  ∷ algebraMorphismSurjectivitySocket
  ∷ regionInclusionRelationSocket
  ∷ causalSeparationRelationSocket
  ∷ timeSliceCoverRelationSocket
  ∷ domainOfDependenceRelationSocket
  ∷ descentCoverFamilySocket
  ∷ descentObjectFamilySocket
  ∷ []

data AQFTRootPostulateBoundaryBlocker : Set where
  missingConcreteRegionCarrier :
    AQFTRootPostulateBoundaryBlocker

  missingConcreteLocalAlgebraFamily :
    AQFTRootPostulateBoundaryBlocker

  missingConcreteAlgebraMorphismFamily :
    AQFTRootPostulateBoundaryBlocker

  missingConcreteAlgebraIsomorphismFamily :
    AQFTRootPostulateBoundaryBlocker

  missingConcreteInclusionRelation :
    AQFTRootPostulateBoundaryBlocker

  missingConcreteCausalSeparationRelation :
    AQFTRootPostulateBoundaryBlocker

  missingConcreteTimeSliceAndDomainOfDependenceRelations :
    AQFTRootPostulateBoundaryBlocker

  missingConcreteDescentCoverAndObjectFamilies :
    AQFTRootPostulateBoundaryBlocker

  missingHaagKastlerLawDerivationsFromConcreteModel :
    AQFTRootPostulateBoundaryBlocker

  missingInteractingQFTPromotionAuthority :
    AQFTRootPostulateBoundaryBlocker

canonicalAQFTRootPostulateBoundaryBlockers :
  List AQFTRootPostulateBoundaryBlocker
canonicalAQFTRootPostulateBoundaryBlockers =
  missingConcreteRegionCarrier
  ∷ missingConcreteLocalAlgebraFamily
  ∷ missingConcreteAlgebraMorphismFamily
  ∷ missingConcreteAlgebraIsomorphismFamily
  ∷ missingConcreteInclusionRelation
  ∷ missingConcreteCausalSeparationRelation
  ∷ missingConcreteTimeSliceAndDomainOfDependenceRelations
  ∷ missingConcreteDescentCoverAndObjectFamilies
  ∷ missingHaagKastlerLawDerivationsFromConcreteModel
  ∷ missingInteractingQFTPromotionAuthority
  ∷ []

data AQFTTypedNetSurfaceStatus : Set where
  typedSurfaceOnlyNoInteractingPromotion :
    AQFTTypedNetSurfaceStatus

data AQFTTypedNetOpenObligation : Set where
  missingConcreteLocalAlgebra :
    AQFTTypedNetOpenObligation

  missingConcreteAlgebraMorphism :
    AQFTTypedNetOpenObligation

  missingConcreteAlgebraIsomorphism :
    AQFTTypedNetOpenObligation

  missingCStarRepresentation :
    AQFTTypedNetOpenObligation

  missingDomainOfDependenceLaw :
    AQFTTypedNetOpenObligation

  missingTimeSliceTheorem :
    AQFTTypedNetOpenObligation

  missingTimeSliceSurjectivityTheorem :
    AQFTTypedNetOpenObligation

  missingDescentColimitCompatibility :
    AQFTTypedNetOpenObligation

  missingVacuumOrGNSAdapter :
    AQFTTypedNetOpenObligation

  missingBornRuleAdapter :
    AQFTTypedNetOpenObligation

  missingConstructiveInteractingNet :
    AQFTTypedNetOpenObligation

data AQFTInteractingPromotionAuthorityToken : Set where

record AQFTTypedNetSurface : Setω where
  field
    status :
      AQFTTypedNetSurfaceStatus

    Algebra :
      Region →
      Set

    algebraMatchesLocalAlgebra :
      (region : Region) →
      Algebra region
      ≡
      LocalAlgebra region

    isotonyMorphism :
      {small large : Region} →
      small ⊆ large →
      AlgebraMorphism small large

    isotonyFunctorialityLaw :
      {small middle large : Region} →
      small ⊆ middle →
      middle ⊆ large →
      Set

    causalityLaw :
      (left right : Region) →
      CausallySeparated left right →
      Set

    domainOfDependenceGivesTimeSlice :
      {source target : Region} →
      DomainOfDependence source target →
      TimeSliceCover source target

    timeSliceLaw :
      {source target : Region} →
      TimeSliceCover source target →
      AlgebraMorphism source target

    timeSliceSurjectivityTarget :
      {source target : Region} →
      (cover : TimeSliceCover source target) →
      AlgebraMorphismSurjective (timeSliceLaw cover)

    timeSliceIsomorphismTarget :
      {source target : Region} →
      TimeSliceCover source target →
      AlgebraIsomorphism source target

    descentWitness :
      (region : Region) →
      DescentCover region →
      DescentObject region

    descentCompatibilityLaw :
      (region : Region) →
      DescentCover region →
      Set

    openObligations :
      List AQFTTypedNetOpenObligation

    interactingQFTPromoted :
      Bool

    interactingQFTPromotedIsFalse :
      interactingQFTPromoted ≡ false

    noPromotionWithoutAuthority :
      AQFTInteractingPromotionAuthorityToken →
      ⊥

    typedSurfaceBoundary :
      List String

open AQFTTypedNetSurface public

postulate
  abstractIsotonyMorphism :
    {small large : Region} →
    small ⊆ large →
    AlgebraMorphism small large

  abstractCausalityLaw :
    (left right : Region) →
    CausallySeparated left right →
    Set

  abstractIsotonyFunctorialityLaw :
    {small middle large : Region} →
    small ⊆ middle →
    middle ⊆ large →
    Set

  abstractDomainOfDependenceGivesTimeSlice :
    {source target : Region} →
    DomainOfDependence source target →
    TimeSliceCover source target

  abstractTimeSliceLaw :
    {source target : Region} →
    TimeSliceCover source target →
    AlgebraMorphism source target

  abstractTimeSliceSurjectivityTarget :
    {source target : Region} →
    (cover : TimeSliceCover source target) →
    AlgebraMorphismSurjective (abstractTimeSliceLaw cover)

  abstractTimeSliceIsomorphismTarget :
    {source target : Region} →
    TimeSliceCover source target →
    AlgebraIsomorphism source target

  abstractDescentWitness :
    (region : Region) →
    DescentCover region →
    DescentObject region

  abstractDescentCompatibilityLaw :
    (region : Region) →
    DescentCover region →
    Set

canonicalAQFTTypedNetSurface :
  AQFTTypedNetSurface
canonicalAQFTTypedNetSurface =
  record
    { status =
        typedSurfaceOnlyNoInteractingPromotion
    ; Algebra =
        LocalAlgebra
    ; algebraMatchesLocalAlgebra =
        λ _ → refl
    ; isotonyMorphism =
        abstractIsotonyMorphism
    ; isotonyFunctorialityLaw =
        abstractIsotonyFunctorialityLaw
    ; causalityLaw =
        abstractCausalityLaw
    ; domainOfDependenceGivesTimeSlice =
        abstractDomainOfDependenceGivesTimeSlice
    ; timeSliceLaw =
        abstractTimeSliceLaw
    ; timeSliceSurjectivityTarget =
        abstractTimeSliceSurjectivityTarget
    ; timeSliceIsomorphismTarget =
        abstractTimeSliceIsomorphismTarget
    ; descentWitness =
        abstractDescentWitness
    ; descentCompatibilityLaw =
        abstractDescentCompatibilityLaw
    ; openObligations =
        missingConcreteLocalAlgebra
        ∷ missingConcreteAlgebraMorphism
        ∷ missingConcreteAlgebraIsomorphism
        ∷ missingCStarRepresentation
        ∷ missingDomainOfDependenceLaw
        ∷ missingTimeSliceTheorem
        ∷ missingTimeSliceSurjectivityTheorem
        ∷ missingDescentColimitCompatibility
        ∷ missingVacuumOrGNSAdapter
        ∷ missingBornRuleAdapter
        ∷ missingConstructiveInteractingNet
        ∷ []
    ; interactingQFTPromoted =
        false
    ; interactingQFTPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; typedSurfaceBoundary =
        "AQFTTypedNetSurface is a typed socket for region-indexed local algebras"
        ∷ "isotony, causality, time-slice, domain-of-dependence, algebra-surjectivity, algebra-isomorphism, and descent are abstract interface fields"
        ∷ "no concrete C*-algebra, Hilbert representation, vacuum, or Born-rule adapter is constructed here"
        ∷ "no time-slice theorem or descent/colimit compatibility theorem is constructed here"
        ∷ "no constructive interacting net or Standard Model QFT is constructed here"
        ∷ "this module does not construct GRQFTClosurePromotionReceipt or any interacting-QFT promotion token"
        ∷ []
    }

record AQFTRootPostulateBoundaryReceipt : Setω where
  field
    typedNetSurface :
      AQFTTypedNetSurface

    foundationalSockets :
      List AQFTFoundationalSocket

    foundationalSocketsAreCanonical :
      foundationalSockets ≡ canonicalAQFTFoundationalSockets

    rootBlockers :
      List AQFTRootPostulateBoundaryBlocker

    rootBlockersAreCanonical :
      rootBlockers ≡ canonicalAQFTRootPostulateBoundaryBlockers

    regionSocket :
      Set

    localAlgebraSocket :
      regionSocket →
      Set

    algebraMorphismSocket :
      regionSocket →
      regionSocket →
      Set

    algebraIsomorphismSocket :
      regionSocket →
      regionSocket →
      Set

    algebraMorphismSurjectivityPredicate :
      {source target : regionSocket} →
      algebraMorphismSocket source target →
      Set

    inclusionSocket :
      regionSocket →
      regionSocket →
      Set

    causalSeparationSocket :
      regionSocket →
      regionSocket →
      Set

    timeSliceCoverSocket :
      regionSocket →
      regionSocket →
      Set

    domainOfDependenceSocket :
      regionSocket →
      regionSocket →
      Set

    descentCoverSocket :
      regionSocket →
      Set

    descentObjectSocket :
      regionSocket →
      Set

    rootOpenObligations :
      List AQFTTypedNetOpenObligation

    rootOpenObligationsAreCanonical :
      rootOpenObligations
      ≡
      AQFTTypedNetSurface.openObligations canonicalAQFTTypedNetSurface

    rootPostulatesExternallySupplied :
      Bool

    rootPostulatesExternallySuppliedIsTrue :
      rootPostulatesExternallySupplied ≡ true

    rootPostulatesEliminatedInternally :
      Bool

    rootPostulatesEliminatedInternallyIsFalse :
      rootPostulatesEliminatedInternally ≡ false

    interactingQFTPromotedByRootLedger :
      Bool

    interactingQFTPromotedByRootLedgerIsFalse :
      interactingQFTPromotedByRootLedger ≡ false

    rootBoundary :
      List String

open AQFTRootPostulateBoundaryReceipt public

canonicalAQFTRootPostulateBoundaryReceipt :
  AQFTRootPostulateBoundaryReceipt
canonicalAQFTRootPostulateBoundaryReceipt =
  record
    { typedNetSurface =
        canonicalAQFTTypedNetSurface
    ; foundationalSockets =
        canonicalAQFTFoundationalSockets
    ; foundationalSocketsAreCanonical =
        refl
    ; rootBlockers =
        canonicalAQFTRootPostulateBoundaryBlockers
    ; rootBlockersAreCanonical =
        refl
    ; regionSocket =
        Region
    ; localAlgebraSocket =
        LocalAlgebra
    ; algebraMorphismSocket =
        AlgebraMorphism
    ; algebraIsomorphismSocket =
        AlgebraIsomorphism
    ; algebraMorphismSurjectivityPredicate =
        AlgebraMorphismSurjective
    ; inclusionSocket =
        _⊆_
    ; causalSeparationSocket =
        CausallySeparated
    ; timeSliceCoverSocket =
        TimeSliceCover
    ; domainOfDependenceSocket =
        DomainOfDependence
    ; descentCoverSocket =
        DescentCover
    ; descentObjectSocket =
        DescentObject
    ; rootOpenObligations =
        AQFTTypedNetSurface.openObligations canonicalAQFTTypedNetSurface
    ; rootOpenObligationsAreCanonical =
        refl
    ; rootPostulatesExternallySupplied =
        true
    ; rootPostulatesExternallySuppliedIsTrue =
        refl
    ; rootPostulatesEliminatedInternally =
        false
    ; rootPostulatesEliminatedInternallyIsFalse =
        refl
    ; interactingQFTPromotedByRootLedger =
        false
    ; interactingQFTPromotedByRootLedgerIsFalse =
        refl
    ; rootBoundary =
        "AQFT root postulates are recorded as foundational sockets consumed by later AQFT and DHR receipts"
        ∷ "Region, LocalAlgebra, morphisms, inclusions, causal separation, time-slice coverage, domain of dependence, and descent remain abstract carriers or relations"
        ∷ "The canonical typed net surface consumes these sockets but does not eliminate them"
        ∷ "Concrete Haag-Kastler laws, C*-representation data, and interacting-QFT promotion remain blocked"
        ∷ []
    }
