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

  DescentCover :
    Region →
    Set

  DescentObject :
    Region →
    Set

data AQFTTypedNetSurfaceStatus : Set where
  typedSurfaceOnlyNoInteractingPromotion :
    AQFTTypedNetSurfaceStatus

data AQFTTypedNetOpenObligation : Set where
  missingConcreteLocalAlgebra :
    AQFTTypedNetOpenObligation

  missingConcreteAlgebraMorphism :
    AQFTTypedNetOpenObligation

  missingCStarRepresentation :
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

    causalityLaw :
      (left right : Region) →
      CausallySeparated left right →
      Set

    timeSliceLaw :
      {source target : Region} →
      TimeSliceCover source target →
      AlgebraMorphism source target

    descentWitness :
      (region : Region) →
      DescentCover region →
      DescentObject region

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

  abstractTimeSliceLaw :
    {source target : Region} →
    TimeSliceCover source target →
    AlgebraMorphism source target

  abstractDescentWitness :
    (region : Region) →
    DescentCover region →
    DescentObject region

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
    ; causalityLaw =
        abstractCausalityLaw
    ; timeSliceLaw =
        abstractTimeSliceLaw
    ; descentWitness =
        abstractDescentWitness
    ; openObligations =
        missingConcreteLocalAlgebra
        ∷ missingConcreteAlgebraMorphism
        ∷ missingCStarRepresentation
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
        ∷ "isotony, causality, time-slice, and descent are abstract interface fields"
        ∷ "no concrete C*-algebra, Hilbert representation, vacuum, or Born-rule adapter is constructed here"
        ∷ "no constructive interacting net or Standard Model QFT is constructed here"
        ∷ "this module does not construct GRQFTClosurePromotionReceipt or any interacting-QFT promotion token"
        ∷ []
    }
