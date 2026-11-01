module DASHI.Physics.Closure.ProjectionContractionOperatorBridgeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes

------------------------------------------------------------------------
-- Manager A / A4: pure operator taxonomy.
--
-- The receipt separates idempotent projection, many-to-one contraction,
-- and invertible endomorphism data.  It only records an internal bridge
-- between operator classes; it does not promote any external target.

data OperatorBridgeStatus : Set where
  operatorTaxonomyBridgeRecorded :
    OperatorBridgeStatus

data OperatorBridgeScope : Set where
  pureEndomorphismTaxonomyOnly :
    OperatorBridgeScope

data OperatorTaxon : Set where
  idempotentProjection :
    OperatorTaxon

  nonInvertibleManyToOneContraction :
    OperatorTaxon

  invertibleEndomorphism :
    OperatorTaxon

  unclassifiedEndomorphism :
    OperatorTaxon

data BridgeAvailability : Set where
  bridgeAvailableAsTaxonomy :
    BridgeAvailability

  bridgeNotClaimed :
    BridgeAvailability

data ExternalPromotion : Set where

externalPromotionImpossibleHere :
  ExternalPromotion → ⊥
externalPromotionImpossibleHere ()

record ManyToOneContraction {S : Set} (K : S → S) : Set where
  field
    sourceA :
      S

    sourceB :
      S

    sourcesDistinct :
      ¬ (sourceA ≡ sourceB)

    contractedImage :
      K sourceA ≡ K sourceB

open ManyToOneContraction public

manyToOneContractionNotInvertible :
  ∀ {S : Set} {K : S → S} →
  ManyToOneContraction K →
  ¬ Invertible K
manyToOneContractionNotInvertible c invK =
  let open Invertible invK
      sourceA′ = ManyToOneContraction.sourceA c
      sourceB′ = ManyToOneContraction.sourceB c
      contractedImage′ = ManyToOneContraction.contractedImage c
      sourceEquality =
        trans
          (sym (left sourceA′))
          (trans (cong inv contractedImage′) (left sourceB′))
  in
  ManyToOneContraction.sourcesDistinct c sourceEquality

record OperatorClassification {S : Set} (K : S → S) : Set₁ where
  field
    taxon :
      OperatorTaxon

    projectionWitness :
      taxon ≡ idempotentProjection →
      Projection K

    contractionWitness :
      taxon ≡ nonInvertibleManyToOneContraction →
      ManyToOneContraction K

    contractionNonInvertible :
      taxon ≡ nonInvertibleManyToOneContraction →
      ¬ Invertible K

    invertibleWitness :
      taxon ≡ invertibleEndomorphism →
      Invertible K

open OperatorClassification public

record ProjectionContractionOperatorBridgeReceipt : Setω where
  field
    status :
      OperatorBridgeStatus

    scope :
      OperatorBridgeScope

    projectionClass :
      OperatorTaxon

    projectionClassIsIdempotent :
      projectionClass ≡ idempotentProjection

    contractionClass :
      OperatorTaxon

    contractionClassIsManyToOne :
      contractionClass ≡ nonInvertibleManyToOneContraction

    invertibleClass :
      OperatorTaxon

    invertibleClassIsInvertible :
      invertibleClass ≡ invertibleEndomorphism

    bridgeStatus :
      BridgeAvailability

    bridgeStatusIsTaxonomy :
      bridgeStatus ≡ bridgeAvailableAsTaxonomy

    paperPromotionConstructed :
      Bool

    paperPromotionConstructedIsFalse :
      paperPromotionConstructed ≡ false

    physicalPromotionConstructed :
      Bool

    physicalPromotionConstructedIsFalse :
      physicalPromotionConstructed ≡ false

    clayPromotionConstructed :
      Bool

    clayPromotionConstructedIsFalse :
      clayPromotionConstructed ≡ false

    terminalPromotionConstructed :
      Bool

    terminalPromotionConstructedIsFalse :
      terminalPromotionConstructed ≡ false

    promotionFlags :
      List ExternalPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    boundaryNotes :
      List String

open ProjectionContractionOperatorBridgeReceipt public

collapseToFalse :
  Bool → Bool
collapseToFalse _ = false

identityBool :
  Bool → Bool
identityBool b = b

false≢true :
  ¬ (false ≡ true)
false≢true ()

collapseToFalseProjection :
  Projection collapseToFalse
collapseToFalseProjection =
  record
    { idem = λ
        { false → refl
        ; true → refl
        }
    }

collapseToFalseManyToOne :
  ManyToOneContraction collapseToFalse
collapseToFalseManyToOne =
  record
    { sourceA =
        false
    ; sourceB =
        true
    ; sourcesDistinct =
        false≢true
    ; contractedImage =
        refl
    }

collapseToFalseClassification :
  OperatorClassification collapseToFalse
collapseToFalseClassification =
  record
    { taxon =
        nonInvertibleManyToOneContraction
    ; projectionWitness =
        λ ()
    ; contractionWitness =
        λ _ → collapseToFalseManyToOne
    ; contractionNonInvertible =
        λ _ → manyToOneContractionNotInvertible collapseToFalseManyToOne
    ; invertibleWitness =
        λ ()
    }

identityBoolInvertible :
  Invertible identityBool
identityBoolInvertible =
  record
    { inv =
        identityBool
    ; left =
        λ _ → refl
    ; right =
        λ _ → refl
    }

identityBoolClassification :
  OperatorClassification identityBool
identityBoolClassification =
  record
    { taxon =
        invertibleEndomorphism
    ; projectionWitness =
        λ ()
    ; contractionWitness =
        λ ()
    ; contractionNonInvertible =
        λ ()
    ; invertibleWitness =
        λ _ → identityBoolInvertible
    }

canonicalProjectionContractionOperatorBridgeReceipt :
  ProjectionContractionOperatorBridgeReceipt
canonicalProjectionContractionOperatorBridgeReceipt =
  record
    { status =
        operatorTaxonomyBridgeRecorded
    ; scope =
        pureEndomorphismTaxonomyOnly
    ; projectionClass =
        idempotentProjection
    ; projectionClassIsIdempotent =
        refl
    ; contractionClass =
        nonInvertibleManyToOneContraction
    ; contractionClassIsManyToOne =
        refl
    ; invertibleClass =
        invertibleEndomorphism
    ; invertibleClassIsInvertible =
        refl
    ; bridgeStatus =
        bridgeAvailableAsTaxonomy
    ; bridgeStatusIsTaxonomy =
        refl
    ; paperPromotionConstructed =
        false
    ; paperPromotionConstructedIsFalse =
        refl
    ; physicalPromotionConstructed =
        false
    ; physicalPromotionConstructedIsFalse =
        refl
    ; clayPromotionConstructed =
        false
    ; clayPromotionConstructedIsFalse =
        refl
    ; terminalPromotionConstructed =
        false
    ; terminalPromotionConstructedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; boundaryNotes =
        "Pure operator taxonomy only"
        ∷ "Projection is recorded as idempotence"
        ∷ "Many-to-one contraction carries a witness of distinct inputs with one image and is therefore not invertible"
        ∷ "Invertible operator carries a two-sided inverse"
        ∷ "No paper, physical, Clay, or terminal promotion is constructed"
        ∷ []
    }

canonicalContractionIsNotInvertible :
  ¬ Invertible collapseToFalse
canonicalContractionIsNotInvertible =
  manyToOneContractionNotInvertible collapseToFalseManyToOne

canonicalPaperPromotionFalse :
  paperPromotionConstructed canonicalProjectionContractionOperatorBridgeReceipt
    ≡ false
canonicalPaperPromotionFalse =
  refl

canonicalPhysicalPromotionFalse :
  physicalPromotionConstructed canonicalProjectionContractionOperatorBridgeReceipt
    ≡ false
canonicalPhysicalPromotionFalse =
  refl

canonicalClayPromotionFalse :
  clayPromotionConstructed canonicalProjectionContractionOperatorBridgeReceipt
    ≡ false
canonicalClayPromotionFalse =
  refl

canonicalTerminalPromotionFalse :
  terminalPromotionConstructed canonicalProjectionContractionOperatorBridgeReceipt
    ≡ false
canonicalTerminalPromotionFalse =
  refl
