module DASHI.Core.FormalLensLawCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.FormalLensQualificationCore as Lens
import DASHI.Core.FormalLensVocabularyCore as Vocabulary
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Generic formal-lens law socket.
--
-- This module is intentionally structural.  It records carrier, structure,
-- law, invariant, morphism, qualification, and authority-boundary surfaces
-- while keeping every claim candidate-only and non-promoting.
--
-- The `StructureLawCore` parameter is the attachment point for a future
-- `FormalStructureLawCore` consumer.  The file does not import that module
-- directly, so the socket stays usable even when that optional core is not
-- present yet.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Compatibility styles.

data FormalLensLawStyle : Set where
  statisticalStyle :
    FormalLensLawStyle

  projectionFingerprintHiddenLiftStyle :
    FormalLensLawStyle

  cryptographicStyle :
    FormalLensLawStyle

  numberResidueStyle :
    FormalLensLawStyle

  graphStyle :
    FormalLensLawStyle

  productVectorStyle :
    FormalLensLawStyle

  namedFormalLensLawStyle :
    String →
    FormalLensLawStyle

styleVocabularyKinds :
  FormalLensLawStyle →
  List Vocabulary.FormalLensKind
styleVocabularyKinds statisticalStyle =
  Vocabulary.Statistical
  ∷ Vocabulary.Inference
  ∷ Vocabulary.RobustStatistic
  ∷ Vocabulary.Estimator
  ∷ Vocabulary.HypothesisTest
  ∷ Vocabulary.ConfidenceInterval
  ∷ Vocabulary.UncertaintyQuantification
  ∷ []
styleVocabularyKinds projectionFingerprintHiddenLiftStyle =
  Vocabulary.Cryptographic
  ∷ Vocabulary.TrapdoorProjection
  ∷ Vocabulary.SecretWitness
  ∷ Vocabulary.QuotientResidue
  ∷ Vocabulary.HiddenLift
  ∷ Vocabulary.Commitment
  ∷ []
styleVocabularyKinds cryptographicStyle =
  Vocabulary.Cryptographic
  ∷ Vocabulary.TrapdoorProjection
  ∷ Vocabulary.SecretWitness
  ∷ Vocabulary.Commitment
  ∷ []
styleVocabularyKinds numberResidueStyle =
  Vocabulary.Number
  ∷ Vocabulary.Arithmetic
  ∷ Vocabulary.Valuation
  ∷ Vocabulary.PrimeDecomposition
  ∷ Vocabulary.LocalGlobal
  ∷ Vocabulary.Modular
  ∷ Vocabulary.QuotientResidue
  ∷ []
styleVocabularyKinds graphStyle =
  Vocabulary.Graph
  ∷ Vocabulary.Hypergraph
  ∷ Vocabulary.Order
  ∷ Vocabulary.Lattice
  ∷ []
styleVocabularyKinds productVectorStyle =
  Vocabulary.Operator
  ∷ Vocabulary.Functional
  ∷ Vocabulary.Category
  ∷ Vocabulary.ConfidenceInterval
  ∷ Vocabulary.RobustStatistic
  ∷ []
styleVocabularyKinds (namedFormalLensLawStyle _) =
  []

styleVocabularyKindCount :
  FormalLensLawStyle →
  Nat
styleVocabularyKindCount style =
  listCount (styleVocabularyKinds style)

canonicalStatisticalStyleVocabularyKinds :
  List Vocabulary.FormalLensKind
canonicalStatisticalStyleVocabularyKinds =
  styleVocabularyKinds statisticalStyle

canonicalProjectionFingerprintHiddenLiftStyleVocabularyKinds :
  List Vocabulary.FormalLensKind
canonicalProjectionFingerprintHiddenLiftStyleVocabularyKinds =
  styleVocabularyKinds projectionFingerprintHiddenLiftStyle

canonicalCryptographicStyleVocabularyKinds :
  List Vocabulary.FormalLensKind
canonicalCryptographicStyleVocabularyKinds =
  styleVocabularyKinds cryptographicStyle

canonicalNumberResidueStyleVocabularyKinds :
  List Vocabulary.FormalLensKind
canonicalNumberResidueStyleVocabularyKinds =
  styleVocabularyKinds numberResidueStyle

canonicalGraphStyleVocabularyKinds :
  List Vocabulary.FormalLensKind
canonicalGraphStyleVocabularyKinds =
  styleVocabularyKinds graphStyle

canonicalProductVectorStyleVocabularyKinds :
  List Vocabulary.FormalLensKind
canonicalProductVectorStyleVocabularyKinds =
  styleVocabularyKinds productVectorStyle

canonicalStatisticalStyleVocabularyKindCount :
  Nat
canonicalStatisticalStyleVocabularyKindCount =
  styleVocabularyKindCount statisticalStyle

canonicalProjectionFingerprintHiddenLiftStyleVocabularyKindCount :
  Nat
canonicalProjectionFingerprintHiddenLiftStyleVocabularyKindCount =
  styleVocabularyKindCount projectionFingerprintHiddenLiftStyle

canonicalCryptographicStyleVocabularyKindCount :
  Nat
canonicalCryptographicStyleVocabularyKindCount =
  styleVocabularyKindCount cryptographicStyle

canonicalNumberResidueStyleVocabularyKindCount :
  Nat
canonicalNumberResidueStyleVocabularyKindCount =
  styleVocabularyKindCount numberResidueStyle

canonicalGraphStyleVocabularyKindCount :
  Nat
canonicalGraphStyleVocabularyKindCount =
  styleVocabularyKindCount graphStyle

canonicalProductVectorStyleVocabularyKindCount :
  Nat
canonicalProductVectorStyleVocabularyKindCount =
  styleVocabularyKindCount productVectorStyle

------------------------------------------------------------------------
-- Carrier surface.

record FormalLensLawCarrierSurface : Set where
  constructor mkFormalLensLawCarrierSurface
  field
    carrierLabel :
      String

    carrierOwner :
      String

    carrierSurface :
      String

    carrierVocabularyKinds :
      List Vocabulary.FormalLensKind

    carrierVocabularyKindCount :
      Nat

    carrierCandidateOnly :
      Bool

    carrierPromoted :
      Bool

open FormalLensLawCarrierSurface public

record FormalLensLawCarrierReceipt
  (carrier : FormalLensLawCarrierSurface) :
  Set where
  constructor mkFormalLensLawCarrierReceipt
  field
    carrierVocabularyKindCountCanonical :
      carrierVocabularyKindCount carrier
      ≡
      listCount (carrierVocabularyKinds carrier)

    carrierCandidateOnlyIsTrue :
      carrierCandidateOnly carrier ≡ true

    carrierPromotedIsFalse :
      carrierPromoted carrier ≡ false

open FormalLensLawCarrierReceipt public

------------------------------------------------------------------------
-- Structure surface.

record FormalLensLawStructureSurface
  (StructureLawCore : Set) :
  Set where
  constructor mkFormalLensLawStructureSurface
  field
    structureLabel :
      String

    structureOwner :
      String

    structureSurface :
      String

    structureCarrier :
      FormalLensLawCarrierSurface

    structureCarrierReceipt :
      FormalLensLawCarrierReceipt structureCarrier

    structureLawCore :
      StructureLawCore

    structureCandidateOnly :
      Bool

    structurePromoted :
      Bool

    structureAuthorityPromotion :
      Bool

open FormalLensLawStructureSurface public

record FormalLensLawStructureReceipt
  {StructureLawCore : Set}
  (structureSurface : FormalLensLawStructureSurface StructureLawCore) :
  Set where
  constructor mkFormalLensLawStructureReceipt
  field
    structureCandidateOnlyIsTrue :
      structureCandidateOnly structureSurface ≡ true

    structurePromotedIsFalse :
      structurePromoted structureSurface ≡ false

    structureAuthorityPromotionIsFalse :
      structureAuthorityPromotion structureSurface ≡ false

open FormalLensLawStructureReceipt public

------------------------------------------------------------------------
-- Law surface.

record FormalLensLawSurface
  (StructureLawCore : Set) :
  Set where
  constructor mkFormalLensLawSurface
  field
    lawLabel :
      String

    lawOwner :
      String

    lawSurface :
      String

    lawStyle :
      FormalLensLawStyle

    lawVocabularyKinds :
      List Vocabulary.FormalLensKind

    lawVocabularyKindCount :
      Nat

    lawStructureSurface :
      FormalLensLawStructureSurface StructureLawCore

    lawQualificationSurface :
      Lens.FormalLensQualificationSurface

    lawQualificationReceipt :
      Lens.FormalLensQualificationReceipt lawQualificationSurface

    lawCarrierSurface :
      FormalLensLawCarrierSurface

    lawCarrierReceipt :
      FormalLensLawCarrierReceipt lawCarrierSurface

    lawInvariantCandidateOnly :
      Bool

    lawInvariantPromoted :
      Bool

    lawAuthorityPromotion :
      Bool

open FormalLensLawSurface public

record FormalLensLawReceipt
  {StructureLawCore : Set}
  (lawSurfaceValue : FormalLensLawSurface StructureLawCore) :
  Set where
  constructor mkFormalLensLawReceipt
  field
    lawVocabularyKindCountCanonical :
      lawVocabularyKindCount lawSurfaceValue
      ≡
      listCount (lawVocabularyKinds lawSurfaceValue)

    lawQualificationCandidateOnlyIsTrue :
      Lens.qualificationCandidateOnly (lawQualificationSurface lawSurfaceValue) ≡ true

    lawQualificationPromotedIsFalse :
      Lens.qualificationPromoted (lawQualificationSurface lawSurfaceValue) ≡ false

    lawInvariantCandidateOnlyIsTrue :
      lawInvariantCandidateOnly lawSurfaceValue ≡ true

    lawInvariantPromotedIsFalse :
      lawInvariantPromoted lawSurfaceValue ≡ false

    lawAuthorityPromotionIsFalse :
      lawAuthorityPromotion lawSurfaceValue ≡ false

    lawQualificationReceiptCandidateOnlyIsTrue :
      Lens.qualificationCandidateOnly (lawQualificationSurface lawSurfaceValue)
      ≡
      true

    lawQualificationReceiptPromotedIsFalse :
      Lens.qualificationPromoted (lawQualificationSurface lawSurfaceValue)
      ≡
      false

open FormalLensLawReceipt public

------------------------------------------------------------------------
-- Invariant surface.

record FormalLensLawInvariantSurface
  (StructureLawCore : Set) :
  Set where
  constructor mkFormalLensLawInvariantSurface
  field
    invariantLabel :
      String

    invariantOwner :
      String

    invariantSurface :
      String

    invariantLawSurface :
      FormalLensLawSurface StructureLawCore

    invariantCandidateOnly :
      Bool

    invariantPromoted :
      Bool

    invariantPreservedBySuppliedMorphism :
      Bool

open FormalLensLawInvariantSurface public

record FormalLensLawInvariantReceipt
  {StructureLawCore : Set}
  (invariantSurfaceValue : FormalLensLawInvariantSurface StructureLawCore) :
  Set where
  constructor mkFormalLensLawInvariantReceipt
  field
    invariantCandidateOnlyIsTrue :
      invariantCandidateOnly invariantSurfaceValue ≡ true

    invariantPromotedIsFalse :
      invariantPromoted invariantSurfaceValue ≡ false

    invariantPreservedBySuppliedMorphismIsTrue :
      invariantPreservedBySuppliedMorphism invariantSurfaceValue ≡ true

open FormalLensLawInvariantReceipt public

------------------------------------------------------------------------
-- Morphism surface.

record FormalLensLawMorphismSurface
  (StructureLawCore : Set) :
  Set where
  constructor mkFormalLensLawMorphismSurface
  field
    morphismLabel :
      String

    morphismOwner :
      String

    morphismSurface :
      String

    morphismSource :
      FormalLensLawSurface StructureLawCore

    morphismTarget :
      FormalLensLawSurface StructureLawCore

    morphismWitness :
      String

    morphismCandidateOnly :
      Bool

    morphismPromoted :
      Bool

    morphismPreservesInvariant :
      Bool

open FormalLensLawMorphismSurface public

record FormalLensLawMorphismReceipt
  {StructureLawCore : Set}
  (morphismSurfaceValue : FormalLensLawMorphismSurface StructureLawCore) :
  Set where
  constructor mkFormalLensLawMorphismReceipt
  field
    morphismCandidateOnlyIsTrue :
      morphismCandidateOnly morphismSurfaceValue ≡ true

    morphismPromotedIsFalse :
      morphismPromoted morphismSurfaceValue ≡ false

    morphismPreservesInvariantIsTrue :
      morphismPreservesInvariant morphismSurfaceValue ≡ true

open FormalLensLawMorphismReceipt public

------------------------------------------------------------------------
-- Qualification surface.

record FormalLensLawQualificationSurface
  (StructureLawCore : Set) :
  Set where
  constructor mkFormalLensLawQualificationSurface
  field
    qualificationLabel :
      String

    qualificationOwner :
      String

    qualificationSurface :
      String

    qualificationLawSurface :
      FormalLensLawSurface StructureLawCore

    qualificationLensSurface :
      Lens.FormalLensQualificationSurface

    qualificationLensReceipt :
      Lens.FormalLensQualificationReceipt qualificationLensSurface

    qualificationCandidateOnly :
      Bool

    qualificationPromoted :
      Bool

    qualificationAuthorityPromotion :
      Bool

open FormalLensLawQualificationSurface public

record FormalLensLawQualificationReceipt
  {StructureLawCore : Set}
  (qualificationSurfaceValue :
     FormalLensLawQualificationSurface StructureLawCore) :
  Set where
  constructor mkFormalLensLawQualificationReceipt
  field
    qualificationCandidateOnlyIsTrue :
      qualificationCandidateOnly qualificationSurfaceValue ≡ true

    qualificationPromotedIsFalse :
      qualificationPromoted qualificationSurfaceValue ≡ false

    qualificationAuthorityPromotionIsFalse :
      qualificationAuthorityPromotion qualificationSurfaceValue ≡ false

    qualificationLensCandidateOnlyIsTrue :
      Lens.qualificationCandidateOnly
        (qualificationLensSurface qualificationSurfaceValue) ≡ true

    qualificationLensPromotedIsFalse :
      Lens.qualificationPromoted
        (qualificationLensSurface qualificationSurfaceValue) ≡ false

open FormalLensLawQualificationReceipt public

------------------------------------------------------------------------
-- Authority boundary surface.

record FormalLensLawAuthorityBoundarySurface
  (StructureLawCore : Set) :
  Set where
  constructor mkFormalLensLawAuthorityBoundarySurface
  field
    authorityBoundaryLabel :
      String

    authorityBoundaryOwner :
      String

    authorityBoundarySurface :
      String

    authorityBoundaryLawSurface :
      FormalLensLawSurface StructureLawCore

    authorityBundle :
      Authority.AuthorityNonPromotionBundle

    authorityBoundaryCandidateOnly :
      Bool

    authorityBoundaryPromoted :
      Bool

    authorityBoundaryPromotion :
      Bool

open FormalLensLawAuthorityBoundarySurface public

record FormalLensLawAuthorityBoundaryReceipt
  {StructureLawCore : Set}
  (authorityBoundarySurfaceValue :
     FormalLensLawAuthorityBoundarySurface StructureLawCore) :
  Set where
  constructor mkFormalLensLawAuthorityBoundaryReceipt
  field
    authorityBoundaryCandidateOnlyIsTrue :
      authorityBoundaryCandidateOnly authorityBoundarySurfaceValue ≡ true

    authorityBoundaryPromotedIsFalse :
      authorityBoundaryPromoted authorityBoundarySurfaceValue ≡ false

    authorityBoundaryPromotionIsFalse :
      authorityBoundaryPromotion authorityBoundarySurfaceValue ≡ false

    authorityBundlePromotesAnyAuthorityIsFalse :
      Authority.promotesAnyAuthority
        (authorityBundle authorityBoundarySurfaceValue) ≡ false

open FormalLensLawAuthorityBoundaryReceipt public

------------------------------------------------------------------------
-- Canonical compatibility receipts.

record FormalLensLawCompatibilityReceipt
  (style : FormalLensLawStyle) :
  Set where
  constructor mkFormalLensLawCompatibilityReceipt
  field
    compatibilityVocabularyKinds :
      List Vocabulary.FormalLensKind

    compatibilityVocabularyKindsAreCanonical :
      compatibilityVocabularyKinds ≡ styleVocabularyKinds style

    compatibilityVocabularyKindCount :
      Nat

    compatibilityVocabularyKindCountIsCanonical :
      compatibilityVocabularyKindCount
      ≡
      listCount compatibilityVocabularyKinds

    compatibilityCandidateOnly :
      Bool

    compatibilityCandidateOnlyIsTrue :
      compatibilityCandidateOnly ≡ true

    compatibilityPromoted :
      Bool

    compatibilityPromotedIsFalse :
      compatibilityPromoted ≡ false

    compatibilityAuthorityPromotion :
      Bool

    compatibilityAuthorityPromotionIsFalse :
      compatibilityAuthorityPromotion ≡ false

open FormalLensLawCompatibilityReceipt public

mkCanonicalFormalLensLawCompatibilityReceipt :
  (style : FormalLensLawStyle) →
  FormalLensLawCompatibilityReceipt style
mkCanonicalFormalLensLawCompatibilityReceipt style =
  mkFormalLensLawCompatibilityReceipt
    (styleVocabularyKinds style)
    refl
    (styleVocabularyKindCount style)
    refl
    true
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Top-level socket.

record FormalLensLawSocket
  (StructureLawCore : Set) :
  Set where
  constructor mkFormalLensLawSocket
  field
    socketLabel :
      String

    socketOwner :
      String

    socketSurface :
      String

    socketStyle :
      FormalLensLawStyle

    socketCarrierSurface :
      FormalLensLawCarrierSurface

    socketCarrierReceipt :
      FormalLensLawCarrierReceipt socketCarrierSurface

    socketStructureSurface :
      FormalLensLawStructureSurface StructureLawCore

    socketStructureReceipt :
      FormalLensLawStructureReceipt socketStructureSurface

    socketLawSurface :
      FormalLensLawSurface StructureLawCore

    socketLawReceipt :
      FormalLensLawReceipt socketLawSurface

    socketInvariantSurface :
      FormalLensLawInvariantSurface StructureLawCore

    socketInvariantReceipt :
      FormalLensLawInvariantReceipt socketInvariantSurface

    socketMorphismSurface :
      FormalLensLawMorphismSurface StructureLawCore

    socketMorphismReceipt :
      FormalLensLawMorphismReceipt socketMorphismSurface

    socketQualificationSurface :
      FormalLensLawQualificationSurface StructureLawCore

    socketQualificationReceipt :
      FormalLensLawQualificationReceipt socketQualificationSurface

    socketAuthorityBoundarySurface :
      FormalLensLawAuthorityBoundarySurface StructureLawCore

    socketAuthorityBoundaryReceipt :
      FormalLensLawAuthorityBoundaryReceipt socketAuthorityBoundarySurface

    socketGenericReceipt :
      GenericReceipt.GenericReceipt

open FormalLensLawSocket public

------------------------------------------------------------------------
-- Surface projections.

socketVocabularyKinds :
  ∀ {StructureLawCore : Set} →
  FormalLensLawSocket StructureLawCore →
  List Vocabulary.FormalLensKind
socketVocabularyKinds socket =
  lawVocabularyKinds (socketLawSurface socket)

socketVocabularyKindCount :
  ∀ {StructureLawCore : Set} →
  FormalLensLawSocket StructureLawCore →
  Nat
socketVocabularyKindCount socket =
  lawVocabularyKindCount (socketLawSurface socket)

socketQualificationLensSurface :
  ∀ {StructureLawCore : Set} →
  FormalLensLawSocket StructureLawCore →
  Lens.FormalLensQualificationSurface
socketQualificationLensSurface socket =
  qualificationLensSurface (socketQualificationSurface socket)

socketAuthorityBundle :
  ∀ {StructureLawCore : Set} →
  FormalLensLawSocket StructureLawCore →
  Authority.AuthorityNonPromotionBundle
socketAuthorityBundle socket =
  authorityBundle (socketAuthorityBoundarySurface socket)

socketCompatibilityReceipt :
  ∀ {StructureLawCore : Set} →
  (socket : FormalLensLawSocket StructureLawCore) →
  FormalLensLawCompatibilityReceipt (socketStyle socket)
socketCompatibilityReceipt socket =
  mkCanonicalFormalLensLawCompatibilityReceipt (socketStyle socket)

------------------------------------------------------------------------
-- Structural and non-promotion lemmas.

lawSurfaceRefinesLensQualification :
  ∀ {StructureLawCore : Set}
  (socket : FormalLensLawSocket StructureLawCore) →
  Lens.FormalLensQualificationReceipt (socketQualificationLensSurface socket)
lawSurfaceRefinesLensQualification socket =
  qualificationLensReceipt (socketQualificationSurface socket)

lawSurfaceRemainsCandidateOnly :
  ∀ {StructureLawCore : Set}
  (socket : FormalLensLawSocket StructureLawCore) →
  qualificationCandidateOnly (socketQualificationSurface socket) ≡ true
lawSurfaceRemainsCandidateOnly socket =
  qualificationCandidateOnlyIsTrue (socketQualificationReceipt socket)

lawSurfaceDoesNotPromote :
  ∀ {StructureLawCore : Set}
  (socket : FormalLensLawSocket StructureLawCore) →
  qualificationPromoted (socketQualificationSurface socket) ≡ false
lawSurfaceDoesNotPromote socket =
  qualificationPromotedIsFalse (socketQualificationReceipt socket)

lawSurfaceDoesNotPromoteAuthority :
  ∀ {StructureLawCore : Set}
  (socket : FormalLensLawSocket StructureLawCore) →
  qualificationAuthorityPromotion (socketQualificationSurface socket) ≡ false
lawSurfaceDoesNotPromoteAuthority socket =
  qualificationAuthorityPromotionIsFalse (socketQualificationReceipt socket)

lawInvariantPreservedOnlyBySuppliedMorphism :
  ∀ {StructureLawCore : Set}
  (socket : FormalLensLawSocket StructureLawCore) →
  invariantPreservedBySuppliedMorphism (socketInvariantSurface socket) ≡ true
lawInvariantPreservedOnlyBySuppliedMorphism socket =
  invariantPreservedBySuppliedMorphismIsTrue (socketInvariantReceipt socket)

lawSurfaceAuthorityBoundaryClosed :
  ∀ {StructureLawCore : Set}
  (socket : FormalLensLawSocket StructureLawCore) →
  Authority.promotesAnyAuthority (socketAuthorityBundle socket) ≡ false
lawSurfaceAuthorityBoundaryClosed socket =
  authorityBundlePromotesAnyAuthorityIsFalse
    (socketAuthorityBoundaryReceipt socket)

lawSurfaceGenericReceiptNonPromoting :
  ∀ {StructureLawCore : Set}
  (socket : FormalLensLawSocket StructureLawCore) →
  GenericReceipt.promotesClaim (socketGenericReceipt socket) ≡ false
lawSurfaceGenericReceiptNonPromoting socket =
  GenericReceipt.receiptIsNonPromoting (socketGenericReceipt socket)

-- Canonical socket building blocks.

canonicalCarrierSurface :
  FormalLensLawCarrierSurface
canonicalCarrierSurface =
  mkFormalLensLawCarrierSurface
    "formal lens law carrier"
    "DASHI.Core.FormalLensLawCore"
    "canonicalCarrierSurface"
    (styleVocabularyKinds statisticalStyle)
    (styleVocabularyKindCount statisticalStyle)
    true
    false

canonicalCarrierReceipt :
  FormalLensLawCarrierReceipt canonicalCarrierSurface
canonicalCarrierReceipt =
  mkFormalLensLawCarrierReceipt refl refl refl

canonicalStructureSurface :
  FormalLensLawStructureSurface String
canonicalStructureSurface =
  mkFormalLensLawStructureSurface
    "formal lens law structure"
    "DASHI.Core.FormalLensLawCore"
    "canonicalStructureSurface"
    canonicalCarrierSurface
    canonicalCarrierReceipt
    "FormalStructureLawCore"
    true
    false
    false

canonicalStructureReceipt :
  FormalLensLawStructureReceipt canonicalStructureSurface
canonicalStructureReceipt =
  mkFormalLensLawStructureReceipt refl refl refl

canonicalLawSurface :
  FormalLensLawSurface String
canonicalLawSurface =
  mkFormalLensLawSurface
    "formal lens law"
    "DASHI.Core.FormalLensLawCore"
    "canonicalLawSurface"
    statisticalStyle
    canonicalStatisticalStyleVocabularyKinds
    canonicalStatisticalStyleVocabularyKindCount
    canonicalStructureSurface
    Lens.canonicalGenericFormalLensQualificationSurface
    Lens.canonicalGenericFormalLensQualificationReceipt
    canonicalCarrierSurface
    canonicalCarrierReceipt
    true
    false
    false

canonicalLawReceipt :
  FormalLensLawReceipt canonicalLawSurface
canonicalLawReceipt =
  mkFormalLensLawReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalInvariantSurface :
  FormalLensLawInvariantSurface String
canonicalInvariantSurface =
  mkFormalLensLawInvariantSurface
    "formal lens law invariant"
    "DASHI.Core.FormalLensLawCore"
    "canonicalInvariantSurface"
    canonicalLawSurface
    true
    false
    true

canonicalInvariantReceipt :
  FormalLensLawInvariantReceipt canonicalInvariantSurface
canonicalInvariantReceipt =
  mkFormalLensLawInvariantReceipt refl refl refl

canonicalMorphismSurface :
  FormalLensLawMorphismSurface String
canonicalMorphismSurface =
  mkFormalLensLawMorphismSurface
    "formal lens law morphism"
    "DASHI.Core.FormalLensLawCore"
    "canonicalMorphismSurface"
    canonicalLawSurface
    canonicalLawSurface
    "morphism witness"
    true
    false
    true

canonicalMorphismReceipt :
  FormalLensLawMorphismReceipt canonicalMorphismSurface
canonicalMorphismReceipt =
  mkFormalLensLawMorphismReceipt refl refl refl

canonicalQualificationSurface :
  FormalLensLawQualificationSurface String
canonicalQualificationSurface =
  mkFormalLensLawQualificationSurface
    "formal lens law qualification"
    "DASHI.Core.FormalLensLawCore"
    "canonicalQualificationSurface"
    canonicalLawSurface
    Lens.canonicalGenericFormalLensQualificationSurface
    Lens.canonicalGenericFormalLensQualificationReceipt
    true
    false
    false

canonicalQualificationReceipt :
  FormalLensLawQualificationReceipt canonicalQualificationSurface
canonicalQualificationReceipt =
  mkFormalLensLawQualificationReceipt refl refl refl refl refl

canonicalAuthorityBoundarySurface :
  FormalLensLawAuthorityBoundarySurface String
canonicalAuthorityBoundarySurface =
  mkFormalLensLawAuthorityBoundarySurface
    "formal lens law authority boundary"
    "DASHI.Core.FormalLensLawCore"
    "canonicalAuthorityBoundarySurface"
    canonicalLawSurface
    Authority.canonicalAuthorityNonPromotionBundle
    true
    false
    false

canonicalAuthorityBoundaryReceipt :
  FormalLensLawAuthorityBoundaryReceipt canonicalAuthorityBoundarySurface
canonicalAuthorityBoundaryReceipt =
  mkFormalLensLawAuthorityBoundaryReceipt refl refl refl refl

canonicalFormalLensLawGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalFormalLensLawGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "formal lens law socket"
    "DASHI.Core.FormalLensLawCore"
    "canonicalFormalLensLawSocket"
    "formal lens law sockets stay candidate-only, qualify lens surfaces, and block authority promotion"
    "the structure-law attachment point is optional and future consumers can refine it separately"
    "agda -i . DASHI/Core/FormalLensLawCore.agda"

canonicalFormalLensLawSocket :
  FormalLensLawSocket String
canonicalFormalLensLawSocket =
  mkFormalLensLawSocket
    "formal lens law socket"
    "DASHI.Core.FormalLensLawCore"
    "canonicalFormalLensLawSocket"
    statisticalStyle
    canonicalCarrierSurface
    canonicalCarrierReceipt
    canonicalStructureSurface
    canonicalStructureReceipt
    canonicalLawSurface
    canonicalLawReceipt
    canonicalInvariantSurface
    canonicalInvariantReceipt
    canonicalMorphismSurface
    canonicalMorphismReceipt
    canonicalQualificationSurface
    canonicalQualificationReceipt
    canonicalAuthorityBoundarySurface
    canonicalAuthorityBoundaryReceipt
    canonicalFormalLensLawGenericReceipt

canonicalFormalLensLawSocketCompatibilityReceipt :
  FormalLensLawCompatibilityReceipt (socketStyle canonicalFormalLensLawSocket)
canonicalFormalLensLawSocketCompatibilityReceipt =
  mkCanonicalFormalLensLawCompatibilityReceipt
    (socketStyle canonicalFormalLensLawSocket)

------------------------------------------------------------------------
-- Style-specific compatibility receipts.

statisticalFormalLensLawCompatibilityReceipt :
  FormalLensLawCompatibilityReceipt statisticalStyle
statisticalFormalLensLawCompatibilityReceipt =
  mkCanonicalFormalLensLawCompatibilityReceipt statisticalStyle

projectionFingerprintHiddenLiftFormalLensLawCompatibilityReceipt :
  FormalLensLawCompatibilityReceipt projectionFingerprintHiddenLiftStyle
projectionFingerprintHiddenLiftFormalLensLawCompatibilityReceipt =
  mkFormalLensLawCompatibilityReceipt
    canonicalProjectionFingerprintHiddenLiftStyleVocabularyKinds
    refl
    canonicalProjectionFingerprintHiddenLiftStyleVocabularyKindCount
    refl
    true
    refl
    false
    refl
    false
    refl

cryptographicFormalLensLawCompatibilityReceipt :
  FormalLensLawCompatibilityReceipt cryptographicStyle
cryptographicFormalLensLawCompatibilityReceipt =
  mkFormalLensLawCompatibilityReceipt
    canonicalCryptographicStyleVocabularyKinds
    refl
    canonicalCryptographicStyleVocabularyKindCount
    refl
    true
    refl
    false
    refl
    false
    refl

numberResidueFormalLensLawCompatibilityReceipt :
  FormalLensLawCompatibilityReceipt numberResidueStyle
numberResidueFormalLensLawCompatibilityReceipt =
  mkFormalLensLawCompatibilityReceipt
    canonicalNumberResidueStyleVocabularyKinds
    refl
    canonicalNumberResidueStyleVocabularyKindCount
    refl
    true
    refl
    false
    refl
    false
    refl

graphFormalLensLawCompatibilityReceipt :
  FormalLensLawCompatibilityReceipt graphStyle
graphFormalLensLawCompatibilityReceipt =
  mkFormalLensLawCompatibilityReceipt
    canonicalGraphStyleVocabularyKinds
    refl
    canonicalGraphStyleVocabularyKindCount
    refl
    true
    refl
    false
    refl
    false
    refl

productVectorFormalLensLawCompatibilityReceipt :
  FormalLensLawCompatibilityReceipt productVectorStyle
productVectorFormalLensLawCompatibilityReceipt =
  mkFormalLensLawCompatibilityReceipt
    canonicalProductVectorStyleVocabularyKinds
    refl
    canonicalProductVectorStyleVocabularyKindCount
    refl
    true
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Public compatibility projections.

formalLensLawQualificationReceiptCandidateOnlyIsTrue :
  ∀ {StructureLawCore : Set}
  (surface : FormalLensLawQualificationSurface StructureLawCore) →
  FormalLensLawQualificationReceipt surface →
  qualificationCandidateOnly surface ≡ true
formalLensLawQualificationReceiptCandidateOnlyIsTrue surface receipt =
  qualificationCandidateOnlyIsTrue receipt

formalLensLawQualificationReceiptPromotedIsFalse :
  ∀ {StructureLawCore : Set}
  (surface : FormalLensLawQualificationSurface StructureLawCore) →
  FormalLensLawQualificationReceipt surface →
  qualificationPromoted surface ≡ false
formalLensLawQualificationReceiptPromotedIsFalse surface receipt =
  qualificationPromotedIsFalse receipt

formalLensLawAuthorityBoundaryReceiptClosed :
  ∀ {StructureLawCore : Set}
  (surface : FormalLensLawAuthorityBoundarySurface StructureLawCore) →
  FormalLensLawAuthorityBoundaryReceipt surface →
  Authority.promotesAnyAuthority (authorityBundle surface) ≡ false
formalLensLawAuthorityBoundaryReceiptClosed surface receipt =
  authorityBundlePromotesAnyAuthorityIsFalse receipt
