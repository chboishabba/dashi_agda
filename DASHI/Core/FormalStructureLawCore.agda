module DASHI.Core.FormalStructureLawCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.FormalLensQualificationCore as Lens
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Generic formal-structure law substrate.
--
-- This module keeps the law-bearing vocabulary candidate-only and additive.
-- It records structural surfaces for finite samples, vectors/products,
-- coordinate projections, equivalence relations, quotient/fiber projections,
-- canonical encodings, and residue systems.  The receipts here do not grant
-- semantic, domain, representation, statistic, projection, digest, or
-- coordinate-model authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

unaryNatEncode : Nat → List Nat
unaryNatEncode n =
  n ∷ []

unaryNatDecode : List Nat → Nat
unaryNatDecode [] =
  zero
unaryNatDecode (n ∷ _) =
  n

alwaysTrueRelation : ∀ {A : Set} → A → A → Bool
alwaysTrueRelation _ _ =
  true

------------------------------------------------------------------------
-- Shared vocabulary.

data FormalStructureLawKind : Set where
  finiteSampleLawKind :
    FormalStructureLawKind

  vectorProductLawKind :
    FormalStructureLawKind

  coordinateProjectionLawKind :
    FormalStructureLawKind

  equivalenceRelationLawKind :
    FormalStructureLawKind

  quotientFiberProjectionLawKind :
    FormalStructureLawKind

  canonicalEncodingLawKind :
    FormalStructureLawKind

  residueSystemLawKind :
    FormalStructureLawKind

  namedFormalStructureLawKind :
    String →
    FormalStructureLawKind

canonicalFormalStructureLawKinds :
  List FormalStructureLawKind
canonicalFormalStructureLawKinds =
  finiteSampleLawKind
  ∷ vectorProductLawKind
  ∷ coordinateProjectionLawKind
  ∷ equivalenceRelationLawKind
  ∷ quotientFiberProjectionLawKind
  ∷ canonicalEncodingLawKind
  ∷ residueSystemLawKind
  ∷ []

canonicalFormalStructureLawKindCount : Nat
canonicalFormalStructureLawKindCount =
  listCount canonicalFormalStructureLawKinds

------------------------------------------------------------------------
-- Shared authority boundary.

record FormalStructureAuthorityBoundary : Set where
  constructor mkFormalStructureAuthorityBoundary
  field
    representationAuthority :
      Bool

    statisticAuthority :
      Bool

    projectionAuthority :
      Bool

    digestAuthority :
      Bool

    coordinateModelAuthority :
      Bool

    semanticAuthority :
      Bool

    domainAuthority :
      Bool

    representationAuthorityIsFalse :
      representationAuthority ≡ false

    statisticAuthorityIsFalse :
      statisticAuthority ≡ false

    projectionAuthorityIsFalse :
      projectionAuthority ≡ false

    digestAuthorityIsFalse :
      digestAuthority ≡ false

    coordinateModelAuthorityIsFalse :
      coordinateModelAuthority ≡ false

    semanticAuthorityIsFalse :
      semanticAuthority ≡ false

    domainAuthorityIsFalse :
      domainAuthority ≡ false

canonicalFormalStructureAuthorityBoundary :
  FormalStructureAuthorityBoundary
canonicalFormalStructureAuthorityBoundary =
  mkFormalStructureAuthorityBoundary
    false
    false
    false
    false
    false
    false
    false
    refl
    refl
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Shared lens socket.

record FormalStructureLawSocket : Set where
  constructor mkFormalStructureLawSocket
  field
    socketLens :
      Lens.FormalLens

    socketRole :
      Lens.QualificationRole

    socketBoundary :
      Lens.ResidualBoundaryLabel

    socketStatement :
      String

    socketRemainingGap :
      String

    socketCandidateOnly :
      Bool

    socketPromoted :
      Bool

    socketCandidateOnlyIsTrue :
      socketCandidateOnly ≡ true

    socketPromotedIsFalse :
      socketPromoted ≡ false

    socketAuthorityBoundary :
      FormalStructureAuthorityBoundary

------------------------------------------------------------------------
-- Binary product helper.

record BinaryProduct (A B : Set) : Set where
  constructor pair
  field
    first :
      A

    second :
      B

binaryProductFirst :
  ∀ {A B : Set} →
  BinaryProduct A B →
  A
binaryProductFirst (pair a b) =
  a

binaryProductSecond :
  ∀ {A B : Set} →
  BinaryProduct A B →
  B
binaryProductSecond (pair a b) =
  b

------------------------------------------------------------------------
-- Finite samples.

record FiniteSampleLawSurface : Set₁ where
  constructor mkFiniteSampleLawSurface
  field
    sampleLabel :
      String

    sampleOwner :
      String

    sampleSurface :
      String

    sampleCarrier :
      Set

    sampleElements :
      List sampleCarrier

    sampleCount :
      Nat

    sampleCountIsCanonical :
      sampleCount ≡ listCount sampleElements

    sampleStatisticAvailable :
      Bool

    sampleStatisticAvailableIsTrue :
      sampleStatisticAvailable ≡ true

    sampleSocket :
      FormalStructureLawSocket

------------------------------------------------------------------------
-- Vector and product surfaces.

record VectorProductLawSurface : Set₁ where
  constructor mkVectorProductLawSurface
  field
    vectorLabel :
      String

    vectorOwner :
      String

    vectorSurface :
      String

    vectorCarrier :
      Set

    vectorCoordinates :
      List vectorCarrier

    vectorCoordinateCount :
      Nat

    vectorCoordinateCountIsCanonical :
      vectorCoordinateCount ≡ listCount vectorCoordinates

    productLeftCarrier :
      Set

    productRightCarrier :
      Set

    productWitness :
      BinaryProduct productLeftCarrier productRightCarrier

    productProjectionLeft :
      BinaryProduct productLeftCarrier productRightCarrier →
      productLeftCarrier

    productProjectionRight :
      BinaryProduct productLeftCarrier productRightCarrier →
      productRightCarrier

    productReconstruction :
      productLeftCarrier →
      productRightCarrier →
      BinaryProduct productLeftCarrier productRightCarrier

    productProjectionLeftByWitness :
      productProjectionLeft productWitness ≡
      binaryProductFirst productWitness

    productProjectionRightByWitness :
      productProjectionRight productWitness ≡
      binaryProductSecond productWitness

    vectorProductSocket :
      FormalStructureLawSocket

------------------------------------------------------------------------
-- Coordinate projections.

record CoordinateProjectionLawSurface : Set₁ where
  constructor mkCoordinateProjectionLawSurface
  field
    coordinateLabel :
      String

    coordinateOwner :
      String

    coordinateSurface :
      String

    coordinateSourceCarrier :
      Set

    coordinateTargetCarrier :
      Set

    coordinateProjection :
      coordinateSourceCarrier →
      coordinateTargetCarrier

    coordinateSuppliedSource :
      coordinateSourceCarrier

    coordinateSuppliedTarget :
      coordinateTargetCarrier

    coordinateProjectionByWitness :
      coordinateProjection coordinateSuppliedSource ≡
      coordinateSuppliedTarget

    coordinateReconstruction :
      coordinateTargetCarrier →
      coordinateSourceCarrier

    coordinateReconstructionByWitness :
      coordinateReconstruction coordinateSuppliedTarget ≡
      coordinateSuppliedSource

    projectionFiberMember :
      coordinateSourceCarrier

    projectionFiberImage :
      coordinateTargetCarrier

    projectionFiberMembership :
      coordinateProjection projectionFiberMember ≡
      projectionFiberImage

    coordinateProjectionSocket :
      FormalStructureLawSocket

------------------------------------------------------------------------
-- Equivalence relations.

record EquivalenceRelationLawSurface : Set₁ where
  constructor mkEquivalenceRelationLawSurface
  field
    equivalenceLabel :
      String

    equivalenceOwner :
      String

    equivalenceSurface :
      String

    equivalenceCarrier :
      Set

    equivalenceRelation :
      equivalenceCarrier →
      equivalenceCarrier →
      Bool

    equivalenceReflexive :
      ∀ x →
      equivalenceRelation x x ≡ true

    equivalenceSymmetric :
      ∀ x y →
      equivalenceRelation x y ≡ true →
      equivalenceRelation y x ≡ true

    equivalenceTransitive :
      ∀ x y z →
      equivalenceRelation x y ≡ true →
      equivalenceRelation y z ≡ true →
      equivalenceRelation x z ≡ true

    equivalenceSocket :
      FormalStructureLawSocket

------------------------------------------------------------------------
-- Quotient and fiber projections.

record QuotientFiberProjectionLawSurface : Set₁ where
  constructor mkQuotientFiberProjectionLawSurface
  field
    quotientLabel :
      String

    quotientOwner :
      String

    quotientSurface :
      String

    quotientSourceCarrier :
      Set

    quotientCarrier :
      Set

    quotientProjection :
      quotientSourceCarrier →
      quotientCarrier

    quotientFiberMember :
      quotientSourceCarrier

    quotientFiberImage :
      quotientCarrier

    quotientFiberMembership :
      quotientProjection quotientFiberMember ≡
      quotientFiberImage

    quotientEqualityBoundary :
      Bool

    quotientEqualityBoundaryIsFalse :
      quotientEqualityBoundary ≡ false

    quotientSocket :
      FormalStructureLawSocket

------------------------------------------------------------------------
-- Canonical encodings.

record CanonicalEncodingLawSurface : Set₁ where
  constructor mkCanonicalEncodingLawSurface
  field
    encodingLabel :
      String

    encodingOwner :
      String

    encodingSurface :
      String

    encodingCarrier :
      Set

    encodingRepresentation :
      Set

    canonicalEncode :
      encodingCarrier →
      encodingRepresentation

    canonicalDecode :
      encodingRepresentation →
      encodingCarrier

    encodingWitness :
      encodingCarrier

    encodedWitness :
      encodingRepresentation

    canonicalEncodingRoundTrip :
      canonicalDecode encodedWitness ≡
      encodingWitness

    canonicalEncodingWitnessMatch :
      canonicalEncode encodingWitness ≡
      encodedWitness

    canonicalEncodingSocket :
      FormalStructureLawSocket

------------------------------------------------------------------------
-- Residue systems.

record ResidueSystemLawSurface : Set₁ where
  constructor mkResidueSystemLawSurface
  field
    residueLabel :
      String

    residueOwner :
      String

    residueSurface :
      String

    residueCarrier :
      Set

    residueModulus :
      Nat

    residueProjection :
      residueCarrier →
      Nat

    residueCanonicalEncoding :
      residueCarrier →
      List Nat

    residueCanonicalDecoding :
      List Nat →
      residueCarrier

    residueWitness :
      residueCarrier

    residueEncodedWitness :
      List Nat

    residueProjectionByWitness :
      residueProjection residueWitness ≡
      unaryNatDecode residueEncodedWitness

    residueCanonicalRoundTrip :
      residueCanonicalDecoding residueEncodedWitness ≡
      residueWitness

    residueEncodingMatch :
      residueCanonicalEncoding residueWitness ≡
      residueEncodedWitness

    residueEqualityBoundary :
      Bool

    residueEqualityBoundaryIsFalse :
      residueEqualityBoundary ≡ false

    residueSocket :
      FormalStructureLawSocket

------------------------------------------------------------------------
-- Bundled substrate.

record FormalStructureLawSurface : Set₁ where
  constructor mkFormalStructureLawSurface
  field
    lawLabel :
      String

    lawOwner :
      String

    lawSurface :
      String

    lawLens :
      Lens.FormalLens

    lawRole :
      Lens.QualificationRole

    lawBoundary :
      Lens.ResidualBoundaryLabel

    lawSocket :
      FormalStructureLawSocket

    finiteSampleSurface :
      FiniteSampleLawSurface

    vectorProductSurface :
      VectorProductLawSurface

    coordinateProjectionSurface :
      CoordinateProjectionLawSurface

    equivalenceRelationSurface :
      EquivalenceRelationLawSurface

    quotientFiberProjectionSurface :
      QuotientFiberProjectionLawSurface

    canonicalEncodingSurface :
      CanonicalEncodingLawSurface

    residueSystemSurface :
      ResidueSystemLawSurface

    lawStatement :
      String

    lawRemainingGap :
      String

------------------------------------------------------------------------
-- Canonical shared boundary values.

canonicalFormalStructureLawSocketBoundary :
  Lens.ResidualBoundaryLabel
canonicalFormalStructureLawSocketBoundary =
  Lens.explicitResidualBoundary

canonicalFormalStructureLawSocket :
  FormalStructureLawSocket
canonicalFormalStructureLawSocket =
  mkFormalStructureLawSocket
    Lens.SymbolicRational
    Lens.sourceLensRole
    canonicalFormalStructureLawSocketBoundary
    "formal structure law socket"
    "representation, statistic, projection, digest, coordinate-model, semantic, and domain authority remain blocked"
    true
    false
    refl
    refl
    canonicalFormalStructureAuthorityBoundary

canonicalFiniteSampleLawSocket :
  FormalStructureLawSocket
canonicalFiniteSampleLawSocket =
  mkFormalStructureLawSocket
    Lens.Number
    Lens.thresholdWitnessRole
    Lens.explicitResidualBoundary
    "finite sample socket"
    "semantic and domain authority remain outside this candidate-only sample surface"
    true
    false
    refl
    refl
    canonicalFormalStructureAuthorityBoundary

canonicalVectorProductLawSocket :
  FormalStructureLawSocket
canonicalVectorProductLawSocket =
  mkFormalStructureLawSocket
    Lens.Operator
    Lens.sourceLensRole
    Lens.explicitOpenResidualBoundary
    "vector and product socket"
    "vector coordinates and binary products remain candidate-only shapes"
    true
    false
    refl
    refl
    canonicalFormalStructureAuthorityBoundary

canonicalCoordinateProjectionLawSocket :
  FormalStructureLawSocket
canonicalCoordinateProjectionLawSocket =
  mkFormalStructureLawSocket
    Lens.Functional
    Lens.sourceLensRole
    Lens.explicitBridgeResidualBoundary
    "coordinate projection socket"
    "projection and reconstruction are supplied as explicit witnesses only"
    true
    false
    refl
    refl
    canonicalFormalStructureAuthorityBoundary

canonicalEquivalenceRelationLawSocket :
  FormalStructureLawSocket
canonicalEquivalenceRelationLawSocket =
  mkFormalStructureLawSocket
    Lens.Group
    Lens.residualBoundaryRole
    Lens.explicitMissingThresholdResidualBoundary
    "equivalence relation socket"
    "reflexivity, symmetry, and transitivity are candidate relation receipts only"
    true
    false
    refl
    refl
    canonicalFormalStructureAuthorityBoundary

canonicalQuotientFiberProjectionLawSocket :
  FormalStructureLawSocket
canonicalQuotientFiberProjectionLawSocket =
  mkFormalStructureLawSocket
    Lens.ResistiveTransport
    Lens.targetLensRole
    Lens.explicitOpenResidualBoundary
    "quotient and fiber projection socket"
    "quotient equality remains a boundary and does not become semantic authority"
    true
    false
    refl
    refl
    canonicalFormalStructureAuthorityBoundary

canonicalCanonicalEncodingLawSocket :
  FormalStructureLawSocket
canonicalCanonicalEncodingLawSocket =
  mkFormalStructureLawSocket
    Lens.Information
    Lens.adapterConsumerRole
    Lens.explicitResidualBoundary
    "canonical encoding socket"
    "round-trips are only explicit witness receipts"
    true
    false
    refl
    refl
    canonicalFormalStructureAuthorityBoundary

canonicalResidueSystemLawSocket :
  FormalStructureLawSocket
canonicalResidueSystemLawSocket =
  mkFormalStructureLawSocket
    Lens.ResistiveTransport
    Lens.sourceLensRole
    Lens.explicitResidualBoundary
    "residue system socket"
    "residue projections stay candidate-only and do not promote domain authority"
    true
    false
    refl
    refl
    canonicalFormalStructureAuthorityBoundary

------------------------------------------------------------------------
-- Canonical surface values.

canonicalFiniteSampleLawSurface :
  FiniteSampleLawSurface
canonicalFiniteSampleLawSurface =
  mkFiniteSampleLawSurface
    "finite sample law"
    "DASHI.Core.FormalStructureLawCore"
    "canonicalFiniteSampleLawSurface"
    Nat
    (zero ∷ suc zero ∷ [])
    (suc (suc zero))
    refl
    true
    refl
    canonicalFiniteSampleLawSocket

canonicalVectorProductLawSurface :
  VectorProductLawSurface
canonicalVectorProductLawSurface =
  mkVectorProductLawSurface
    "vector product law"
    "DASHI.Core.FormalStructureLawCore"
    "canonicalVectorProductLawSurface"
    Nat
    (zero ∷ suc zero ∷ [])
    (suc (suc zero))
    refl
    Nat
    Nat
    (pair zero zero)
    binaryProductFirst
    binaryProductSecond
    (λ left right → pair left right)
    refl
    refl
    canonicalVectorProductLawSocket

canonicalCoordinateProjectionLawSurface :
  CoordinateProjectionLawSurface
canonicalCoordinateProjectionLawSurface =
  mkCoordinateProjectionLawSurface
    "coordinate projection law"
    "DASHI.Core.FormalStructureLawCore"
    "canonicalCoordinateProjectionLawSurface"
    Nat
    Nat
    (λ n → n)
    zero
    zero
    refl
    (λ n → n)
    refl
    zero
    zero
    refl
    canonicalCoordinateProjectionLawSocket

canonicalEquivalenceRelationLawSurface :
  EquivalenceRelationLawSurface
canonicalEquivalenceRelationLawSurface =
  mkEquivalenceRelationLawSurface
    "equivalence relation law"
    "DASHI.Core.FormalStructureLawCore"
    "canonicalEquivalenceRelationLawSurface"
    Nat
    alwaysTrueRelation
    (λ _ → refl)
    (λ _ _ _ → refl)
    (λ _ _ _ _ _ → refl)
    canonicalEquivalenceRelationLawSocket

canonicalQuotientFiberProjectionLawSurface :
  QuotientFiberProjectionLawSurface
canonicalQuotientFiberProjectionLawSurface =
  mkQuotientFiberProjectionLawSurface
    "quotient fiber projection law"
    "DASHI.Core.FormalStructureLawCore"
    "canonicalQuotientFiberProjectionLawSurface"
    Nat
    Nat
    (λ _ → zero)
    zero
    zero
    refl
    false
    refl
    canonicalQuotientFiberProjectionLawSocket

canonicalCanonicalEncodingLawSurface :
  CanonicalEncodingLawSurface
canonicalCanonicalEncodingLawSurface =
  mkCanonicalEncodingLawSurface
    "canonical encoding law"
    "DASHI.Core.FormalStructureLawCore"
    "canonicalCanonicalEncodingLawSurface"
    Nat
    (List Nat)
    unaryNatEncode
    unaryNatDecode
    zero
    (zero ∷ [])
    refl
    refl
    canonicalCanonicalEncodingLawSocket

canonicalResidueSystemLawSurface :
  ResidueSystemLawSurface
canonicalResidueSystemLawSurface =
  mkResidueSystemLawSurface
    "residue system law"
    "DASHI.Core.FormalStructureLawCore"
    "canonicalResidueSystemLawSurface"
    Nat
    (suc (suc zero))
    (λ n → n)
    unaryNatEncode
    unaryNatDecode
    zero
    (zero ∷ [])
    refl
    refl
    refl
    false
    refl
    canonicalResidueSystemLawSocket

canonicalFormalStructureLawSurface :
  FormalStructureLawSurface
canonicalFormalStructureLawSurface =
  mkFormalStructureLawSurface
    "formal structure law"
    "DASHI.Core.FormalStructureLawCore"
    "canonicalFormalStructureLawSurface"
    Lens.SymbolicRational
    Lens.sourceLensRole
    Lens.explicitResidualBoundary
    canonicalFormalStructureLawSocket
    canonicalFiniteSampleLawSurface
    canonicalVectorProductLawSurface
    canonicalCoordinateProjectionLawSurface
    canonicalEquivalenceRelationLawSurface
    canonicalQuotientFiberProjectionLawSurface
    canonicalCanonicalEncodingLawSurface
    canonicalResidueSystemLawSurface
    "formal structure law records candidate-only structural sockets, witnesses, and non-promoting boundaries"
    "semantic, domain, representation, statistic, projection, digest, and coordinate-model authority remain blocked"

------------------------------------------------------------------------
-- Generic receipt.

canonicalFormalStructureLawGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalFormalStructureLawGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "formal structure law core"
    "DASHI.Core.FormalStructureLawCore"
    "canonicalFormalStructureLawSurface"
    "candidate-only structural law surfaces, sockets, and witness receipts are centralized here"
    "semantic, domain, representation, statistic, projection, digest, and coordinate-model authority remain blocked"
    "agda -i . DASHI/Core/FormalStructureLawCore.agda"
