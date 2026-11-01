module DASHI.Physics.QFT.FibreFunctorFaithfulnessReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.U1CMOrbitIntegralReceipt as U1CM
import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional
import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as Ledger
import DASHI.Physics.QFT.TannakaKreinFibreFunctorReceipt as Tannaka

------------------------------------------------------------------------
-- Finite fibre-functor faithfulness/separability receipt.
--
-- This receipt is deliberately finite.  It separates only the enumerated
-- rho_p2, rho_p3, and rho_p5 prime-lane sectors using lane invariants that
-- are already finite data: Frobenius-prime labels, the p2 CM conductor-four
-- receipt, finite Hilbert dimensions, and SM-row labels.  It does not claim a
-- faithful exact fibre functor on the full arbitrary DHR category and does
-- not promote G_DHR ~= G_SM.

data FiniteFibreSector : Set where
  rho-p2 :
    FiniteFibreSector

  rho-p3 :
    FiniteFibreSector

  rho-p5 :
    FiniteFibreSector

finiteFibreSectorRow :
  FiniteFibreSector →
  Ledger.FinitePrimeLaneSMRow
finiteFibreSectorRow rho-p2 =
  Ledger.p2U1YFinitePrimeLaneSMRow
finiteFibreSectorRow rho-p3 =
  Ledger.p3SU2LFinitePrimeLaneSMRow
finiteFibreSectorRow rho-p5 =
  Ledger.p5SU3cFinitePrimeLaneSMRow

finiteFibreSectorDimension :
  FiniteFibreSector →
  Nat
finiteFibreSectorDimension rho-p2 =
  1
finiteFibreSectorDimension rho-p3 =
  2
finiteFibreSectorDimension rho-p5 =
  3

finiteFibreSectorFrobeniusPrimeLabel :
  FiniteFibreSector →
  Nat
finiteFibreSectorFrobeniusPrimeLabel rho-p2 =
  2
finiteFibreSectorFrobeniusPrimeLabel rho-p3 =
  3
finiteFibreSectorFrobeniusPrimeLabel rho-p5 =
  5

finiteFibreSectorCMConductorLabel :
  FiniteFibreSector →
  Nat
finiteFibreSectorCMConductorLabel rho-p2 =
  4
finiteFibreSectorCMConductorLabel rho-p3 =
  3
finiteFibreSectorCMConductorLabel rho-p5 =
  7

finiteFibreSectorGaugeLabel :
  FiniteFibreSector →
  String
finiteFibreSectorGaugeLabel rho-p2 =
  "U1Y"
finiteFibreSectorGaugeLabel rho-p3 =
  "SU2L"
finiteFibreSectorGaugeLabel rho-p5 =
  "SU3c"

canonicalFiniteFibreSectors :
  List FiniteFibreSector
canonicalFiniteFibreSectors =
  rho-p2
  ∷ rho-p3
  ∷ rho-p5
  ∷ []

data FibreLaneInvariantKind : Set where
  frobeniusPrimeLaneInvariant :
    FibreLaneInvariantKind

  cmConductorLaneInvariant :
    FibreLaneInvariantKind

  finiteHilbertDimensionInvariant :
    FibreLaneInvariantKind

  standardModelRowLabelInvariant :
    FibreLaneInvariantKind

canonicalFibreLaneInvariantKinds :
  List FibreLaneInvariantKind
canonicalFibreLaneInvariantKinds =
  frobeniusPrimeLaneInvariant
  ∷ cmConductorLaneInvariant
  ∷ finiteHilbertDimensionInvariant
  ∷ standardModelRowLabelInvariant
  ∷ []

record FiniteFibreLaneInvariantSignature : Set where
  field
    sector :
      FiniteFibreSector

    ledgerRow :
      Ledger.FinitePrimeLaneSMRow

    ledgerRowIsSectorRow :
      ledgerRow ≡ finiteFibreSectorRow sector

    frobeniusPrimeLabel :
      Nat

    frobeniusPrimeLabelIsSectorLabel :
      frobeniusPrimeLabel
      ≡
      finiteFibreSectorFrobeniusPrimeLabel sector

    cmConductorLabel :
      Nat

    cmConductorLabelIsSectorLabel :
      cmConductorLabel
      ≡
      finiteFibreSectorCMConductorLabel sector

    hilbertDimension :
      Nat

    hilbertDimensionIsSectorDimension :
      hilbertDimension
      ≡
      finiteFibreSectorDimension sector

    gaugeLabel :
      String

    gaugeLabelIsSectorLabel :
      gaugeLabel
      ≡
      finiteFibreSectorGaugeLabel sector

    signatureBoundary :
      List String

open FiniteFibreLaneInvariantSignature public

p2FiniteFibreLaneInvariantSignature :
  FiniteFibreLaneInvariantSignature
p2FiniteFibreLaneInvariantSignature =
  record
    { sector =
        rho-p2
    ; ledgerRow =
        Ledger.p2U1YFinitePrimeLaneSMRow
    ; ledgerRowIsSectorRow =
        refl
    ; frobeniusPrimeLabel =
        2
    ; frobeniusPrimeLabelIsSectorLabel =
        refl
    ; cmConductorLabel =
        4
    ; cmConductorLabelIsSectorLabel =
        refl
    ; hilbertDimension =
        1
    ; hilbertDimensionIsSectorDimension =
        refl
    ; gaugeLabel =
        "U1Y"
    ; gaugeLabelIsSectorLabel =
        refl
    ; signatureBoundary =
        "rho_p2 is separated by Frobenius prime label 2, CM conductor 4, fibre dimension 1, and U1Y row label"
        ∷ "The conductor-four value is the finite p2 Gaussian-CM lane invariant consumed from U1CMOrbitIntegralReceipt"
        ∷ []
    }

p3FiniteFibreLaneInvariantSignature :
  FiniteFibreLaneInvariantSignature
p3FiniteFibreLaneInvariantSignature =
  record
    { sector =
        rho-p3
    ; ledgerRow =
        Ledger.p3SU2LFinitePrimeLaneSMRow
    ; ledgerRowIsSectorRow =
        refl
    ; frobeniusPrimeLabel =
        3
    ; frobeniusPrimeLabelIsSectorLabel =
        refl
    ; cmConductorLabel =
        3
    ; cmConductorLabelIsSectorLabel =
        refl
    ; hilbertDimension =
        2
    ; hilbertDimensionIsSectorDimension =
        refl
    ; gaugeLabel =
        "SU2L"
    ; gaugeLabelIsSectorLabel =
        refl
    ; signatureBoundary =
        "rho_p3 is separated by Frobenius prime label 3, CM/lane label 3, fibre dimension 2, and SU2L row label"
        ∷ "This is finite row separation only, not a full SU2 representation-category equivalence"
        ∷ []
    }

p5FiniteFibreLaneInvariantSignature :
  FiniteFibreLaneInvariantSignature
p5FiniteFibreLaneInvariantSignature =
  record
    { sector =
        rho-p5
    ; ledgerRow =
        Ledger.p5SU3cFinitePrimeLaneSMRow
    ; ledgerRowIsSectorRow =
        refl
    ; frobeniusPrimeLabel =
        5
    ; frobeniusPrimeLabelIsSectorLabel =
        refl
    ; cmConductorLabel =
        7
    ; cmConductorLabelIsSectorLabel =
        refl
    ; hilbertDimension =
        3
    ; hilbertDimensionIsSectorDimension =
        refl
    ; gaugeLabel =
        "SU3c"
    ; gaugeLabelIsSectorLabel =
        refl
    ; signatureBoundary =
        "rho_p5 is separated by Frobenius prime label 5, corrected Heegner CM conductor 7, fibre dimension 3, and SU3c row label"
        ∷ "This is finite row separation only, not a full SU3 representation-category equivalence"
        ∷ []
    }

data FiniteFibreSectorPair : Set where
  rho-p2-rho-p3 :
    FiniteFibreSectorPair

  rho-p2-rho-p5 :
    FiniteFibreSectorPair

  rho-p3-rho-p5 :
    FiniteFibreSectorPair

canonicalFiniteFibreSectorPairs :
  List FiniteFibreSectorPair
canonicalFiniteFibreSectorPairs =
  rho-p2-rho-p3
  ∷ rho-p2-rho-p5
  ∷ rho-p3-rho-p5
  ∷ []

data FiniteFibrePairSeparationWitness : Set where
  separatedByFrobeniusPrimeAndDimension :
    FiniteFibrePairSeparationWitness

  separatedByFrobeniusPrimeAndCMConductor :
    FiniteFibrePairSeparationWitness

finiteFibrePairSeparationWitness :
  FiniteFibreSectorPair →
  FiniteFibrePairSeparationWitness
finiteFibrePairSeparationWitness rho-p2-rho-p3 =
  separatedByFrobeniusPrimeAndDimension
finiteFibrePairSeparationWitness rho-p2-rho-p5 =
  separatedByFrobeniusPrimeAndCMConductor
finiteFibrePairSeparationWitness rho-p3-rho-p5 =
  separatedByFrobeniusPrimeAndDimension

record FinitePrimeLaneFibreSeparationReceipt : Setω where
  field
    p2Signature :
      FiniteFibreLaneInvariantSignature

    p2SignatureIsCanonical :
      p2Signature ≡ p2FiniteFibreLaneInvariantSignature

    p3Signature :
      FiniteFibreLaneInvariantSignature

    p3SignatureIsCanonical :
      p3Signature ≡ p3FiniteFibreLaneInvariantSignature

    p5Signature :
      FiniteFibreLaneInvariantSignature

    p5SignatureIsCanonical :
      p5Signature ≡ p5FiniteFibreLaneInvariantSignature

    separatedPairs :
      List FiniteFibreSectorPair

    separatedPairsAreCanonical :
      separatedPairs ≡ canonicalFiniteFibreSectorPairs

    invariantKinds :
      List FibreLaneInvariantKind

    invariantKindsAreCanonical :
      invariantKinds ≡ canonicalFibreLaneInvariantKinds

    p2p3Separation :
      FiniteFibrePairSeparationWitness

    p2p3SeparationIsCanonical :
      p2p3Separation
      ≡
      finiteFibrePairSeparationWitness rho-p2-rho-p3

    p2p5Separation :
      FiniteFibrePairSeparationWitness

    p2p5SeparationIsCanonical :
      p2p5Separation
      ≡
      finiteFibrePairSeparationWitness rho-p2-rho-p5

    p3p5Separation :
      FiniteFibrePairSeparationWitness

    p3p5SeparationIsCanonical :
      p3p5Separation
      ≡
      finiteFibrePairSeparationWitness rho-p3-rho-p5

    finitePrimeLaneSeparated :
      Bool

    finitePrimeLaneSeparatedIsTrue :
      finitePrimeLaneSeparated ≡ true

    arbitraryDHRSeparationPromoted :
      Bool

    arbitraryDHRSeparationPromotedIsFalse :
      arbitraryDHRSeparationPromoted ≡ false

    separationBoundary :
      List String

open FinitePrimeLaneFibreSeparationReceipt public

canonicalFinitePrimeLaneFibreSeparationReceipt :
  FinitePrimeLaneFibreSeparationReceipt
canonicalFinitePrimeLaneFibreSeparationReceipt =
  record
    { p2Signature =
        p2FiniteFibreLaneInvariantSignature
    ; p2SignatureIsCanonical =
        refl
    ; p3Signature =
        p3FiniteFibreLaneInvariantSignature
    ; p3SignatureIsCanonical =
        refl
    ; p5Signature =
        p5FiniteFibreLaneInvariantSignature
    ; p5SignatureIsCanonical =
        refl
    ; separatedPairs =
        canonicalFiniteFibreSectorPairs
    ; separatedPairsAreCanonical =
        refl
    ; invariantKinds =
        canonicalFibreLaneInvariantKinds
    ; invariantKindsAreCanonical =
        refl
    ; p2p3Separation =
        separatedByFrobeniusPrimeAndDimension
    ; p2p3SeparationIsCanonical =
        refl
    ; p2p5Separation =
        separatedByFrobeniusPrimeAndCMConductor
    ; p2p5SeparationIsCanonical =
        refl
    ; p3p5Separation =
        separatedByFrobeniusPrimeAndDimension
    ; p3p5SeparationIsCanonical =
        refl
    ; finitePrimeLaneSeparated =
        true
    ; finitePrimeLaneSeparatedIsTrue =
        refl
    ; arbitraryDHRSeparationPromoted =
        false
    ; arbitraryDHRSeparationPromotedIsFalse =
        refl
    ; separationBoundary =
        "The finite p2, p3, and p5 fibre sectors have pairwise distinct invariant signatures"
        ∷ "The signatures use finite Frobenius prime labels, the p2 CM conductor-four lane invariant, finite fibre dimensions, and ledger row labels"
        ∷ "This proves only enumerated finite prime-lane separability"
        ∷ "No arbitrary transportable DHR sector separation theorem is promoted"
        ∷ []
    }

data FibreFunctorFaithfulnessBlocker : Set where
  missingFullArbitraryDHRObjectClass :
    FibreFunctorFaithfulnessBlocker

  missingExactFibreFunctorOnAllMorphisms :
    FibreFunctorFaithfulnessBlocker

  missingKernelReflectionForArbitraryIntertwiners :
    FibreFunctorFaithfulnessBlocker

  missingDoplicherRobertsAutTensorConstruction :
    FibreFunctorFaithfulnessBlocker

  missingExactGDHRToGSMIdentification :
    FibreFunctorFaithfulnessBlocker

canonicalFibreFunctorFaithfulnessBlockers :
  List FibreFunctorFaithfulnessBlocker
canonicalFibreFunctorFaithfulnessBlockers =
  missingFullArbitraryDHRObjectClass
  ∷ missingExactFibreFunctorOnAllMorphisms
  ∷ missingKernelReflectionForArbitraryIntertwiners
  ∷ missingDoplicherRobertsAutTensorConstruction
  ∷ missingExactGDHRToGSMIdentification
  ∷ []

record FibreFunctorFaithfulnessReceipt : Setω where
  field
    tannakaFibreFunctorReceipt :
      Tannaka.TannakaKreinFibreFunctorReceipt

    conditionalGDHRSMPromotionReceipt :
      Conditional.ConditionalGDHRSMPromotionReceipt

    p2CMOrbitIntegralReceipt :
      U1CM.U1CMOrbitIntegralReceipt

    p2CMConductorFourConsumed :
      U1CM.p2LaneConductor p2CMOrbitIntegralReceipt ≡ 4

    finiteFibreFunctorRecorded :
      Tannaka.finiteFibreFunctorRecorded tannakaFibreFunctorReceipt
      ≡
      true

    tannakaDualGroupStillNotConstructed :
      Tannaka.tannakaDualGroupConstructed tannakaFibreFunctorReceipt
      ≡
      false

    conditionalPromotionStillNotUnconditional :
      Conditional.unconditionalGDHREqualsGSMPromoted
        conditionalGDHRSMPromotionReceipt
      ≡
      false

    finiteSeparationReceipt :
      FinitePrimeLaneFibreSeparationReceipt

    finiteSeparationReceiptCanonicalSelected :
      Bool

    finiteSeparationReceiptCanonicalSelectedIsTrue :
      finiteSeparationReceiptCanonicalSelected ≡ true

    finitePrimeLaneSeparated :
      Bool

    finitePrimeLaneSeparatedIsTrue :
      finitePrimeLaneSeparated ≡ true

    finitePrimeLaneFaithfulOnEnumeratedObjects :
      Bool

    finitePrimeLaneFaithfulOnEnumeratedObjectsIsTrue :
      finitePrimeLaneFaithfulOnEnumeratedObjects ≡ true

    faithfulExactFibreFunctorOnFullArbitraryDHRCategory :
      Bool

    faithfulExactFibreFunctorOnFullArbitraryDHRCategoryIsFalse :
      faithfulExactFibreFunctorOnFullArbitraryDHRCategory ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    blockers :
      List FibreFunctorFaithfulnessBlocker

    blockersAreCanonical :
      blockers ≡ canonicalFibreFunctorFaithfulnessBlockers

    receiptBoundary :
      List String

open FibreFunctorFaithfulnessReceipt public

canonicalFibreFunctorFaithfulnessReceipt :
  FibreFunctorFaithfulnessReceipt
canonicalFibreFunctorFaithfulnessReceipt =
  record
    { tannakaFibreFunctorReceipt =
        Tannaka.canonicalTannakaKreinFibreFunctorReceipt
    ; conditionalGDHRSMPromotionReceipt =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; p2CMOrbitIntegralReceipt =
        U1CM.canonicalU1CMOrbitIntegralReceipt
    ; p2CMConductorFourConsumed =
        refl
    ; finiteFibreFunctorRecorded =
        refl
    ; tannakaDualGroupStillNotConstructed =
        refl
    ; conditionalPromotionStillNotUnconditional =
        refl
    ; finiteSeparationReceipt =
        canonicalFinitePrimeLaneFibreSeparationReceipt
    ; finiteSeparationReceiptCanonicalSelected =
        true
    ; finiteSeparationReceiptCanonicalSelectedIsTrue =
        refl
    ; finitePrimeLaneSeparated =
        true
    ; finitePrimeLaneSeparatedIsTrue =
        refl
    ; finitePrimeLaneFaithfulOnEnumeratedObjects =
        true
    ; finitePrimeLaneFaithfulOnEnumeratedObjectsIsTrue =
        refl
    ; faithfulExactFibreFunctorOnFullArbitraryDHRCategory =
        false
    ; faithfulExactFibreFunctorOnFullArbitraryDHRCategoryIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; blockers =
        canonicalFibreFunctorFaithfulnessBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "Finite fibre-functor faithfulness is recorded only as object separation on rho_p2, rho_p3, and rho_p5"
        ∷ "The separating invariants are finite Frobenius prime labels, the p2 CM conductor-four invariant, finite Hilbert dimensions, and finite ledger row labels"
        ∷ "The existing Tannaka receipt still records only a finite fibre functor and keeps the dual group unconstructed"
        ∷ "The existing conditional G_DHR/SM receipt remains non-unconditional"
        ∷ "Faithful exact fibre functor on the full arbitrary DHR category remains false"
        ∷ "gDHREqualsGSMPromoted remains false"
        ∷ []
    }

finitePrimeLaneFibreSeparated :
  finitePrimeLaneSeparated canonicalFibreFunctorFaithfulnessReceipt
  ≡
  true
finitePrimeLaneFibreSeparated =
  refl

finitePrimeLaneFibreFaithfulOnEnumeratedObjects :
  finitePrimeLaneFaithfulOnEnumeratedObjects
    canonicalFibreFunctorFaithfulnessReceipt
  ≡
  true
finitePrimeLaneFibreFaithfulOnEnumeratedObjects =
  refl

fullArbitraryDHRFaithfulExactFibreFunctorStillFalse :
  faithfulExactFibreFunctorOnFullArbitraryDHRCategory
    canonicalFibreFunctorFaithfulnessReceipt
  ≡
  false
fullArbitraryDHRFaithfulExactFibreFunctorStillFalse =
  refl

gDHREqualsGSMPromotionStillFalse :
  gDHREqualsGSMPromoted canonicalFibreFunctorFaithfulnessReceipt
  ≡
  false
gDHREqualsGSMPromotionStillFalse =
  refl
