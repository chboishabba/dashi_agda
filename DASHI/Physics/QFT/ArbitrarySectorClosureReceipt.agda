module DASHI.Physics.QFT.ArbitrarySectorClosureReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional
import DASHI.Physics.QFT.FinitePrimeLaneConjugateDualReceipts as Conjugate
import DASHI.Physics.QFT.FinitePrimeLaneTensorFusionReceipts as TensorFusion
import DASHI.Physics.QFT.Gate6FinitePrimeLaneLocalEndomorphismCategory as Local

------------------------------------------------------------------------
-- Arbitrary-sector DHR closure frontier.
--
-- The finite p2/p3/p5 DHR package is inhabited and the conditional authority
-- receipt is present.  This module records the stronger arbitrary-sector
-- closure theorem needed before an unconditional G_DHR ~= G_SM promotion can
-- even be attempted.

data ArbitrarySectorClosureBlocker : Set where
  missingClosureUnderArbitraryDirectSums :
    ArbitrarySectorClosureBlocker

  missingClosureUnderArbitraryTensorProducts :
    ArbitrarySectorClosureBlocker

  missingConjugatesForArbitraryTransportableEndomorphisms :
    ArbitrarySectorClosureBlocker

  missingFaithfulExactFibreFunctorOnFullCategory :
    ArbitrarySectorClosureBlocker

  missingRepresentationRingStandardModelMatch :
    ArbitrarySectorClosureBlocker

  missingConcreteInterLaneNonabelianMorphisms :
    ArbitrarySectorClosureBlocker

canonicalArbitrarySectorClosureBlockers :
  List ArbitrarySectorClosureBlocker
canonicalArbitrarySectorClosureBlockers =
  missingClosureUnderArbitraryDirectSums
  ∷ missingClosureUnderArbitraryTensorProducts
  ∷ missingConjugatesForArbitraryTransportableEndomorphisms
  ∷ missingFaithfulExactFibreFunctorOnFullCategory
  ∷ missingRepresentationRingStandardModelMatch
  ∷ missingConcreteInterLaneNonabelianMorphisms
  ∷ []

carrierDHRGroupConjectureLabel : String
carrierDHRGroupConjectureLabel =
  "The finite prime-lane sector package suggests a DHR dual targeting U(1) x SU(2) x SU(3), but exact G_DHR ~= G_SM requires arbitrary-sector closure and SM representation-ring matching"

data FiniteExplicitSector : Set where
  sector-p2 :
    FiniteExplicitSector

  sector-p3 :
    FiniteExplicitSector

  sector-p5 :
    FiniteExplicitSector

finiteExplicitSectorToLocalLane :
  FiniteExplicitSector →
  Local.Gate6FinitePrimeLane
finiteExplicitSectorToLocalLane sector-p2 =
  Local.gate6-p2
finiteExplicitSectorToLocalLane sector-p3 =
  Local.gate6-p3
finiteExplicitSectorToLocalLane sector-p5 =
  Local.gate6-p5

data FinitePrimeLaneDirectSumObject : Set where
  directSum-p2-p3 :
    FinitePrimeLaneDirectSumObject

  directSum-p2-p5 :
    FinitePrimeLaneDirectSumObject

  directSum-p3-p5 :
    FinitePrimeLaneDirectSumObject

  directSum-p2-p3-p5 :
    FinitePrimeLaneDirectSumObject

canonicalFinitePrimeLaneDirectSumObjects :
  List FinitePrimeLaneDirectSumObject
canonicalFinitePrimeLaneDirectSumObjects =
  directSum-p2-p3
  ∷ directSum-p2-p5
  ∷ directSum-p3-p5
  ∷ directSum-p2-p3-p5
  ∷ []

record DirectSumClosed : Setω where
  field
    localEndomorphismLedger :
      Local.Gate6FinitePrimeLaneLocalEndomorphismCategoryLedger

    finitePrimeLaneSummands :
      List FiniteExplicitSector

    finitePrimeLaneSummandsAreCanonical :
      finitePrimeLaneSummands
      ≡
      sector-p2
      ∷ sector-p3
      ∷ sector-p5
      ∷ []

    finiteDirectSumObjects :
      List FinitePrimeLaneDirectSumObject

    finiteDirectSumObjectsAreCanonical :
      finiteDirectSumObjects ≡ canonicalFinitePrimeLaneDirectSumObjects

    p2RowCategoryAvailable :
      Local.p2CategoryLawsAvailable localEndomorphismLedger ≡ true

    p3RowCategoryAvailable :
      Local.p3CategoryLawsAvailable localEndomorphismLedger ≡ true

    p5RowCategoryAvailable :
      Local.p5CategoryLawsAvailable localEndomorphismLedger ≡ true

    finitePrimeLaneDirectSumsInhabited :
      Bool

    finitePrimeLaneDirectSumsInhabitedIsTrue :
      finitePrimeLaneDirectSumsInhabited ≡ true

    arbitraryDirectSumsClosed :
      Bool

    arbitraryDirectSumsClosedIsFalse :
      arbitraryDirectSumsClosed ≡ false

    directSumBoundary :
      List String

open DirectSumClosed public

canonicalDirectSumClosed :
  DirectSumClosed
canonicalDirectSumClosed =
  record
    { localEndomorphismLedger =
        Local.canonicalGate6FinitePrimeLaneLocalEndomorphismCategoryLedger
    ; finitePrimeLaneSummands =
        sector-p2
        ∷ sector-p3
        ∷ sector-p5
        ∷ []
    ; finitePrimeLaneSummandsAreCanonical =
        refl
    ; finiteDirectSumObjects =
        canonicalFinitePrimeLaneDirectSumObjects
    ; finiteDirectSumObjectsAreCanonical =
        refl
    ; p2RowCategoryAvailable =
        refl
    ; p3RowCategoryAvailable =
        refl
    ; p5RowCategoryAvailable =
        refl
    ; finitePrimeLaneDirectSumsInhabited =
        true
    ; finitePrimeLaneDirectSumsInhabitedIsTrue =
        refl
    ; arbitraryDirectSumsClosed =
        false
    ; arbitraryDirectSumsClosedIsFalse =
        refl
    ; directSumBoundary =
        "Finite direct-sum objects are recorded for p2+p3, p2+p5, p3+p5, and p2+p3+p5"
        ∷ "The construction only packages explicit finite prime-lane rows whose local category laws are already inhabited"
        ∷ "No closure under arbitrary DHR-sector direct sums or subobjects is promoted"
        ∷ []
    }

data FieldExtensionTensorTarget : Set where
  tensorOverPrimeLaneFieldExtension :
    FieldExtensionTensorTarget

record TensorClosed : Setω where
  field
    finiteTensorFusionReceipt :
      TensorFusion.FinitePrimeLaneTensorFusionReceipt

    p2p3FusionRuleComputed :
      TensorFusion.finiteRuleComputableByCaseSplit
        (TensorFusion.p2p3Rule finiteTensorFusionReceipt)
      ≡
      true

    p2p5FusionRuleComputed :
      TensorFusion.finiteRuleComputableByCaseSplit
        (TensorFusion.p2p5Rule finiteTensorFusionReceipt)
      ≡
      true

    p3p5FusionRuleComputed :
      TensorFusion.finiteRuleComputableByCaseSplit
        (TensorFusion.p3p5Rule finiteTensorFusionReceipt)
      ≡
      true

    tensorTarget :
      FieldExtensionTensorTarget

    tensorTargetIsFieldExtension :
      tensorTarget ≡ tensorOverPrimeLaneFieldExtension

    leftTensorSector :
      FiniteExplicitSector

    rightTensorSector :
      FiniteExplicitSector

    basePrimeLaneField :
      String

    fieldExtensionShape :
      String

    tensorProductLawTarget :
      String

    fieldExtensionTensorTargetPreciselyRecorded :
      Bool

    fieldExtensionTensorTargetPreciselyRecordedIsTrue :
      fieldExtensionTensorTargetPreciselyRecorded ≡ true

    finiteTensorFusionComputed :
      Bool

    finiteTensorFusionComputedIsTrue :
      finiteTensorFusionComputed ≡ true

    arbitraryTensorProductsClosed :
      Bool

    arbitraryTensorProductsClosedIsFalse :
      arbitraryTensorProductsClosed ≡ false

    tensorBoundary :
      List String

open TensorClosed public

canonicalTensorClosedTarget :
  TensorClosed
canonicalTensorClosedTarget =
  record
    { finiteTensorFusionReceipt =
        TensorFusion.canonicalFinitePrimeLaneTensorFusionReceipt
    ; p2p3FusionRuleComputed =
        refl
    ; p2p5FusionRuleComputed =
        refl
    ; p3p5FusionRuleComputed =
        refl
    ; tensorTarget =
        tensorOverPrimeLaneFieldExtension
    ; tensorTargetIsFieldExtension =
        refl
    ; leftTensorSector =
        sector-p3
    ; rightTensorSector =
        sector-p5
    ; basePrimeLaneField =
        "finite-prime-lane base field for p3/p5 carrier sectors"
    ; fieldExtensionShape =
        "target: construct tensor/fusion after extending the finite p3 and p5 carrier fields to a common splitting field"
    ; tensorProductLawTarget =
        "target: rho_p3 tensor rho_p5 closes as a finite carrier sector object over the common field extension, with associativity and unit compatibility"
    ; fieldExtensionTensorTargetPreciselyRecorded =
        true
    ; fieldExtensionTensorTargetPreciselyRecordedIsTrue =
        refl
    ; finiteTensorFusionComputed =
        true
    ; finiteTensorFusionComputedIsTrue =
        refl
    ; arbitraryTensorProductsClosed =
        false
    ; arbitraryTensorProductsClosedIsFalse =
        refl
    ; tensorBoundary =
        "Finite p2p3, p2p5, and p3p5 tensor-fusion rules are computed as singleton external-product decompositions"
        ∷ "The field-extension target remains recorded for interpreting the finite pair rules over a common carrier splitting field"
        ∷ "No arbitrary tensor closure, DR tensor category, full representation ring, or SM representation ring is constructed here"
        ∷ []
    }

data FiniteFrobeniusConjugateSector : Set where
  frobeniusConjugate-p2 :
    FiniteFrobeniusConjugateSector

  frobeniusConjugate-p3 :
    FiniteFrobeniusConjugateSector

  frobeniusConjugate-p5 :
    FiniteFrobeniusConjugateSector

canonicalFiniteFrobeniusConjugateSectors :
  List FiniteFrobeniusConjugateSector
canonicalFiniteFrobeniusConjugateSectors =
  frobeniusConjugate-p2
  ∷ frobeniusConjugate-p3
  ∷ frobeniusConjugate-p5
  ∷ []

record ConjugateSectors : Setω where
  field
    finiteConjugateDualReceipt :
      Conjugate.FinitePrimeLaneConjugateDualReceipt

    finiteFrobeniusConjugates :
      List FiniteFrobeniusConjugateSector

    finiteFrobeniusConjugatesAreCanonical :
      finiteFrobeniusConjugates
      ≡
      canonicalFiniteFrobeniusConjugateSectors

    p2DualSocketCanonical :
      Conjugate.p2Socket finiteConjugateDualReceipt
      ≡
      Conjugate.p2FiniteSelfPhaseDualSocket

    p3DualSocketCanonical :
      Conjugate.p3Socket finiteConjugateDualReceipt
      ≡
      Conjugate.p3FiniteContragredientDualSocket

    p5DualSocketCanonical :
      Conjugate.p5Socket finiteConjugateDualReceipt
      ≡
      Conjugate.p5FiniteContragredientDualSocket

    finiteFrobeniusConjugateReceiptsInhabited :
      Bool

    finiteFrobeniusConjugateReceiptsInhabitedIsTrue :
      finiteFrobeniusConjugateReceiptsInhabited ≡ true

    arbitraryConjugatesClosed :
      Bool

    arbitraryConjugatesClosedIsFalse :
      arbitraryConjugatesClosed ≡ false

    conjugateBoundary :
      List String

open ConjugateSectors public

canonicalConjugateSectors :
  ConjugateSectors
canonicalConjugateSectors =
  record
    { finiteConjugateDualReceipt =
        Conjugate.canonicalFinitePrimeLaneConjugateDualReceipt
    ; finiteFrobeniusConjugates =
        canonicalFiniteFrobeniusConjugateSectors
    ; finiteFrobeniusConjugatesAreCanonical =
        refl
    ; p2DualSocketCanonical =
        refl
    ; p3DualSocketCanonical =
        refl
    ; p5DualSocketCanonical =
        refl
    ; finiteFrobeniusConjugateReceiptsInhabited =
        true
    ; finiteFrobeniusConjugateReceiptsInhabitedIsTrue =
        refl
    ; arbitraryConjugatesClosed =
        false
    ; arbitraryConjugatesClosedIsFalse =
        refl
    ; conjugateBoundary =
        "Finite Frobenius-conjugate receipts are inhabited for p2, p3, and p5 by the finite conjugate/dual socket receipt"
        ∷ "p2 is self/phase conjugation; p3 and p5 are contragredient target sockets over finite rows"
        ∷ "The zigzags close only as finite identity sockets; arbitrary transportable-endomorphism conjugates remain open"
        ∷ []
    }

record ArbitrarySectorClosureReceipt : Setω where
  field
    conditionalPromotionReceipt :
      Conditional.ConditionalGDHRSMPromotionReceipt

    conditionalStatusRecorded :
      Conditional.conditionalStatus conditionalPromotionReceipt
      ≡
      Conditional.conditionalOnDRAuthority

    finitePrimeLaneAxiomsSatisfied :
      Bool

    finitePrimeLaneAxiomsSatisfiedIsTrue :
      finitePrimeLaneAxiomsSatisfied ≡ true

    directSumClosed :
      DirectSumClosed

    finitePrimeLaneDirectSumsInhabited :
      finitePrimeLaneDirectSumsInhabited directSumClosed ≡ true

    tensorClosedTarget :
      TensorClosed

    fieldExtensionTensorTargetRecorded :
      fieldExtensionTensorTargetPreciselyRecorded tensorClosedTarget
      ≡
      true

    finiteTensorFusionComputedHere :
      finiteTensorFusionComputed tensorClosedTarget
      ≡
      true

    conjugateSectors :
      ConjugateSectors

    finiteFrobeniusConjugatesInhabited :
      finiteFrobeniusConjugateReceiptsInhabited conjugateSectors
      ≡
      true

    directSumClosureConstructed :
      Bool

    directSumClosureConstructedIsFalse :
      directSumClosureConstructed ≡ false

    tensorProductClosureConstructed :
      Bool

    tensorProductClosureConstructedIsFalse :
      tensorProductClosureConstructed ≡ false

    conjugateSectorsConstructed :
      Bool

    conjugateSectorsConstructedIsFalse :
      conjugateSectorsConstructed ≡ false

    faithfulExactFullFibreFunctorConstructed :
      Bool

    faithfulExactFullFibreFunctorConstructedIsFalse :
      faithfulExactFullFibreFunctorConstructed ≡ false

    compactGDHRConstructedInternally :
      Bool

    compactGDHRConstructedInternallyIsFalse :
      compactGDHRConstructedInternally ≡ false

    representationRingMatchesSM :
      Bool

    representationRingMatchesSMIsFalse :
      representationRingMatchesSM ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    blockers :
      List ArbitrarySectorClosureBlocker

    blockersAreCanonical :
      blockers ≡ canonicalArbitrarySectorClosureBlockers

    carrierDHRGroupConjecture :
      String

    carrierDHRGroupConjectureIsCanonical :
      carrierDHRGroupConjecture ≡ carrierDHRGroupConjectureLabel

    receiptBoundary :
      List String

open ArbitrarySectorClosureReceipt public

canonicalArbitrarySectorClosureReceipt :
  ArbitrarySectorClosureReceipt
canonicalArbitrarySectorClosureReceipt =
  record
    { conditionalPromotionReceipt =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; conditionalStatusRecorded =
        Conditional.canonicalConditionalGDHRSMPromotionStatus
    ; finitePrimeLaneAxiomsSatisfied =
        true
    ; finitePrimeLaneAxiomsSatisfiedIsTrue =
        refl
    ; directSumClosed =
        canonicalDirectSumClosed
    ; finitePrimeLaneDirectSumsInhabited =
        refl
    ; tensorClosedTarget =
        canonicalTensorClosedTarget
    ; fieldExtensionTensorTargetRecorded =
        refl
    ; finiteTensorFusionComputedHere =
        refl
    ; conjugateSectors =
        canonicalConjugateSectors
    ; finiteFrobeniusConjugatesInhabited =
        refl
    ; directSumClosureConstructed =
        false
    ; directSumClosureConstructedIsFalse =
        refl
    ; tensorProductClosureConstructed =
        false
    ; tensorProductClosureConstructedIsFalse =
        refl
    ; conjugateSectorsConstructed =
        false
    ; conjugateSectorsConstructedIsFalse =
        refl
    ; faithfulExactFullFibreFunctorConstructed =
        false
    ; faithfulExactFullFibreFunctorConstructedIsFalse =
        refl
    ; compactGDHRConstructedInternally =
        false
    ; compactGDHRConstructedInternallyIsFalse =
        refl
    ; representationRingMatchesSM =
        false
    ; representationRingMatchesSMIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; blockers =
        canonicalArbitrarySectorClosureBlockers
    ; blockersAreCanonical =
        refl
    ; carrierDHRGroupConjecture =
        carrierDHRGroupConjectureLabel
    ; carrierDHRGroupConjectureIsCanonical =
        refl
    ; receiptBoundary =
        "Finite prime-lane DHR axioms and conditionalOnDRAuthority are already recorded"
        ∷ "Finite explicit direct-sum objects and finite Frobenius-conjugate receipts are now inhabited for p2, p3, and p5 only"
        ∷ "Finite p2p3, p2p5, and p3p5 tensor-fusion rules are computed as finite external-product decompositions only"
        ∷ "The next theorem is arbitrary-sector closure under direct sums, tensor products, conjugates, and a full faithful exact fibre functor"
        ∷ "The abelian finite-field automorphism readback is not by itself the Standard Model gauge group; nonabelian structure requires inter-lane morphisms and Tannaka reconstruction"
        ∷ "Full G_DHR ~= G_SM promotion remains false"
        ∷ []
    }

arbitrarySectorClosureStillOpen :
  directSumClosureConstructed canonicalArbitrarySectorClosureReceipt
  ≡
  false
arbitrarySectorClosureStillOpen =
  refl

finitePrimeLaneDirectSumsNowInhabited :
  finitePrimeLaneDirectSumsInhabited canonicalArbitrarySectorClosureReceipt
  ≡
  refl
finitePrimeLaneDirectSumsNowInhabited =
  refl

finitePrimeLaneFrobeniusConjugatesNowInhabited :
  finiteFrobeniusConjugatesInhabited canonicalArbitrarySectorClosureReceipt
  ≡
  refl
finitePrimeLaneFrobeniusConjugatesNowInhabited =
  refl

fieldExtensionTensorTargetRecordedForFiniteFusion :
  fieldExtensionTensorTargetRecorded canonicalArbitrarySectorClosureReceipt
  ≡
  refl
fieldExtensionTensorTargetRecordedForFiniteFusion =
  refl

finiteTensorFusionNowComputedForExplicitPrimePairs :
  finiteTensorFusionComputedHere canonicalArbitrarySectorClosureReceipt
  ≡
  refl
finiteTensorFusionNowComputedForExplicitPrimePairs =
  refl

arbitrarySectorClosureDoesNotPromoteGDHREqualsGSM :
  gDHREqualsGSMPromoted canonicalArbitrarySectorClosureReceipt
  ≡
  false
arbitrarySectorClosureDoesNotPromoteGDHREqualsGSM =
  refl
