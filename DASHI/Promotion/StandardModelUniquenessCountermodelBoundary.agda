module DASHI.Promotion.StandardModelUniquenessCountermodelBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.StandardModelFiniteAnomalyHyperchargeCheck as AnomalyCheck
import DASHI.Promotion.StandardModelFiniteRepresentationNarrowing as Narrow
import DASHI.Promotion.StandardModelTerminalObligations as Terminal

------------------------------------------------------------------------
-- Standard Model uniqueness countermodel boundary.
--
-- This module separates finite consistency checks from uniqueness theorems.
-- The rows below are proof-obligation and countermodel-boundary rows: they
-- record ways bookkeeping can remain anomaly-compatible or conventionally
-- equivalent without proving that the Standard Model is uniquely forced.
--
-- No row adopts a physical alternative.  Each row keeps the exact Standard
-- Model, uniqueness, and terminal/full-unification promotion bits false.

data BoundarySurface : Set where
  finiteConsistencyCheckSurface :
    BoundarySurface

  uniquenessTheoremSurface :
    BoundarySurface

boundarySurfaceLabel :
  BoundarySurface →
  String
boundarySurfaceLabel finiteConsistencyCheckSurface =
  "finite consistency check"
boundarySurfaceLabel uniquenessTheoremSurface =
  "uniqueness theorem"

data CountermodelBoundaryKind : Set where
  alternativeGenerationCountBoundary :
    CountermodelBoundaryKind

  hyperchargeNormalizationVariantBoundary :
    CountermodelBoundaryKind

  vectorlikeAdditionBoundary :
    CountermodelBoundaryKind

  sterileNeutrinoOptionBoundary :
    CountermodelBoundaryKind

  extraU1FactorBoundary :
    CountermodelBoundaryKind

  gutEmbeddingBoundary :
    CountermodelBoundaryKind

  finitePrimeRelabellingBoundary :
    CountermodelBoundaryKind

countermodelBoundaryKindLabel :
  CountermodelBoundaryKind →
  String
countermodelBoundaryKindLabel alternativeGenerationCountBoundary =
  "alternative generation counts"
countermodelBoundaryKindLabel hyperchargeNormalizationVariantBoundary =
  "hypercharge normalization variants"
countermodelBoundaryKindLabel vectorlikeAdditionBoundary =
  "vectorlike additions"
countermodelBoundaryKindLabel sterileNeutrinoOptionBoundary =
  "sterile neutrino options"
countermodelBoundaryKindLabel extraU1FactorBoundary =
  "extra U1 factors"
countermodelBoundaryKindLabel gutEmbeddingBoundary =
  "GUT embeddings"
countermodelBoundaryKindLabel finitePrimeRelabellingBoundary =
  "finite-prime relabellings"

data BoundaryRowStatus : Set where
  consistencyCompatibleBookkeeping :
    BoundaryRowStatus

  conventionVariantBookkeeping :
    BoundaryRowStatus

  extensionBoundaryBookkeeping :
    BoundaryRowStatus

  embeddingBoundaryBookkeeping :
    BoundaryRowStatus

  relabellingBoundaryBookkeeping :
    BoundaryRowStatus

data UniquenessGap : Set where
  generationNumberNotDerived :
    UniquenessGap

  physicalNormalizationNotDerived :
    UniquenessGap

  minimalityAxiomNotDerived :
    UniquenessGap

  sterileSectorConventionNotClosed :
    UniquenessGap

  abelianFactorExclusionNotProved :
    UniquenessGap

  embeddingExclusionNotProved :
    UniquenessGap

  primeNameRigidityNotProved :
    UniquenessGap

data UniquenessPromotionToken : Set where

uniquenessPromotionTokenImpossibleHere :
  UniquenessPromotionToken →
  ⊥
uniquenessPromotionTokenImpossibleHere ()

record ConsistencyVsUniquenessRow : Set where
  field
    boundaryKind :
      CountermodelBoundaryKind

    boundaryKindName :
      String

    boundaryKindNameIsCanonical :
      boundaryKindName ≡ countermodelBoundaryKindLabel boundaryKind

    checkSurface :
      BoundarySurface

    checkSurfaceName :
      String

    checkSurfaceNameIsCanonical :
      checkSurfaceName ≡ boundarySurfaceLabel checkSurface

    uniquenessSurface :
      BoundarySurface

    uniquenessSurfaceName :
      String

    uniquenessSurfaceNameIsCanonical :
      uniquenessSurfaceName ≡ boundarySurfaceLabel uniquenessSurface

    rowStatus :
      BoundaryRowStatus

    uniquenessGap :
      UniquenessGap

    finiteAnomalyCompatibleBookkeeping :
      Bool

    finiteAnomalyCompatibleBookkeepingIsTrue :
      finiteAnomalyCompatibleBookkeeping ≡ true

    adoptedAsPhysicalAlternative :
      Bool

    adoptedAsPhysicalAlternativeIsFalse :
      adoptedAsPhysicalAlternative ≡ false

    provesStandardModelUniqueness :
      Bool

    provesStandardModelUniquenessIsFalse :
      provesStandardModelUniqueness ≡ false

    boundaryStatement :
      String

open ConsistencyVsUniquenessRow public

alternativeGenerationCountRow :
  ConsistencyVsUniquenessRow
alternativeGenerationCountRow =
  record
    { boundaryKind =
        alternativeGenerationCountBoundary
    ; boundaryKindName =
        "alternative generation counts"
    ; boundaryKindNameIsCanonical =
        refl
    ; checkSurface =
        finiteConsistencyCheckSurface
    ; checkSurfaceName =
        "finite consistency check"
    ; checkSurfaceNameIsCanonical =
        refl
    ; uniquenessSurface =
        uniquenessTheoremSurface
    ; uniquenessSurfaceName =
        "uniqueness theorem"
    ; uniquenessSurfaceNameIsCanonical =
        refl
    ; rowStatus =
        consistencyCompatibleBookkeeping
    ; uniquenessGap =
        generationNumberNotDerived
    ; finiteAnomalyCompatibleBookkeeping =
        true
    ; finiteAnomalyCompatibleBookkeepingIsTrue =
        refl
    ; adoptedAsPhysicalAlternative =
        false
    ; adoptedAsPhysicalAlternativeIsFalse =
        refl
    ; provesStandardModelUniqueness =
        false
    ; provesStandardModelUniquenessIsFalse =
        refl
    ; boundaryStatement =
        "Anomaly cancellation can be checked per generation, but the number of physical generations is not derived here"
    }

hyperchargeNormalizationVariantRow :
  ConsistencyVsUniquenessRow
hyperchargeNormalizationVariantRow =
  record
    { boundaryKind =
        hyperchargeNormalizationVariantBoundary
    ; boundaryKindName =
        "hypercharge normalization variants"
    ; boundaryKindNameIsCanonical =
        refl
    ; checkSurface =
        finiteConsistencyCheckSurface
    ; checkSurfaceName =
        "finite consistency check"
    ; checkSurfaceNameIsCanonical =
        refl
    ; uniquenessSurface =
        uniquenessTheoremSurface
    ; uniquenessSurfaceName =
        "uniqueness theorem"
    ; uniquenessSurfaceNameIsCanonical =
        refl
    ; rowStatus =
        conventionVariantBookkeeping
    ; uniquenessGap =
        physicalNormalizationNotDerived
    ; finiteAnomalyCompatibleBookkeeping =
        true
    ; finiteAnomalyCompatibleBookkeepingIsTrue =
        refl
    ; adoptedAsPhysicalAlternative =
        false
    ; adoptedAsPhysicalAlternativeIsFalse =
        refl
    ; provesStandardModelUniqueness =
        false
    ; provesStandardModelUniquenessIsFalse =
        refl
    ; boundaryStatement =
        "Signed-sixth anomaly rows fix a finite convention, not a theorem selecting the physical U1Y normalization"
    }

vectorlikeAdditionRow :
  ConsistencyVsUniquenessRow
vectorlikeAdditionRow =
  record
    { boundaryKind =
        vectorlikeAdditionBoundary
    ; boundaryKindName =
        "vectorlike additions"
    ; boundaryKindNameIsCanonical =
        refl
    ; checkSurface =
        finiteConsistencyCheckSurface
    ; checkSurfaceName =
        "finite consistency check"
    ; checkSurfaceNameIsCanonical =
        refl
    ; uniquenessSurface =
        uniquenessTheoremSurface
    ; uniquenessSurfaceName =
        "uniqueness theorem"
    ; uniquenessSurfaceNameIsCanonical =
        refl
    ; rowStatus =
        extensionBoundaryBookkeeping
    ; uniquenessGap =
        minimalityAxiomNotDerived
    ; finiteAnomalyCompatibleBookkeeping =
        true
    ; finiteAnomalyCompatibleBookkeepingIsTrue =
        refl
    ; adoptedAsPhysicalAlternative =
        false
    ; adoptedAsPhysicalAlternativeIsFalse =
        refl
    ; provesStandardModelUniqueness =
        false
    ; provesStandardModelUniquenessIsFalse =
        refl
    ; boundaryStatement =
        "Vectorlike matter can be anomaly-neutral bookkeeping, but excluding it requires an extra minimality or dynamics theorem"
    }

sterileNeutrinoOptionRow :
  ConsistencyVsUniquenessRow
sterileNeutrinoOptionRow =
  record
    { boundaryKind =
        sterileNeutrinoOptionBoundary
    ; boundaryKindName =
        "sterile neutrino options"
    ; boundaryKindNameIsCanonical =
        refl
    ; checkSurface =
        finiteConsistencyCheckSurface
    ; checkSurfaceName =
        "finite consistency check"
    ; checkSurfaceNameIsCanonical =
        refl
    ; uniquenessSurface =
        uniquenessTheoremSurface
    ; uniquenessSurfaceName =
        "uniqueness theorem"
    ; uniquenessSurfaceNameIsCanonical =
        refl
    ; rowStatus =
        extensionBoundaryBookkeeping
    ; uniquenessGap =
        sterileSectorConventionNotClosed
    ; finiteAnomalyCompatibleBookkeeping =
        true
    ; finiteAnomalyCompatibleBookkeepingIsTrue =
        refl
    ; adoptedAsPhysicalAlternative =
        false
    ; adoptedAsPhysicalAlternativeIsFalse =
        refl
    ; provesStandardModelUniqueness =
        false
    ; provesStandardModelUniquenessIsFalse =
        refl
    ; boundaryStatement =
        "A sterile nu^c row is anomaly-neutral, but the sterile-neutrino sector is not selected or excluded by this finite ledger"
    }

extraU1FactorRow :
  ConsistencyVsUniquenessRow
extraU1FactorRow =
  record
    { boundaryKind =
        extraU1FactorBoundary
    ; boundaryKindName =
        "extra U1 factors"
    ; boundaryKindNameIsCanonical =
        refl
    ; checkSurface =
        finiteConsistencyCheckSurface
    ; checkSurfaceName =
        "finite consistency check"
    ; checkSurfaceNameIsCanonical =
        refl
    ; uniquenessSurface =
        uniquenessTheoremSurface
    ; uniquenessSurfaceName =
        "uniqueness theorem"
    ; uniquenessSurfaceNameIsCanonical =
        refl
    ; rowStatus =
        extensionBoundaryBookkeeping
    ; uniquenessGap =
        abelianFactorExclusionNotProved
    ; finiteAnomalyCompatibleBookkeeping =
        true
    ; finiteAnomalyCompatibleBookkeepingIsTrue =
        refl
    ; adoptedAsPhysicalAlternative =
        false
    ; adoptedAsPhysicalAlternativeIsFalse =
        refl
    ; provesStandardModelUniqueness =
        false
    ; provesStandardModelUniquenessIsFalse =
        refl
    ; boundaryStatement =
        "The finite SM U1Y check does not by itself exclude additional anomaly-managed abelian bookkeeping factors"
    }

gutEmbeddingRow :
  ConsistencyVsUniquenessRow
gutEmbeddingRow =
  record
    { boundaryKind =
        gutEmbeddingBoundary
    ; boundaryKindName =
        "GUT embeddings"
    ; boundaryKindNameIsCanonical =
        refl
    ; checkSurface =
        finiteConsistencyCheckSurface
    ; checkSurfaceName =
        "finite consistency check"
    ; checkSurfaceNameIsCanonical =
        refl
    ; uniquenessSurface =
        uniquenessTheoremSurface
    ; uniquenessSurfaceName =
        "uniqueness theorem"
    ; uniquenessSurfaceNameIsCanonical =
        refl
    ; rowStatus =
        embeddingBoundaryBookkeeping
    ; uniquenessGap =
        embeddingExclusionNotProved
    ; finiteAnomalyCompatibleBookkeeping =
        true
    ; finiteAnomalyCompatibleBookkeepingIsTrue =
        refl
    ; adoptedAsPhysicalAlternative =
        false
    ; adoptedAsPhysicalAlternativeIsFalse =
        refl
    ; provesStandardModelUniqueness =
        false
    ; provesStandardModelUniquenessIsFalse =
        refl
    ; boundaryStatement =
        "A low-energy SM ledger is compatible with embedding questions; this module proves neither a GUT nor its exclusion"
    }

finitePrimeRelabellingRow :
  ConsistencyVsUniquenessRow
finitePrimeRelabellingRow =
  record
    { boundaryKind =
        finitePrimeRelabellingBoundary
    ; boundaryKindName =
        "finite-prime relabellings"
    ; boundaryKindNameIsCanonical =
        refl
    ; checkSurface =
        finiteConsistencyCheckSurface
    ; checkSurfaceName =
        "finite consistency check"
    ; checkSurfaceNameIsCanonical =
        refl
    ; uniquenessSurface =
        uniquenessTheoremSurface
    ; uniquenessSurfaceName =
        "uniqueness theorem"
    ; uniquenessSurfaceNameIsCanonical =
        refl
    ; rowStatus =
        relabellingBoundaryBookkeeping
    ; uniquenessGap =
        primeNameRigidityNotProved
    ; finiteAnomalyCompatibleBookkeeping =
        true
    ; finiteAnomalyCompatibleBookkeepingIsTrue =
        refl
    ; adoptedAsPhysicalAlternative =
        false
    ; adoptedAsPhysicalAlternativeIsFalse =
        refl
    ; provesStandardModelUniqueness =
        false
    ; provesStandardModelUniquenessIsFalse =
        refl
    ; boundaryStatement =
        "p2/p3/p5 gauge-name bookkeeping is finite evidence, not a rigidity theorem forbidding all prime-lane relabellings"
    }

canonicalConsistencyVsUniquenessRows :
  List ConsistencyVsUniquenessRow
canonicalConsistencyVsUniquenessRows =
  alternativeGenerationCountRow
  ∷ hyperchargeNormalizationVariantRow
  ∷ vectorlikeAdditionRow
  ∷ sterileNeutrinoOptionRow
  ∷ extraU1FactorRow
  ∷ gutEmbeddingRow
  ∷ finitePrimeRelabellingRow
  ∷ []

listCount :
  {A : Set} →
  List A →
  Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

canonicalBoundaryStatement :
  String
canonicalBoundaryStatement =
  "Finite anomaly-compatible bookkeeping is a consistency check, not a Standard Model uniqueness theorem."

standardModelUniquenessPromoted :
  Bool
standardModelUniquenessPromoted =
  false

record StandardModelUniquenessCountermodelBoundaryReceipt : Setω where
  field
    terminalPromotionObligationReceipt :
      Terminal.StandardModelTerminalPromotionObligationReceipt

    terminalReceiptKeepsSMPromotionFalse :
      Terminal.standardModelPromoted terminalPromotionObligationReceipt
      ≡
      false

    finiteRepresentationNarrowingReceipt :
      Narrow.StandardModelFiniteRepresentationNarrowingReceipt

    finiteNarrowingIsNotBroadSMPromotion :
      Narrow.broadStandardModelPromoted finiteRepresentationNarrowingReceipt
      ≡
      false

    finiteAnomalyHyperchargeCheckReceipt :
      AnomalyCheck.FiniteSMAnomalyHyperchargeCheckReceipt

    finiteCheckHasSixHyperchargeRows :
      AnomalyCheck.finiteHyperchargeMultipletRowCount
        finiteAnomalyHyperchargeCheckReceipt
      ≡
      6

    finiteCheckHasFourAnomalyRows :
      AnomalyCheck.anomalyBalanceRowCount
        finiteAnomalyHyperchargeCheckReceipt
      ≡
      4

    finiteCheckKeepsBroadSMPromotionFalse :
      AnomalyCheck.broadStandardModelPromoted
        finiteAnomalyHyperchargeCheckReceipt
      ≡
      false

    consistencyVsUniquenessRows :
      List ConsistencyVsUniquenessRow

    consistencyVsUniquenessRowsAreCanonical :
      consistencyVsUniquenessRows
      ≡
      canonicalConsistencyVsUniquenessRows

    boundaryRowCount :
      Nat

    boundaryRowCountIsSeven :
      boundaryRowCount ≡ 7

    consistencyCheckRowCount :
      Nat

    consistencyCheckRowCountIsSeven :
      consistencyCheckRowCount ≡ 7

    uniquenessTheoremRowCount :
      Nat

    uniquenessTheoremRowCountIsSeven :
      uniquenessTheoremRowCount ≡ 7

    physicalAlternativeAdoptionCount :
      Nat

    physicalAlternativeAdoptionCountIsZero :
      physicalAlternativeAdoptionCount ≡ 0

    uniquenessProofCount :
      Nat

    uniquenessProofCountIsZero :
      uniquenessProofCount ≡ 0

    finiteConsistencyChecksRecorded :
      Bool

    finiteConsistencyChecksRecordedIsTrue :
      finiteConsistencyChecksRecorded ≡ true

    anomalyCompatibleBookkeepingRecorded :
      Bool

    anomalyCompatibleBookkeepingRecordedIsTrue :
      anomalyCompatibleBookkeepingRecorded ≡ true

    uniquenessTheoremRecorded :
      Bool

    uniquenessTheoremRecordedIsFalse :
      uniquenessTheoremRecorded ≡ false

    standardModelUniquenessPromotedReceipt :
      Bool

    standardModelUniquenessPromotedReceiptIsGlobal :
      standardModelUniquenessPromotedReceipt
      ≡
      standardModelUniquenessPromoted

    standardModelUniquenessPromotedReceiptIsFalse :
      standardModelUniquenessPromotedReceipt ≡ false

    promotionTokens :
      List UniquenessPromotionToken

    promotionTokensAreEmpty :
      promotionTokens ≡ []

    receiptStatement :
      String

    receiptStatementIsCanonical :
      receiptStatement ≡ canonicalBoundaryStatement

    receiptBoundary :
      List String

open StandardModelUniquenessCountermodelBoundaryReceipt public

canonicalStandardModelUniquenessCountermodelBoundaryReceipt :
  StandardModelUniquenessCountermodelBoundaryReceipt
canonicalStandardModelUniquenessCountermodelBoundaryReceipt =
  record
    { terminalPromotionObligationReceipt =
        Terminal.canonicalStandardModelTerminalPromotionObligationReceipt
    ; terminalReceiptKeepsSMPromotionFalse =
        refl
    ; finiteRepresentationNarrowingReceipt =
        Narrow.canonicalStandardModelFiniteRepresentationNarrowingReceipt
    ; finiteNarrowingIsNotBroadSMPromotion =
        refl
    ; finiteAnomalyHyperchargeCheckReceipt =
        AnomalyCheck.canonicalFiniteSMAnomalyHyperchargeCheckReceipt
    ; finiteCheckHasSixHyperchargeRows =
        refl
    ; finiteCheckHasFourAnomalyRows =
        refl
    ; finiteCheckKeepsBroadSMPromotionFalse =
        refl
    ; consistencyVsUniquenessRows =
        canonicalConsistencyVsUniquenessRows
    ; consistencyVsUniquenessRowsAreCanonical =
        refl
    ; boundaryRowCount =
        listCount canonicalConsistencyVsUniquenessRows
    ; boundaryRowCountIsSeven =
        refl
    ; consistencyCheckRowCount =
        7
    ; consistencyCheckRowCountIsSeven =
        refl
    ; uniquenessTheoremRowCount =
        7
    ; uniquenessTheoremRowCountIsSeven =
        refl
    ; physicalAlternativeAdoptionCount =
        0
    ; physicalAlternativeAdoptionCountIsZero =
        refl
    ; uniquenessProofCount =
        0
    ; uniquenessProofCountIsZero =
        refl
    ; finiteConsistencyChecksRecorded =
        true
    ; finiteConsistencyChecksRecordedIsTrue =
        refl
    ; anomalyCompatibleBookkeepingRecorded =
        true
    ; anomalyCompatibleBookkeepingRecordedIsTrue =
        refl
    ; uniquenessTheoremRecorded =
        false
    ; uniquenessTheoremRecordedIsFalse =
        refl
    ; standardModelUniquenessPromotedReceipt =
        standardModelUniquenessPromoted
    ; standardModelUniquenessPromotedReceiptIsGlobal =
        refl
    ; standardModelUniquenessPromotedReceiptIsFalse =
        refl
    ; promotionTokens =
        []
    ; promotionTokensAreEmpty =
        refl
    ; receiptStatement =
        canonicalBoundaryStatement
    ; receiptStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Existing finite receipts record six hypercharge rows and four zero anomaly balance rows"
        ∷ "Seven boundary rows record candidate-compatible bookkeeping surfaces that do not prove uniqueness"
        ∷ "Alternative generation counts, hypercharge normalization variants, vectorlike additions, sterile neutrino options, extra U1 factors, GUT embeddings, and finite-prime relabellings are not adopted"
        ∷ "The uniqueness theorem token type is empty and standardModelUniquenessPromoted remains false"
        ∷ []
    }

canonicalCountermodelBoundaryRowCountIsSeven :
  boundaryRowCount canonicalStandardModelUniquenessCountermodelBoundaryReceipt
  ≡
  7
canonicalCountermodelBoundaryRowCountIsSeven =
  refl

canonicalCountermodelBoundaryConsistencyCheckRowCountIsSeven :
  consistencyCheckRowCount
    canonicalStandardModelUniquenessCountermodelBoundaryReceipt
  ≡
  7
canonicalCountermodelBoundaryConsistencyCheckRowCountIsSeven =
  refl

canonicalCountermodelBoundaryUniquenessTheoremRowCountIsSeven :
  uniquenessTheoremRowCount
    canonicalStandardModelUniquenessCountermodelBoundaryReceipt
  ≡
  7
canonicalCountermodelBoundaryUniquenessTheoremRowCountIsSeven =
  refl

canonicalCountermodelBoundaryAdoptedAlternativeCountIsZero :
  physicalAlternativeAdoptionCount
    canonicalStandardModelUniquenessCountermodelBoundaryReceipt
  ≡
  0
canonicalCountermodelBoundaryAdoptedAlternativeCountIsZero =
  refl

canonicalCountermodelBoundaryUniquenessProofCountIsZero :
  uniquenessProofCount canonicalStandardModelUniquenessCountermodelBoundaryReceipt
  ≡
  0
canonicalCountermodelBoundaryUniquenessProofCountIsZero =
  refl

standardModelUniquenessPromotedIsFalse :
  standardModelUniquenessPromoted ≡ false
standardModelUniquenessPromotedIsFalse =
  refl

canonicalCountermodelBoundaryDoesNotPromoteUniqueness :
  standardModelUniquenessPromotedReceipt
    canonicalStandardModelUniquenessCountermodelBoundaryReceipt
  ≡
  false
canonicalCountermodelBoundaryDoesNotPromoteUniqueness =
  refl
