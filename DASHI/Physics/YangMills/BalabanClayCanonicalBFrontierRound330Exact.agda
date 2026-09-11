{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound330Exact where

------------------------------------------------------------------------
-- ROUND330 / CROSS-LANE ARCHAEOLOGY AFTER R329
--
-- R329 correctly leaves five consumer-facing coordinates, but archaeology now
-- classifies all five more sharply.  On the preferred source-native route there
-- is still no mandatory fresh B-side Yang--Mills decay inequality:
--
--   H1  CMP116 J-localization       source theorem + same-object application
--   H2a Euclidean-time semantics    OS1/O(4) compiler + same-object geometry
--   H2b bounded Wilson tests        finite-cylinder theorem + presentation weld
--   H2c order passage               shared sequential-order-closure capability
--   H3  gap transfer                standard spectral theorem + same-H weld
--
-- The H2c correction is cross-lane reuse: Navier--Stokes already owns the
-- generic SequentialOrderClosure consumer.  This file proves that, once the T5
-- scalar convergence is identified with one rational instance of that shared
-- capability, R310's one-sided upper-closure package is compiler output.
--
-- No inhabitant of the shared closure or any same-object application is created
-- here.  Debt-kind normalization does not manufacture theorem content.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Physics.Closure.NSCompactGammaGalerkinLimitBridge as Sequential
import DASHI.Physics.Closure.NSTriadKNIntegratedDangerOccupationWeldRound92Exact as RationalNS
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound329Exact as R329
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanO4SpatialToTemporalClusteringRound276Exact as O4
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact as R315
import DASHI.Physics.YangMills.BalabanHalfRateTransferCoordinateMassGapRound316Exact as R316
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram

------------------------------------------------------------------------
-- Snowball attribution / classification coordinates.
------------------------------------------------------------------------

balabanCMP116Source : Attr.AttributedSource
balabanCMP116Source = Attr.mkDOISource
  "Tadeusz Balaban"
  "Renormalization Group Approach to Lattice Gauge Field Theories. II. Cluster Expansions"
  "Communications in Mathematical Physics 116(1), 1-22"
  "1988"
  "10.1007/BF01239022"
  "https://doi.org/10.1007/BF01239022"
  Attr.academicArticleSource
  "primary source for differentiated U/J/B localization and retained exponential tree-distance decay; applicability to the selected T5 carrier remains separate"
  Attr.publicAttribution

osISource : Attr.AttributedSource
osISource = Attr.mkDOISource
  "Konrad Osterwalder; Robert Schrader"
  "Axioms for Euclidean Green's Functions"
  "Communications in Mathematical Physics 31, 83-112"
  "1973"
  "10.1007/BF01645738"
  "https://doi.org/10.1007/BF01645738"
  Attr.academicArticleSource
  "primary OS reconstruction/covariance provenance; citation does not identify the selected Yang-Mills carrier"
  Attr.publicAttribution

osIISource : Attr.AttributedSource
osIISource = Attr.mkDOISource
  "Konrad Osterwalder; Robert Schrader"
  "Axioms for Euclidean Green's Functions II"
  "Communications in Mathematical Physics 42, 281-305"
  "1975"
  "10.1007/BF01608978"
  "https://doi.org/10.1007/BF01608978"
  Attr.academicArticleSource
  "primary OS reconstruction/spectral-transfer provenance; same reconstructed Hamiltonian remains an application coordinate"
  Attr.publicAttribution

davoudiSavageSource : Attr.AttributedSource
davoudiSavageSource = Attr.mkDOISource
  "Zohreh Davoudi; Martin J. Savage"
  "Restoration of Rotational Symmetry in the Continuum Limit of Lattice Field Theories"
  "Physical Review D 86, 054505"
  "2012"
  "10.1103/PhysRevD.86.054505"
  "https://doi.org/10.1103/PhysRevD.86.054505"
  Attr.academicArticleSource
  "perturbative precedent for rotational restoration only; not authority for nonperturbative four-dimensional Yang-Mills OS1"
  Attr.publicAttribution

canonicalR330SourceAtlas : Attr.AttributedSourceAtlas
canonicalR330SourceAtlas = Attr.mkSourceAtlas
  "YM canonical-B source/application atlas"
  "DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound330Exact"
  (balabanCMP116Source ∷ osISource ∷ osIISource ∷ davoudiSavageSource ∷ [])
  "primary sources motivating H1/H2a/H3; source identity is kept separate from selected-carrier applicability and kernel proof"

record ClassificationCoordinates : Set where
  constructor classification-coordinates
  field
    yangMillsWikidataQID : String
    quantumFieldTheoryDewey : String
    osAxiomsWikidataQID : String
    clayYMProblemWikidataQID : String
    unresolvedIdentifiersAreNotGuessed : Bool
    unresolvedIdentifiersAreNotGuessedIsTrue : unresolvedIdentifiersAreNotGuessed ≡ true
    classificationCoordinatesImportProof : Bool
    classificationCoordinatesImportProofIsFalse : classificationCoordinatesImportProof ≡ false

canonicalClassificationCoordinates : ClassificationCoordinates
canonicalClassificationCoordinates = classification-coordinates
  "Q1192873"
  "530.14"
  "unresolved"
  "unresolved"
  true refl
  false refl

------------------------------------------------------------------------
-- Debt-kind normalization.
------------------------------------------------------------------------

data CanonicalBCoordinate330 : Set where
  h1SelectedCMP116Application : CanonicalBCoordinate330
  h2aEuclideanTimeSupportSemantics : CanonicalBCoordinate330
  h2bWilsonCylinderPresentation : CanonicalBCoordinate330
  h2cSequentialOrderClosure : CanonicalBCoordinate330
  h3SameHamiltonianTransferCoordinate : CanonicalBCoordinate330

data DebtOrigin330 : Set where
  sourceApplication : DebtOrigin330
  physicalRepresentationWeld : DebtOrigin330
  sharedAnalysisCapability : DebtOrigin330
  transferSameObjectWeld : DebtOrigin330

debtOrigin330 : CanonicalBCoordinate330 → DebtOrigin330
debtOrigin330 h1SelectedCMP116Application = sourceApplication
debtOrigin330 h2aEuclideanTimeSupportSemantics = physicalRepresentationWeld
debtOrigin330 h2bWilsonCylinderPresentation = physicalRepresentationWeld
debtOrigin330 h2cSequentialOrderClosure = sharedAnalysisCapability
debtOrigin330 h3SameHamiltonianTransferCoordinate = transferSameObjectWeld

freshYMAnalyticInequalityRequired330 : CanonicalBCoordinate330 → Bool
freshYMAnalyticInequalityRequired330 _ = false

------------------------------------------------------------------------
-- H2c: reuse the cross-lane SequentialOrderClosure consumer.
------------------------------------------------------------------------

RationalSequentialOrderClosure : Set₁
RationalSequentialOrderClosure =
  Sequential.SequentialOrderClosure RationalNS.rationalAbsorptionArithmetic

record T5SequentialOrderClosureWeld
    {Measure TestObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (closure : RationalSequentialOrderClosure) : Set₁ where
  field
    sameConvergence : ∀ sequence limit →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence limit
      ≡ Sequential.Converges closure sequence limit

open T5SequentialOrderClosureWeld public

toR310RationalUpperOrderClosure :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ} →
  (closure : RationalSequentialOrderClosure) →
  T5SequentialOrderClosureWeld dataSet closure →
  R310.RationalUpperOrderClosure dataSet
toR310RationalUpperOrderClosure {dataSet = dataSet} closure weld = record
  { R310.RationalUpperOrderClosure.upperClosed =
      λ sequence target upper sequenceConverges sequenceUpper →
        Sequential.orderClosed closure
          (subst (λ proposition → proposition)
            (sameConvergence weld sequence target)
            sequenceConverges)
          (subst (λ proposition → proposition)
            (sameConvergence weld (λ _ → upper) upper)
            (Gram.constantConverges (Gram.scalarConvergence dataSet) upper))
          sequenceUpper
  }

------------------------------------------------------------------------
-- Current status: the five consumer coordinates remain real, but none is a
-- mandatory fresh B-side decay inequality on the source-native route.
------------------------------------------------------------------------

record Round330Boundary : Set where
  constructor round330-boundary
  field
    consumerCoordinateCountStillFive : Bool
    consumerCoordinateCountStillFiveIsTrue : consumerCoordinateCountStillFive ≡ true

    mandatoryFreshBYMAnalyticInequalityCountIsZero : Bool
    mandatoryFreshBYMAnalyticInequalityCountIsZeroIsTrue :
      mandatoryFreshBYMAnalyticInequalityCountIsZero ≡ true

    h1SourceLocalizationAlreadyOwned : Bool
    h1SourceLocalizationAlreadyOwnedIsTrue : h1SourceLocalizationAlreadyOwned ≡ true

    h2aO4TransportCompilerAlreadyOwned : Bool
    h2aO4TransportCompilerAlreadyOwnedIsTrue : h2aO4TransportCompilerAlreadyOwned ≡ true

    h2bWilsonBoundTheoremAlreadyOwned : Bool
    h2bWilsonBoundTheoremAlreadyOwnedIsTrue : h2bWilsonBoundTheoremAlreadyOwned ≡ true

    h2cIsSharedAnalysisCapabilityNotYMEstimate : Bool
    h2cIsSharedAnalysisCapabilityNotYMEstimateIsTrue :
      h2cIsSharedAnalysisCapabilityNotYMEstimate ≡ true

    h2cSharedClosureInhabitantStillRequired : Bool
    h2cSharedClosureInhabitantStillRequiredIsTrue :
      h2cSharedClosureInhabitantStillRequired ≡ true

    h3SpectralTransferAlreadyImported : Bool
    h3SpectralTransferAlreadyImportedIsTrue : h3SpectralTransferAlreadyImported ≡ true

    sameObjectApplicationDebtsStillReal : Bool
    sameObjectApplicationDebtsStillRealIsTrue : sameObjectApplicationDebtsStillReal ≡ true

canonicalRound330Boundary : Round330Boundary
canonicalRound330Boundary = round330-boundary
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl

round330H1SourceTheoremLevel : ProofLevel
round330H1SourceTheoremLevel = CMP116.cmp116DifferentiatedActivityLocalizationLevel

round330H2aCompilerLevel : ProofLevel
round330H2aCompilerLevel = O4.round276SpatialToTemporalO4CompilerLevel

round330H2bCompilerLevel : ProofLevel
round330H2bCompilerLevel = R315.round315BoundedTestCompilerLevel

round330H2cAdapterLevel : ProofLevel
round330H2cAdapterLevel = machineChecked

round330H3SpectralTransferLevel : ProofLevel
round330H3SpectralTransferLevel = R316.round316HalfRateClusteringSpectrumTransferLevel

round330PriorFrontierClassificationLevel : ProofLevel
round330PriorFrontierClassificationLevel = R329.round329ClassificationLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
