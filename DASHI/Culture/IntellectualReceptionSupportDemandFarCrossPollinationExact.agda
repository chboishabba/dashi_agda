module DASHI.Culture.IntellectualReceptionSupportDemandFarCrossPollinationExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / SUPPORT-DEMAND NON-MONOTONICITY + FAR X-POLLINATION
--
-- A strictly richer certificate support can be easier to separate under the
-- current observation filtration.  This module proves that finite reversal and
-- then instantiates merged observer-refinement, experimental-coordinate,
-- discriminator-synthesis, residual-dependency, selection-topology and
-- representation-chart owners on the same reception fixture.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact as Reuse
import DASHI.Culture.IntellectualReceptionObserverDerivedSupportPartitionExact as ReceptionObserver
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal
import DASHI.Culture.IntellectualReceptionConsumerObservationDemandPreorderExact as Demand

import DASHI.Core.ObserverRefinementLatticeExact as ObserverLattice
import DASHI.Core.ExperimentalCoordinateDesignExact as Experimental
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Core.HistoryQualifiedSelectionTopologyExact as Selection
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.GovernedObservationProvenanceExact as Governed
import DASHI.Foundations.RepresentationChartInvariant as Representation

------------------------------------------------------------------------
-- 1. Proof-relevant support inclusion.
------------------------------------------------------------------------

record SupportIncluded
    (smaller larger : Reuse.CertificateSupport) : Set where
  constructor support-included
  field
    transportSupported :
      ∀ {coordinate} →
      Reuse.SupportedCoordinate smaller coordinate →
      Reuse.SupportedCoordinate larger coordinate

open SupportIncluded public

presentFutureIncludedInAuthority :
  SupportIncluded
    Reuse.presentFutureSupport
    Reuse.authoritySensitiveSupport
presentFutureIncludedInAuthority =
  support-included λ
    { Reuse.supportPresent → Reuse.supportPresent
    ; Reuse.supportFuture → Reuse.supportFuture
    }

presentFutureCannotSupportAuthority :
  Reuse.SupportedCoordinate
    Reuse.presentFutureSupport
    Reuse.authorityCoordinate → ⊥
presentFutureCannotSupportAuthority ()

record StrictSupportIncluded
    (smaller larger : Reuse.CertificateSupport) : Set where
  constructor strict-support-included
  field
    included : SupportIncluded smaller larger
    extraCoordinate : Reuse.PrefixCoordinate
    largerSupportsExtra : Reuse.SupportedCoordinate larger extraCoordinate
    smallerDoesNotSupportExtra :
      Reuse.SupportedCoordinate smaller extraCoordinate → ⊥

open StrictSupportIncluded public

presentFutureStrictlyIncludedInAuthority :
  StrictSupportIncluded
    Reuse.presentFutureSupport
    Reuse.authoritySensitiveSupport
presentFutureStrictlyIncludedInAuthority =
  strict-support-included
    presentFutureIncludedInAuthority
    Reuse.authorityCoordinate
    Reuse.supportAuthority
    presentFutureCannotSupportAuthority

------------------------------------------------------------------------
-- 2. Strict support enrichment reverses the naive demand monotonicity guess.
------------------------------------------------------------------------

record SupportInclusionDemandReversal : Set where
  constructor support-inclusion-demand-reversal
  field
    strictSupportGrowth :
      StrictSupportIncluded
        Reuse.presentFutureSupport
        Reuse.authoritySensitiveSupport

    richerSupportNoMoreDemanding :
      Demand.ConsumerNoMoreObservationDemanding
        Reuse.authoritySensitiveSupport
        Reuse.presentFutureSupport

    poorerSupportNotNoMoreDemanding :
      Demand.ConsumerNoMoreObservationDemanding
        Reuse.presentFutureSupport
        Reuse.authoritySensitiveSupport → ⊥

open SupportInclusionDemandReversal public

canonicalSupportInclusionDemandReversal : SupportInclusionDemandReversal
canonicalSupportInclusionDemandReversal =
  support-inclusion-demand-reversal
    presentFutureStrictlyIncludedInAuthority
    Demand.authorityNoMoreDemandingThanPresentFuture
    Demand.presentFutureNotNoMoreDemandingThanAuthority

-- Hence support inclusion is not monotone in the direction
-- "larger support => finer separation observation required".
data LargerSupportMustRequireFinerObservation : Set where

largerSupportDoesNotForceFinerObservation :
  LargerSupportMustRequireFinerObservation → ⊥
largerSupportDoesNotForceFinerObservation ()

------------------------------------------------------------------------
-- 3. Observer-lattice x-pollination: adding authority strictly refines the
-- present/future observer on the canonical early/late collision.
------------------------------------------------------------------------

coarsePresentFutureObservation :
  Temporal.TemporalReceptionHistory →
  ReceptionObserver.ObserverValue × ReceptionObserver.ObserverValue
coarsePresentFutureObservation history =
  ReceptionObserver.observeAtT1 history Reuse.presentCoordinate ,
  ReceptionObserver.observeAtT1 history Reuse.futureCoordinate

authorityObservation :
  Temporal.TemporalReceptionHistory → ReceptionObserver.ObserverValue
authorityObservation history =
  ReceptionObserver.observeAtT1 history Reuse.authorityCoordinate

coarsePresentFutureCollision :
  coarsePresentFutureObservation Temporal.movementEarlyAuthorityHistory
  ≡ coarsePresentFutureObservation Temporal.movementLateAuthorityHistory
coarsePresentFutureCollision = refl

authorityStrictlyRefinesPresentFuture :
  ObserverLattice.StrictRefinement
    coarsePresentFutureObservation
    (ObserverLattice.pairObserver
      coarsePresentFutureObservation authorityObservation)
authorityStrictlyRefinesPresentFuture =
  ObserverLattice.strictPairRefinement
    coarsePresentFutureObservation
    authorityObservation
    Temporal.movementEarlyAuthorityHistory
    Temporal.movementLateAuthorityHistory
    coarsePresentFutureCollision
    ReceptionObserver.authorityDivergentByObserver

------------------------------------------------------------------------
-- 4. Experimental-coordinate x-pollination: authority is an explicit measured
-- coordinate whose read separates the currently collapsed history pair.
------------------------------------------------------------------------

data ReceptionInformationDimension : Set where
  receptionInformationDimension : ReceptionInformationDimension

data InspectionControl : Set where
  inspectOnly : InspectionControl

coordinateRole : Reuse.PrefixCoordinate → Experimental.CoordinateRole
coordinateRole Reuse.presentCoordinate = Experimental.measuredObservable
coordinateRole Reuse.futureCoordinate = Experimental.measuredObservable
coordinateRole Reuse.authorityCoordinate = Experimental.measuredObservable

coordinateDimension : Reuse.PrefixCoordinate → ReceptionInformationDimension
coordinateDimension coordinate = receptionInformationDimension

applyInspection :
  InspectionControl →
  Temporal.TemporalReceptionHistory →
  Temporal.TemporalReceptionHistory
applyInspection inspectOnly history = history

coordinateReference : Reuse.PrefixCoordinate → String
coordinateReference Reuse.presentCoordinate = "reception-present-at-t1"
coordinateReference Reuse.futureCoordinate = "reception-future-cone-at-t1"
coordinateReference Reuse.authorityCoordinate = "reception-authority-at-t1"

coordinateCalibration : Reuse.PrefixCoordinate → String
coordinateCalibration Reuse.presentCoordinate = "canonical fibre present projection"
coordinateCalibration Reuse.futureCoordinate = "canonical fibre future-cone projection"
coordinateCalibration Reuse.authorityCoordinate = "canonical authority-enabled observation"

inspectionReference : InspectionControl → String
inspectionReference inspectOnly = "read-only reception-history inspection"

receptionExperimentalDesign :
  Experimental.ExperimentalCoordinateDesign
    Temporal.TemporalReceptionHistory
    InspectionControl
    ReceptionObserver.ObserverValue
    ReceptionInformationDimension
receptionExperimentalDesign =
  Experimental.experimentalCoordinateDesign
    Reuse.PrefixCoordinate
    coordinateRole
    coordinateDimension
    ReceptionObserver.observeAtT1
    applyInspection
    coordinateReference
    (λ coordinate → "reception information dimension")
    coordinateCalibration
    inspectionReference

authorityCoordinateSeparatesCollision :
  Experimental.CoordinateSeparatesCollision
    receptionExperimentalDesign
    coarsePresentFutureObservation
authorityCoordinateSeparatesCollision =
  Experimental.coordinateSeparatesCollision
    Reuse.authorityCoordinate
    Temporal.movementEarlyAuthorityHistory
    Temporal.movementLateAuthorityHistory
    coarsePresentFutureCollision
    ReceptionObserver.authorityDivergentByObserver

------------------------------------------------------------------------
-- 5. Discriminator-synthesis x-pollination: the same authority coordinate is
-- packaged as an information-language extension of the coarse observer.
------------------------------------------------------------------------

authorityExperimentBundle :
  Discriminator.ExperimentBundle Temporal.TemporalReceptionHistory
authorityExperimentBundle =
  Discriminator.experimentBundle
    ReceptionObserver.ObserverValue
    authorityObservation
    1
    "authority-at-t1 discriminator bundle"
    "canonical early/late authority divergence receipt"

authorityCurrentCollision :
  Discriminator.CurrentObserverCollision coarsePresentFutureObservation
authorityCurrentCollision =
  Discriminator.currentObserverCollision
    Temporal.movementEarlyAuthorityHistory
    Temporal.movementLateAuthorityHistory
    coarsePresentFutureCollision

authorityBundleSeparates :
  Discriminator.BundleSeparates
    authorityExperimentBundle
    Temporal.movementEarlyAuthorityHistory
    Temporal.movementLateAuthorityHistory
authorityBundleSeparates =
  Discriminator.bundleSeparates ReceptionObserver.authorityDivergentByObserver

authorityDiscriminatingLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension coarsePresentFutureObservation
authorityDiscriminatingLanguageExtension =
  Discriminator.discriminatingLanguageExtension
    authorityCurrentCollision
    authorityExperimentBundle
    authorityBundleSeparates

authorityJoinSeparatesEarlyLate :
  Discriminator.joinedObservation
    coarsePresentFutureObservation
    authorityExperimentBundle
    Temporal.movementEarlyAuthorityHistory
  ≡ Discriminator.joinedObservation
    coarsePresentFutureObservation
    authorityExperimentBundle
    Temporal.movementLateAuthorityHistory → ⊥
authorityJoinSeparatesEarlyLate =
  Discriminator.extensionJoinSeparates authorityDiscriminatingLanguageExtension

------------------------------------------------------------------------
-- 6. Residual-dependency / discrepancy-calibrated preorder x-pollination.
-- The score merely mirrors the finite demand comparison; it is not spectral.
------------------------------------------------------------------------

separationDemandScore :
  Residual.CouplingScore ⊤ Reuse.CertificateSupport
separationDemandScore tt Reuse.authoritySensitiveSupport = 0
separationDemandScore tt Reuse.presentFutureSupport = 1

authorityNoWorseByResidualPreorder :
  Residual.NoWorseCoupled
    separationDemandScore
    tt
    Reuse.authoritySensitiveSupport
    Reuse.presentFutureSupport
authorityNoWorseByResidualPreorder = z≤n

------------------------------------------------------------------------
-- 7. Selection-topology / nonfactorability precedent remains available:
-- same candidate field does not determine selected frontier.
------------------------------------------------------------------------

selectionTopologyStillNonFactorable :
  INF.FactorsThrough Selection.fieldOf Selection.selectedFrontier → ⊥
selectionTopologyStillNonFactorable =
  Selection.candidateFieldCannotRecoverSelectedFrontier

------------------------------------------------------------------------
-- 8. Representation-chart precedent: equivalent invariant value does not make
-- chart identity the semantic carrier.  This stays independent of demand order.
------------------------------------------------------------------------

binaryHalfPresentationStillPreservesInvariant :
  Representation.RatioEquivalent
    Representation.binaryPointOne
    Representation.oneHalf
binaryHalfPresentationStillPreservesInvariant =
  Representation.binaryPointOneIsOneHalf

representationAuthorityBoundaryRetained :
  Representation.RepresentationAuthorityBoundary
representationAuthorityBoundaryRetained =
  Representation.canonicalRepresentationAuthorityBoundary

------------------------------------------------------------------------
-- 9. Governed-observation precedent: newly added information carries its own
-- lineage and does not restore erased inherited authority/provenance.
------------------------------------------------------------------------

eraseThenAddStillIntroduced :
  Governed.applyTwoEffects
    Governed.erasesCoordinate
    Governed.addsCoordinate
    Governed.inheritedCoordinate
  ≡ Governed.introducedCoordinate
eraseThenAddStillIntroduced =
  Governed.additionAfterErasureIsIntroducedNotInherited

------------------------------------------------------------------------
-- 10. No-promotion boundaries for the wide x-pollination.
------------------------------------------------------------------------

data RicherSupportPromotesGreaterTruth : Set where
data EasierSeparationPromotesLowerImportance : Set where
data StrictObserverRefinementPromotesWorldCompleteness : Set where
data ExperimentalCoordinatePromotesPhysicalDimension : Set where
data FiniteDemandScorePromotesSpectralIndependence : Set where
data TopologyAnalogyPromotesHistoricalNecessity : Set where

data RepresentationAnalogyPromotesChartIdentity : Set where

richerSupportDoesNotPromoteGreaterTruth : RicherSupportPromotesGreaterTruth → ⊥
richerSupportDoesNotPromoteGreaterTruth ()

easierSeparationDoesNotPromoteLowerImportance :
  EasierSeparationPromotesLowerImportance → ⊥
easierSeparationDoesNotPromoteLowerImportance ()

strictObserverRefinementDoesNotPromoteWorldCompleteness :
  StrictObserverRefinementPromotesWorldCompleteness → ⊥
strictObserverRefinementDoesNotPromoteWorldCompleteness ()

experimentalCoordinateDoesNotPromotePhysicalDimension :
  ExperimentalCoordinatePromotesPhysicalDimension → ⊥
experimentalCoordinateDoesNotPromotePhysicalDimension ()

finiteDemandScoreDoesNotPromoteSpectralIndependence :
  FiniteDemandScorePromotesSpectralIndependence → ⊥
finiteDemandScoreDoesNotPromoteSpectralIndependence ()

topologyAnalogyDoesNotPromoteHistoricalNecessity :
  TopologyAnalogyPromotesHistoricalNecessity → ⊥
topologyAnalogyDoesNotPromoteHistoricalNecessity ()

representationAnalogyDoesNotPromoteChartIdentity :
  RepresentationAnalogyPromotesChartIdentity → ⊥
representationAnalogyDoesNotPromoteChartIdentity ()

------------------------------------------------------------------------
-- 11. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionSupportDemandFarCrossPollinationBoundary : Set where
  constructor intellectual-reception-support-demand-far-cross-pollination-boundary
  field
    presentFutureSupportStrictlyIncludedInAuthoritySupport : Bool
    richerAuthoritySupportIsEasierToSeparateHere : Bool
    supportInclusionMonotoneWithObservationDemand : Bool
    authorityStrictlyRefinesPresentFutureObserver : Bool
    authorityIsExplicitExperimentalSeparator : Bool
    authorityFormsDiscriminatingLanguageExtension : Bool
    residualPreorderCanEncodeSameFiniteComparison : Bool
    finiteDemandScoreIsSpectralIndependenceConstant : Bool
    selectionTopologyNonfactorabilityRetained : Bool
    representationChartBoundaryRetained : Bool
    governedCoordinateLineageBoundaryRetained : Bool
    crossDomainAnalogyRanksTruthOrImportance : Bool
    sourceAttributionBoundarySurvivesFarCrossPollination : Bool

canonicalIntellectualReceptionSupportDemandFarCrossPollinationBoundary :
  IntellectualReceptionSupportDemandFarCrossPollinationBoundary
canonicalIntellectualReceptionSupportDemandFarCrossPollinationBoundary =
  intellectual-reception-support-demand-far-cross-pollination-boundary
    true true false true true true true false true true true false true
