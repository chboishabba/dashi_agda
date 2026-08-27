module DASHI.Governance.InstitutionPreservingRechartAntiSublationExact where

------------------------------------------------------------------------
-- INSTITUTION-PRESERVING RECHART / SKELETON / ANTI-SUBLATION CONVERSE
--
-- Generic formalisation of the Brennan-style "skeleton of principle" shape
-- without attributing a theorem to any live court or jurisdiction.  Internal
-- admissibility of a rechart is indexed by the carrier's own required
-- invariants.  Failure to find an admissible host-side rechart does not refute
-- an independently constituted external state.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact as Ambient
import DASHI.Governance.DomainIndexedPeaceSubjectCarrier as Peace
import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice

------------------------------------------------------------------------
-- 1. Skeleton as carrier-relative required invariants.
------------------------------------------------------------------------

record Skeleton (State : Set) : Set₁ where
  constructor skeleton
  field
    Invariant : Set
    holds : State → Invariant → Set

open Skeleton public

record Rechart (State : Set) : Set where
  constructor rechart
  field
    transform : State → State

open Rechart public

record PreservesSkeleton
    {State : Set}
    (skel : Skeleton State)
    (chart : Rechart State) : Set₁ where
  constructor preservesSkeleton
  field
    preservation :
      (state : State) →
      (invariant : Invariant skel) →
      holds skel state invariant →
      holds skel (transform chart state) invariant

open PreservesSkeleton public

record AdmissibleRechart
    {State : Set}
    (skel : Skeleton State)
    (chart : Rechart State) : Set₁ where
  constructor admissibleRechart
  field
    skeletonPreserved : PreservesSkeleton skel chart
    authoritySource : Authority.AuthoritySource
    authorityAdmissible : Authority.AdmissibleAuthoritySource authoritySource

open AdmissibleRechart public

------------------------------------------------------------------------
-- 2. A finite internal skeleton example: a rechart can change one coordinate
--    while preserving a declared load-bearing coordinate.
------------------------------------------------------------------------

data InternalState : Set where
  inheritedState correctedState : InternalState

data InternalInvariant : Set where
  continuityInvariant : InternalInvariant

data ContinuityWitness : InternalState → InternalInvariant → Set where
  inheritedContinuity : ContinuityWitness inheritedState continuityInvariant
  correctedContinuity : ContinuityWitness correctedState continuityInvariant

internalSkeleton : Skeleton InternalState
internalSkeleton = skeleton InternalInvariant ContinuityWitness

correctionRechart : Rechart InternalState
correctionRechart =
  rechart (λ { inheritedState → correctedState ; correctedState → correctedState })

correctionPreservesSkeleton : PreservesSkeleton internalSkeleton correctionRechart
correctionPreservesSkeleton =
  preservesSkeleton
    (λ { inheritedState continuityInvariant inheritedContinuity → correctedContinuity
       ; correctedState continuityInvariant correctedContinuity → correctedContinuity })

canonicalAdmissibleCorrection :
  AdmissibleRechart internalSkeleton correctionRechart
canonicalAdmissibleCorrection =
  admissibleRechart
    correctionPreservesSkeleton
    Authority.constituencyMandate
    tt

------------------------------------------------------------------------
-- 3. Skeleton preservation is internal, not a supremacy rule over another
--    carrier.
------------------------------------------------------------------------

record ExternalValidityWitness : Set where
  constructor externalValidityWitness
  field
    externalState : Ambient.State Ambient.sourceCarrier
    independentAuthority : Authority.AuthoritySource
    independentAuthorityAdmissible :
      Authority.AdmissibleAuthoritySource independentAuthority

canonicalExternalValidity : ExternalValidityWitness
canonicalExternalValidity =
  externalValidityWitness
    Ambient.sourceExterior
    (Ambient.IndependentlyAuthoritativeExterior.independentAuthoritySource
      Ambient.canonicalIndependentExterior)
    (Ambient.IndependentlyAuthoritativeExterior.independentAuthorityAdmissible
      Ambient.canonicalIndependentExterior)

-- Host-side obstruction is represented as absence of an admitted interface
-- witness for this external state.  The external validity witness survives.
record NoAdmissibleHostRechartForExterior : Set where
  constructor noAdmissibleHostRechartForExterior
  field
    noInterfaceRepresentation :
      (meet : Ambient.Meet Ambient.canonicalPartialInterface) →
      Ambient.left Ambient.canonicalPartialInterface meet
        ≡ Ambient.sourceExterior →
      ⊥

canonicalNoAdmissibleHostRechartForExterior : NoAdmissibleHostRechartForExterior
canonicalNoAdmissibleHostRechartForExterior =
  noAdmissibleHostRechartForExterior
    (Ambient.ExteriorWitness.notRepresented Ambient.canonicalExterior)

record ExternalValiditySurvivesHostObstruction : Set where
  constructor externalValiditySurvivesHostObstruction
  field
    hostObstruction : NoAdmissibleHostRechartForExterior
    externalValidity : ExternalValidityWitness

hostObstructionDoesNotRefuteExternalValidity :
  ExternalValiditySurvivesHostObstruction
hostObstructionDoesNotRefuteExternalValidity =
  externalValiditySurvivesHostObstruction
    canonicalNoAdmissibleHostRechartForExterior
    canonicalExternalValidity

------------------------------------------------------------------------
-- 4. Historical derivation != current justification.
------------------------------------------------------------------------

data DerivationRoute : Set where
  inheritedHistoricalRoute reconstructedJustificationRoute : DerivationRoute

data PresentDoctrine : Set where
  retainedPresentDoctrine : PresentDoctrine

routePresent : DerivationRoute → PresentDoctrine
routePresent _ = retainedPresentDoctrine

samePresentDifferentDerivation :
  routePresent inheritedHistoricalRoute
  ≡ routePresent reconstructedJustificationRoute
samePresentDifferentDerivation = refl

derivationRoutesRemainDistinct :
  inheritedHistoricalRoute ≡ reconstructedJustificationRoute → ⊥
derivationRoutesRemainDistinct ()

record GenealogyJustificationSeparationWitness : Set where
  constructor genealogyJustificationSeparationWitness
  field
    historicalRoute : DerivationRoute
    justificatoryRoute : DerivationRoute
    sameCurrentSurface : routePresent historicalRoute ≡ routePresent justificatoryRoute
    routesNotIdentical : historicalRoute ≡ justificatoryRoute → ⊥

canonicalGenealogyJustificationSeparation :
  GenealogyJustificationSeparationWitness
canonicalGenealogyJustificationSeparation =
  genealogyJustificationSeparationWitness
    inheritedHistoricalRoute
    reconstructedJustificationRoute
    refl
    (λ ())

------------------------------------------------------------------------
-- 5. Order surface != justice closure: a direct observer witness.
------------------------------------------------------------------------

data PoliticalFineState : Set where
  justQuietState suppressedQuietState visibleConflictState : PoliticalFineState

data OrderObservation : Set where
  quietOrder visibleDisturbance : OrderObservation

data JusticeObservation : Set where
  justiceSatisfied justiceResidualOpen : JusticeObservation

orderObserver : Observer.Observer PoliticalFineState OrderObservation
orderObserver justQuietState = quietOrder
orderObserver suppressedQuietState = quietOrder
orderObserver visibleConflictState = visibleDisturbance

justiceObserver : Observer.Observer PoliticalFineState JusticeObservation
justiceObserver justQuietState = justiceSatisfied
justiceObserver suppressedQuietState = justiceResidualOpen
justiceObserver visibleConflictState = justiceResidualOpen

orderCollisionHidesJusticeDifference : Observer.ObserverCollision orderObserver
orderCollisionHidesJusticeDifference =
  Observer.observerCollision justQuietState suppressedQuietState refl (λ ())

orderObserverIsNotSeparating : Observer.Separating orderObserver → ⊥
orderObserverIsNotSeparating =
  Observer.collisionBlocksSeparation orderCollisionHidesJusticeDifference

justiceRefinesOrderAtQuietCollision :
  Observer.StrictRefinement orderObserver
    (Observer.pairObserver orderObserver justiceObserver)
justiceRefinesOrderAtQuietCollision =
  Observer.strictPairRefinement
    orderObserver justiceObserver
    justQuietState suppressedQuietState
    refl
    (λ ())

-- Quieting the public surface is therefore not a proof that the justice
-- residual closed.
quietSurfaceDoesNotDetermineJustice :
  orderObserver justQuietState ≡ orderObserver suppressedQuietState
  × (justiceObserver justQuietState ≡ justiceObserver suppressedQuietState → ⊥)
quietSurfaceDoesNotDetermineJustice = refl , (λ ())

------------------------------------------------------------------------
-- 6. Domain-local peace remains non-global under the existing theorem owner.
------------------------------------------------------------------------

domainLocalPeaceDoesNotBecomeGlobalJusticeCertificate :
  ∀ {P actor domain} {p : Peace.PeaceAt P actor domain} →
  Peace.DomainPeaceAutomaticallyGlobal p → ⊥
domainLocalPeaceDoesNotBecomeGlobalJusticeCertificate =
  Peace.domainPeaceDoesNotAutomaticallyGlobalise

forceStillDoesNotEstablishJustice : Justice.ForceAloneEstablishesJustice → ⊥
forceStillDoesNotEstablishJustice = Justice.forceDoesNotEstablishJustice

------------------------------------------------------------------------
-- 7. Boundary.
------------------------------------------------------------------------

record InstitutionPreservingRechartAntiSublationBoundary : Set where
  constructor institutionPreservingRechartAntiSublationBoundary
  field
    internalRechartMustPreserveDeclaredSkeleton : Bool
    internalSkeletonAutomaticallyBindsExternalCarrier : Bool
    hostObstructionRefutesExternalValidity : Bool
    currentJustificationEqualsHistoricalGenealogy : Bool
    quietOrderImpliesJusticeClosure : Bool
    domainPeaceImpliesGlobalJustice : Bool
    forceCreatesJustice : Bool
    externalValidityMaySurviveHostObstruction : Bool

canonicalInstitutionPreservingRechartAntiSublationBoundary :
  InstitutionPreservingRechartAntiSublationBoundary
canonicalInstitutionPreservingRechartAntiSublationBoundary =
  institutionPreservingRechartAntiSublationBoundary
    true false false false false false false true

institutionPreservingRechartAntiSublationStatement : String
institutionPreservingRechartAntiSublationStatement =
  "A carrier may permit a correction only through skeleton-preserving, authority-backed recharts, but that internal admissibility mask is not a universal supremacy theorem. Failure to represent or absorb an independently constituted exterior state is an obstruction in the host/interface algebra, not refutation of the exterior. Historical derivation and current justification may share a present surface while remaining distinct, and restoration of a quiet/order surface does not certify closure of the justice residual."
