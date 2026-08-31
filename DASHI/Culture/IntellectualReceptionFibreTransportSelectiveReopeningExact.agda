module DASHI.Culture.IntellectualReceptionFibreTransportSelectiveReopeningExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / PATH-LOCAL FIBRE TRANSPORT SELECTIVE REOPENING
--
-- A changed transport edge creates a reopening obligation only for certificates
-- whose declared transport path actually contains that edge instance.  The
-- resulting dependency then composes through the canonical reverse-dependency
-- closure.  Same semantic edge kind is deliberately too coarse.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.IntellectualReceptionComposableFibreTransportPathExact as Paths

------------------------------------------------------------------------
-- 1. Fine edge instances versus coarse semantic edge kinds.
------------------------------------------------------------------------

data TransportEdgeInstance : Set where
  earlyAcquire01
  earlyCarry12
  lateAbsent01
  lateAcquire12
  : TransportEdgeInstance

data TransportEdgeKind : Set where
  authorityAcquisition
  authorityCarry
  authorityAbsent
  : TransportEdgeKind

edgeKind : TransportEdgeInstance → TransportEdgeKind
edgeKind earlyAcquire01 = authorityAcquisition
edgeKind earlyCarry12 = authorityCarry
edgeKind lateAbsent01 = authorityAbsent
edgeKind lateAcquire12 = authorityAcquisition

earlyLateAcquisitionShareKind :
  edgeKind earlyAcquire01 ≡ edgeKind lateAcquire12
earlyLateAcquisitionShareKind = refl

data EdgeInstanceCase : Set where
  earlyAcquisitionInstance lateAcquisitionInstance : EdgeInstanceCase

coarseAcquisitionKind : EdgeInstanceCase → TransportEdgeKind
coarseAcquisitionKind _ = authorityAcquisition

fineAcquisitionInstance : EdgeInstanceCase → TransportEdgeInstance
fineAcquisitionInstance earlyAcquisitionInstance = earlyAcquire01
fineAcquisitionInstance lateAcquisitionInstance = lateAcquire12

acquisitionInstancesDiffer :
  fineAcquisitionInstance earlyAcquisitionInstance
  ≡ fineAcquisitionInstance lateAcquisitionInstance → ⊥
acquisitionInstancesDiffer ()

sameEdgeKindCannotRecoverEdgeInstance :
  INF.FactorsThrough coarseAcquisitionKind fineAcquisitionInstance → ⊥
sameEdgeKindCannotRecoverEdgeInstance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      earlyAcquisitionInstance
      lateAcquisitionInstance
      refl
      acquisitionInstancesDiffer)

------------------------------------------------------------------------
-- 2. Proof-relevant occurrence in the two canonical composed transport paths.
------------------------------------------------------------------------

data MovementRoute : Set where
  earlyRoute lateRoute : MovementRoute

data EdgeOccursInRoute : TransportEdgeInstance → MovementRoute → Set where
  earlyAcquireOccurs : EdgeOccursInRoute earlyAcquire01 earlyRoute
  earlyCarryOccurs : EdgeOccursInRoute earlyCarry12 earlyRoute
  lateAbsentOccurs : EdgeOccursInRoute lateAbsent01 lateRoute
  lateAcquireOccurs : EdgeOccursInRoute lateAcquire12 lateRoute

-- These route witnesses are anchored to the actual composed path objects from
-- the preceding owner rather than being free-floating route labels.

earlyRouteHasCanonicalPath :
  Paths.pathLength Paths.earlyAuthorityPath02 ≡ 2
earlyRouteHasCanonicalPath = Paths.earlyAuthorityPathHasLengthTwo

lateRouteHasCanonicalPath :
  Paths.pathLength Paths.lateAuthorityPath02 ≡ 2
lateRouteHasCanonicalPath = Paths.lateAuthorityPathHasLengthTwo

earlyAcquisitionDoesNotOccurInLateRoute :
  EdgeOccursInRoute earlyAcquire01 lateRoute → ⊥
earlyAcquisitionDoesNotOccurInLateRoute ()

lateAcquisitionDoesNotOccurInEarlyRoute :
  EdgeOccursInRoute lateAcquire12 earlyRoute → ⊥
lateAcquisitionDoesNotOccurInEarlyRoute ()

------------------------------------------------------------------------
-- 3. Certificates and dependency edges are path-instance qualified.
------------------------------------------------------------------------

data FibreCertificateArtifact : Set where
  earlyAcquire01Artifact
  lateAcquire12Artifact
  earlyTerminalFibreCertificate
  lateTerminalFibreCertificate
  earlyFutureUseCertificate
  lateFutureUseCertificate
  : FibreCertificateArtifact

data FibreCertificateDepends :
  FibreCertificateArtifact → FibreCertificateArtifact → Set where

  earlyPathOccurrenceCreatesDependency :
    EdgeOccursInRoute earlyAcquire01 earlyRoute →
    FibreCertificateDepends
      earlyAcquire01Artifact
      earlyTerminalFibreCertificate

  latePathOccurrenceCreatesDependency :
    EdgeOccursInRoute lateAcquire12 lateRoute →
    FibreCertificateDepends
      lateAcquire12Artifact
      lateTerminalFibreCertificate

  earlyTerminalFeedsFutureUse :
    FibreCertificateDepends
      earlyTerminalFibreCertificate
      earlyFutureUseCertificate

  lateTerminalFeedsFutureUse :
    FibreCertificateDepends
      lateTerminalFibreCertificate
      lateFutureUseCertificate

------------------------------------------------------------------------
-- 4. Actual path occurrence creates direct reopening obligations.
------------------------------------------------------------------------

earlyChangedEdgeReopensEarlyTerminal :
  Affected.ReopeningObligation
    FibreCertificateDepends
    earlyAcquire01Artifact
    earlyTerminalFibreCertificate
earlyChangedEdgeReopensEarlyTerminal =
  Affected.oneEdgeCreatesReopeningObligation
    (earlyPathOccurrenceCreatesDependency earlyAcquireOccurs)

lateChangedEdgeReopensLateTerminal :
  Affected.ReopeningObligation
    FibreCertificateDepends
    lateAcquire12Artifact
    lateTerminalFibreCertificate
lateChangedEdgeReopensLateTerminal =
  Affected.oneEdgeCreatesReopeningObligation
    (latePathOccurrenceCreatesDependency lateAcquireOccurs)

------------------------------------------------------------------------
-- 5. Reopening propagates transitively to downstream future-use certificates.
------------------------------------------------------------------------

earlyTerminalReopensEarlyFutureUse :
  Affected.ReopeningObligation
    FibreCertificateDepends
    earlyTerminalFibreCertificate
    earlyFutureUseCertificate
earlyTerminalReopensEarlyFutureUse =
  Affected.oneEdgeCreatesReopeningObligation earlyTerminalFeedsFutureUse

lateTerminalReopensLateFutureUse :
  Affected.ReopeningObligation
    FibreCertificateDepends
    lateTerminalFibreCertificate
    lateFutureUseCertificate
lateTerminalReopensLateFutureUse =
  Affected.oneEdgeCreatesReopeningObligation lateTerminalFeedsFutureUse

earlyChangedEdgeReopensEarlyFutureUse :
  Affected.ReopeningObligation
    FibreCertificateDepends
    earlyAcquire01Artifact
    earlyFutureUseCertificate
earlyChangedEdgeReopensEarlyFutureUse =
  Affected.obligationsCompose
    earlyChangedEdgeReopensEarlyTerminal
    earlyTerminalReopensEarlyFutureUse

lateChangedEdgeReopensLateFutureUse :
  Affected.ReopeningObligation
    FibreCertificateDepends
    lateAcquire12Artifact
    lateFutureUseCertificate
lateChangedEdgeReopensLateFutureUse =
  Affected.obligationsCompose
    lateChangedEdgeReopensLateTerminal
    lateTerminalReopensLateFutureUse

------------------------------------------------------------------------
-- 6. Same semantic edge kind cannot manufacture cross-route dependencies.
------------------------------------------------------------------------

earlyChangedEdgeDoesNotDirectlyDependOnLateTerminal :
  FibreCertificateDepends
    earlyAcquire01Artifact
    lateTerminalFibreCertificate → ⊥
earlyChangedEdgeDoesNotDirectlyDependOnLateTerminal ()

lateChangedEdgeDoesNotDirectlyDependOnEarlyTerminal :
  FibreCertificateDepends
    lateAcquire12Artifact
    earlyTerminalFibreCertificate → ⊥
lateChangedEdgeDoesNotDirectlyDependOnEarlyTerminal ()

-- Absence here is deliberately stated at the installed dependency-edge level:
-- a coarse authority-acquisition classification is insufficient to construct
-- the path-instance dependency receipt required by selective reopening.

data CoarseKindPromotesCrossRouteReopening : Set where

coarseKindDoesNotPromoteCrossRouteReopening :
  CoarseKindPromotesCrossRouteReopening → ⊥
coarseKindDoesNotPromoteCrossRouteReopening ()

------------------------------------------------------------------------
-- 7. Reopening means stale/reconsider, not automatic refutation.
------------------------------------------------------------------------

data ReopeningPromotesRefutation : Set where
data ReopeningPromotesHistoricalFalsity : Set where
data DependencyPathPromotesCausalNecessity : Set where

reopeningDoesNotPromoteRefutation : ReopeningPromotesRefutation → ⊥
reopeningDoesNotPromoteRefutation ()

reopeningDoesNotPromoteHistoricalFalsity :
  ReopeningPromotesHistoricalFalsity → ⊥
reopeningDoesNotPromoteHistoricalFalsity ()

dependencyPathDoesNotPromoteCausalNecessity :
  DependencyPathPromotesCausalNecessity → ⊥
dependencyPathDoesNotPromoteCausalNecessity ()

------------------------------------------------------------------------
-- 8. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionFibreTransportSelectiveReopeningBoundary : Set where
  constructor intellectual-reception-fibre-transport-selective-reopening-boundary
  field
    edgeInstanceOccurrenceIsProofRelevant : Bool
    sameEdgeKindDeterminesEdgeInstance : Bool
    traversedChangedEdgeCreatesLocalReopening : Bool
    reopeningPropagatesThroughDependencyClosure : Bool
    sameEdgeKindCreatesCrossRouteReopening : Bool
    reopeningMeansAutomaticRefutation : Bool
    dependencyPathIsCausalNecessity : Bool
    sourceAttributionBoundarySurvivesSelectiveReopening : Bool

canonicalIntellectualReceptionFibreTransportSelectiveReopeningBoundary :
  IntellectualReceptionFibreTransportSelectiveReopeningBoundary
canonicalIntellectualReceptionFibreTransportSelectiveReopeningBoundary =
  intellectual-reception-fibre-transport-selective-reopening-boundary
    true false true true false false false true
