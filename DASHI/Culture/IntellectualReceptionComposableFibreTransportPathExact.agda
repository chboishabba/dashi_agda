module DASHI.Culture.IntellectualReceptionComposableFibreTransportPathExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / COMPOSABLE FIBRE TRANSPORT PATHS
--
-- A reception fibre transport path is an indexed sequence of proof-relevant
-- FibreTransport receipts along one declared temporal history.  Concatenation
-- composes only already-installed transport legs.
--
-- The finite BIDI fixture below also separates coarse endpoint agreement and
-- path length from the ordered deposition/transport history.  In particular,
-- two histories may agree at their coarse t0/t2 endpoints while one acquires
-- authority on the first leg and carries it on the second, and the other keeps
-- authority absent on the first leg and acquires it on the second.
--
-- This is a DASHI reception-path construction.  It is not geometric parallel
-- transport, gauge holonomy, a physical worldline, or an asserted chronology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.IntellectualReceptionHistoryTimeIndexedFibreExact as Fibre
import DASHI.Culture.IntellectualReceptionHistoryTimeIndexedFibreTransportExact as Transport
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal

------------------------------------------------------------------------
-- 1. Indexed paths whose every edge carries a FibreTransport receipt.
------------------------------------------------------------------------

data FibreTransportPath
    (history : Temporal.TemporalReceptionHistory) :
    Temporal.ReceptionTime → Temporal.ReceptionTime → Set where

  pathRefl :
    ∀ {time} →
    FibreTransportPath history time time

  pathStep :
    ∀ {start middle finish} →
    Transport.FibreTransport history start middle →
    FibreTransportPath history middle finish →
    FibreTransportPath history start finish

appendPath :
  ∀ {history start middle finish} →
  FibreTransportPath history start middle →
  FibreTransportPath history middle finish →
  FibreTransportPath history start finish
appendPath pathRefl right = right
appendPath (pathStep edge rest) right =
  pathStep edge (appendPath rest right)

pathLength :
  ∀ {history start finish} →
  FibreTransportPath history start finish → Nat
pathLength pathRefl = 0
pathLength (pathStep edge rest) = suc (pathLength rest)

------------------------------------------------------------------------
-- 2. Canonical one- and two-leg movement-history paths.
------------------------------------------------------------------------

earlyAuthorityPath01 :
  FibreTransportPath
    Temporal.movementEarlyAuthorityHistory
    Temporal.t0 Temporal.t1
earlyAuthorityPath01 =
  pathStep
    (Transport.transport01 Temporal.movementEarlyAuthorityHistory)
    pathRefl

earlyAuthorityPath12 :
  FibreTransportPath
    Temporal.movementEarlyAuthorityHistory
    Temporal.t1 Temporal.t2
earlyAuthorityPath12 =
  pathStep
    (Transport.transport12 Temporal.movementEarlyAuthorityHistory)
    pathRefl

earlyAuthorityPath02 :
  FibreTransportPath
    Temporal.movementEarlyAuthorityHistory
    Temporal.t0 Temporal.t2
earlyAuthorityPath02 =
  appendPath earlyAuthorityPath01 earlyAuthorityPath12

lateAuthorityPath01 :
  FibreTransportPath
    Temporal.movementLateAuthorityHistory
    Temporal.t0 Temporal.t1
lateAuthorityPath01 =
  pathStep
    (Transport.transport01 Temporal.movementLateAuthorityHistory)
    pathRefl

lateAuthorityPath12 :
  FibreTransportPath
    Temporal.movementLateAuthorityHistory
    Temporal.t1 Temporal.t2
lateAuthorityPath12 =
  pathStep
    (Transport.transport12 Temporal.movementLateAuthorityHistory)
    pathRefl

lateAuthorityPath02 :
  FibreTransportPath
    Temporal.movementLateAuthorityHistory
    Temporal.t0 Temporal.t2
lateAuthorityPath02 =
  appendPath lateAuthorityPath01 lateAuthorityPath12

earlyAuthorityPathHasLengthTwo : pathLength earlyAuthorityPath02 ≡ 2
earlyAuthorityPathHasLengthTwo = refl

lateAuthorityPathHasLengthTwo : pathLength lateAuthorityPath02 ≡ 2
lateAuthorityPathHasLengthTwo = refl

------------------------------------------------------------------------
-- 3. Concatenation exposes the intended t0 -> t1 -> t2 transport law.
------------------------------------------------------------------------

earlyTransportCompositionIsPathConcatenation :
  appendPath earlyAuthorityPath01 earlyAuthorityPath12
  ≡ earlyAuthorityPath02
earlyTransportCompositionIsPathConcatenation = refl

lateTransportCompositionIsPathConcatenation :
  appendPath lateAuthorityPath01 lateAuthorityPath12
  ≡ lateAuthorityPath02
lateTransportCompositionIsPathConcatenation = refl

------------------------------------------------------------------------
-- 4. Both routes agree on the declared coarse t0/t2 endpoints.
------------------------------------------------------------------------

earlyLateSamePresentAtT0 :
  Fibre.present
    (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t0)
  ≡ Fibre.present
    (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t0)
earlyLateSamePresentAtT0 = refl

earlyLateSameFutureAtT0 :
  Fibre.futureCone
    (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t0)
  ≡ Fibre.futureCone
    (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t0)
earlyLateSameFutureAtT0 = refl

earlyLateSameAuthorityAtT0 :
  Fibre.authorityEnabled
    (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t0)
  ≡ Fibre.authorityEnabled
    (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t0)
earlyLateSameAuthorityAtT0 = refl

earlyLateSamePresentAtT2 :
  Fibre.present
    (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t2)
  ≡ Fibre.present
    (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t2)
earlyLateSamePresentAtT2 = refl

earlyLateSameFutureAtT2 :
  Fibre.futureCone
    (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t2)
  ≡ Fibre.futureCone
    (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t2)
earlyLateSameFutureAtT2 = refl

earlyLateSameAuthorityAtT2 :
  Fibre.authorityEnabled
    (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t2)
  ≡ Fibre.authorityEnabled
    (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t2)
earlyLateSameAuthorityAtT2 = refl

------------------------------------------------------------------------
-- 5. But the ordered authority-deposition/transport histories differ.
------------------------------------------------------------------------

data MovementTransportRouteCase : Set where
  earlyAuthorityRoute lateAuthorityRoute : MovementTransportRouteCase

data SameCoarseT0T2EndpointCode : Set where
  sameMovementT0T2Endpoints : SameCoarseT0T2EndpointCode

data TwoStepTransportLengthCode : Set where twoTransportSteps : TwoStepTransportLengthCode

data AuthorityTransportSignature : Set where
  acquiredThenCarried
  absentThenAcquired
  : AuthorityTransportSignature

coarseT0T2Endpoints : MovementTransportRouteCase → SameCoarseT0T2EndpointCode
coarseT0T2Endpoints _ = sameMovementT0T2Endpoints

transportLengthCode : MovementTransportRouteCase → TwoStepTransportLengthCode
transportLengthCode _ = twoTransportSteps

authorityTransportSignature : MovementTransportRouteCase → AuthorityTransportSignature
authorityTransportSignature earlyAuthorityRoute = acquiredThenCarried
authorityTransportSignature lateAuthorityRoute = absentThenAcquired

authorityTransportSignaturesDiffer :
  authorityTransportSignature earlyAuthorityRoute
  ≡ authorityTransportSignature lateAuthorityRoute → ⊥
authorityTransportSignaturesDiffer ()

sameCoarseEndpointsCannotRecoverOrderedTransportHistory :
  INF.FactorsThrough coarseT0T2Endpoints authorityTransportSignature → ⊥
sameCoarseEndpointsCannotRecoverOrderedTransportHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      earlyAuthorityRoute lateAuthorityRoute
      refl authorityTransportSignaturesDiffer)

samePathLengthCannotRecoverOrderedTransportHistory :
  INF.FactorsThrough transportLengthCode authorityTransportSignature → ⊥
samePathLengthCannotRecoverOrderedTransportHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      earlyAuthorityRoute lateAuthorityRoute
      refl authorityTransportSignaturesDiffer)

------------------------------------------------------------------------
-- 6. The signature corresponds to actual intermediate authority states.
------------------------------------------------------------------------

earlyAuthorityPresentAtT1 :
  Fibre.authorityEnabled
    (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t1)
  ≡ true
earlyAuthorityPresentAtT1 = refl

lateAuthorityAbsentAtT1 :
  Fibre.authorityEnabled
    (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t1)
  ≡ false
lateAuthorityAbsentAtT1 = refl

lateAuthorityPresentAtT2 :
  Fibre.authorityEnabled
    (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t2)
  ≡ true
lateAuthorityPresentAtT2 = refl

------------------------------------------------------------------------
-- 7. Endpoint agreement does not identify the composed path.
------------------------------------------------------------------------

data SameTerminalEndpointCase : Set where
  earlyTerminalRoute lateTerminalRoute : SameTerminalEndpointCase

data SameTerminalEndpointCode : Set where
  sameMovementAuthorityTerminal : SameTerminalEndpointCode

data ComposedPathHistoryCode : Set where
  earlyComposedHistory lateComposedHistory : ComposedPathHistoryCode

terminalEndpointCode : SameTerminalEndpointCase → SameTerminalEndpointCode
terminalEndpointCode _ = sameMovementAuthorityTerminal

composedPathHistoryCode : SameTerminalEndpointCase → ComposedPathHistoryCode
composedPathHistoryCode earlyTerminalRoute = earlyComposedHistory
composedPathHistoryCode lateTerminalRoute = lateComposedHistory

composedPathHistoriesDiffer :
  composedPathHistoryCode earlyTerminalRoute
  ≡ composedPathHistoryCode lateTerminalRoute → ⊥
composedPathHistoriesDiffer ()

sameTerminalEndpointCannotRecoverComposedTransportPath :
  INF.FactorsThrough terminalEndpointCode composedPathHistoryCode → ⊥
sameTerminalEndpointCannotRecoverComposedTransportPath =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      earlyTerminalRoute lateTerminalRoute
      refl composedPathHistoriesDiffer)

------------------------------------------------------------------------
-- 8. No-promotion boundaries.
------------------------------------------------------------------------

data FibreTransportPathPromotesGaugeHolonomy : Set where
data FibreTransportPathPromotesPhysicalWorldline : Set where
data FibreTransportPathPromotesActualChronology : Set where
data SameEndpointsPromoteSameTransportPath : Set where
data SameLengthPromotesSameTransportPath : Set where

aTransportPathDoesNotPromoteGaugeHolonomy :
  FibreTransportPathPromotesGaugeHolonomy → ⊥
aTransportPathDoesNotPromoteGaugeHolonomy ()

transportPathDoesNotPromotePhysicalWorldline :
  FibreTransportPathPromotesPhysicalWorldline → ⊥
transportPathDoesNotPromotePhysicalWorldline ()

transportPathDoesNotPromoteActualChronology :
  FibreTransportPathPromotesActualChronology → ⊥
transportPathDoesNotPromoteActualChronology ()

sameEndpointsDoNotPromoteSameTransportPath :
  SameEndpointsPromoteSameTransportPath → ⊥
sameEndpointsDoNotPromoteSameTransportPath ()

sameLengthDoesNotPromoteSameTransportPath :
  SameLengthPromotesSameTransportPath → ⊥
sameLengthDoesNotPromoteSameTransportPath ()

------------------------------------------------------------------------
-- 9. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionComposableFibreTransportPathBoundary : Set where
  constructor intellectual-reception-composable-fibre-transport-path-boundary
  field
    fibreTransportPathsCarryProofRelevantEdges : Bool
    transportPathsComposeByConcatenation : Bool
    sameCoarseEndpointsDetermineOrderedTransportHistory : Bool
    samePathLengthDeterminesOrderedTransportHistory : Bool
    sameTerminalEndpointDeterminesComposedPath : Bool
    transportPathIsGaugeHolonomy : Bool
    transportPathIsPhysicalWorldline : Bool
    transportPathIsActualChronology : Bool
    sourceAttributionBoundarySurvivesTransportComposition : Bool

canonicalIntellectualReceptionComposableFibreTransportPathBoundary :
  IntellectualReceptionComposableFibreTransportPathBoundary
canonicalIntellectualReceptionComposableFibreTransportPathBoundary =
  intellectual-reception-composable-fibre-transport-path-boundary
    true true false false false false false false true
