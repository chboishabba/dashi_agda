module DASHI.Cognition.PNF.SensibLawUnsupportedDemandRoutingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawGWBv01UnsupportedResidualCertificationV04Exact as V04
import DASHI.Cognition.PNF.ContextualFractranDirectDeltaAdapterExact as ContextualDirect

------------------------------------------------------------------------
-- Consumer-indexed work routing over the certified v0.4 fine residual fibre.
--
-- This is NOT a semantic classifier. It only chooses the first producer/reviewer
-- family for the current legal-PNF workflow. Parser labels remain observations.
------------------------------------------------------------------------

data WorkRoute : Set where
  surfaceStructural
  relationAttachment
  nominalStructure
  predicateAction
  coordination
  parserUnknown : WorkRoute

route : V04.UnsupportedDependencyLabel → WorkRoute
route V04.punct = surfaceStructural
route V04.det = surfaceStructural
route V04.predet = surfaceStructural
route V04.intj = surfaceStructural
route V04.meta = surfaceStructural
route V04.prep = relationAttachment
route V04.pobj = relationAttachment
route V04.pcomp = relationAttachment
route V04.agent = relationAttachment
route V04.dative = relationAttachment
route V04.case = relationAttachment
route V04.prt = relationAttachment
route V04.compound = nominalStructure
route V04.poss = nominalStructure
route V04.nummod = nominalStructure
route V04.quantmod = nominalStructure
route V04.ROOT = predicateAction
route V04.attr = predicateAction
route V04.acomp = predicateAction
route V04.oprd = predicateAction
route V04.csubj = predicateAction
route V04.csubjpass = predicateAction
route V04.expl = predicateAction
route V04.parataxis = predicateAction
route V04.conj = coordination
route V04.cc = coordination
route V04.preconj = coordination
route V04.dep = parserUnknown

routeCount : WorkRoute → Nat
routeCount surfaceStructural = 173167
routeCount relationAttachment = 159562
routeCount nominalStructure = 88326
routeCount predicateAction = 55368
routeCount coordination = 43403
routeCount parserUnknown = 14168

routingTotal : Nat
routingTotal = 533994

record RoutingBoundary : Set where
  constructor routingBoundary
  field
    routingIsConsumerIndexed : Bool
    routingChangesSemanticAuthority : Bool
    routingChangesCanonicalObservation : Bool
    parserLabelDeterminesLegalMeaning : Bool
    workRouteDeterminesAdmittedNormativeDelta : Bool
    directRuntimeNeedsReplacement : Bool
    coarseRoutingMayIgnoreFineExecutionIdentity : Bool

canonicalRoutingBoundary : RoutingBoundary
canonicalRoutingBoundary =
  routingBoundary true false false false false false true

routingPreservesNoSecondRuntimeBoundary :
  ContextualDirect.requiresSecondRelationalRuntime
    ContextualDirect.canonicalDirectContextualBoundary
  ≡ false
routingPreservesNoSecondRuntimeBoundary = refl

routingUsesConsumerRelativeCoarseIdentity :
  ContextualDirect.consumerParityCanIgnoreFineExecutionIdentity
    ContextualDirect.canonicalDirectContextualBoundary
  ≡ true
routingUsesConsumerRelativeCoarseIdentity = refl

data WorkRouteIsLegalMeaning : Set where
data WorkRouteAuthorizesAdmission : Set where

workRouteIsNotLegalMeaning : WorkRouteIsLegalMeaning → ⊥
workRouteIsNotLegalMeaning ()

workRouteDoesNotAuthorizeAdmission : WorkRouteAuthorizesAdmission → ⊥
workRouteDoesNotAuthorizeAdmission ()
