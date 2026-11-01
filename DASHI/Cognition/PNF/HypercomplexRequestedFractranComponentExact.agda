module DASHI.Cognition.PNF.HypercomplexRequestedFractranComponentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry

------------------------------------------------------------------------
-- A requested coordinate may sit over any fine carrier: vector/tensor,
-- hypercomplex algebra, graph, PNF bundle, temporal dependent state, or another
-- hyperfabric. SSPTrit is only the coarse sign observation of its compiled
-- signed FRACTRAN valuation.
------------------------------------------------------------------------

record RequestedFractranComponent : Set₁ where
  constructor requestedFractranComponent
  field
    FineCarrier : Set
    requestedPrime : Signed.SSPPrime
    compileValuation : FineCarrier → Context.ContextualValuation

open RequestedFractranComponent public

observeFine :
  (component : RequestedFractranComponent) →
  FineCarrier component →
  Trit.SSPTrit
observeFine component state =
  Context.coarseSSPTrit
    (compileValuation component state (requestedPrime component))

record CoarsePreimageFibre
  (component : RequestedFractranComponent)
  (coarse : Trit.SSPTrit)
  : Set₁ where
  constructor coarsePreimageFibre
  field
    fineState : FineCarrier component
    observationExact : observeFine component fineState ≡ coarse

open CoarsePreimageFibre public

observedAddress3 :
  (xComponent yComponent zComponent : RequestedFractranComponent) →
  FineCarrier xComponent →
  FineCarrier yComponent →
  FineCarrier zComponent →
  Geometry.Ternary27Point
observedAddress3 xComponent yComponent zComponent x y z =
  Geometry.ternary27Point
    (observeFine xComponent x)
    (observeFine yComponent y)
    (observeFine zComponent z)

record RequestedCubie3 : Set₁ where
  constructor requestedCubie3
  field
    xComponent yComponent zComponent : RequestedFractranComponent
    xState : FineCarrier xComponent
    yState : FineCarrier yComponent
    zState : FineCarrier zComponent
    coarseAddress : Geometry.Ternary27Point
    addressExact :
      coarseAddress ≡
      observedAddress3 xComponent yComponent zComponent xState yState zState

open RequestedCubie3 public

record FinePhaseTransport
  (source target : RequestedFractranComponent)
  : Set₁ where
  constructor finePhaseTransport
  field
    lift : FineCarrier source → FineCarrier target
    coarseIntertwines :
      (state : FineCarrier source) →
      observeFine target (lift state)
      ≡ Context.negateTrit (observeFine source state)

open FinePhaseTransport public

record HypercomplexComponentBoundary : Set where
  constructor hypercomplexComponentBoundary
  field
    fineCarrierIsDefinitionallySSPTrit : Bool
    cubieIsOneFineState : Bool
    tritIsOnlyCoarseSignedObservation : Bool
    finePhaseInversionMayBeNontrivial : Bool
    cubieAddressIsDerivedFromFineStates : Bool

canonicalHypercomplexComponentBoundary : HypercomplexComponentBoundary
canonicalHypercomplexComponentBoundary =
  hypercomplexComponentBoundary false false true true true
