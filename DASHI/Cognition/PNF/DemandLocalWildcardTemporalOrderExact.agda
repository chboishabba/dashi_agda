{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.DemandLocalWildcardTemporalOrderExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardExact as Wildcard

------------------------------------------------------------------------
-- DEMAND-LOCAL TEMPORAL RESTRICTION MUST PRECEDE OBJECT QUOTIENTING
--
-- The sparse wildcard regression exposed a generic non-commutation hazard:
-- collapsing an object fibre to one global representative and only afterwards
-- applying a demand-local time restriction can hide an earlier representative
-- that is still admissible for that demand.
--
-- The safe carrier therefore has the order
--
--   fine representatives
--     -> restrict to the demand-local admissible fibre
--     -> quotient equivalent nearest representatives
--
-- rather than quotienting globally first.
------------------------------------------------------------------------

record RestrictionQuotientSystem
  (Fine Restricted Quotient : Set) : Set₁ where
  field
    restrictFine : Fine → Restricted
    quotientFine : Fine → Quotient
    quotientRestricted : Restricted → Quotient
    restrictQuotient : Quotient → Quotient

open RestrictionQuotientSystem public

record RestrictionQuotientCommutation
  {Fine Restricted Quotient : Set}
  (system : RestrictionQuotientSystem Fine Restricted Quotient) : Set where
  field
    commutes :
      (fine : Fine) →
      restrictQuotient system (quotientFine system fine)
        ≡ quotientRestricted system (restrictFine system fine)

open RestrictionQuotientCommutation public

commutingGlobalQuotientMayImplementRestrictionFirst :
  ∀ {Fine Restricted Quotient : Set}
    (system : RestrictionQuotientSystem Fine Restricted Quotient) →
  RestrictionQuotientCommutation system →
  (fine : Fine) →
  restrictQuotient system (quotientFine system fine)
    ≡ quotientRestricted system (restrictFine system fine)
commutingGlobalQuotientMayImplementRestrictionFirst system certificate =
  commutes certificate

------------------------------------------------------------------------
-- Runtime-oriented demand-local representative contract.
--
-- ActiveSegment is an already-restricted object/position fibre.  Exactness of
-- the compressed temporal carrier means each demand/object pair sees exactly
-- the same nearest-eligible segment relation as the legacy raw-profile semantics.
-- Score ambiguity inside that segment remains a separate interval fibre and is
-- handled by the existing MUST/MAY theorem.
------------------------------------------------------------------------

record DemandLocalTemporalCarrier
  (Demand Object ActiveSegment : Set) : Set₁ where
  field
    LegacyNearestEligible : Demand → Object → ActiveSegment → Set
    ActiveForDemand : Demand → Object → ActiveSegment → Set

    activeSound :
      ∀ demand object segment →
      ActiveForDemand demand object segment →
      LegacyNearestEligible demand object segment

    activeComplete :
      ∀ demand object segment →
      LegacyNearestEligible demand object segment →
      ActiveForDemand demand object segment

open DemandLocalTemporalCarrier public

demandLocalCarrierIsExtensionallyLegacyExact :
  ∀ {Demand Object ActiveSegment : Set}
    (carrier : DemandLocalTemporalCarrier Demand Object ActiveSegment) →
    (demand : Demand) →
    (object : Object) →
    (segment : ActiveSegment) →
  Wildcard._↔_
    (ActiveForDemand carrier demand object segment)
    (LegacyNearestEligible carrier demand object segment)
demandLocalCarrierIsExtensionallyLegacyExact carrier demand object segment =
  Wildcard.iff
    (activeSound carrier demand object segment)
    (activeComplete carrier demand object segment)

------------------------------------------------------------------------
-- No theorem below promotes a globally collapsed representative merely because
-- it is cheaper.  A global quotient may be used only with an explicit
-- commutation certificate.  Otherwise the implementation must use the
-- restriction-first carrier above.
------------------------------------------------------------------------

data GlobalQuotientWithoutCommutationPermission : Set where

globalQuotientWithoutCommutationIsForbidden :
  GlobalQuotientWithoutCommutationPermission → ⊥
globalQuotientWithoutCommutationIsForbidden ()
