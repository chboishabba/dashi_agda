module DASHI.Culture.MissingDeceasedEventTimeConcentrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedCommonObjectProgrammeDiscriminatorExact as Common

------------------------------------------------------------------------
-- EVENT-TIME CONCENTRATION SURFACE
--
-- This owner keeps event identity separate from publication/source discovery
-- and does not report a population-level significance result until a sourced
-- comparison population and exposure denominator are supplied.
------------------------------------------------------------------------

record EventTimeCoordinate : Set where
  constructor event-time-coordinate
  field
    person : String
    eventClass : Common.EventClass
    eventDateOrRange : String
    ageOrExposureState : String
    workDateOrRange : String
    publicationDateOrRange : String
    sourceReference : String
    exactEventDatePaid : Bool
    eventClassPaid : Bool

open EventTimeCoordinate public

record EventTimeConcentrationContract : Set where
  constructor event-time-concentration-contract
  field
    cohortSize : Nat
    typedEventClassesRequired : Bool
    comparisonPopulationRequired : Bool
    ageOrExposureAdjustmentRequired : Bool
    publicationLagSeparated : Bool
    sourceDiscoveryLagSeparated : Bool
    populationLevelSignificancePaid : Bool

open EventTimeConcentrationContract public

canonicalEventTimeConcentrationContract : EventTimeConcentrationContract
canonicalEventTimeConcentrationContract = event-time-concentration-contract
  20 true true true true true false

calendarProximityPaysCausalProximity : Bool
calendarProximityPaysCausalProximity = false

publicationDateEqualsWorkDate : Bool
publicationDateEqualsWorkDate = false

deathDateEqualsDisappearanceDate : Bool
deathDateEqualsDisappearanceDate = false

posthumousPublicationPaysPostLossParticipation : Bool
posthumousPublicationPaysPostLossParticipation = false

staleWebpageDatePaysSuccessionDate : Bool
staleWebpageDatePaysSuccessionDate = false

populationLevelSignificancePaid : Bool
populationLevelSignificancePaid = false

nextPopulationLeaf : String
nextPopulationLeaf = "construct an institution/field/age/exposure comparison population before computing event-rate or concentration significance"
