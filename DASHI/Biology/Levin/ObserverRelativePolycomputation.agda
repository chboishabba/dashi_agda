module DASHI.Biology.Levin.ObserverRelativePolycomputation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.PolycomputationBiologyAdapter as Poly
import DASHI.Biology.Levin.BoundaryHiddenStateNonrecurrence as Hidden
import DASHI.Biology.Levin.SeparableBoundaryPersistence as Boundary

record ComputationReading : Set where
  field
    observerSpecified      : Bool
    observableSpecified    : Bool
    coarseGrainingSpecified : Bool
    encodingSpecified      : Bool
    transitionReadingSpecified : Bool
    decodingSpecified      : Bool
    interventionSemanticsSpecified : Bool
    interpretation         : String

record RelationalComputationWitness : Set where
  field
    samePhysicalEvents        : Bool
    firstReadingValid         : Bool
    secondReadingValid        : Bool
    readingsComputationallyDistinct : Bool
    neitherReadingExhaustsDynamics  : Bool
    compatibilityTestSpecified      : Bool

record ObserverRelativePolycomputationBoundary : Set where
  field
    biologyAdapter       : Poly.PolycomputationBiologyAdapter
    hiddenStateType      : Set
    boundaryType         : Set
    noPrivilegedComputationByDefault : Bool
    observerRelativeNotArbitrary     : Bool
    empiricalAdequacyStillRequired   : Bool
    internalPerspectiveNotRecoveredFromOutputAlone : Bool
    multipleReadingsNotMultipleConsciousSubjectsByDefinition : Bool
    interpretation : String

canonicalObserverRelativePolycomputationBoundary :
  ObserverRelativePolycomputationBoundary
canonicalObserverRelativePolycomputationBoundary = record
  { biologyAdapter = Poly.canonicalPolycomputationBiologyAdapter
  ; hiddenStateType = Hidden.HiddenStateNonrecurrenceBoundary
  ; boundaryType = Boundary.SeparableBoundaryPersistence
  ; noPrivilegedComputationByDefault = true
  ; observerRelativeNotArbitrary = true
  ; empiricalAdequacyStillRequired = true
  ; internalPerspectiveNotRecoveredFromOutputAlone = true
  ; multipleReadingsNotMultipleConsciousSubjectsByDefinition = true
  ; interpretation = "A computation is a typed relation among physical events, an observer or constraint, and an encoding-decoding practice; multiple adequate readings may coexist without exhausting the underlying dynamics"
  }
