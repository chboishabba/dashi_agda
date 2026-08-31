module DASHI.Core.ContextGovernedLineageTransportExact where

------------------------------------------------------------------------
-- CONTEXT-INDEXED GOVERNED COORDINATE LINEAGE TRANSPORT
--
-- Consumer/governance safety and provenance-lineage preservation are separate
-- obligations.  A context/rechart transition may preserve the consumer-visible
-- value while erasing an inherited coordinate, and a later transition may add
-- new information on that nominal coordinate without restoring the old lineage.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.GovernedObservationProvenanceExact as Provenance

record ContextCoordinateLineage
    (Context Coordinate : Set) : Set₁ where
  constructor context-coordinate-lineage
  field
    lineageAt : Context → Coordinate → Provenance.CoordinateLineage

open ContextCoordinateLineage public

record LineageTransportReceipt
    {Context Coordinate : Set}
    (family : ContextCoordinateLineage Context Coordinate)
    (source target : Context) : Set₁ where
  constructor lineage-transport-receipt
  field
    effect : Coordinate → Provenance.CoordinateEffect
    transportEquation :
      (coordinate : Coordinate) →
      lineageAt family target coordinate
      ≡ Provenance.applyCoordinateEffect
          (effect coordinate)
          (lineageAt family source coordinate)

open LineageTransportReceipt public

-- A coordinate explicitly marked preserved retains exactly the same lineage.
preservedCoordinateRetainsLineage :
  ∀ {Context Coordinate : Set}
    {family : ContextCoordinateLineage Context Coordinate}
    {source target : Context}
    (receipt : LineageTransportReceipt family source target)
    (coordinate : Coordinate) →
  effect receipt coordinate ≡ Provenance.preservesCoordinate →
  lineageAt family target coordinate ≡ lineageAt family source coordinate
preservedCoordinateRetainsLineage receipt coordinate refl =
  transportEquation receipt coordinate

-- If an inherited coordinate is explicitly erased, the target lineage is
-- absent.  Consumer safety on some other axis does not alter this theorem.
erasedInheritedCoordinateBecomesAbsent :
  ∀ {Context Coordinate : Set}
    {family : ContextCoordinateLineage Context Coordinate}
    {source target : Context}
    (receipt : LineageTransportReceipt family source target)
    (coordinate : Coordinate) →
  lineageAt family source coordinate ≡ Provenance.inheritedCoordinate →
  effect receipt coordinate ≡ Provenance.erasesCoordinate →
  lineageAt family target coordinate ≡ Provenance.absentCoordinate
erasedInheritedCoordinateBecomesAbsent receipt coordinate refl refl =
  transportEquation receipt coordinate

-- Two context transitions compose coordinate-wise through the existing lineage
-- action.  This is deliberately not collapsed to a single surface-level flag.
twoStepTransportEquation :
  ∀ {Context Coordinate : Set}
    {family : ContextCoordinateLineage Context Coordinate}
    {first second third : Context}
    (firstReceipt : LineageTransportReceipt family first second)
    (secondReceipt : LineageTransportReceipt family second third)
    (coordinate : Coordinate) →
  lineageAt family third coordinate
  ≡ Provenance.applyTwoEffects
      (effect firstReceipt coordinate)
      (effect secondReceipt coordinate)
      (lineageAt family first coordinate)
twoStepTransportEquation firstReceipt secondReceipt coordinate =
  trans
    (transportEquation secondReceipt coordinate)
    (cong
      (Provenance.applyCoordinateEffect (effect secondReceipt coordinate))
      (transportEquation firstReceipt coordinate))

-- The crucial non-restoration theorem lifted from one abstract lineage to an
-- actual two-step context transport.
eraseThenAddAcrossContextsIsIntroduced :
  ∀ {Context Coordinate : Set}
    {family : ContextCoordinateLineage Context Coordinate}
    {first second third : Context}
    (firstReceipt : LineageTransportReceipt family first second)
    (secondReceipt : LineageTransportReceipt family second third)
    (coordinate : Coordinate) →
  lineageAt family first coordinate ≡ Provenance.inheritedCoordinate →
  effect firstReceipt coordinate ≡ Provenance.erasesCoordinate →
  effect secondReceipt coordinate ≡ Provenance.addsCoordinate →
  lineageAt family third coordinate ≡ Provenance.introducedCoordinate
eraseThenAddAcrossContextsIsIntroduced
  firstReceipt secondReceipt coordinate refl refl refl =
  trans
    (twoStepTransportEquation firstReceipt secondReceipt coordinate)
    Provenance.additionAfterErasureIsIntroducedNotInherited

eraseThenAddAcrossContextsDoesNotRestoreInherited :
  ∀ {Context Coordinate : Set}
    {family : ContextCoordinateLineage Context Coordinate}
    {first second third : Context}
    (firstReceipt : LineageTransportReceipt family first second)
    (secondReceipt : LineageTransportReceipt family second third)
    (coordinate : Coordinate) →
  lineageAt family first coordinate ≡ Provenance.inheritedCoordinate →
  effect firstReceipt coordinate ≡ Provenance.erasesCoordinate →
  effect secondReceipt coordinate ≡ Provenance.addsCoordinate →
  lineageAt family third coordinate ≡ Provenance.inheritedCoordinate →
  ⊥
eraseThenAddAcrossContextsDoesNotRestoreInherited
  firstReceipt secondReceipt coordinate sourceInherited firstErases secondAdds thirdInherited =
  Provenance.additionAfterErasureDoesNotRestoreInheritedLineage
    (trans
      (sym
        (eraseThenAddAcrossContextsIsIntroduced
          firstReceipt secondReceipt coordinate
          sourceInherited firstErases secondAdds))
      thirdInherited)

record ContextGovernedLineageTransportBoundary : Set where
  field
    transportEffectsAreCoordinateIndexed : Bool
    preservedCoordinateRetainsLineageExactly : Bool
    erasedInheritedCoordinateBecomesAbsentExactly : Bool
    twoStepEffectsComposeOnLineage : Bool
    eraseThenAddAcrossContextsRestoresInheritedLineage : Bool
    consumerSafetyAutomaticallyImpliesLineageIdentity : Bool

canonicalContextGovernedLineageTransportBoundary :
  ContextGovernedLineageTransportBoundary
canonicalContextGovernedLineageTransportBoundary = record
  { transportEffectsAreCoordinateIndexed = true
  ; preservedCoordinateRetainsLineageExactly = true
  ; erasedInheritedCoordinateBecomesAbsentExactly = true
  ; twoStepEffectsComposeOnLineage = true
  ; eraseThenAddAcrossContextsRestoresInheritedLineage = false
  ; consumerSafetyAutomaticallyImpliesLineageIdentity = false
  }
