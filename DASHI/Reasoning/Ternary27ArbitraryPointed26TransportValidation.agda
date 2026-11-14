module DASHI.Reasoning.Ternary27ArbitraryPointed26TransportValidation where

open import DASHI.Core.Prelude
open import Data.Sum.Base using (inj₁; inj₂)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Shape26
import DASHI.Reasoning.Ternary27ArbitraryPointed26TransportExact as Transport

selectedMapsToScalar :
  (selected : Geometry.Ternary27Point) →
  Transport.toSelectedShape selected selected ≡ inj₁ Exceptional.scalarLine
selectedMapsToScalar = Transport.selectedMapsToScalar

roundTripPoint :
  (selected point : Geometry.Ternary27Point) →
  Transport.fromSelectedShape selected (Transport.toSelectedShape selected point) ≡ point
roundTripPoint = Transport.fromAfterToSelected

roundTripShape :
  (selected : Geometry.Ternary27Point) →
  (shape : Shape26.CubeAlbert27) →
  Transport.toSelectedShape selected (Transport.fromSelectedShape selected shape) ≡ shape
roundTripShape = Transport.toAfterFromSelected

complementAvoidsSelected :
  (selected : Geometry.Ternary27Point) →
  (q : Shape26.NonOrigin26) →
  Transport.transportedComplementPoint selected q ≡ selected → ⊥
complementAvoidsSelected = Transport.transportedComplementNeverSelected

complementInjective :
  (selected : Geometry.Ternary27Point) →
  {left right : Shape26.NonOrigin26} →
  Transport.transportedComplementPoint selected left
  ≡ Transport.transportedComplementPoint selected right →
  left ≡ right
complementInjective = Transport.transportedComplementInjective

boundaryPointed :
  Transport.everySelectedPointHasExactOnePlus26 Transport.canonicalBoundary ≡ true
boundaryPointed = refl

boundaryNotGridSymmetry :
  Transport.recenteringPreservesNonperiodicGridAdjacencyByDefinition Transport.canonicalBoundary ≡ false
boundaryNotGridSymmetry = refl

end DASHI.Reasoning.Ternary27ArbitraryPointed26TransportValidation
