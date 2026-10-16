module DASHI.Physics.QuantumVacuum.CasimirSide4CartanCurvatureClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (0ℚ)

import DASHI.Physics.Foundations.CMP119FlatSide4CurvatureStressExact as FlatStress
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as Flat
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Wilson

------------------------------------------------------------------------
-- LITERAL SIDE-4 CARTAN CLOSURE
--
-- The physical side-four SU(2) tangent field is three scalar bond fields.  A
-- Cartan-z restriction is therefore literally the statement that the x and y
-- Lie-coordinate bond fields vanish pointwise.  Since the repository curl is a
-- difference of forward differences, those two curl coordinates then vanish
-- exactly as well.  This is the finite derivative closure that the generic
-- continuum Cartan receipt intentionally did not assume.
------------------------------------------------------------------------

record Side4CartanBondField
    (field : Physical.PhysicalSU2BondField4) : Set where
  field
    coordinateXZero :
      ∀ site axis →
      field Physical.coordinateX (Hodge.pair site axis) ≡ 0ℚ

    coordinateYZero :
      ∀ site axis →
      field Physical.coordinateY (Hodge.pair site axis) ≡ 0ℚ

open Side4CartanBondField public

cartanCurlXZero :
  ∀ {field} →
  Side4CartanBondField field →
  ∀ left right site →
  Flat.plaquetteCurlCoordinate
    field Physical.coordinateX left right site ≡ 0ℚ
cartanCurlXZero restriction left right site
  rewrite coordinateXZero restriction (Hodge.shiftForward left site) right
        | coordinateXZero restriction site right
        | coordinateXZero restriction (Hodge.shiftForward right site) left
        | coordinateXZero restriction site left = refl

cartanCurlYZero :
  ∀ {field} →
  Side4CartanBondField field →
  ∀ left right site →
  Flat.plaquetteCurlCoordinate
    field Physical.coordinateY left right site ≡ 0ℚ
cartanCurlYZero restriction left right site
  rewrite coordinateYZero restriction (Hodge.shiftForward left site) right
        | coordinateYZero restriction site right
        | coordinateYZero restriction (Hodge.shiftForward right site) left
        | coordinateYZero restriction site left = refl

cartanLocalCurvatureVector :
  ∀ {field} →
  Side4CartanBondField field →
  ∀ left right site →
  FlatStress.localCurvatureVector field left right site
  ≡ Wilson.vec3
      0ℚ
      0ℚ
      (Flat.plaquetteCurlCoordinate
        field Physical.coordinateZ left right site)
cartanLocalCurvatureVector restriction left right site
  rewrite cartanCurlXZero restriction left right site
        | cartanCurlYZero restriction left right site = refl

------------------------------------------------------------------------
-- Authority boundary.
--
-- This theorem is exact on the existing literal flat/tangent side-four field.
-- The donor explicitly keeps identification of the selected nonlinear
-- CMP109/116 generated-action source with that field open.  Therefore this
-- compiler retires a second finite Cartan-curl calculation, but not the
-- same-object nonlinear transport.
------------------------------------------------------------------------

data FlatSide4CartanClosureAutomaticallyIdentifiesSelectedNonlinearCurvature : Set where

flatSide4ClosureDoesNotIdentifySelectedNonlinearCurvature :
  FlatSide4CartanClosureAutomaticallyIdentifiesSelectedNonlinearCurvature → ⊥
flatSide4ClosureDoesNotIdentifySelectedNonlinearCurvature ()

record CasimirSide4CartanCurvatureBoundary : Set where
  constructor casimir-side4-cartan-curvature-boundary
  field
    side4CartanFieldToCartanCurlCompilerOwned : Bool
    transverseLieCoordinateCurlVanishes : Bool
    selectedNonlinearFieldIdentifiedWithSide4FlatField : Bool

open CasimirSide4CartanCurvatureBoundary public

canonicalSide4CartanCurvatureBoundary : CasimirSide4CartanCurvatureBoundary
canonicalSide4CartanCurvatureBoundary =
  casimir-side4-cartan-curvature-boundary true true false

casimirSide4CartanCurvatureReading : String
casimirSide4CartanCurvatureReading =
  "On the literal side-four physical SU(2) tangent field, pointwise vanishing of the x/y Lie coordinates compiles exactly to vanishing of the x/y plaquette-curl coordinates; the local curvature vector is therefore Cartan-z. This is a genuine finite derivative theorem, not a new assumption. It does not identify the selected nonlinear CMP109/116/R457 field with the flat side-four field, so the remaining exterior-Cartan payment is same-object nonlinear transport rather than another curl calculation."
