module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlPolynomialExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- The public theorem is unchanged.  Its proof is now only a composition of
-- scalar atom-family recursion, scalar dot/coordinate transport, and three
-- independent four-variable coordinate curl identities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlGeometryExact public
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlAtomAssemblyExact as Atoms
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlDotCoordinateBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlCoordinatesExact as Curl

flatPlaquetteWilsonIsCurlSquare :
  ∀ forward0 forward1 inverse2 inverse3 →
  flatOrientedPlaquetteSecondVariation forward0 forward1 inverse2 inverse3
  ≡ vectorNormSq (plaquetteCurlVector forward0 forward1 inverse2 inverse3)
flatPlaquetteWilsonIsCurlSquare
    (vec3 x0 y0 z0) (vec3 x1 y1 z1)
    (vec3 x2 y2 z2) (vec3 x3 y3 z3) =
  trans
    (Atoms.flatSecondVariationRecursionDotExpansion
      (vec3 x0 y0 z0) (vec3 x1 y1 z1)
      (vec3 x2 y2 z2) (vec3 x3 y3 z3))
    (trans
      (Bridge.flatRecursionDotExpansionIsCoordinateSum
        x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3)
      (sym
        (Curl.flatCurlSquareCoordinateExpansion
          x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3)))
