module DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Wikimedia.IbrahimA027907PathCubeConvolutionAttributionProofExact as A027907

------------------------------------------------------------------------
-- TERNARY 27 = DISTINGUISHED ORIGIN + 26 NON-ORIGIN POINTS
--
-- This is the next carrier-level bridge after the A027907 convolution proof.
-- The exceptional owner defines the *shape*
--
--   Albert27 A = ScalarLine ⊎ J0 A.
--
-- Here we instantiate J0 with the literal 26 non-origin points of the existing
-- {-1,0,+1}^3 ternary cube and prove a two-sided bijection
--
--   Ternary27Point  <->  ScalarLine ⊎ NonOrigin26.
--
-- This pays the 1+26 carrier decomposition on the SAME ternary 27 object used
-- by the path-cube spectral lane.  It does not construct an Albert product,
-- cubic norm, F4 action, E6 action, or intertwiner.
------------------------------------------------------------------------

data NonOrigin26 : Set where
  nnn nnz nnp nzn nzz nzp npn npz npp : NonOrigin26
  znn znz znp zzn zzp zpn zpz zpp : NonOrigin26
  pnn pnz pnp pzn pzz pzp ppn ppz ppp : NonOrigin26

nonOriginConstructorCount : Nat
nonOriginConstructorCount = 26

cubeAlbertCarrier : Exceptional.AlbertCarrier
Exceptional.AlbertCarrier.J0 cubeAlbertCarrier = NonOrigin26

CubeAlbert27 : Set
CubeAlbert27 = Exceptional.Albert27 cubeAlbertCarrier

nonOriginToPoint : NonOrigin26 → Geometry.Ternary27Point
nonOriginToPoint nnn = Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne
nonOriginToPoint nnz = Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero
nonOriginToPoint nnp = Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne
nonOriginToPoint nzn = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne
nonOriginToPoint nzz = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero
nonOriginToPoint nzp = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne
nonOriginToPoint npn = Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne
nonOriginToPoint npz = Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero
nonOriginToPoint npp = Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne
nonOriginToPoint znn = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne
nonOriginToPoint znz = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero
nonOriginToPoint znp = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne
nonOriginToPoint zzn = Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne
nonOriginToPoint zzp = Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne
nonOriginToPoint zpn = Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne
nonOriginToPoint zpz = Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero
nonOriginToPoint zpp = Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne
nonOriginToPoint pnn = Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne
nonOriginToPoint pnz = Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero
nonOriginToPoint pnp = Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne
nonOriginToPoint pzn = Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne
nonOriginToPoint pzz = Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero
nonOriginToPoint pzp = Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne
nonOriginToPoint ppn = Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne
nonOriginToPoint ppz = Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero
nonOriginToPoint ppp = Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne

toAlbertShape : Geometry.Ternary27Point → CubeAlbert27
toAlbertShape (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = inj₂ nnn
toAlbertShape (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = inj₂ nnz
toAlbertShape (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = inj₂ nnp
toAlbertShape (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = inj₂ nzn
toAlbertShape (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = inj₂ nzz
toAlbertShape (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = inj₂ nzp
toAlbertShape (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = inj₂ npn
toAlbertShape (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = inj₂ npz
toAlbertShape (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = inj₂ npp
toAlbertShape (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = inj₂ znn
toAlbertShape (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = inj₂ znz
toAlbertShape (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = inj₂ znp
toAlbertShape (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = inj₂ zzn
toAlbertShape (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = inj₁ Exceptional.scalarLine
toAlbertShape (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = inj₂ zzp
toAlbertShape (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = inj₂ zpn
toAlbertShape (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = inj₂ zpz
toAlbertShape (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = inj₂ zpp
toAlbertShape (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = inj₂ pnn
toAlbertShape (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = inj₂ pnz
toAlbertShape (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = inj₂ pnp
toAlbertShape (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = inj₂ pzn
toAlbertShape (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = inj₂ pzz
toAlbertShape (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = inj₂ pzp
toAlbertShape (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = inj₂ ppn
toAlbertShape (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = inj₂ ppz
toAlbertShape (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = inj₂ ppp

fromAlbertShape : CubeAlbert27 → Geometry.Ternary27Point
fromAlbertShape (inj₁ Exceptional.scalarLine) = Geometry.origin
fromAlbertShape (inj₂ q) = nonOriginToPoint q

fromAfterTo : (p : Geometry.Ternary27Point) → fromAlbertShape (toAlbertShape p) ≡ p
fromAfterTo (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
fromAfterTo (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl

toAfterFrom : (a : CubeAlbert27) → toAlbertShape (fromAlbertShape a) ≡ a
toAfterFrom (inj₁ Exceptional.scalarLine) = refl
toAfterFrom (inj₂ nnn) = refl
toAfterFrom (inj₂ nnz) = refl
toAfterFrom (inj₂ nnp) = refl
toAfterFrom (inj₂ nzn) = refl
toAfterFrom (inj₂ nzz) = refl
toAfterFrom (inj₂ nzp) = refl
toAfterFrom (inj₂ npn) = refl
toAfterFrom (inj₂ npz) = refl
toAfterFrom (inj₂ npp) = refl
toAfterFrom (inj₂ znn) = refl
toAfterFrom (inj₂ znz) = refl
toAfterFrom (inj₂ znp) = refl
toAfterFrom (inj₂ zzn) = refl
toAfterFrom (inj₂ zzp) = refl
toAfterFrom (inj₂ zpn) = refl
toAfterFrom (inj₂ zpz) = refl
toAfterFrom (inj₂ zpp) = refl
toAfterFrom (inj₂ pnn) = refl
toAfterFrom (inj₂ pnz) = refl
toAfterFrom (inj₂ pnp) = refl
toAfterFrom (inj₂ pzn) = refl
toAfterFrom (inj₂ pzz) = refl
toAfterFrom (inj₂ pzp) = refl
toAfterFrom (inj₂ ppn) = refl
toAfterFrom (inj₂ ppz) = refl
toAfterFrom (inj₂ ppp) = refl

------------------------------------------------------------------------
-- The distinguished scalar really is the existing geometric origin.
------------------------------------------------------------------------

originMapsToScalar : toAlbertShape Geometry.origin ≡ inj₁ Exceptional.scalarLine
originMapsToScalar = refl

scalarMapsToOrigin : fromAlbertShape (inj₁ Exceptional.scalarLine) ≡ Geometry.origin
scalarMapsToOrigin = refl

------------------------------------------------------------------------
-- A027907 remains the spectral multiplicity proof on this same 27 carrier.
------------------------------------------------------------------------

pathRowSumStillTwentySeven : A027907.provedRowSum ≡ 27
pathRowSumStillTwentySeven = A027907.provedRowSumIsTwentySeven

------------------------------------------------------------------------
-- WrongType boundaries: carrier shape is not Albert algebra/action semantics.
------------------------------------------------------------------------

data CubeAlbertShapeCreatesJordanProduct : Set where
data CubeAlbertShapeCreatesF4Action : Set where
data CubeAlbertShapeCreatesE6MinusculeAction : Set where
data OriginEqualsAlbertIdentityElement : Set where

aBijectionDoesNotCreateJordanProduct : CubeAlbertShapeCreatesJordanProduct → ⊥
aBijectionDoesNotCreateJordanProduct ()

aBijectionDoesNotCreateF4Action : CubeAlbertShapeCreatesF4Action → ⊥
aBijectionDoesNotCreateF4Action ()

aBijectionDoesNotCreateE6Action : CubeAlbertShapeCreatesE6MinusculeAction → ⊥
aBijectionDoesNotCreateE6Action ()

originDistinguishedDoesNotIdentifyJordanUnit : OriginEqualsAlbertIdentityElement → ⊥
originDistinguishedDoesNotIdentifyJordanUnit ()

record Ternary27AlbertShapeFrontier : Set where
  constructor ternary27-albert-shape-frontier
  field
    literalTernary27CarrierReused : Bool
    explicitNonOrigin26ConstructorsPaid : Bool
    originPlus26BijectionPaid : Bool
    albert27ShapeInstantiatedOnSameCarrier : Bool
    originMapsToScalarSummand : Bool
    a027907SpectralRowRemainsAttached : Bool
    jordanProductPaid : Bool
    f4ActionPaid : Bool
    e6ActionPaid : Bool
    nextResidual : String
open Ternary27AlbertShapeFrontier public

currentTernary27AlbertShapeFrontier : Ternary27AlbertShapeFrontier
currentTernary27AlbertShapeFrontier = ternary27-albert-shape-frontier
  true true true true true true false false false
  "the cardinality wall is now removed: the SAME ternary 27 carrier has an exact origin + 26 decomposition matching the Albert27 sum shape. Next search for an existing Albert/Jordan product or cubic-norm carrier whose underlying 1+26 decomposition can be transported through this bijection. Only after a product-preservation theorem should F4/E6 action recognition be attempted; do not promote the distinguished ternary origin to the Albert/Jordan unit by shape alone."
