module DASHI.Moonshine.JInvariant369ReflectionEquivarianceExact where

------------------------------------------------------------------------
-- J-PHASE REFLECTION -> FINITE OBSERVER EQUIVARIANCE
--
-- This owner upgrades the finite 3/6/9/27 observers from mere equal-sector
-- bookkeeping to an explicit equivariance target.
--
-- The continuous phase reflection remains supplied by the analytic renderer.
-- The finite target actions below are concrete involutions:
--
--   C3  : balanced-trit sign reversal,
--   C6  : k |-> -k mod 6,
--   C9  : coordinatewise balanced-trit reversal on NineSheet,
--   27  : coordinatewise sign reversal on the existing 3x3x3 hypervoxel.
--
-- Once a renderer proves that its phase quantisers intertwine continuous
-- reflection with these finite actions, the commuting squares are theorems.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Base369 as Base
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render

------------------------------------------------------------------------
-- 1. Concrete finite reflection actions.
------------------------------------------------------------------------

reflect3 : Triadic.KernelTrit → Triadic.KernelTrit
reflect3 = Triadic.negateTrit

reflect3Involutive :
  (x : Triadic.KernelTrit) →
  reflect3 (reflect3 x) ≡ x
reflect3Involutive = Triadic.negateTritInvolutive

reflect6 : Base.HexTruth → Base.HexTruth
reflect6 Base.hex-0 = Base.hex-0
reflect6 Base.hex-1 = Base.hex-5
reflect6 Base.hex-2 = Base.hex-4
reflect6 Base.hex-3 = Base.hex-3
reflect6 Base.hex-4 = Base.hex-2
reflect6 Base.hex-5 = Base.hex-1

reflect6Involutive :
  (x : Base.HexTruth) →
  reflect6 (reflect6 x) ≡ x
reflect6Involutive Base.hex-0 = refl
reflect6Involutive Base.hex-1 = refl
reflect6Involutive Base.hex-2 = refl
reflect6Involutive Base.hex-3 = refl
reflect6Involutive Base.hex-4 = refl
reflect6Involutive Base.hex-5 = refl

reflect9 : Triadic.NineSheet → Triadic.NineSheet
reflect9 = Triadic.negateNine

reflect9Involutive :
  (x : Triadic.NineSheet) →
  reflect9 (reflect9 x) ≡ x
reflect9Involutive (a , b)
  rewrite Triadic.negateTritInvolutive a
        | Triadic.negateTritInvolutive b = refl

negateSSP : SSP.SSPTrit → SSP.SSPTrit
negateSSP SSP.sspNegOne = SSP.sspPosOne
negateSSP SSP.sspZero = SSP.sspZero
negateSSP SSP.sspPosOne = SSP.sspNegOne

negateSSPInvolutive :
  (x : SSP.SSPTrit) →
  negateSSP (negateSSP x) ≡ x
negateSSPInvolutive SSP.sspNegOne = refl
negateSSPInvolutive SSP.sspZero = refl
negateSSPInvolutive SSP.sspPosOne = refl

reflect27 : Fabric.Ternary27Point → Fabric.Ternary27Point
reflect27 p =
  Fabric.ternary27Point
    (negateSSP (Fabric.x p))
    (negateSSP (Fabric.y p))
    (negateSSP (Fabric.z p))

reflect27Involutive :
  (p : Fabric.Ternary27Point) →
  reflect27 (reflect27 p) ≡ p
reflect27Involutive (Fabric.ternary27Point x y z)
  rewrite negateSSPInvolutive x
        | negateSSPInvolutive y
        | negateSSPInvolutive z = refl

------------------------------------------------------------------------
-- 2. Equivariance interface.
--
-- This is deliberately stronger than cardinality coincidence.  Each observer
-- must intertwine the SAME continuous reflection with its target involution.
------------------------------------------------------------------------

record J369ReflectionEquivariance
    (R : Render.JPhaseRenderingAlgebra) : Set₁ where
  constructor j369-reflection-equivariance
  field
    reflectPoint :
      DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact.Point
        (Render.klein R)
      →
      DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact.Point
        (Render.klein R)

    reflectPhase :
      Render.Phase R → Render.Phase R

    phaseReflection :
      (z :
        DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact.Point
          (Render.klein R)) →
      Render.jPhase R (reflectPoint z)
      ≡
      reflectPhase (Render.jPhase R z)

    observer3Intertwines :
      (phase : Render.Phase R) →
      Render.phase3 R (reflectPhase phase)
      ≡ reflect3 (Render.phase3 R phase)

    observer6Intertwines :
      (phase : Render.Phase R) →
      Render.phase6 R (reflectPhase phase)
      ≡ reflect6 (Render.phase6 R phase)

    observer9Intertwines :
      (phase : Render.Phase R) →
      Render.phase9 R (reflectPhase phase)
      ≡ reflect9 (Render.phase9 R phase)

    observer27Intertwines :
      (phase : Render.Phase R) →
      Render.phase27 R (reflectPhase phase)
      ≡ reflect27 (Render.phase27 R phase)

open J369ReflectionEquivariance public

------------------------------------------------------------------------
-- 3. The four commuting squares.
------------------------------------------------------------------------

observer3ReflectionCommutes :
  (R : Render.JPhaseRenderingAlgebra) →
  (E : J369ReflectionEquivariance R) →
  (z :
    DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact.Point
      (Render.klein R)) →
  Render.observer3 (Render.renderAt R (reflectPoint E z))
  ≡
  reflect3 (Render.observer3 (Render.renderAt R z))
observer3ReflectionCommutes R E z =
  trans
    (cong (Render.phase3 R) (phaseReflection E z))
    (observer3Intertwines E (Render.jPhase R z))

observer6ReflectionCommutes :
  (R : Render.JPhaseRenderingAlgebra) →
  (E : J369ReflectionEquivariance R) →
  (z :
    DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact.Point
      (Render.klein R)) →
  Render.observer6 (Render.renderAt R (reflectPoint E z))
  ≡
  reflect6 (Render.observer6 (Render.renderAt R z))
observer6ReflectionCommutes R E z =
  trans
    (cong (Render.phase6 R) (phaseReflection E z))
    (observer6Intertwines E (Render.jPhase R z))

observer9ReflectionCommutes :
  (R : Render.JPhaseRenderingAlgebra) →
  (E : J369ReflectionEquivariance R) →
  (z :
    DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact.Point
      (Render.klein R)) →
  Render.observer9 (Render.renderAt R (reflectPoint E z))
  ≡
  reflect9 (Render.observer9 (Render.renderAt R z))
observer9ReflectionCommutes R E z =
  trans
    (cong (Render.phase9 R) (phaseReflection E z))
    (observer9Intertwines E (Render.jPhase R z))

observer27ReflectionCommutes :
  (R : Render.JPhaseRenderingAlgebra) →
  (E : J369ReflectionEquivariance R) →
  (z :
    DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact.Point
      (Render.klein R)) →
  Render.observer27 (Render.renderAt R (reflectPoint E z))
  ≡
  reflect27 (Render.observer27 (Render.renderAt R z))
observer27ReflectionCommutes R E z =
  trans
    (cong (Render.phase27 R) (phaseReflection E z))
    (observer27Intertwines E (Render.jPhase R z))

------------------------------------------------------------------------
-- 4. Meaning of the result.
--
-- With an inhabitant E, each finite observer is an equivariant map for the
-- C2 reflection action.  It is therefore no longer merely a bin count:
--
--     Phase --------reflect--------> Phase
--       |                              |
--      O_n                            O_n
--       |                              |
--       v                              v
--     Finite_n -----reflect_n------> Finite_n
--
-- This still does not make the finite carrier equal to the continuous phase.
------------------------------------------------------------------------

record J369ReflectionEquivarianceBoundary : Set where
  constructor j369-reflection-equivariance-boundary
  field
    concreteC3ReflectionOwned : Bool
    concreteC6ReflectionOwned : Bool
    concreteC9ReflectionOwned : Bool
    concrete27HypervoxelReflectionOwned : Bool
    allFiniteReflectionsInvolutive : Bool
    commutingSquaresDerivedFromIntertwiner : Bool

    rendererIntertwinerInstantiated : Bool
    finiteObserverEqualsContinuousPhase : Bool
    cyclic27EqualsHypervoxel27AsGroup : Bool

    nextResidual : String

open J369ReflectionEquivarianceBoundary public

canonicalJ369ReflectionEquivarianceBoundary :
  J369ReflectionEquivarianceBoundary
canonicalJ369ReflectionEquivarianceBoundary =
  j369-reflection-equivariance-boundary
    true true true true true true
    false false false
    "instantiate one concrete analytic phase renderer and prove its 3/6/9/27 quantisers intertwine the Delta/j reflection action with the finite involutions defined here"
