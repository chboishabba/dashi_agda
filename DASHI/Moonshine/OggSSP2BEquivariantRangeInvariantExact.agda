module DASHI.Moonshine.OggSSP2BEquivariantRangeInvariantExact where

------------------------------------------------------------------------
-- EQUIVARIANT MAP -> INVARIANT RANGE
--
-- Once the source-native norm and the residual block projection are
-- equivariant, their composite residual coordinate is equivariant.  Therefore
-- its image is stable under the target Co1 action.  Range invariance is not an
-- additional same-object datum after the actual block split/projector is
-- identified.
--
-- We package images proof-relevantly via explicit preimages; no finite linear
-- algebra library is required on the Agda side.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl; trans; sym)

record EquivariantMap (G X Y : Set) : Set₁ where
  constructor equivariant-map
  field
    map : X -> Y
    actX : G -> X -> X
    actY : G -> Y -> Y
    equivariant : (g : G) (x : X) ->
      map (actX g x) ≡ actY g (map x)

open EquivariantMap public

record InImage {X Y : Set} (f : X -> Y) (y : Y) : Set where
  constructor image-witness
  field
    preimage : X
    mapsTo : f preimage ≡ y

open InImage public

rangeInvariant :
  {G X Y : Set} ->
  (f : EquivariantMap G X Y) ->
  (g : G) ->
  (y : Y) ->
  InImage (map f) y ->
  InImage (map f) (actY f g y)
rangeInvariant f g y witness =
  image-witness
    (actX f g (preimage witness))
    (trans
      (equivariant f g (preimage witness))
      (congAct (mapsTo witness)) )
  where
    congAct :
      {u v : Y} ->
      u ≡ v ->
      actY f g u ≡ actY f g v
    congAct refl = refl

rangeInvariantCompilerPaid : Bool
rangeInvariantCompilerPaid = true
