module DASHI.Moonshine.OggSSPP2TernaryHeisenbergAxis0Exact where

------------------------------------------------------------------------
-- The ternary rank-one 27-state Heisenberg carrier is the ACTUAL axis-0
-- subgroup of the repo-native Monster3B F3^6 finite Heisenberg extension.
--
-- This is NOT an asserted equivalence with elliptic E(F4)[3].  The actual
-- elliptic P,Q basis and the Weil-pairing transport remain source obligations.
--
-- Lean comparison: Integration/OggSSPP2TernaryHeisenbergAction.lean
-- uses EXISTING Base369Heisenberg.H 1, not a parallel finite group.
-- Its shear is (x,y,z) -> (x+y,y,z+2*y*y); its Frobenius-type reflection
-- is (x,y,z)->(x,-y,-z). The quadratic correction is required by this
-- unsymmetrized Schrodinger cocycle. In the alternating gauge
-- z_alt=z+dot(y,x), shear fixes the centre while reflection negates it.
--
-- The actual F4 curve owner separately proves generator-level
-- F(P)=P, F(Q)=-Q and the chord P+Q=shear(Q) in its own Mathlib carrier.
-- The missing E(F4)[3] basis equivalence/actual Weil pairing and the
-- absent analytic map to the RH signed cap are not inferred here.
--
-- The full group law is already proved in the Monster3B owners. Here we
-- preserve that exact unsymmetrized cocycle y*x' rather than introducing
-- a second unrelated 27-state law.
------------------------------------------------------------------------

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H

record RankOneHeisenberg : Set where
  constructor heisenbergOne
  field
    translation : Trit
    modulation : Trit
    phase : Trit

open RankOneHeisenberg public

embedAxis0 : RankOneHeisenberg → H.Heisenberg6
embedAxis0 (heisenbergOne x y z) =
  H.heisenberg6
    (H.symplectic12
      (G.x6 x zer zer zer zer zer)
      (G.x6 y zer zer zer zer zer))
    z

composeOne : RankOneHeisenberg → RankOneHeisenberg → RankOneHeisenberg
composeOne (heisenbergOne x y z) (heisenbergOne x' y' z') =
  heisenbergOne
    (G._+3_ x x')
    (G._+3_ y y')
    (G._+3_ z (G._+3_ z' (H._*3_ y x')))

------------------------------------------------------------------------
-- Same-object multiplication in the actual six-dimensional source group.
-- The nine cases discharge the right-zero simplification of the exact dot6.
------------------------------------------------------------------------

embedComposeOne :
  (a b : RankOneHeisenberg) →
  embedAxis0 (composeOne a b)
  ≡ H.compose (embedAxis0 a) (embedAxis0 b)
embedComposeOne (heisenbergOne x neg z) (heisenbergOne neg y' z') = refl
embedComposeOne (heisenbergOne x neg z) (heisenbergOne zer y' z') = refl
embedComposeOne (heisenbergOne x neg z) (heisenbergOne pos y' z') = refl
embedComposeOne (heisenbergOne x zer z) (heisenbergOne neg y' z') = refl
embedComposeOne (heisenbergOne x zer z) (heisenbergOne zer y' z') = refl
embedComposeOne (heisenbergOne x zer z) (heisenbergOne pos y' z') = refl
embedComposeOne (heisenbergOne x pos z) (heisenbergOne neg y' z') = refl
embedComposeOne (heisenbergOne x pos z) (heisenbergOne zer y' z') = refl
embedComposeOne (heisenbergOne x pos z) (heisenbergOne pos y' z') = refl

centerOne : Trit → RankOneHeisenberg
centerOne z = heisenbergOne zer zer z

embedCenterOne : (z : Trit) →
  embedAxis0 (centerOne z) ≡ H.central z
embedCenterOne z = refl

reflectionOne : RankOneHeisenberg → RankOneHeisenberg
reflectionOne (heisenbergOne x y z) =
  heisenbergOne x (G.negate3 y) (G.negate3 z)

reflectionCenterOne : (z : Trit) →
  reflectionOne (centerOne z) ≡ centerOne (G.negate3 z)
reflectionCenterOne z = refl

reflectionOneSquared : (a : RankOneHeisenberg) →
  reflectionOne (reflectionOne a) ≡ a
reflectionOneSquared (heisenbergOne x neg z)
  with z
... | neg = refl
... | zer = refl
... | pos = refl
reflectionOneSquared (heisenbergOne x zer z)
  with z
... | neg = refl
... | zer = refl
... | pos = refl
reflectionOneSquared (heisenbergOne x pos z)
  with z
... | neg = refl
... | zer = refl
... | pos = refl

------------------------------------------------------------------------
-- The centre-reversing involution is not a centre-preserving shear.
-- No arithmetic Weil pairing or Frobenius intertwiners have been promoted.
------------------------------------------------------------------------

record Axis0Boundary : Set where
  constructor axis0Boundary
  field
    rankOneEmbedsExistingH6 : Bool
    embeddingRespectsSourceCocycle : Bool
    rankOneCenterIsExistingCenter : Bool
    centreReversingReflectionConstructed : Bool
    genuineEllipticThreeTorsionTransportPaid : Bool
    actualWeilPairingTransportPaid : Bool

open Axis0Boundary public

canonicalAxis0Boundary : Axis0Boundary
canonicalAxis0Boundary =
  axis0Boundary true true true true false false
