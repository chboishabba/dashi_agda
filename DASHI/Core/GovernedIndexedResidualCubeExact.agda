module DASHI.Core.GovernedIndexedResidualCubeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
import DASHI.Core.GovernedDiagramCore as G

-- Eight independently typed vertices; axes x,y,z.
record Cube : Set₁ where
  field
    A B C D E F H I : Set
    x00 : A → B
    x10 : C → D
    x01 : E → F
    x11 : H → I
    y00 : A → C
    y10 : B → D
    y01 : E → H
    y11 : F → I
    z00 : A → E
    z10 : B → F
    z01 : C → H
    z11 : D → I
open Cube public

face : (A B C D : Set) → (A → B) → (A → C) →
  (B → D) → (C → D) → (A → Set) → G.GovernedSquare
face A B C D f g h i R =
  G.governedSquare A B C D f g h i
    (λ a → h (f a) ≡ i (g a)) R true false

record Faces (c : Cube) : Set₁ where
  field
    Rxy0 : A c → Set
    Rxz0 : A c → Set
    Ryz0 : A c → Set
    Rxy1 : E c → Set
    Rxz1 : C c → Set
    Ryz1 : B c → Set
open Faces public

xy0 : (c : Cube) → Faces c → G.GovernedSquare
xy0 c r = face (A c) (B c) (C c) (D c)
  (x00 c) (y00 c) (y10 c) (x10 c) (Rxy0 r)
xz0 : (c : Cube) → Faces c → G.GovernedSquare
xz0 c r = face (A c) (B c) (E c) (F c)
  (x00 c) (z00 c) (z10 c) (x01 c) (Rxz0 r)
yz0 : (c : Cube) → Faces c → G.GovernedSquare
yz0 c r = face (A c) (C c) (E c) (H c)
  (y00 c) (z00 c) (z01 c) (y01 c) (Ryz0 r)
xy1 : (c : Cube) → Faces c → G.GovernedSquare
xy1 c r = face (E c) (F c) (H c) (I c)
  (x01 c) (y01 c) (y11 c) (x11 c) (Rxy1 r)
xz1 : (c : Cube) → Faces c → G.GovernedSquare
xz1 c r = face (C c) (D c) (H c) (I c)
  (x10 c) (z01 c) (z11 c) (x11 c) (Rxz1 r)
yz1 : (c : Cube) → Faces c → G.GovernedSquare
yz1 c r = face (B c) (D c) (F c) (I c)
  (y10 c) (z10 c) (z11 c) (y11 c) (Ryz1 r)

record ExactFaces (c : Cube) (r : Faces c) : Set where
  field
    pxy0 : G.CommutingSquareWitness (xy0 c r)
    pxz0 : G.CommutingSquareWitness (xz0 c r)
    pyz0 : G.CommutingSquareWitness (yz0 c r)
    pxy1 : G.CommutingSquareWitness (xy1 c r)
    pxz1 : G.CommutingSquareWitness (xz1 c r)
    pyz1 : G.CommutingSquareWitness (yz1 c r)
open ExactFaces public

-- Residuals alone do not prove equality or supply a correction map.
record ResidualFaces (c : Cube) (r : Faces c) : Set where
  field
    rxy0 : G.ResidualSquareWitness (xy0 c r)
    rxz0 : G.ResidualSquareWitness (xz0 c r)
    ryz0 : G.ResidualSquareWitness (yz0 c r)
    rxy1 : G.ResidualSquareWitness (xy1 c r)
    rxz1 : G.ResidualSquareWitness (xz1 c r)
    ryz1 : G.ResidualSquareWitness (yz1 c r)

cong : {X Y : Set} (f : X → Y) {a b : X} → a ≡ b → f a ≡ f b
cong f refl = refl
trans : {X : Set} {a b d : X} → a ≡ b → b ≡ d → a ≡ d
trans refl q = q

xyz xzy yxz yzx zxy zyx : (c : Cube) → A c → I c
xyz c a = z11 c (y10 c (x00 c a))
xzy c a = y11 c (z10 c (x00 c a))
yxz c a = z11 c (x10 c (y00 c a))
yzx c a = x11 c (z01 c (y00 c a))
zxy c a = y11 c (x01 c (z00 c a))
zyx c a = x11 c (y01 c (z00 c a))

xyz-xzy : {c : Cube} {r : Faces c} → ExactFaces c r →
  (a : A c) → xyz c a ≡ xzy c a
xyz-xzy {c} p a = G.commutes (pyz1 p) (x00 c a)

xyz-yxz : {c : Cube} {r : Faces c} → ExactFaces c r →
  (a : A c) → xyz c a ≡ yxz c a
xyz-yxz {c} p a = cong (z11 c) (G.commutes (pxy0 p) a)

xyz-yzx : {c : Cube} {r : Faces c} → ExactFaces c r →
  (a : A c) → xyz c a ≡ yzx c a
xyz-yzx {c} p a = trans (xyz-yxz p a)
  (G.commutes (pxz1 p) (y00 c a))

xyz-zxy : {c : Cube} {r : Faces c} → ExactFaces c r →
  (a : A c) → xyz c a ≡ zxy c a
xyz-zxy {c} p a = trans (xyz-xzy p a)
  (cong (y11 c) (G.commutes (pxz0 p) a))

xyz-zyx : {c : Cube} {r : Faces c} → ExactFaces c r →
  (a : A c) → xyz c a ≡ zyx c a
xyz-zyx {c} p a = trans (xyz-zxy p a)
  (G.commutes (pxy1 p) (z00 c a))

-- A second route uses the sixth face; equality of endpoints, not proof paths.
xyz-zyx-via-y : {c : Cube} {r : Faces c} → ExactFaces c r →
  (a : A c) → xyz c a ≡ zyx c a
xyz-zyx-via-y {c} p a = trans (xyz-yzx p a)
  (cong (x11 c) (G.commutes (pyz0 p) a))

-- Independent history/time/refinement/Frobenius/version indices.
record Index (History Time Depth Frob Version : Set) : Set where
  field
    history : History
    time : Time
    depth : Depth
    iteration : Frob
    version : Version

-- Every indexed instance supplies its own vertices and residual types.
record IndexedCube (K : Set) : Set₁ where
  field
    cubeAt : K → Cube
    facesAt : (k : K) → Faces (cubeAt k)
    residualAt : (k : K) → ResidualFaces (cubeAt k) (facesAt k)
