module DASHI.Codec.IndexedCubeGeometryChartExact where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Core.GovernedDiagramCore as G

-- Vertex-specific reversible charts of the original cube.
record Chart (X : Set) : Set₁ where
  field
    Coordinates : Set
    encode : X → Coordinates
    decode : Coordinates → X
    decodeEncode : (x : X) → decode (encode x) ≡ x
    encodeDecode : (x : Coordinates) → encode (decode x) ≡ x
open Chart public

record Charts (q : Q.Cube) : Set₁ where
  field
    a : Chart (Q.A q)
    b : Chart (Q.B q)
    c : Chart (Q.C q)
    d : Chart (Q.D q)
    e : Chart (Q.E q)
    f : Chart (Q.F q)
    h : Chart (Q.H q)
    i : Chart (Q.I q)
open Charts public

lift : ∀ {X Y} → (s : Chart X) → (t : Chart Y) →
  (X → Y) → Coordinates s → Coordinates t
lift s t g x = encode t (g (decode s x))

recharted : (q : Q.Cube) → Charts q → Q.Cube
recharted q k = record
  { A = Coordinates (a k); B = Coordinates (b k)
  ; C = Coordinates (c k); D = Coordinates (d k)
  ; E = Coordinates (e k); F = Coordinates (f k)
  ; H = Coordinates (h k); I = Coordinates (i k)
  ; x00 = lift (a k) (b k) (Q.x00 q)
  ; x10 = lift (c k) (d k) (Q.x10 q)
  ; x01 = lift (e k) (f k) (Q.x01 q)
  ; x11 = lift (h k) (i k) (Q.x11 q)
  ; y00 = lift (a k) (c k) (Q.y00 q)
  ; y10 = lift (b k) (d k) (Q.y10 q)
  ; y01 = lift (e k) (h k) (Q.y01 q)
  ; y11 = lift (f k) (i k) (Q.y11 q)
  ; z00 = lift (a k) (e k) (Q.z00 q)
  ; z10 = lift (b k) (f k) (Q.z10 q)
  ; z01 = lift (c k) (h k) (Q.z01 q)
  ; z11 = lift (d k) (i k) (Q.z11 q)
  }

liftSquare : ∀ {A B C D : Set}
  (a : Chart A) (b : Chart B) (c : Chart C) (d : Chart D)
  (f : A → B) (g : A → C) (h : B → D) (i : C → D) →
  ((x : A) → h (f x) ≡ i (g x)) →
  (x : Coordinates a) →
  lift b d h (lift a b f x) ≡ lift c d i (lift a c g x)
liftSquare a b c d f g h i p x
  rewrite decodeEncode b (f (decode a x))
        | decodeEncode c (g (decode a x))
        | p (decode a x) = refl

-- Retain the original dependent residual at the decoded source.
rechartedFaces : (q : Q.Cube) (r : Q.Faces q) (k : Charts q) →
  Q.Faces (recharted q k)
rechartedFaces q r k = record
  { Rxy0 = λ x → Q.Rxy0 r (decode (a k) x)
  ; Rxz0 = λ x → Q.Rxz0 r (decode (a k) x)
  ; Ryz0 = λ x → Q.Ryz0 r (decode (a k) x)
  ; Rxy1 = λ x → Q.Rxy1 r (decode (e k) x)
  ; Rxz1 = λ x → Q.Rxz1 r (decode (c k) x)
  ; Ryz1 = λ x → Q.Ryz1 r (decode (b k) x)
  }

rechartedExact : (q : Q.Cube) (r : Q.Faces q) (k : Charts q) →
  Q.ExactFaces q r → Q.ExactFaces (recharted q k) (rechartedFaces q r k)
rechartedExact q r k p = record
  { pxy0 = G.commutingSquareWitness (liftSquare (a k) (b k) (c k) (d k)
      (Q.x00 q) (Q.y00 q) (Q.y10 q) (Q.x10 q) (G.commutes (Q.pxy0 p)))
  ; pxz0 = G.commutingSquareWitness (liftSquare (a k) (b k) (e k) (f k)
      (Q.x00 q) (Q.z00 q) (Q.z10 q) (Q.x01 q) (G.commutes (Q.pxz0 p)))
  ; pyz0 = G.commutingSquareWitness (liftSquare (a k) (c k) (e k) (h k)
      (Q.y00 q) (Q.z00 q) (Q.z01 q) (Q.y01 q) (G.commutes (Q.pyz0 p)))
  ; pxy1 = G.commutingSquareWitness (liftSquare (e k) (f k) (h k) (i k)
      (Q.x01 q) (Q.y01 q) (Q.y11 q) (Q.x11 q) (G.commutes (Q.pxy1 p)))
  ; pxz1 = G.commutingSquareWitness (liftSquare (c k) (d k) (h k) (i k)
      (Q.x10 q) (Q.z01 q) (Q.z11 q) (Q.x11 q) (G.commutes (Q.pxz1 p)))
  ; pyz1 = G.commutingSquareWitness (liftSquare (b k) (d k) (f k) (i k)
      (Q.y10 q) (Q.z10 q) (Q.z11 q) (Q.y11 q) (G.commutes (Q.pyz1 p)))
  }
