module DASHI.Codec.IndexedCubeProperFrameExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; inv; inv-invol)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Codec.IndexedCubeMaskSignInstanceExact as I
import DASHI.Codec.IndexedCubeGeometryChartExact as T
import DASHI.Core.GovernedIndexedResidualCubeExact as Q

-- Selected proper frame: (x,y,z) -> (-y,x,z), determinant +1.
-- Its inverse is (x,y,z) -> (y,-x,z).
flip : M.FactorizedTrit → M.FactorizedTrit
flip M.inactive = M.inactive
flip (M.active M.negative) = M.active M.positive
flip (M.active M.positive) = M.active M.negative

flipTwice : (x : M.FactorizedTrit) → flip (flip x) ≡ x
flipTwice M.inactive = refl
flipTwice (M.active M.negative) = refl
flipTwice (M.active M.positive) = refl

invTwice : (x : Trit) → inv (inv x) ≡ x
invTwice = inv-invol

turn : ∀ {A : Set} → (A → A) → M.Triple A → M.Triple A
turn n (M.triple x y z) = M.triple (n y) x z

unturn : ∀ {A : Set} → (A → A) → M.Triple A → M.Triple A
unturn n (M.triple x y z) = M.triple y (n x) z

turnBack : ∀ {A : Set} (n : A → A) →
  ((x : A) → n (n x) ≡ x) → (x : M.Triple A) →
  unturn n (turn n x) ≡ x
turnBack n p (M.triple x y z) rewrite p y = refl

backTurn : ∀ {A : Set} (n : A → A) →
  ((x : A) → n (n x) ≡ x) → (x : M.Triple A) →
  turn n (unturn n x) ≡ x
backTurn n p (M.triple x y z) rewrite p x = refl

blocksMap : ∀ {A : Set} → (M.Triple A → M.Triple A) →
  C.Blocks A → C.Blocks A
blocksMap f (C.blocks a b c) = C.blocks (f a) (f b) (f c)

splitMap : ∀ {A : Set} → (M.Triple A → M.Triple A) →
  C.PrefixResidual A → C.PrefixResidual A
splitMap f (C.split a b c) = C.split (f a) (f b) (f c)

blocksChart : ∀ {A : Set} (n : A → A) →
  ((x : A) → n (n x) ≡ x) → T.Chart (C.Blocks A)
blocksChart n p = record
  { Coordinates = C.Blocks _
  ; encode = blocksMap (turn n)
  ; decode = blocksMap (unturn n)
  ; decodeEncode = λ { (C.blocks a b c) →
      blocksBack n p a b c }
  ; encodeDecode = λ { (C.blocks a b c) →
      blocksForward n p a b c }
  }
  where
  blocksBack : ∀ {A : Set} (n : A → A) →
    ((x : A) → n (n x) ≡ x) → (a b c : M.Triple A) →
    blocksMap (unturn n) (blocksMap (turn n) (C.blocks a b c)) ≡ C.blocks a b c
  blocksBack n p a b c rewrite turnBack n p a | turnBack n p b | turnBack n p c = refl
  blocksForward : ∀ {A : Set} (n : A → A) →
    ((x : A) → n (n x) ≡ x) → (a b c : M.Triple A) →
    blocksMap (turn n) (blocksMap (unturn n) (C.blocks a b c)) ≡ C.blocks a b c
  blocksForward n p a b c rewrite backTurn n p a | backTurn n p b | backTurn n p c = refl

splitChart : ∀ {A : Set} (n : A → A) →
  ((x : A) → n (n x) ≡ x) → T.Chart (C.PrefixResidual A)
splitChart n p = record
  { Coordinates = C.PrefixResidual _
  ; encode = splitMap (turn n)
  ; decode = splitMap (unturn n)
  ; decodeEncode = λ { (C.split a b c) → splitBack n p a b c }
  ; encodeDecode = λ { (C.split a b c) → splitForward n p a b c }
  }
  where
  splitBack : ∀ {A : Set} (n : A → A) →
    ((x : A) → n (n x) ≡ x) → (a b c : M.Triple A) →
    splitMap (unturn n) (splitMap (turn n) (C.split a b c)) ≡ C.split a b c
  splitBack n p a b c rewrite turnBack n p a | turnBack n p b | turnBack n p c = refl
  splitForward : ∀ {A : Set} (n : A → A) →
    ((x : A) → n (n x) ≡ x) → (a b c : M.Triple A) →
    splitMap (turn n) (splitMap (unturn n) (C.split a b c)) ≡ C.split a b c
  splitForward n p a b c rewrite backTurn n p a | backTurn n p b | backTurn n p c = refl

properCharts : T.Charts I.codecCube
properCharts = record
  { a = blocksChart inv invTwice
  ; b = splitChart inv invTwice
  ; c = blocksChart inv invTwice
  ; d = splitChart inv invTwice
  ; e = blocksChart flip flipTwice
  ; f = splitChart flip flipTwice
  ; h = blocksChart flip flipTwice
  ; i = splitChart flip flipTwice
  }

properCube : Q.Cube
properCube = T.recharted I.codecCube properCharts

properFaces : Q.Faces properCube
properFaces = T.rechartedFaces I.codecCube I.codecFaces properCharts

properExact : Q.ExactFaces properCube properFaces
properExact = T.rechartedExact I.codecCube I.codecFaces properCharts I.codecExactFaces
