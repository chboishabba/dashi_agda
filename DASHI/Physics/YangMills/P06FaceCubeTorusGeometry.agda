module DASHI.Physics.YangMills.P06FaceCubeTorusGeometry where

------------------------------------------------------------------------
-- Source-faithful base geometry for the P06 polymer carrier.
--
-- Balaban, CMP 116 (1988), PDF p. 4 defines connected components using
-- successive cube boundaries with a common (d - 1)-dimensional wall.
-- Thus the P06 carrier uses face adjacency.  Enlarged domains (tilde) are
-- a later localization operation and deliberately do not occur here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (_≢_; sym; cong; trans; subst)
open import Data.Empty using (⊥)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using
  (_≟_; toℕ-injective; toℕ<n; toℕ-fromℕ<)
open import Data.Nat.Base using (NonZero; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.DivMod using
  (_mod_; _%_; n%n≡0; [m+n]%n≡m%n; m<n⇒m%n≡m; m%n<n)
open import Data.Nat.Properties using
  (+-suc; +-assoc; +-identityʳ; n<1+n; n≤1+n; ≤-trans;
   m≤n⇒m<n∨m≡n)
open import Data.Product.Base using (_×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_; length; map)
open import Relation.Nullary using (Dec; yes; no)
open import DASHI.Physics.YangMills.GraphCombinatorics
  using (Graph; Connected; NonEmpty; NoDuplicates)
open import DASHI.Physics.YangMills.P06ConstructiveSpanningTreeDFS
  using (UndirectedGraphStructure)

------------------------------------------------------------------------
-- Periodic four-dimensional M-cube coordinates.  This is deliberately a
-- four-field record rather than the extensionally equivalent function type
-- `Fin 4 → Fin N`: P06 needs intrinsic cube equality for filtering and
-- canonicalising the finite neighbour list, and no function-extensionality
-- principle should enter this combinatorial lane.
------------------------------------------------------------------------

record Cube4 (N : Nat) : Set where
  constructor cube4
  field
    x₀ x₁ x₂ x₃ : Fin N

open Cube4 public

data Axis4 : Set where
  axis₀ axis₁ axis₂ axis₃ : Axis4

data FaceOrientation : Set where
  forward backward : FaceOrientation

FaceMove : Set
FaceMove = Axis4 × FaceOrientation

allFaceMoves : List FaceMove
allFaceMoves =
  (axis₀ , forward) ∷ (axis₀ , backward) ∷
  (axis₁ , forward) ∷ (axis₁ , backward) ∷
  (axis₂ , forward) ∷ (axis₂ , backward) ∷
  (axis₃ , forward) ∷ (axis₃ , backward) ∷ []

allFaceMovesLength : length allFaceMoves ≡ 8
allFaceMovesLength = refl

-- In dimension four there are four coordinate axes and two orientations.
-- A later neighbour-list theorem will remove any collisions on small tori.
faceCubeDegreeBound : Nat
faceCubeDegreeBound = length allFaceMoves

fin0 : Fin 4
fin0 = Data.Fin.Base.zero

fin1 : Fin 4
fin1 = Data.Fin.Base.suc Data.Fin.Base.zero

fin2 : Fin 4
fin2 = Data.Fin.Base.suc (Data.Fin.Base.suc Data.Fin.Base.zero)

fin3 : Fin 4
fin3 =
  Data.Fin.Base.suc
    (Data.Fin.Base.suc (Data.Fin.Base.suc Data.Fin.Base.zero))

axisFin : Axis4 → Fin 4
axisFin axis₀ = fin0
axisFin axis₁ = fin1
axisFin axis₂ = fin2
axisFin axis₃ = fin3

coordinates : ∀ {N} → Cube4 N → Fin 4 → Fin N
coordinates (cube4 a₀ a₁ a₂ a₃) Data.Fin.Base.zero = a₀
coordinates (cube4 a₀ a₁ a₂ a₃)
  (Data.Fin.Base.suc Data.Fin.Base.zero) = a₁
coordinates (cube4 a₀ a₁ a₂ a₃)
  (Data.Fin.Base.suc (Data.Fin.Base.suc Data.Fin.Base.zero)) = a₂
coordinates (cube4 a₀ a₁ a₂ a₃)
  (Data.Fin.Base.suc
    (Data.Fin.Base.suc (Data.Fin.Base.suc Data.Fin.Base.zero))) = a₃

fromCoordinates : ∀ {N} → (Fin 4 → Fin N) → Cube4 N
fromCoordinates f = cube4 (f fin0) (f fin1) (f fin2) (f fin3)

coordinates-fromCoordinates :
  ∀ {N} (f : Fin 4 → Fin N) (i : Fin 4) →
  coordinates (fromCoordinates f) i ≡ f i
coordinates-fromCoordinates f Data.Fin.Base.zero = refl
coordinates-fromCoordinates f (Data.Fin.Base.suc Data.Fin.Base.zero) = refl
coordinates-fromCoordinates f
  (Data.Fin.Base.suc (Data.Fin.Base.suc Data.Fin.Base.zero)) = refl
coordinates-fromCoordinates f
  (Data.Fin.Base.suc
    (Data.Fin.Base.suc (Data.Fin.Base.suc Data.Fin.Base.zero))) = refl

fromCoordinates-coordinates :
  ∀ {N} (x : Cube4 N) →
  fromCoordinates (coordinates x) ≡ x
fromCoordinates-coordinates (cube4 a₀ a₁ a₂ a₃) = refl

cube4Ext :
  ∀ {N} {x y : Cube4 N} →
  x₀ x ≡ x₀ y →
  x₁ x ≡ x₁ y →
  x₂ x ≡ x₂ y →
  x₃ x ≡ x₃ y →
  x ≡ y
cube4Ext {x = cube4 a₀ a₁ a₂ a₃} {cube4 .a₀ .a₁ .a₂ .a₃}
  refl refl refl refl = refl

cube4Eq? : ∀ {N} (x y : Cube4 N) → Dec (x ≡ y)
cube4Eq? (cube4 a₀ a₁ a₂ a₃) (cube4 b₀ b₁ b₂ b₃)
  with a₀ ≟ b₀
... | no a₀≢b₀ = no (λ eq → a₀≢b₀ (cong x₀ eq))
... | yes refl with a₁ ≟ b₁
... | no a₁≢b₁ = no (λ eq → a₁≢b₁ (cong x₁ eq))
... | yes refl with a₂ ≟ b₂
... | no a₂≢b₂ = no (λ eq → a₂≢b₂ (cong x₂ eq))
... | yes refl with a₃ ≟ b₃
... | no a₃≢b₃ = no (λ eq → a₃≢b₃ (cong x₃ eq))
... | yes refl = yes refl

-- Addition modulo the torus side.  The implicit NonZero witness excludes
-- the empty torus; it is supplied automatically for every concrete side.
nextCoordinate : ∀ {N : Nat} → {{_ : NonZero N}} → Fin N → Fin N
nextCoordinate {N} i = (toℕ i + 1) mod N

-- The negative periodic coordinate move.  Written as `(i + N - 1) mod N`,
-- this handles the wrap at zero uniformly and is the form used by the
-- finite-arithmetic inverse proofs below.
previousCoordinate : ∀ {N : Nat} → {{_ : NonZero N}} → Fin N → Fin N
previousCoordinate {N} i = (toℕ i + (N ∸ 1)) mod N

-- The two elementary modular identities are kept at the natural-number
-- level.  Stating them this way makes the vacuous N = 0 case disappear
-- before any periodic arithmetic is considered.
nextPreviousNat :
  ∀ n k → k < suc n →
  ((k + n) % suc n + 1) % suc n ≡ k
nextPreviousNat n zero k<n =
  trans
    (cong (λ q → (q + 1) % suc n)
      (m<n⇒m%n≡m (n<1+n n)))
    (trans
      (cong (λ q → q % suc n)
          (trans (+-suc n zero)
          (cong suc (+-identityʳ n))))
      (n%n≡0 (suc n)))
nextPreviousNat n (suc k) (s≤s k<n) =
  trans
    (cong (λ q → (q % suc n + 1) % suc n)
      (sym (+-suc k n)))
    (trans
      (cong (λ q → (q + 1) % suc n)
        ([m+n]%n≡m%n k (suc n)))
      (trans
        (cong (λ q → (q + 1) % suc n)
          (m<n⇒m%n≡m (≤-trans k<n (n≤1+n n))))
        (trans
          (cong (λ q → q % suc n)
            (trans (+-suc k zero)
              (cong suc (+-identityʳ k))))
          (m<n⇒m%n≡m (s≤s k<n)))))

nextPrevious :
  ∀ {N : Nat} {{_ : NonZero N}} (i : Fin N) →
  nextCoordinate (previousCoordinate i) ≡ i
nextPrevious {suc n} i =
  toℕ-injective
    (trans
      (toℕ-fromℕ<
        (m%n<n
          (toℕ (previousCoordinate i) + 1)
          (suc n)))
      (trans
        (cong (λ q → (q + 1) % suc n)
          (toℕ-fromℕ< (m%n<n (toℕ i + n) (suc n))))
        (nextPreviousNat n (toℕ i) (toℕ<n i))))

lastPreviousNextNat :
  ∀ n → (((n + 1) % suc n + n) % suc n) ≡ n
lastPreviousNextNat n =
  trans
    (cong (λ q → (q + n) % suc n)
      (trans
        (cong (λ q → q % suc n)
          (trans (+-suc n zero)
            (cong suc (+-identityʳ n))))
        (n%n≡0 (suc n))))
    (m<n⇒m%n≡m (n<1+n n))

plusOneThenN : ∀ k n → (suc k + 1) + n ≡ suc k + suc n
plusOneThenN k n = +-assoc (suc k) 1 n

previousNextNat :
  ∀ n k → k < suc n →
  (((k + 1) % suc n + n) % suc n) ≡ k
previousNextNat zero zero k<n = refl
previousNextNat (suc n) zero k<n =
  trans
    (cong (λ q → (q + suc n) % suc (suc n))
      (m<n⇒m%n≡m one<side))
    (n%n≡0 (suc (suc n)))
  where
    one<side : suc zero < suc (suc n)
    one<side = s≤s (s≤s z≤n)
previousNextNat n (suc k) (s≤s k≤n)
  with m≤n⇒m<n∨m≡n k≤n
... | inj₁ suc-k<n =
  trans
    (cong (λ q → (q % suc n + n) % suc n)
      (trans (+-suc (suc k) zero)
        (cong suc (+-identityʳ (suc k)))))
    (trans
      (cong (λ q → (q + n) % suc n)
        (m<n⇒m%n≡m (s≤s suc-k<n)))
      (trans
        (cong (λ q → q % suc n)
          (trans
            (cong (_+ n)
              (sym
                (trans (+-suc (suc k) zero)
                  (cong suc (+-identityʳ (suc k))))))
            (plusOneThenN k n)))
        (trans
          ([m+n]%n≡m%n (suc k) (suc n))
          (m<n⇒m%n≡m (s≤s k≤n)))))
... | inj₂ refl = lastPreviousNextNat (suc k)

previousNext :
  ∀ {N : Nat} {{_ : NonZero N}} (i : Fin N) →
  previousCoordinate (nextCoordinate i) ≡ i
previousNext {suc n} i =
  toℕ-injective
    (trans
      (toℕ-fromℕ<
        (m%n<n
          (toℕ (nextCoordinate i) + n)
          (suc n)))
      (trans
        (cong (λ q → (q + n) % suc n)
          (toℕ-fromℕ< (m%n<n (toℕ i + 1) (suc n))))
        (previousNextNat n (toℕ i) (toℕ<n i))))

shiftForward :
  ∀ {N : Nat} → {{_ : NonZero N}} →
  Axis4 → Cube4 N → Cube4 N
shiftForward axis₀ (cube4 a₀ a₁ a₂ a₃) =
  cube4 (nextCoordinate a₀) a₁ a₂ a₃
shiftForward axis₁ (cube4 a₀ a₁ a₂ a₃) =
  cube4 a₀ (nextCoordinate a₁) a₂ a₃
shiftForward axis₂ (cube4 a₀ a₁ a₂ a₃) =
  cube4 a₀ a₁ (nextCoordinate a₂) a₃
shiftForward axis₃ (cube4 a₀ a₁ a₂ a₃) =
  cube4 a₀ a₁ a₂ (nextCoordinate a₃)

shiftBackward :
  ∀ {N : Nat} → {{_ : NonZero N}} →
  Axis4 → Cube4 N → Cube4 N
shiftBackward axis₀ (cube4 a₀ a₁ a₂ a₃) =
  cube4 (previousCoordinate a₀) a₁ a₂ a₃
shiftBackward axis₁ (cube4 a₀ a₁ a₂ a₃) =
  cube4 a₀ (previousCoordinate a₁) a₂ a₃
shiftBackward axis₂ (cube4 a₀ a₁ a₂ a₃) =
  cube4 a₀ a₁ (previousCoordinate a₂) a₃
shiftBackward axis₃ (cube4 a₀ a₁ a₂ a₃) =
  cube4 a₀ a₁ a₂ (previousCoordinate a₃)

shiftForwardBackward :
  ∀ {N : Nat} {{_ : NonZero N}} →
  (axis : Axis4) (x : Cube4 N) →
  shiftForward axis (shiftBackward axis x) ≡ x
shiftForwardBackward axis₀ (cube4 a₀ a₁ a₂ a₃) =
  cong (λ q → cube4 q a₁ a₂ a₃) (nextPrevious a₀)
shiftForwardBackward axis₁ (cube4 a₀ a₁ a₂ a₃) =
  cong (λ q → cube4 a₀ q a₂ a₃) (nextPrevious a₁)
shiftForwardBackward axis₂ (cube4 a₀ a₁ a₂ a₃) =
  cong (λ q → cube4 a₀ a₁ q a₃) (nextPrevious a₂)
shiftForwardBackward axis₃ (cube4 a₀ a₁ a₂ a₃) =
  cong (λ q → cube4 a₀ a₁ a₂ q) (nextPrevious a₃)

shiftBackwardForward :
  ∀ {N : Nat} {{_ : NonZero N}} →
  (axis : Axis4) (x : Cube4 N) →
  shiftBackward axis (shiftForward axis x) ≡ x
shiftBackwardForward axis₀ (cube4 a₀ a₁ a₂ a₃) =
  cong (λ q → cube4 q a₁ a₂ a₃) (previousNext a₀)
shiftBackwardForward axis₁ (cube4 a₀ a₁ a₂ a₃) =
  cong (λ q → cube4 a₀ q a₂ a₃) (previousNext a₁)
shiftBackwardForward axis₂ (cube4 a₀ a₁ a₂ a₃) =
  cong (λ q → cube4 a₀ a₁ q a₃) (previousNext a₂)
shiftBackwardForward axis₃ (cube4 a₀ a₁ a₂ a₃) =
  cong (λ q → cube4 a₀ a₁ a₂ q) (previousNext a₃)

faceMoveTarget :
  ∀ {N : Nat} → {{_ : NonZero N}} →
  Cube4 N → FaceMove → Cube4 N
faceMoveTarget x (axis , forward) = shiftForward axis x
faceMoveTarget x (axis , backward) = shiftBackward axis x

faceNeighbourCandidates :
  ∀ {N : Nat} → {{_ : NonZero N}} →
  Cube4 N → List (Cube4 N)
faceNeighbourCandidates x = map (faceMoveTarget x) allFaceMoves

faceNeighbourCandidatesLength :
  ∀ {N : Nat} {{_ : NonZero N}} (x : Cube4 N) →
  length (faceNeighbourCandidates x) ≡ faceCubeDegreeBound
faceNeighbourCandidatesLength x = refl

------------------------------------------------------------------------
-- Face adjacency.  A pair is adjacent precisely when two *distinct*
-- periodic M-cubes differ by one positive face move in one coordinate.
-- Distinctness matters on the degenerate one-cube torus: a periodic move
-- there returns its source, but a cube does not share a wall with itself.
-- Including both orientations in the relation makes symmetry structural; no
-- enlarged- or overlap-domain relation is being conflated with this base
-- graph.
------------------------------------------------------------------------

FaceCubeAdj :
  ∀ {N : Nat} → {{_ : NonZero N}} →
  Cube4 N → Cube4 N → Set
FaceCubeAdj x y =
  (x ≢ y) ×
  (Σ Axis4 λ axis →
    (y ≡ shiftForward axis x) ⊎ (x ≡ shiftForward axis y))

faceCubeAdjSymmetric :
  ∀ {N : Nat} {{_ : NonZero N}} {x y : Cube4 N} →
  FaceCubeAdj x y → FaceCubeAdj y x
faceCubeAdjSymmetric (x≢y , axis , inj₁ y≡shift-x) =
  (λ y≡x → x≢y (sym y≡x)) , axis , inj₂ y≡shift-x
faceCubeAdjSymmetric (x≢y , axis , inj₂ x≡shift-y) =
  (λ y≡x → x≢y (sym y≡x)) , axis , inj₁ x≡shift-y

faceCubeAdjIrreflexive :
  ∀ {N : Nat} {{_ : NonZero N}} (x : Cube4 N) →
  FaceCubeAdj x x → ⊥
faceCubeAdjIrreflexive x (x≢x , _) = x≢x refl

forwardFaceMoveAdjacent :
  ∀ {N : Nat} {{_ : NonZero N}} →
  (x : Cube4 N) (axis : Axis4) →
  x ≢ shiftForward axis x →
  FaceCubeAdj x (shiftForward axis x)
forwardFaceMoveAdjacent x axis x≢forward =
  x≢forward , axis , inj₁ refl

backwardFaceMoveAdjacent :
  ∀ {N : Nat} {{_ : NonZero N}} →
  (x : Cube4 N) (axis : Axis4) →
  x ≢ shiftBackward axis x →
  FaceCubeAdj x (shiftBackward axis x)
backwardFaceMoveAdjacent x axis x≢backward =
  x≢backward , axis , inj₂
    (sym (shiftForwardBackward axis x))

faceCubeGraph : ∀ {N : Nat} → {{_ : NonZero N}} → Graph
faceCubeGraph {N} = record
  { Vertex = Cube4 N
  ; Edge = Cube4 N × Cube4 N
  ; Adj = FaceCubeAdj
  }

faceCubeUndirected :
  ∀ {N : Nat} {{_ : NonZero N}} →
  UndirectedGraphStructure (faceCubeGraph {N})
faceCubeUndirected = record
  { adjSym = faceCubeAdjSymmetric }

------------------------------------------------------------------------
-- A base Bałaban polymer for the counting lane is a finite nonempty,
-- duplicate-free, face-connected support.  Its later analytic labels and
-- enlarged localization domains are intentionally not fields of this type.
------------------------------------------------------------------------

record BalabanFacePolymer
  {N : Nat} {{_ : NonZero N}}
  : Set where
  field
    support : List (Cube4 N)
    supportNonEmpty : NonEmpty support
    supportNoDuplicates : NoDuplicates support
    supportFaceConnected : Connected faceCubeGraph support
