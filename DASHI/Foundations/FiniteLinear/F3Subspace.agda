module DASHI.Foundations.FiniteLinear.F3Subspace where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import Base369 using (TriTruth)
import DASHI.Foundations.Base369TriTruthField as F3

------------------------------------------------------------------------
-- Minimal reusable finite-linear API.
--
-- This is deliberately narrower than a general algebra hierarchy.  It gives
-- the concrete consumers currently needed by DASHI first-class F3 spaces,
-- subspaces, linear maps, kernels, inclusions and extensional equality.
-- Generic field/rank machinery can be factored out later from demonstrated
-- consumers rather than imposed on the current theorem graph in advance.
------------------------------------------------------------------------

infixr 4 _,_ _×_
infix 3 _⊆_ _≈ₛ_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

cong :
  ∀ {A B : Set} (f : A → B) {x y : A} →
  x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ :
  ∀ {A B C : Set} (f : A → B → C)
    {x x′ : A} {y y′ : B} →
  x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong₂ f refl refl = refl

------------------------------------------------------------------------
-- F3 spaces and subspaces.
------------------------------------------------------------------------

record F3Space : Set₁ where
  field
    Carrier : Set
    zero : Carrier
    add : Carrier → Carrier → Carrier
    scale : TriTruth → Carrier → Carrier

    addZeroZero : add zero zero ≡ zero
    scaleZero : (a : TriTruth) → scale a zero ≡ zero

open F3Space public

record F3Subspace (space : F3Space) : Set₁ where
  field
    Member : Carrier space → Set
    zeroMember : Member (zero space)
    addMember :
      ∀ {x y} →
      Member x → Member y →
      Member (add space x y)
    scaleMember :
      (a : TriTruth) →
      ∀ {x} →
      Member x →
      Member (scale space a x)

open F3Subspace public

_⊆_ :
  ∀ {space : F3Space} →
  F3Subspace space → F3Subspace space → Set
left ⊆ right =
  ∀ {x} → Member left x → Member right x

record _≈ₛ_
    {space : F3Space}
    (left right : F3Subspace space) : Set where
  constructor subspaceEquality
  field
    forward : left ⊆ right
    backward : right ⊆ left

open _≈ₛ_ public

subspaceRefl :
  ∀ {space : F3Space} (subspace : F3Subspace space) →
  subspace ≈ₛ subspace
subspaceRefl subspace = subspaceEquality (λ x → x) (λ x → x)

subspaceSym :
  ∀ {space : F3Space} {left right : F3Subspace space} →
  left ≈ₛ right → right ≈ₛ left
subspaceSym equality =
  subspaceEquality
    (backward equality)
    (forward equality)

subspaceTrans :
  ∀ {space : F3Space}
    {left middle right : F3Subspace space} →
  left ≈ₛ middle →
  middle ≈ₛ right →
  left ≈ₛ right
subspaceTrans first second =
  subspaceEquality
    (λ x → forward second (forward first x))
    (λ x → backward first (backward second x))

selfDualFromInclusions :
  ∀ {space : F3Space}
    (code dualCode : F3Subspace space) →
  code ⊆ dualCode →
  dualCode ⊆ code →
  code ≈ₛ dualCode
selfDualFromInclusions code dualCode forward backward =
  subspaceEquality forward backward

------------------------------------------------------------------------
-- Linear maps and kernels.
------------------------------------------------------------------------

record F3LinearMap (domain codomain : F3Space) : Set₁ where
  field
    apply : Carrier domain → Carrier codomain
    preservesZero : apply (zero domain) ≡ zero codomain
    preservesAdd :
      (x y : Carrier domain) →
      apply (add domain x y)
      ≡ add codomain (apply x) (apply y)
    preservesScale :
      (a : TriTruth) (x : Carrier domain) →
      apply (scale domain a x)
      ≡ scale codomain a (apply x)

open F3LinearMap public

kernel :
  ∀ {domain codomain : F3Space} →
  F3LinearMap domain codomain →
  F3Subspace domain
kernel {domain} {codomain} linearMap = record
  { Member = λ x → apply linearMap x ≡ zero codomain
  ; zeroMember = preservesZero linearMap
  ; addMember = λ {x} {y} xZero yZero →
      trans
        (preservesAdd linearMap x y)
        (trans
          (cong₂ (add codomain) xZero yZero)
          (addZeroZero codomain))
  ; scaleMember = λ a {x} xZero →
      trans
        (preservesScale linearMap a x)
        (trans
          (cong (scale codomain a) xZero)
          (scaleZero codomain a))
  }

------------------------------------------------------------------------
-- Linear image predicates.  Closure becomes available whenever the supplied
-- map is linear; no quotient or ambient rank package is needed.
------------------------------------------------------------------------

record ImageMember
    {domain codomain : F3Space}
    (linearMap : F3LinearMap domain codomain)
    (value : Carrier codomain) : Set where
  constructor imageMember
  field
    preimage : Carrier domain
    imageEquation : apply linearMap preimage ≡ value

open ImageMember public

imageSubspace :
  ∀ {domain codomain : F3Space} →
  F3LinearMap domain codomain →
  F3Subspace codomain
imageSubspace {domain} {codomain} linearMap = record
  { Member = ImageMember linearMap
  ; zeroMember =
      imageMember
        (zero domain)
        (preservesZero linearMap)
  ; addMember = λ
      {x} {y}
      (imageMember x₀ xEquation)
      (imageMember y₀ yEquation) →
      imageMember
        (add domain x₀ y₀)
        (trans
          (preservesAdd linearMap x₀ y₀)
          (cong₂ (add codomain) xEquation yEquation))
  ; scaleMember = λ
      a {x}
      (imageMember x₀ xEquation) →
      imageMember
        (scale domain a x₀)
        (trans
          (preservesScale linearMap a x₀)
          (cong (scale codomain a) xEquation))
  }

------------------------------------------------------------------------
-- Small list algebra used by concrete fixed-dimensional vector carriers.
------------------------------------------------------------------------

zipAdd : List TriTruth → List TriTruth → List TriTruth
zipAdd [] ys = ys
zipAdd xs [] = xs
zipAdd (x ∷ xs) (y ∷ ys) = F3.triAdd x y ∷ zipAdd xs ys

scaleList : TriTruth → List TriTruth → List TriTruth
scaleList a [] = []
scaleList a (x ∷ xs) = F3.triMul a x ∷ scaleList a xs

dotList : List TriTruth → List TriTruth → TriTruth
dotList [] ys = F3.triZero
dotList xs [] = F3.triZero
dotList (x ∷ xs) (y ∷ ys) =
  F3.triAdd (F3.triMul x y) (dotList xs ys)

addInterchange :
  (a b c d : TriTruth) →
  F3.triAdd (F3.triAdd a b) (F3.triAdd c d)
  ≡
  F3.triAdd (F3.triAdd a c) (F3.triAdd b d)
addInterchange a b c d =
  trans
    (sym (F3.triAdd-assoc a b (F3.triAdd c d)))
    (trans
      (cong (F3.triAdd a)
        (trans
          (F3.triAdd-assoc b c d)
          (trans
            (cong (λ x → F3.triAdd x d) (F3.triAdd-comm b c))
            (sym (F3.triAdd-assoc c b d)))))
      (F3.triAdd-assoc a c (F3.triAdd b d)))

dotAddRight :
  (left right₁ right₂ : List TriTruth) →
  dotList left (zipAdd right₁ right₂)
  ≡
  F3.triAdd (dotList left right₁) (dotList left right₂)
dotAddRight [] right₁ right₂ = refl
dotAddRight (x ∷ xs) [] [] = refl
dotAddRight (x ∷ xs) [] (y ∷ ys) =
  sym (F3.triAdd-identityˡ (dotList (x ∷ xs) (y ∷ ys)))
dotAddRight (x ∷ xs) (y ∷ ys) [] =
  sym (F3.triAdd-identityʳ (dotList (x ∷ xs) (y ∷ ys)))
dotAddRight (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  trans
    (cong₂ F3.triAdd
      (F3.triDistribˡ x y z)
      (dotAddRight xs ys zs))
    (addInterchange
      (F3.triMul x y)
      (F3.triMul x z)
      (dotList xs ys)
      (dotList xs zs))

dotAddLeft :
  (left₁ left₂ right : List TriTruth) →
  dotList (zipAdd left₁ left₂) right
  ≡
  F3.triAdd (dotList left₁ right) (dotList left₂ right)
dotAddLeft [] [] right = refl
dotAddLeft [] (x ∷ xs) [] = refl
dotAddLeft [] (x ∷ xs) (y ∷ ys) =
  sym (F3.triAdd-identityˡ (dotList (x ∷ xs) (y ∷ ys)))
dotAddLeft (x ∷ xs) [] [] = refl
dotAddLeft (x ∷ xs) [] (y ∷ ys) =
  sym (F3.triAdd-identityʳ (dotList (x ∷ xs) (y ∷ ys)))
dotAddLeft (x ∷ xs) (y ∷ ys) [] = refl
dotAddLeft (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  trans
    (cong₂ F3.triAdd
      (F3.triDistribʳ x y z)
      (dotAddLeft xs ys zs))
    (addInterchange
      (F3.triMul x z)
      (F3.triMul y z)
      (dotList xs zs)
      (dotList ys zs))

mulReassociateRight :
  (a x y : TriTruth) →
  F3.triMul x (F3.triMul a y)
  ≡
  F3.triMul a (F3.triMul x y)
mulReassociateRight a x y =
  trans
    (F3.triMul-assoc x a y)
    (trans
      (cong (λ z → F3.triMul z y) (F3.triMul-comm x a))
      (sym (F3.triMul-assoc a x y)))

dotScaleRight :
  (a : TriTruth) (left right : List TriTruth) →
  dotList left (scaleList a right)
  ≡ F3.triMul a (dotList left right)
dotScaleRight a [] right =
  sym (F3.triMul-zeroʳ a)
dotScaleRight a (x ∷ xs) [] =
  sym (F3.triMul-zeroʳ a)
dotScaleRight a (x ∷ xs) (y ∷ ys) =
  trans
    (cong₂ F3.triAdd
      (mulReassociateRight a x y)
      (dotScaleRight a xs ys))
    (sym
      (F3.triDistribˡ
        a
        (F3.triMul x y)
        (dotList xs ys)))

dotScaleLeft :
  (a : TriTruth) (left right : List TriTruth) →
  dotList (scaleList a left) right
  ≡ F3.triMul a (dotList left right)
dotScaleLeft a [] right =
  sym (F3.triMul-zeroʳ a)
dotScaleLeft a (x ∷ xs) [] =
  sym (F3.triMul-zeroʳ a)
dotScaleLeft a (x ∷ xs) (y ∷ ys) =
  trans
    (cong₂ F3.triAdd
      (F3.triMul-assoc a x y)
      (dotScaleLeft a xs ys))
    (sym
      (F3.triDistribˡ
        a
        (F3.triMul x y)
        (dotList xs ys)))
