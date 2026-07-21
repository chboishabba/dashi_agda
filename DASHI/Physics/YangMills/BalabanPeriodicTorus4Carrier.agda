module DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- A kernel-visible finite cyclic carrier.
--
-- We deliberately define the bounded index, enumeration and decidable
-- equality here instead of hiding them behind an abstract finite-set field.
-- The physical periodic four-torus is the fourfold product of this carrier.
------------------------------------------------------------------------

data Empty : Set where

Not : Set → Set
Not P = P → Empty

infix 4 _≢_
_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = Not (left ≡ right)

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

data CyclicIndex : Nat → Set where
  zeroᵢ : ∀ {n} → CyclicIndex (suc n)
  sucᵢ  : ∀ {n} → CyclicIndex n → CyclicIndex (suc n)

zeroNotSuc : ∀ {n} {x : CyclicIndex n} → zeroᵢ ≢ sucᵢ x
zeroNotSuc ()

sucNotZero : ∀ {n} {x : CyclicIndex n} → sucᵢ x ≢ zeroᵢ
sucNotZero ()

sucInjective : ∀ {n} {x y : CyclicIndex n} → sucᵢ x ≡ sucᵢ y → x ≡ y
sucInjective refl = refl

cyclicIndexDecidableEquality : ∀ {n} → (x y : CyclicIndex n) → Dec (x ≡ y)
cyclicIndexDecidableEquality zeroᵢ zeroᵢ = yes refl
cyclicIndexDecidableEquality zeroᵢ (sucᵢ y) = no zeroNotSuc
cyclicIndexDecidableEquality (sucᵢ x) zeroᵢ = no sucNotZero
cyclicIndexDecidableEquality (sucᵢ x) (sucᵢ y)
  with cyclicIndexDecidableEquality x y
... | yes x≡y = yes (cong sucᵢ x≡y)
... | no x≢y = no (λ equality → x≢y (sucInjective equality))

------------------------------------------------------------------------
-- Literal finite enumerations.
------------------------------------------------------------------------

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

mapMembership :
  ∀ {A B : Set} (f : A → B) {x : A} {xs : List A} →
  x ∈ xs → f x ∈ map f xs
mapMembership f here = here
mapMembership f (there membership) = there (mapMembership f membership)

appendMembershipLeft :
  ∀ {A : Set} {x : A} {xs ys : List A} →
  x ∈ xs → x ∈ (xs ++ ys)
appendMembershipLeft here = here
appendMembershipLeft (there membership) =
  there (appendMembershipLeft membership)

appendMembershipRight :
  ∀ {A : Set} {x : A} {xs ys : List A} →
  x ∈ ys → x ∈ (xs ++ ys)
appendMembershipRight {xs = []} membership = membership
appendMembershipRight {xs = y ∷ xs} membership =
  there (appendMembershipRight {xs = xs} membership)

allCyclicIndices : (n : Nat) → List (CyclicIndex n)
allCyclicIndices zero = []
allCyclicIndices (suc n) = zeroᵢ ∷ map sucᵢ (allCyclicIndices n)

allCyclicIndicesComplete :
  ∀ {n} (x : CyclicIndex n) → x ∈ allCyclicIndices n
allCyclicIndicesComplete {zero} ()
allCyclicIndicesComplete {suc n} zeroᵢ = here
allCyclicIndicesComplete {suc n} (sucᵢ x) =
  there (mapMembership sucᵢ (allCyclicIndicesComplete x))

record Product (A B : Set) : Set where
  constructor pair
  field
    first : A
    second : B

open Product public

productFirstInjective :
  ∀ {A B : Set} {a a' : A} {b b' : B} →
  pair a b ≡ pair a' b' → a ≡ a'
productFirstInjective refl = refl

productSecondInjective :
  ∀ {A B : Set} {a a' : A} {b b' : B} →
  pair a b ≡ pair a' b' → b ≡ b'
productSecondInjective refl = refl

DecidableEquality : Set → Set
DecidableEquality A = (x y : A) → Dec (x ≡ y)

productDecidableEquality :
  ∀ {A B : Set} →
  DecidableEquality A → DecidableEquality B →
  DecidableEquality (Product A B)
productDecidableEquality decideA decideB (pair a b) (pair a' b')
  with decideA a a' | decideB b b'
... | yes refl | yes refl = yes refl
... | no a≢a' | decisionB =
  no (λ equality → a≢a' (productFirstInjective equality))
... | yes a≡a' | no b≢b' =
  no (λ equality → b≢b' (productSecondInjective equality))

cartesian :
  ∀ {A B : Set} → List A → List B → List (Product A B)
cartesian [] ys = []
cartesian (x ∷ xs) ys =
  map (λ y → pair x y) ys ++ cartesian xs ys

cartesianMembership :
  ∀ {A B : Set} {x : A} {y : B} {xs : List A} {ys : List B} →
  x ∈ xs → y ∈ ys → pair x y ∈ cartesian xs ys
cartesianMembership {xs = []} () yMembership
cartesianMembership {x = x} {y = y} {xs = x ∷ xs} here yMembership =
  appendMembershipLeft (mapMembership (λ value → pair x value) yMembership)
cartesianMembership {x = x} {y = y} {xs = z ∷ xs}
  (there xMembership) yMembership =
  appendMembershipRight
    (cartesianMembership xMembership yMembership)

record FiniteEnumeration (A : Set) : Set where
  field
    elements : List A
    complete : ∀ x → x ∈ elements

open FiniteEnumeration public

cyclicIndexFinite : ∀ n → FiniteEnumeration (CyclicIndex n)
cyclicIndexFinite n = record
  { elements = allCyclicIndices n
  ; complete = allCyclicIndicesComplete
  }

productFinite :
  ∀ {A B : Set} →
  FiniteEnumeration A → FiniteEnumeration B →
  FiniteEnumeration (Product A B)
productFinite finiteA finiteB = record
  { elements = cartesian (elements finiteA) (elements finiteB)
  ; complete = λ where
      (pair x y) → cartesianMembership (complete finiteA x) (complete finiteB y)
  }

------------------------------------------------------------------------
-- The literal periodic four-torus and its dual momentum carrier.
------------------------------------------------------------------------

Pair2 : Set → Set
Pair2 A = Product A A

Fourfold : Set → Set
Fourfold A = Product (Pair2 A) (Pair2 A)

periodicTorus4Definition : Nat → Set
periodicTorus4Definition L = Fourfold (CyclicIndex L)

periodicTorus4Finite : ∀ L → FiniteEnumeration (periodicTorus4Definition L)
periodicTorus4Finite L =
  productFinite
    (productFinite (cyclicIndexFinite L) (cyclicIndexFinite L))
    (productFinite (cyclicIndexFinite L) (cyclicIndexFinite L))

periodicTorus4DecidableEquality :
  ∀ L → DecidableEquality (periodicTorus4Definition L)
periodicTorus4DecidableEquality L =
  productDecidableEquality
    (productDecidableEquality cyclicIndexDecidableEquality
      cyclicIndexDecidableEquality)
    (productDecidableEquality cyclicIndexDecidableEquality
      cyclicIndexDecidableEquality)

dualPeriodicTorus4Definition : Nat → Set
dualPeriodicTorus4Definition = periodicTorus4Definition

momentumCharactersEnumerated :
  ∀ L → FiniteEnumeration (dualPeriodicTorus4Definition L)
momentumCharactersEnumerated = periodicTorus4Finite

------------------------------------------------------------------------
-- Positive-axis bonds are definitionally axis-indexed site fields.
------------------------------------------------------------------------

four : Nat
four = suc (suc (suc (suc zero)))

Axis4 : Set
Axis4 = CyclicIndex four

PositiveBond : Nat → Set
PositiveBond L = Product (periodicTorus4Definition L) Axis4

BondField : Nat → Set → Set
BondField L Value = PositiveBond L → Value

AxisIndexedSiteField : Nat → Set → Set
AxisIndexedSiteField L Value = Axis4 → periodicTorus4Definition L → Value

bondFieldAsAxisIndexedSiteField :
  ∀ {L Value} → BondField L Value → AxisIndexedSiteField L Value
bondFieldAsAxisIndexedSiteField field axis site = field (pair site axis)

axisIndexedSiteFieldAsBondField :
  ∀ {L Value} → AxisIndexedSiteField L Value → BondField L Value
axisIndexedSiteFieldAsBondField field (pair site axis) = field axis site

bondFieldRoundTrip :
  ∀ {L Value} (field : BondField L Value) site axis →
  axisIndexedSiteFieldAsBondField
    (bondFieldAsAxisIndexedSiteField field)
    (pair site axis)
  ≡ field (pair site axis)
bondFieldRoundTrip field site axis = refl

axisIndexedSiteFieldRoundTrip :
  ∀ {L Value} (field : AxisIndexedSiteField L Value) axis site →
  bondFieldAsAxisIndexedSiteField
    (axisIndexedSiteFieldAsBondField field)
    axis site
  ≡ field axis site
axisIndexedSiteFieldRoundTrip field axis site = refl

periodicTorus4CarrierLevel : ProofLevel
periodicTorus4CarrierLevel = machineChecked

periodicTorus4FiniteLevel : ProofLevel
periodicTorus4FiniteLevel = machineChecked

periodicTorus4DecidableEqualityLevel : ProofLevel
periodicTorus4DecidableEqualityLevel = machineChecked

bondFieldAxisRepresentationLevel : ProofLevel
bondFieldAxisRepresentationLevel = machineChecked
