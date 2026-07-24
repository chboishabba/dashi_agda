module DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; -_)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicOfficialFiniteSumIdentification as Official
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Small self-contained finite-list library.
------------------------------------------------------------------------

infix 4 _∈_
infixr 5 _++_

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {y ys} → x ≡ y → x ∈ (y ∷ ys)
  there : ∀ {y ys} → x ∈ ys → x ∈ (y ∷ ys)

_∉_ : ∀ {A : Set} → A → List A → Set
x ∉ xs = x ∈ xs → ⊥

data NoDuplicates {A : Set} : List A → Set where
  unique[] : NoDuplicates []
  unique∷ : ∀ {x xs} → x ∉ xs → NoDuplicates xs → NoDuplicates (x ∷ xs)

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

Disjoint : ∀ {A : Set} → List A → List A → Set
Disjoint xs ys = ∀ {z} → z ∈ xs → z ∈ ys → ⊥

cong₂ : ∀ {A B C : Set} (f : A → B → C) {a a′ b b′} →
  a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
cong₂ f refl refl = refl

memberAppendLeft :
  ∀ {A : Set} {x : A} {xs ys} → x ∈ xs → x ∈ (xs ++ ys)
memberAppendLeft {xs = []} ()
memberAppendLeft {xs = _ ∷ _} (here equality) = here equality
memberAppendLeft {xs = _ ∷ _} (there member) =
  there (memberAppendLeft member)

memberAppendRight :
  ∀ {A : Set} {x : A} {xs ys} → x ∈ ys → x ∈ (xs ++ ys)
memberAppendRight {xs = []} member = member
memberAppendRight {xs = _ ∷ xs} member =
  there (memberAppendRight {xs = xs} member)

memberAppendCases :
  ∀ {A : Set} {x : A} {xs ys} →
  x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
memberAppendCases {xs = []} member = inj₂ member
memberAppendCases {xs = _ ∷ _} (here equality) = inj₁ (here equality)
memberAppendCases {xs = _ ∷ xs} (there member)
  with memberAppendCases {xs = xs} member
... | inj₁ left = inj₁ (there left)
... | inj₂ right = inj₂ right

mapMember :
  ∀ {A B : Set} {f : A → B} {x xs} →
  x ∈ xs → f x ∈ map f xs
mapMember {f = f} (here equality) = here (cong f equality)
mapMember (there member) = there (mapMember member)

mapMemberReflect :
  ∀ {A B : Set} {f : A → B} →
  Injective f →
  ∀ {x xs} → f x ∈ map f xs → x ∈ xs
mapMemberReflect injective (here equality) =
  here (injective equality)
mapMemberReflect injective (there member) =
  there (mapMemberReflect injective member)

mapNoDuplicates :
  ∀ {A B : Set} (f : A → B) →
  Injective f →
  ∀ {xs} → NoDuplicates xs → NoDuplicates (map f xs)
mapNoDuplicates f injective unique[] = unique[]
mapNoDuplicates f injective (unique∷ fresh rest) =
  unique∷
    (λ member → fresh (mapMemberReflect injective member))
    (mapNoDuplicates f injective rest)

noDuplicatesAppend :
  ∀ {A : Set} {xs ys : List A} →
  NoDuplicates xs →
  NoDuplicates ys →
  Disjoint xs ys →
  NoDuplicates (xs ++ ys)
noDuplicatesAppend unique[] right disjoint = right
noDuplicatesAppend {ys = ys}
  (unique∷ {x = x} {xs = xs} fresh left) right disjoint =
  unique∷ combinedFresh
    (noDuplicatesAppend left right tailDisjoint)
  where
  combinedFresh : x ∉ (xs ++ ys)
  combinedFresh member with memberAppendCases member
  ... | inj₁ leftMember = fresh leftMember
  ... | inj₂ rightMember = disjoint (here refl) rightMember

  tailDisjoint : Disjoint xs ys
  tailDisjoint tailMember rightMember =
    disjoint (there tailMember) rightMember

mapLength :
  ∀ {A B : Set} (f : A → B) (xs : List A) →
  length (map f xs) ≡ length xs
mapLength f [] = refl
mapLength f (_ ∷ xs) = cong suc (mapLength f xs)

appendLength :
  ∀ {A : Set} (xs ys : List A) →
  length (xs ++ ys) ≡ length xs + length ys
appendLength [] ys = refl
appendLength (_ ∷ xs) ys = cong suc (appendLength xs ys)

------------------------------------------------------------------------
-- Cartesian products preserve literal uniqueness.
------------------------------------------------------------------------

record Pair (A B : Set) : Set where
  constructor pair
  field
    first : A
    second : B

open Pair public

pairWithLeftInjective :
  ∀ {A B : Set} {x : A} →
  Injective (λ y → pair {A = A} {B = B} x y)
pairWithLeftInjective refl = refl

cartesian :
  ∀ {A B : Set} → List A → List B → List (Pair A B)
cartesian [] ys = []
cartesian (x ∷ xs) ys =
  map (λ y → pair x y) ys ++ cartesian xs ys

mappedPairFirst :
  ∀ {A B : Set} {x : A} {ys : List B} {z : Pair A B} →
  z ∈ map (λ y → pair x y) ys → first z ≡ x
mappedPairFirst (here equality) = cong first equality
mappedPairFirst (there member) = mappedPairFirst member

mappedPairSecondMember :
  ∀ {A B : Set} {x : A} {ys : List B} {z : Pair A B} →
  z ∈ map (λ y → pair x y) ys → second z ∈ ys
mappedPairSecondMember (here equality) = here (cong second equality)
mappedPairSecondMember (there member) =
  there (mappedPairSecondMember member)

cartesianFirstMember :
  ∀ {A B : Set} {xs : List A} {ys : List B} {z : Pair A B} →
  z ∈ cartesian xs ys → first z ∈ xs
cartesianFirstMember {xs = []} ()
cartesianFirstMember {xs = x ∷ xs} member
  with memberAppendCases member
... | inj₁ block = here (mappedPairFirst block)
... | inj₂ tail = there (cartesianFirstMember tail)

cartesianSecondMember :
  ∀ {A B : Set} {xs : List A} {ys : List B} {z : Pair A B} →
  z ∈ cartesian xs ys → second z ∈ ys
cartesianSecondMember {xs = []} ()
cartesianSecondMember {xs = _ ∷ _} member
  with memberAppendCases member
... | inj₁ block = mappedPairSecondMember block
... | inj₂ tail = cartesianSecondMember tail

cartesianComplete :
  ∀ {A B : Set} {xs : List A} {ys : List B} {x y} →
  x ∈ xs → y ∈ ys → pair x y ∈ cartesian xs ys
cartesianComplete (here refl) yMember =
  memberAppendLeft (mapMember yMember)
cartesianComplete (there xMember) yMember =
  memberAppendRight (cartesianComplete xMember yMember)

cartesianNoDuplicates :
  ∀ {A B : Set} {xs : List A} {ys : List B} →
  NoDuplicates xs →
  NoDuplicates ys →
  NoDuplicates (cartesian xs ys)
cartesianNoDuplicates unique[] ysUnique = unique[]
cartesianNoDuplicates {xs = x ∷ xs} {ys = ys}
  (unique∷ fresh xsUnique) ysUnique =
  noDuplicatesAppend
    (mapNoDuplicates (λ y → pair x y) pairWithLeftInjective ysUnique)
    (cartesianNoDuplicates xsUnique ysUnique)
    blockTailDisjoint
  where
  blockTailDisjoint :
    Disjoint
      (map (λ y → pair x y) ys)
      (cartesian xs ys)
  blockTailDisjoint blockMember tailMember =
    fresh
      (subst
        (λ coordinate → coordinate ∈ xs)
        (mappedPairFirst blockMember)
        (cartesianFirstMember tailMember))

cartesianLength :
  ∀ {A B : Set} (xs : List A) (ys : List B) →
  length (cartesian xs ys) ≡ length xs * length ys
cartesianLength [] ys = refl
cartesianLength (x ∷ xs) ys =
  trans
    (appendLength (map (λ y → pair x y) ys) (cartesian xs ys))
    (trans
      (cong₂ _+_ (mapLength (λ y → pair x y) ys)
        (cartesianLength xs ys))
      refl)

------------------------------------------------------------------------
-- Literal signed interval [-N,N].
------------------------------------------------------------------------

infix 4 _≤ᴺ_

data _≤ᴺ_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ᴺ n
  s≤s : ∀ {m n} → m ≤ᴺ n → suc m ≤ᴺ suc n

≤ᴺ-refl : ∀ n → n ≤ᴺ n
≤ᴺ-refl zero = z≤n
≤ᴺ-refl (suc n) = s≤s (≤ᴺ-refl n)

≤ᴺ-step : ∀ {m n} → m ≤ᴺ n → m ≤ᴺ suc n
≤ᴺ-step z≤n = z≤n
≤ᴺ-step (s≤s proof) = s≤s (≤ᴺ-step proof)

notSuc≤Self : ∀ {n} → suc n ≤ᴺ n → ⊥
notSuc≤Self {zero} ()
notSuc≤Self {suc n} (s≤s proof) = notSuc≤Self proof

≤ᴺ-equalOrStrict :
  ∀ {m n} → m ≤ᴺ n → (m ≡ n) ⊎ (suc m ≤ᴺ n)
≤ᴺ-equalOrStrict {zero} {zero} z≤n = inj₁ refl
≤ᴺ-equalOrStrict {zero} {suc n} z≤n = inj₂ (s≤s z≤n)
≤ᴺ-equalOrStrict {suc m} {zero} ()
≤ᴺ-equalOrStrict {suc m} {suc n} (s≤s proof)
  with ≤ᴺ-equalOrStrict proof
... | inj₁ equality = inj₁ (cong suc equality)
... | inj₂ strict = inj₂ (s≤s strict)

integerMagnitude : ℤ → Nat
integerMagnitude (+ n) = n
integerMagnitude (-[1+ n ]) = suc n

integerMagnitudeNegate : ∀ z →
  integerMagnitude (- z) ≡ integerMagnitude z
integerMagnitudeNegate (+ zero) = refl
integerMagnitudeNegate (+ (suc n)) = refl
integerMagnitudeNegate (-[1+ n ]) = refl

signedInterval : Nat → List ℤ
signedInterval zero = (+ zero) ∷ []
signedInterval (suc n) =
  (-[1+ n ]) ∷ (+ (suc n)) ∷ signedInterval n

intervalMagnitudeBound :
  ∀ {N z} → z ∈ signedInterval N → integerMagnitude z ≤ᴺ N
intervalMagnitudeBound {N = zero} (here refl) = z≤n
intervalMagnitudeBound {N = zero} (there ())
intervalMagnitudeBound {N = suc N} (here refl) = ≤ᴺ-refl (suc N)
intervalMagnitudeBound {N = suc N} (there (here refl)) =
  ≤ᴺ-refl (suc N)
intervalMagnitudeBound {N = suc N} (there (there member)) =
  ≤ᴺ-step (intervalMagnitudeBound member)

intervalComplete :
  ∀ {N z} → integerMagnitude z ≤ᴺ N → z ∈ signedInterval N
intervalComplete {N = zero} {z = + zero} proof = here refl
intervalComplete {N = zero} {z = + (suc n)} ()
intervalComplete {N = zero} {z = -[1+ n ]} ()
intervalComplete {N = suc N} {z = + zero} proof =
  there (there (intervalComplete z≤n))
intervalComplete {N = suc N} {z = + (suc n)} (s≤s proof)
  with ≤ᴺ-equalOrStrict proof
... | inj₁ refl = there (here refl)
... | inj₂ strict = there (there (intervalComplete strict))
intervalComplete {N = suc N} {z = -[1+ n ]} (s≤s proof)
  with ≤ᴺ-equalOrStrict proof
... | inj₁ refl = here refl
... | inj₂ strict = there (there (intervalComplete strict))

negativePositiveDisjoint :
  ∀ {n m} → (-[1+ n ]) ≡ (+ m) → ⊥
negativePositiveDisjoint ()

outerNegativeFresh : ∀ N → (-[1+ N ]) ∉ signedInterval N
outerNegativeFresh N member =
  notSuc≤Self (intervalMagnitudeBound member)

outerPositiveFresh : ∀ N → (+ (suc N)) ∉ signedInterval N
outerPositiveFresh N member =
  notSuc≤Self (intervalMagnitudeBound member)

signedIntervalNoDuplicates : ∀ N → NoDuplicates (signedInterval N)
signedIntervalNoDuplicates zero =
  unique∷ (λ ()) unique[]
signedIntervalNoDuplicates (suc N) =
  unique∷ negativeFresh
    (unique∷ (outerPositiveFresh N) (signedIntervalNoDuplicates N))
  where
  negativeFresh :
    (-[1+ N ]) ∉ ((+ (suc N)) ∷ signedInterval N)
  negativeFresh (here equality) = negativePositiveDisjoint equality
  negativeFresh (there member) = outerNegativeFresh N member

intervalNegationClosed :
  ∀ {N z} → z ∈ signedInterval N → (- z) ∈ signedInterval N
intervalNegationClosed {N} {z} member =
  intervalComplete
    (subst
      (λ magnitude → magnitude ≤ᴺ N)
      (sym (integerMagnitudeNegate z))
      (intervalMagnitudeBound member))

intervalCardinality : Nat → Nat
intervalCardinality zero = suc zero
intervalCardinality (suc N) = suc (suc (intervalCardinality N))

signedIntervalLength : ∀ N →
  length (signedInterval N) ≡ intervalCardinality N
signedIntervalLength zero = refl
signedIntervalLength (suc N) =
  cong suc (cong suc (signedIntervalLength N))

------------------------------------------------------------------------
-- The exact max-coordinate cutoff cube.
------------------------------------------------------------------------

Tripleℤ : Set
Tripleℤ = Pair ℤ (Pair ℤ ℤ)

tripleToMode : Tripleℤ → Z3.FourierMode
tripleToMode (pair x (pair y z)) = Z3.mode x y z

modeToTriple : Z3.FourierMode → Tripleℤ
modeToTriple (Z3.mode x y z) = pair x (pair y z)

tripleRoundtrip : ∀ t → modeToTriple (tripleToMode t) ≡ t
tripleRoundtrip (pair x (pair y z)) = refl

tripleToModeInjective : Injective tripleToMode
tripleToModeInjective {x} {y} equality =
  trans
    (sym (tripleRoundtrip x))
    (trans (cong modeToTriple equality) (tripleRoundtrip y))

cutoffModes : Nat → List Z3.FourierMode
cutoffModes N =
  map tripleToMode
    (cartesian (signedInterval N)
      (cartesian (signedInterval N) (signedInterval N)))

record InCutoffCube (N : Nat) (k : Z3.FourierMode) : Set where
  constructor cutoff-membership
  field
    x-member : Z3.kx k ∈ signedInterval N
    y-member : Z3.ky k ∈ signedInterval N
    z-member : Z3.kz k ∈ signedInterval N

open InCutoffCube public

cutoffModeEnumerationComplete :
  ∀ N k → InCutoffCube N k → k ∈ cutoffModes N
cutoffModeEnumerationComplete N (Z3.mode x y z)
  (cutoff-membership xMember yMember zMember) =
  mapMember
    (cartesianComplete xMember
      (cartesianComplete yMember zMember))

cutoffModeEnumerationSound :
  ∀ N k → k ∈ cutoffModes N → InCutoffCube N k
cutoffModeEnumerationSound N (Z3.mode x y z) member =
  cutoff-membership
    (cartesianFirstMember tripleMember)
    (cartesianFirstMember yzMember)
    (cartesianSecondMember yzMember)
  where
  tripleMember :
    pair x (pair y z) ∈
      cartesian (signedInterval N)
        (cartesian (signedInterval N) (signedInterval N))
  tripleMember = mapMemberReflect tripleToModeInjective member

  yzMember : pair y z ∈ cartesian (signedInterval N) (signedInterval N)
  yzMember = cartesianSecondMember tripleMember

cutoffModeEnumerationNoDuplicates : ∀ N →
  NoDuplicates (cutoffModes N)
cutoffModeEnumerationNoDuplicates N =
  mapNoDuplicates tripleToMode tripleToModeInjective
    (cartesianNoDuplicates
      (signedIntervalNoDuplicates N)
      (cartesianNoDuplicates
        (signedIntervalNoDuplicates N)
        (signedIntervalNoDuplicates N)))

cutoffCubeCardinality : Nat → Nat
cutoffCubeCardinality N =
  intervalCardinality N *
    (intervalCardinality N * intervalCardinality N)

literalCutoffCubeLength : ∀ N →
  length (cutoffModes N) ≡ cutoffCubeCardinality N
literalCutoffCubeLength N =
  trans
    (mapLength tripleToMode
      (cartesian (signedInterval N)
        (cartesian (signedInterval N) (signedInterval N))))
    (trans
      (cartesianLength (signedInterval N)
        (cartesian (signedInterval N) (signedInterval N)))
      (trans
        (cong
          (λ innerLength → length (signedInterval N) * innerLength)
          (cartesianLength (signedInterval N) (signedInterval N)))
        (cong₂ _*_
          (signedIntervalLength N)
          (cong₂ _*_
            (signedIntervalLength N)
            (signedIntervalLength N)))))

cutoffClosedUnderNegation :
  ∀ N k → k ∈ cutoffModes N → Z3.negateMode k ∈ cutoffModes N
cutoffClosedUnderNegation N k member =
  cutoffModeEnumerationComplete N (Z3.negateMode k)
    negatedMembership
  where
  original : InCutoffCube N k
  original = cutoffModeEnumerationSound N k member

  negatedMembership : InCutoffCube N (Z3.negateMode k)
  negatedMembership = cutoff-membership
    (intervalNegationClosed (x-member original))
    (intervalNegationClosed (y-member original))
    (intervalNegationClosed (z-member original))

zeroModeListed : ∀ N → Z3.zeroMode ∈ cutoffModes N
zeroModeListed N =
  cutoffModeEnumerationComplete N Z3.zeroMode
    (cutoff-membership
      (intervalComplete z≤n)
      (intervalComplete z≤n)
      (intervalComplete z≤n))

record CutoffCubeRealityCompatible : Set where
  field
    negation-closed : ∀ N k →
      k ∈ cutoffModes N → Z3.negateMode k ∈ cutoffModes N

cutoffCubeRealityCompatible : CutoffCubeRealityCompatible
cutoffCubeRealityCompatible = record
  { negation-closed = cutoffClosedUnderNegation }

record ZeroModeHandledExactlyOnce (N : Nat) : Set where
  field
    zero-listed : Z3.zeroMode ∈ cutoffModes N
    cube-duplicate-free : NoDuplicates (cutoffModes N)

zeroModeHandledExactlyOnce : ∀ N → ZeroModeHandledExactlyOnce N
zeroModeHandledExactlyOnce N = record
  { zero-listed = zeroModeListed N
  ; cube-duplicate-free = cutoffModeEnumerationNoDuplicates N
  }

------------------------------------------------------------------------
-- Official norm owner using the literal cube.
------------------------------------------------------------------------

record ConcreteFourierNormWeights
    (A : AbsorptionArithmetic) : Set₁ where
  field
    l2Weight h1Weight : Nat → Z3.FourierMode → Scalar A
    shellWeight : Nat → Nat → Z3.FourierMode → Scalar A

open ConcreteFourierNormWeights public

concreteCutoffCubeNormCarrier :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteFourierNormWeights A →
  Official.ConcreteFiniteFourierNormCarrier A
concreteCutoffCubeNormCarrier W = record
  { cutoffModes = cutoffModes
  ; InCutoff = InCutoffCube
  ; Listed = _∈_
  ; DuplicateFree = NoDuplicates
  ; cutoffModeEnumerationComplete = cutoffModeEnumerationComplete
  ; cutoffModeEnumerationSound = cutoffModeEnumerationSound
  ; cutoffModeEnumerationNoDuplicates = cutoffModeEnumerationNoDuplicates
  ; l2ModeWeight = l2Weight W
  ; h1ModeWeight = h1Weight W
  ; shellModeWeight = shellWeight W
  ; RealityCompatible = CutoffCubeRealityCompatible
  ; realityCompatible = cutoffCubeRealityCompatible
  ; ZeroModeHandledExactlyOnce = ZeroModeHandledExactlyOnce
  ; zeroModeHandledExactlyOnce = zeroModeHandledExactlyOnce
  }

------------------------------------------------------------------------
-- Status: the max-coordinate cube, completeness/soundness, literal uniqueness,
-- exact recursive cardinality, zero-mode handling and reality closure are all
-- constructed.  Only the PDE coefficient weights remain to be supplied.
------------------------------------------------------------------------

concreteCutoffCubeCarrierLevel : ProofLevel
concreteCutoffCubeCarrierLevel = machineChecked
