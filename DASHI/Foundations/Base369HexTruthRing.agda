module DASHI.Foundations.Base369HexTruthRing where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Base369 public using
  ( HexTruth
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  )

------------------------------------------------------------------------
-- HexTruth as the concrete residue ring Z/6Z, reusing Base369's carrier.

hexZero : HexTruth
hexZero = hex-0

hexOne : HexTruth
hexOne = hex-1

hexAdd : HexTruth → HexTruth → HexTruth
hexAdd hex-0 y = y
hexAdd hex-1 hex-0 = hex-1
hexAdd hex-1 hex-1 = hex-2
hexAdd hex-1 hex-2 = hex-3
hexAdd hex-1 hex-3 = hex-4
hexAdd hex-1 hex-4 = hex-5
hexAdd hex-1 hex-5 = hex-0
hexAdd hex-2 hex-0 = hex-2
hexAdd hex-2 hex-1 = hex-3
hexAdd hex-2 hex-2 = hex-4
hexAdd hex-2 hex-3 = hex-5
hexAdd hex-2 hex-4 = hex-0
hexAdd hex-2 hex-5 = hex-1
hexAdd hex-3 hex-0 = hex-3
hexAdd hex-3 hex-1 = hex-4
hexAdd hex-3 hex-2 = hex-5
hexAdd hex-3 hex-3 = hex-0
hexAdd hex-3 hex-4 = hex-1
hexAdd hex-3 hex-5 = hex-2
hexAdd hex-4 hex-0 = hex-4
hexAdd hex-4 hex-1 = hex-5
hexAdd hex-4 hex-2 = hex-0
hexAdd hex-4 hex-3 = hex-1
hexAdd hex-4 hex-4 = hex-2
hexAdd hex-4 hex-5 = hex-3
hexAdd hex-5 hex-0 = hex-5
hexAdd hex-5 hex-1 = hex-0
hexAdd hex-5 hex-2 = hex-1
hexAdd hex-5 hex-3 = hex-2
hexAdd hex-5 hex-4 = hex-3
hexAdd hex-5 hex-5 = hex-4

hexNeg : HexTruth → HexTruth
hexNeg hex-0 = hex-0
hexNeg hex-1 = hex-5
hexNeg hex-2 = hex-4
hexNeg hex-3 = hex-3
hexNeg hex-4 = hex-2
hexNeg hex-5 = hex-1

hexSub : HexTruth → HexTruth → HexTruth
hexSub x y = hexAdd x (hexNeg y)

hexMul : HexTruth → HexTruth → HexTruth
hexMul hex-0 y = hex-0
hexMul hex-1 y = y
hexMul hex-2 hex-0 = hex-0
hexMul hex-2 hex-1 = hex-2
hexMul hex-2 hex-2 = hex-4
hexMul hex-2 hex-3 = hex-0
hexMul hex-2 hex-4 = hex-2
hexMul hex-2 hex-5 = hex-4
hexMul hex-3 hex-0 = hex-0
hexMul hex-3 hex-1 = hex-3
hexMul hex-3 hex-2 = hex-0
hexMul hex-3 hex-3 = hex-3
hexMul hex-3 hex-4 = hex-0
hexMul hex-3 hex-5 = hex-3
hexMul hex-4 hex-0 = hex-0
hexMul hex-4 hex-1 = hex-4
hexMul hex-4 hex-2 = hex-2
hexMul hex-4 hex-3 = hex-0
hexMul hex-4 hex-4 = hex-4
hexMul hex-4 hex-5 = hex-2
hexMul hex-5 hex-0 = hex-0
hexMul hex-5 hex-1 = hex-5
hexMul hex-5 hex-2 = hex-4
hexMul hex-5 hex-3 = hex-3
hexMul hex-5 hex-4 = hex-2
hexMul hex-5 hex-5 = hex-1

------------------------------------------------------------------------
-- Small table checker for finite proof surfaces.

infixr 6 _&&_

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

data IsTrue : Bool → Set where
  is-true : IsTrue true

hexEq : HexTruth → HexTruth → Bool
hexEq hex-0 hex-0 = true
hexEq hex-0 _ = false
hexEq hex-1 hex-1 = true
hexEq hex-1 _ = false
hexEq hex-2 hex-2 = true
hexEq hex-2 _ = false
hexEq hex-3 hex-3 = true
hexEq hex-3 _ = false
hexEq hex-4 hex-4 = true
hexEq hex-4 _ = false
hexEq hex-5 hex-5 = true
hexEq hex-5 _ = false

hexEq-sound : (x y : HexTruth) → IsTrue (hexEq x y) → x ≡ y
hexEq-sound hex-0 hex-0 is-true = refl
hexEq-sound hex-0 hex-1 ()
hexEq-sound hex-0 hex-2 ()
hexEq-sound hex-0 hex-3 ()
hexEq-sound hex-0 hex-4 ()
hexEq-sound hex-0 hex-5 ()
hexEq-sound hex-1 hex-0 ()
hexEq-sound hex-1 hex-1 is-true = refl
hexEq-sound hex-1 hex-2 ()
hexEq-sound hex-1 hex-3 ()
hexEq-sound hex-1 hex-4 ()
hexEq-sound hex-1 hex-5 ()
hexEq-sound hex-2 hex-0 ()
hexEq-sound hex-2 hex-1 ()
hexEq-sound hex-2 hex-2 is-true = refl
hexEq-sound hex-2 hex-3 ()
hexEq-sound hex-2 hex-4 ()
hexEq-sound hex-2 hex-5 ()
hexEq-sound hex-3 hex-0 ()
hexEq-sound hex-3 hex-1 ()
hexEq-sound hex-3 hex-2 ()
hexEq-sound hex-3 hex-3 is-true = refl
hexEq-sound hex-3 hex-4 ()
hexEq-sound hex-3 hex-5 ()
hexEq-sound hex-4 hex-0 ()
hexEq-sound hex-4 hex-1 ()
hexEq-sound hex-4 hex-2 ()
hexEq-sound hex-4 hex-3 ()
hexEq-sound hex-4 hex-4 is-true = refl
hexEq-sound hex-4 hex-5 ()
hexEq-sound hex-5 hex-0 ()
hexEq-sound hex-5 hex-1 ()
hexEq-sound hex-5 hex-2 ()
hexEq-sound hex-5 hex-3 ()
hexEq-sound hex-5 hex-4 ()
hexEq-sound hex-5 hex-5 is-true = refl

allHex : (HexTruth → Bool) → Bool
allHex p =
  p hex-0 && p hex-1 && p hex-2 && p hex-3 && p hex-4 && p hex-5

allHex-sound :
  (p : HexTruth → Bool) →
  IsTrue (allHex p) →
  (x : HexTruth) →
  IsTrue (p x)
allHex-sound p ok hex-0 with p hex-0
... | true = is-true
allHex-sound p () hex-0 | false
allHex-sound p ok hex-1 with p hex-0 | p hex-1
... | true | true = is-true
allHex-sound p () hex-1 | true | false
allHex-sound p () hex-1 | false | _
allHex-sound p ok hex-2 with p hex-0 | p hex-1 | p hex-2
... | true | true | true = is-true
allHex-sound p () hex-2 | true | true | false
allHex-sound p () hex-2 | true | false | _
allHex-sound p () hex-2 | false | _ | _
allHex-sound p ok hex-3 with p hex-0 | p hex-1 | p hex-2 | p hex-3
... | true | true | true | true = is-true
allHex-sound p () hex-3 | true | true | true | false
allHex-sound p () hex-3 | true | true | false | _
allHex-sound p () hex-3 | true | false | _ | _
allHex-sound p () hex-3 | false | _ | _ | _
allHex-sound p ok hex-4 with p hex-0 | p hex-1 | p hex-2 | p hex-3 | p hex-4
... | true | true | true | true | true = is-true
allHex-sound p () hex-4 | true | true | true | true | false
allHex-sound p () hex-4 | true | true | true | false | _
allHex-sound p () hex-4 | true | true | false | _ | _
allHex-sound p () hex-4 | true | false | _ | _ | _
allHex-sound p () hex-4 | false | _ | _ | _ | _
allHex-sound p ok hex-5 with p hex-0 | p hex-1 | p hex-2 | p hex-3 | p hex-4 | p hex-5
... | true | true | true | true | true | true = is-true
allHex-sound p () hex-5 | true | true | true | true | true | false
allHex-sound p () hex-5 | true | true | true | true | false | _
allHex-sound p () hex-5 | true | true | true | false | _ | _
allHex-sound p () hex-5 | true | true | false | _ | _ | _
allHex-sound p () hex-5 | true | false | _ | _ | _ | _
allHex-sound p () hex-5 | false | _ | _ | _ | _ | _

allHex2 : (HexTruth → HexTruth → Bool) → Bool
allHex2 p = allHex (λ x → allHex (p x))

allHex2-sound :
  (p : HexTruth → HexTruth → Bool) →
  IsTrue (allHex2 p) →
  (x y : HexTruth) →
  IsTrue (p x y)
allHex2-sound p ok x y =
  allHex-sound (p x) (allHex-sound (λ a → allHex (p a)) ok x) y

allHex3 : (HexTruth → HexTruth → HexTruth → Bool) → Bool
allHex3 p = allHex (λ x → allHex2 (p x))

allHex3-sound :
  (p : HexTruth → HexTruth → HexTruth → Bool) →
  IsTrue (allHex3 p) →
  (x y z : HexTruth) →
  IsTrue (p x y z)
allHex3-sound p ok x y z =
  allHex2-sound (p x) (allHex-sound (λ a → allHex2 (p a)) ok x) y z

hexEqProof :
  (x y : HexTruth) →
  IsTrue (hexEq x y) →
  x ≡ y
hexEqProof = hexEq-sound

------------------------------------------------------------------------
-- Ring laws, discharged through finite table checks.

hexAddComm-table : IsTrue (allHex2 (λ x y → hexEq (hexAdd x y) (hexAdd y x)))
hexAddComm-table = is-true

hexAddComm : (x y : HexTruth) → hexAdd x y ≡ hexAdd y x
hexAddComm x y =
  hexEqProof
    (hexAdd x y)
    (hexAdd y x)
    (allHex2-sound
      (λ a b → hexEq (hexAdd a b) (hexAdd b a))
      hexAddComm-table
      x
      y)

hexAddAssoc-table :
  IsTrue
    (allHex3
      (λ x y z →
        hexEq
          (hexAdd (hexAdd x y) z)
          (hexAdd x (hexAdd y z))))
hexAddAssoc-table = is-true

hexAddAssoc :
  (x y z : HexTruth) →
  hexAdd (hexAdd x y) z ≡ hexAdd x (hexAdd y z)
hexAddAssoc x y z =
  hexEqProof
    (hexAdd (hexAdd x y) z)
    (hexAdd x (hexAdd y z))
    (allHex3-sound
      (λ a b c →
        hexEq
          (hexAdd (hexAdd a b) c)
          (hexAdd a (hexAdd b c)))
      hexAddAssoc-table
      x
      y
      z)

hexAddIdentityˡ : (x : HexTruth) → hexAdd hexZero x ≡ x
hexAddIdentityˡ x = refl

hexAddIdentityʳ-table : IsTrue (allHex (λ x → hexEq (hexAdd x hexZero) x))
hexAddIdentityʳ-table = is-true

hexAddIdentityʳ : (x : HexTruth) → hexAdd x hexZero ≡ x
hexAddIdentityʳ x =
  hexEqProof
    (hexAdd x hexZero)
    x
    (allHex-sound
      (λ a → hexEq (hexAdd a hexZero) a)
      hexAddIdentityʳ-table
      x)

hexAddInverseˡ-table : IsTrue (allHex (λ x → hexEq (hexAdd (hexNeg x) x) hexZero))
hexAddInverseˡ-table = is-true

hexAddInverseˡ : (x : HexTruth) → hexAdd (hexNeg x) x ≡ hexZero
hexAddInverseˡ x =
  hexEqProof
    (hexAdd (hexNeg x) x)
    hexZero
    (allHex-sound
      (λ a → hexEq (hexAdd (hexNeg a) a) hexZero)
      hexAddInverseˡ-table
      x)

hexAddInverseʳ-table : IsTrue (allHex (λ x → hexEq (hexAdd x (hexNeg x)) hexZero))
hexAddInverseʳ-table = is-true

hexAddInverseʳ : (x : HexTruth) → hexAdd x (hexNeg x) ≡ hexZero
hexAddInverseʳ x =
  hexEqProof
    (hexAdd x (hexNeg x))
    hexZero
    (allHex-sound
      (λ a → hexEq (hexAdd a (hexNeg a)) hexZero)
      hexAddInverseʳ-table
      x)

hexMulComm-table : IsTrue (allHex2 (λ x y → hexEq (hexMul x y) (hexMul y x)))
hexMulComm-table = is-true

hexMulComm : (x y : HexTruth) → hexMul x y ≡ hexMul y x
hexMulComm x y =
  hexEqProof
    (hexMul x y)
    (hexMul y x)
    (allHex2-sound
      (λ a b → hexEq (hexMul a b) (hexMul b a))
      hexMulComm-table
      x
      y)

hexMulAssoc-table :
  IsTrue
    (allHex3
      (λ x y z →
        hexEq
          (hexMul (hexMul x y) z)
          (hexMul x (hexMul y z))))
hexMulAssoc-table = is-true

hexMulAssoc :
  (x y z : HexTruth) →
  hexMul (hexMul x y) z ≡ hexMul x (hexMul y z)
hexMulAssoc x y z =
  hexEqProof
    (hexMul (hexMul x y) z)
    (hexMul x (hexMul y z))
    (allHex3-sound
      (λ a b c →
        hexEq
          (hexMul (hexMul a b) c)
          (hexMul a (hexMul b c)))
      hexMulAssoc-table
      x
      y
      z)

hexMulIdentityˡ : (x : HexTruth) → hexMul hexOne x ≡ x
hexMulIdentityˡ x = refl

hexMulIdentityʳ-table : IsTrue (allHex (λ x → hexEq (hexMul x hexOne) x))
hexMulIdentityʳ-table = is-true

hexMulIdentityʳ : (x : HexTruth) → hexMul x hexOne ≡ x
hexMulIdentityʳ x =
  hexEqProof
    (hexMul x hexOne)
    x
    (allHex-sound
      (λ a → hexEq (hexMul a hexOne) a)
      hexMulIdentityʳ-table
      x)

hexMulZeroˡ : (x : HexTruth) → hexMul hexZero x ≡ hexZero
hexMulZeroˡ x = refl

hexMulZeroʳ-table : IsTrue (allHex (λ x → hexEq (hexMul x hexZero) hexZero))
hexMulZeroʳ-table = is-true

hexMulZeroʳ : (x : HexTruth) → hexMul x hexZero ≡ hexZero
hexMulZeroʳ x =
  hexEqProof
    (hexMul x hexZero)
    hexZero
    (allHex-sound
      (λ a → hexEq (hexMul a hexZero) hexZero)
      hexMulZeroʳ-table
      x)

hexDistribˡ-table :
  IsTrue
    (allHex3
      (λ x y z →
        hexEq
          (hexMul x (hexAdd y z))
          (hexAdd (hexMul x y) (hexMul x z))))
hexDistribˡ-table = is-true

hexDistribˡ :
  (x y z : HexTruth) →
  hexMul x (hexAdd y z) ≡ hexAdd (hexMul x y) (hexMul x z)
hexDistribˡ x y z =
  hexEqProof
    (hexMul x (hexAdd y z))
    (hexAdd (hexMul x y) (hexMul x z))
    (allHex3-sound
      (λ a b c →
        hexEq
          (hexMul a (hexAdd b c))
          (hexAdd (hexMul a b) (hexMul a c)))
      hexDistribˡ-table
      x
      y
      z)

hexDistribʳ-table :
  IsTrue
    (allHex3
      (λ x y z →
        hexEq
          (hexMul (hexAdd x y) z)
          (hexAdd (hexMul x z) (hexMul y z))))
hexDistribʳ-table = is-true

hexDistribʳ :
  (x y z : HexTruth) →
  hexMul (hexAdd x y) z ≡ hexAdd (hexMul x z) (hexMul y z)
hexDistribʳ x y z =
  hexEqProof
    (hexMul (hexAdd x y) z)
    (hexAdd (hexMul x z) (hexMul y z))
    (allHex3-sound
      (λ a b c →
        hexEq
          (hexMul (hexAdd a b) c)
          (hexAdd (hexMul a c) (hexMul b c)))
      hexDistribʳ-table
      x
      y
      z)

------------------------------------------------------------------------
-- Stable ring and not-field receipts.

record HexTruthRingSurface : Set₁ where
  field
    Carrier : Set
    zero one : Carrier
    _+_ _*_ : Carrier → Carrier → Carrier
    -_ : Carrier → Carrier

    +-comm :
      (x y : Carrier) →
      x + y ≡ y + x

    +-assoc :
      (x y z : Carrier) →
      (x + y) + z ≡ x + (y + z)

    +-identityˡ :
      (x : Carrier) →
      zero + x ≡ x

    +-identityʳ :
      (x : Carrier) →
      x + zero ≡ x

    +-inverseˡ :
      (x : Carrier) →
      (- x) + x ≡ zero

    +-inverseʳ :
      (x : Carrier) →
      x + (- x) ≡ zero

    *-comm :
      (x y : Carrier) →
      x * y ≡ y * x

    *-assoc :
      (x y z : Carrier) →
      (x * y) * z ≡ x * (y * z)

    *-identityˡ :
      (x : Carrier) →
      one * x ≡ x

    *-identityʳ :
      (x : Carrier) →
      x * one ≡ x

    *-zeroˡ :
      (x : Carrier) →
      zero * x ≡ zero

    *-zeroʳ :
      (x : Carrier) →
      x * zero ≡ zero

    distribˡ :
      (x y z : Carrier) →
      x * (y + z) ≡ (x * y) + (x * z)

    distribʳ :
      (x y z : Carrier) →
      (x + y) * z ≡ (x * z) + (y * z)

open HexTruthRingSurface public

hexTruthRingSurface : HexTruthRingSurface
hexTruthRingSurface =
  record
    { Carrier = HexTruth
    ; zero = hexZero
    ; one = hexOne
    ; _+_ = hexAdd
    ; _*_ = hexMul
    ; -_ = hexNeg
    ; +-comm = hexAddComm
    ; +-assoc = hexAddAssoc
    ; +-identityˡ = hexAddIdentityˡ
    ; +-identityʳ = hexAddIdentityʳ
    ; +-inverseˡ = hexAddInverseˡ
    ; +-inverseʳ = hexAddInverseʳ
    ; *-comm = hexMulComm
    ; *-assoc = hexMulAssoc
    ; *-identityˡ = hexMulIdentityˡ
    ; *-identityʳ = hexMulIdentityʳ
    ; *-zeroˡ = hexMulZeroˡ
    ; *-zeroʳ = hexMulZeroʳ
    ; distribˡ = hexDistribˡ
    ; distribʳ = hexDistribʳ
    }

hex-2*hex-3≡hex-0 : hexMul hex-2 hex-3 ≡ hex-0
hex-2*hex-3≡hex-0 = refl

record HexZeroDivisorWitness : Set where
  constructor hexZeroDivisorWitness
  field
    left right : HexTruth
    left-nonzero : hexEq left hexZero ≡ false
    right-nonzero : hexEq right hexZero ≡ false
    product-zero : hexMul left right ≡ hexZero

open HexZeroDivisorWitness public

hexZeroDivisorWitness-2-3 : HexZeroDivisorWitness
hexZeroDivisorWitness-2-3 =
  hexZeroDivisorWitness hex-2 hex-3 refl refl hex-2*hex-3≡hex-0

hexIsField : Bool
hexIsField = false

hexNotField : Bool
hexNotField = true

record HexNotFieldReceipt : Set where
  constructor hexNotFieldReceipt
  field
    field-claim : Bool
    not-field : Bool
    zero-divisor : HexZeroDivisorWitness
    zero-divisor-product-check : hexMul hex-2 hex-3 ≡ hexZero

open HexNotFieldReceipt public

hexNotFieldReceipt-2-3 : HexNotFieldReceipt
hexNotFieldReceipt-2-3 =
  hexNotFieldReceipt
    hexIsField
    hexNotField
    hexZeroDivisorWitness-2-3
    hex-2*hex-3≡hex-0
