module DASHI.Moonshine.CM163Hecke41FullIntegerMatrixExact where

-- SOURCE-WRITTEN, kernel pending. Full bivariate principal-part
-- reconstruction from cyclic trace Newton identities. Every candidate
-- division is checked as integer multiplication. No hash is a proof.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_∸_)
open import Data.Integer.Base as Z using (ℤ; +_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec)
import Data.Integer.Properties as ZP
import Data.Nat.Properties as NP
open import Relation.Nullary using (yes; no)
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Shift
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import Data.Rational.Unnormalised as Q
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as C
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
open C using (slot; build; divPositive; Through; decThrough; unitZ; power)
open I using (SeriesZ; rowZ)

Matrix : Set
Matrix = List (List ℤ)

row : Matrix → Nat → SeriesZ
row [] k n = + 0
row (a ∷ as) zero n = slot a n
row (a ∷ as) (suc k) n = row as k n

sum : Nat → (Nat → ℤ) → ℤ
sum zero f = + 0
sum (suc n) f = Z._+_ (sum n f) (f n)

sign : Nat → ℤ
sign zero = + 1
sign (suc n) = Z.- (sign n)

zpow : ℤ → Nat → ℤ
zpow a zero = + 1
zpow a (suc n) = Z._*_ a (zpow a n)

-- Trace q^n coefficient of the k-th power, for k<=41.
-- k=41 also has one negative coefficient q^-1=41.
trace : SeriesZ → Nat → SeriesZ
trace j k n = Z._*_ (+ 41) (power j k (41 * n + k))

newton : SeriesZ → Matrix → Nat → SeriesZ
newton j es k n = sum k (λ i → Z._*_ (sign i)
  (rowZ (row es (k ∸ suc i)) (trace j (suc i)) n))

nextE : SeriesZ → Matrix → Nat → List ℤ
nextE j es k = build (λ _ n → divPositive (newton j es (suc k) n) k) 41

elementariesFrom : SeriesZ → Matrix → Nat → Nat → Matrix
elementariesFrom j es k zero = es
elementariesFrom j es k (suc fuel) =
  elementariesFrom j (es ++ (nextE j es k ∷ [])) (suc k) fuel

elementaries : SeriesZ → Matrix
elementaries j = elementariesFrom j ((+ 1 ∷ []) ∷ []) zero 41

-- q^42 F_q(Y) through order 42, all 43 columns.
-- The finite-part negative e_41 mode has sign -1 in F.
coeff : Matrix → Nat → Nat → ℤ
coeff es y n =
  let k = 41 ∸ y
      a = Z._*_ (sign k) (row es k (n ∸ 1))
      at0 = ifEq y zero (ifEq n zero (+ 1) (ifEq n 41 (+ 744) (+ 0))) (+ 0)
      at1 = ifEq y 1 (ifEq n 41 (Z.- (+ 1)) (+ 0)) (+ 0)
      finiteY = ifEq y zero (+ 0)
        (ifEq n 42 (Z._*_ (sign (42 ∸ y)) (row es (42 ∸ y) zero)) (+ 0))
      infinityY = ifEq y 42 (+ 0)
        (ifEq n zero (+ 0) (Z.- a))
      constantInf = ifEq y 42 (+ 0)
        (ifEq n 42 (Z.- (Z._*_ (+ 744) (Z._*_ (sign k) (row es k zero)))) (+ 0))
  in Z._+_ at0 (Z._+_ at1 (Z._+_ finiteY (Z._+_ infinityY constantInf)))
  where
  ifEq : Nat → Nat → ℤ → ℤ → ℤ
  ifEq zero zero a b = a
  ifEq zero (suc n) a b = b
  ifEq (suc n) zero a b = b
  ifEq (suc n) (suc m) a b = ifEq n m a b

-- Descending X coefficients, computed by triangular residual removal.
columnFrom : SeriesZ → SeriesZ → List ℤ → Nat → Nat → List ℤ
columnFrom j source acc k zero = acc
columnFrom j source acc k (suc fuel) =
  let c = Z._-_ (source k)
        (sum k (λ i → Z._*_ (slot acc i) (power j (42 ∸ i) (k ∸ i))))
  in columnFrom j source (acc ++ (c ∷ [])) (suc k) fuel

column : SeriesZ → Matrix → Nat → List ℤ
column j es y = columnFrom j (coeff es y) [] zero 43

-- c(x,y) uses ascending exponents; each stored column is descending X.
candidate : SeriesZ → Nat → Nat → ℤ
candidate j x y = slot (column j (elementaries j) y) (42 ∸ x)

NewtonGate : SeriesZ → Matrix → Set
NewtonGate j es = Through 40 (λ k → Through 41 (λ n →
  Z._*_ (+ (suc k)) (row es (suc k) n) ≡ newton j es (suc k) n))

ColumnGate : SeriesZ → Matrix → (Nat → Nat → ℤ) → Set
ColumnGate j es c = Through 42 (λ y → Through 42 (λ n →
  coeff es y n ≡ sum (suc n) (λ i →
    Z._*_ (c (42 ∸ i) y) (power j (42 ∸ i) (n ∸ i)))))

SymmetryGate : (Nat → Nat → ℤ) → Set
SymmetryGate c = Through 42 (λ x → Through 42 (λ y → c x y ≡ c y x))

diagonal : (Nat → Nat → ℤ) → SeriesZ
diagonal c n = sum 43 (λ x → ifIn x (n ∸ x))
  where
  ifIn : Nat → Nat → ℤ
  ifIn x y with x NP.≤? n | y NP.≤? 42
  ... | yes _ | yes _ = c x y
  ... | _ | _ = + 0

slice : (Nat → Nat → ℤ) → SeriesZ
slice c x = sum 43 (λ y → Z._*_ (c x y) (zpow C.K y))

PacketGate : (Nat → Nat → ℤ) → Set
PacketGate c = Through 84 (λ n → diagonal c n ≡ originalD n) ×
  Through 42 (λ n → slice c n ≡ originalS n)
  where
  originalD : SeriesZ
  originalD n with n NP.≤? 82
  ... | yes _ = Q.numerator (Shift.coeff (82 ∸ n) Packet.diagonal)
  ... | no _ = + 0
  originalS : SeriesZ
  originalS n = Q.numerator (Shift.coeff (42 ∸ n) Packet.slice)


-- Exact executable decisions for the canonical matrix, separately
-- from analytic rigidity and without reducing them on every import.
newtonDec : ∀ j es → Dec (NewtonGate j es)
newtonDec j es = decThrough 40 _ (λ k → decThrough 41 _ (λ n →
  ZP._≟_ (Z._*_ (+ (suc k)) (row es (suc k) n)) (newton j es (suc k) n)))

columnDec : ∀ j es c → Dec (ColumnGate j es c)
columnDec j es c = decThrough 42 _ (λ y → decThrough 42 _ (λ n →
  ZP._≟_ (coeff es y n) (sum (suc n) (λ i →
    Z._*_ (c (42 ∸ i) y) (power j (42 ∸ i) (n ∸ i))))))

symmetryDec : ∀ c → Dec (SymmetryGate c)
symmetryDec c = decThrough 42 _ (λ x → decThrough 42 _ (λ y → ZP._≟_ (c x y) (c y x)))

packetDiagonalZ : SeriesZ
packetDiagonalZ n with n NP.≤? 82
... | yes _ = Q.numerator (Shift.coeff (82 ∸ n) Packet.diagonal)
... | no _ = + 0

packetSliceZ : SeriesZ
packetSliceZ n = Q.numerator (Shift.coeff (42 ∸ n) Packet.slice)

packetDec : ∀ c → Dec (PacketGate c)
packetDec c with decThrough 84 _ (λ n → ZP._≟_ (diagonal c n) (packetDiagonalZ n))
               | decThrough 42 _ (λ n → ZP._≟_ (slice c n) (packetSliceZ n))
... | yes d | yes s = yes (d , s)
... | no d | _ = no (λ h → d (proj₁ h))
... | yes d | no s = no (λ h → s (proj₂ h))

originalMatrix : Nat → Nat → ℤ
originalMatrix = candidate C.j

originalSymmetryCheck : Dec (SymmetryGate originalMatrix)
originalSymmetryCheck = symmetryDec originalMatrix

originalPacketCheck : Dec (PacketGate originalMatrix)
originalPacketCheck = packetDec originalMatrix
