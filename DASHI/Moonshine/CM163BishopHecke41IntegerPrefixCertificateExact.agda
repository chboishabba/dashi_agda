module DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact where

-- SOURCE-WRITTEN, kernel pending. Exact bounded integer candidate
-- construction. Candidate division is untrusted: the checked
-- residuals are multiplication equations on the original rowZ.
-- No float phase, hash receipt, or native_decide premise.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; _∸_)
import Data.Nat.Properties as NP
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_])
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
import Data.Integer.Properties as ZP
import Relation.Binary.PropositionalEquality as Eq
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as Fold
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as One
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Shift
import Data.Rational.Unnormalised as Q

open I using (SeriesZ; rowZ)

slot : List ℤ → SeriesZ
slot [] n = + 0
slot (a ∷ as) zero = a
slot (a ∷ as) (suc n) = slot as n

-- Coefficients generated in increasing degree. All candidate
-- computations read only the existing prefix, never their own slot.
buildFrom : (List ℤ → Nat → ℤ) → List ℤ → Nat → Nat → List ℤ
buildFrom f acc k zero = acc
buildFrom f acc k (suc n) = buildFrom f (acc ++ (f acc k ∷ [])) (suc k) n

build : (List ℤ → Nat → ℤ) → Nat → List ℤ
build f D = buildFrom f [] zero (suc D)

divPositive : ℤ → Nat → ℤ
divPositive (+ n) d = + (n / suc d)
divPositive -[1+ n ] d = Z.- (+ (suc n / suc d))

X Y X3 Y2 : SeriesZ
X = I.coefficient 3 (+ 240)
Y = I.coefficient 5 (Z.- (+ 504))
X3 = rowZ (rowZ X X) X
Y2 = rowZ Y Y

disc : SeriesZ
disc n = Z._-_ (X3 n) (Y2 n)

candidateU : Nat → List ℤ
candidateU D = build (λ _ n → divPositive (disc (suc n)) 1727) D

tailRow : SeriesZ → SeriesZ → Nat → ℤ
tailRow a b n = Fold.foldZ (λ i → Z._*_ (a i) (b (n ∸ i))) (One.oneTo n)

candidateJ : Nat → List ℤ → List ℤ
candidateJ D u = build (λ acc n → Z._-_ (X3 n) (tailRow (slot u) (slot acc) n)) D

delay : Nat → SeriesZ → SeriesZ
delay zero f n = f n
delay (suc k) f zero = + 0
delay (suc k) f (suc n) = delay k f n

expand : SeriesZ → SeriesZ
expand f n with n % 41 NP.≟ zero
... | yes _ = f (n / 41)
... | no _ = + 0

unitZ : SeriesZ
unitZ zero = + 1
unitZ (suc n) = + 0

K : ℤ
K = Z.- (+ (640320 * 640320 * 640320))

constant : ℤ → SeriesZ
constant a zero = a
constant a (suc n) = + 0

hDiag hSlice gDiag gSlice : SeriesZ → SeriesZ
hDiag j n = Z._-_ (expand j n) (delay 40 j n)
hSlice j n = Z._-_ (j n) (delay 1 (constant K) n)
gDiag j n = Z._-_ (delay 40 j n) (expand j n)
gSlice j n = Z._-_ (expand j n) (delay 41 (constant K) n)

candidateL : Nat → SeriesZ → List ℤ
candidateL D h = build (λ acc n → Z._-_ (Z._*_ (+ n) (h n)) (tailRow h (slot acc) n)) D

traceDriver : SeriesZ → SeriesZ
traceDriver l n = l (n * 41)

candidateN : Nat → SeriesZ → List ℤ
candidateN D l = build next D
  where
  next : List ℤ → Nat → ℤ
  next acc zero = + 1
  next acc (suc n) = divPositive (tailRow (traceDriver l) (slot acc) (suc n)) n

power : SeriesZ → Nat → SeriesZ
power a zero = unitZ
power a (suc k) = rowZ a (power a k)

-- Original descending column, normalized in q, not fitted.
column : SeriesZ → List Q.ℚᵘ → SeriesZ
column j [] n = + 0
column j (c ∷ cs) n = Z._+_
  (Z._*_ (Q.numerator c) (power j (length cs) n))
  (delay 1 (column j cs) n)

-- A bounded predicate retains each individual proof. It is not an
-- arbitrary Boolean flag. All residuals are decidable integer equality.
Through : Nat → (Nat → Set) → Set
Through zero p = p zero
Through (suc n) p = Through n p × p (suc n)

throughAt : ∀ {p : Nat → Set} n → Through n p → ∀ k → k ≤ n → p k
throughAt {p} zero h zero hk = h
throughAt {p} zero h (suc k) ()
throughAt {p} (suc n) h k hk with k NP.≟ suc n
... | yes refl = proj₂ h
... | no neq = throughAt n (proj₁ h) k (NP.≤-pred (NP.≤∧≢⇒< hk neq))

decThrough : ∀ n (p : Nat → Set) → (∀ k → Dec (p k)) → Dec (Through n p)
decThrough zero p d = d zero
decThrough (suc n) p d with decThrough n p d | d (suc n)
... | yes a | yes b = yes (a , b)
... | no a | _ = no (λ h → a (proj₁ h))
... | yes a | no b = no (λ h → b (proj₂ h))

UnitGate : Nat → SeriesZ → SeriesZ → Set
UnitGate D u j =
  Through D (λ n → Z._*_ (+ 1728) (u n) ≡ disc (suc n)) ×
  Through D (λ n → rowZ u j n ≡ X3 n)

SectorGate : Nat → SeriesZ → SeriesZ → SeriesZ → SeriesZ → List Q.ℚᵘ → SeriesZ → Set
SectorGate D h g l a cs j =
  Through (D * 41) (λ n → rowZ h l n ≡ Z._*_ (+ n) (h n)) ×
  Through D (λ n → rowZ (traceDriver l) a n ≡ Z._*_ (+ n) (a n)) ×
  Through D (λ n → rowZ g a n ≡ column j cs n)

unitDec : ∀ D u j → Dec (UnitGate D u j)
unitDec D u j with decThrough D _ (λ n → ZP._≟_ (Z._*_ (+ 1728) (u n)) (disc (suc n)))
                  | decThrough D _ (λ n → ZP._≟_ (rowZ u j n) (X3 n))
... | yes a | yes b = yes (a , b)
... | no a | _ = no (λ h → a (proj₁ h))
... | yes a | no b = no (λ h → b (proj₂ h))

sectorDec : ∀ D h g l a cs j → Dec (SectorGate D h g l a cs j)
sectorDec D h g l a cs j
  with decThrough (D * 41) _ (λ n → ZP._≟_ (rowZ h l n) (Z._*_ (+ n) (h n)))
     | decThrough D _ (λ n → ZP._≟_ (rowZ (traceDriver l) a n) (Z._*_ (+ n) (a n)))
     | decThrough D _ (λ n → ZP._≟_ (rowZ g a n) (column j cs n))
... | yes x | yes y | yes z = yes (x , y , z)
... | no x | _ | _ = no (λ h → x (proj₁ h))
... | yes x | no y | _ = no (λ h → y (proj₁ (proj₂ h)))
... | yes x | yes y | no z = no (λ h → z (proj₂ (proj₂ h)))

-- The exact depth of J is 3322 for the shifted diagonal h, but
-- 1722 for the unshifted fixed slice. Pad the slice with the same
-- already-computed J stream, not a different generator.
u j lD nD lS nS : SeriesZ
u = slot (candidateU 3322)
j = slot (candidateJ 3322 (candidateU 3322))
lD = slot (candidateL 3362 (hDiag j))
nD = slot (candidateN 82 lD)
lS = slot (candidateL 1722 (hSlice j))
nS = slot (candidateN 42 lS)

unitCheck : Dec (UnitGate 3322 u j)
unitCheck = unitDec 3322 u j

diagCheck : Dec (SectorGate 82 (hDiag j) (gDiag j) lD nD Packet.diagonal j)
diagCheck = sectorDec 82 (hDiag j) (gDiag j) lD nD Packet.diagonal j

sliceCheck : Dec (SectorGate 42 (hSlice j) (gSlice j) lS nS Packet.slice j)
sliceCheck = sectorDec 42 (hSlice j) (gSlice j) lS nS Packet.slice j

-- Do not force these large decisions into every importing module.
-- A separate local kernel acceptance target should consume yes
-- witnesses; these are exact executable definitions, not receipts.
