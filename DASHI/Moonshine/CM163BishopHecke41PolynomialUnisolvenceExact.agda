module DASHI.Moonshine.CM163BishopHecke41PolynomialUnisolvenceExact where

-- SOURCE-WRITTEN, KERNEL PENDING.
-- Degree-indexed Horner geometry, using the existing length-indexed
-- complex row. Divided differences are constructed as polynomials;
-- there is NEVER division by the evaluation coordinate at a root.
-- Distinct-node apartness is needed only in the finite root induction.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.CM163BishopHecke41NodeDifferenceExact as D
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_)
open Comp using (complexTrans; complexSym)
open D using (Row; nil; cons)

-- Ascending coefficients: Row (suc n) has degree at most n.
eval : ∀ {n} → Row n → BishopComplex → BishopComplex
eval nil x = A.zeroC
eval (cons a p) x = a +C x *C eval p x

singleRead : ∀ a x → eval (cons a nil) x ≈C a
singleRead a x = complexTrans
  (A.addCCongruent (C.≈C-refl _) (L.complexMultiplyRightZero x))
  (L.complexAddRightIdentity a)

pad : ∀ {n} → Row n → Row (suc n)
pad nil = cons A.zeroC nil
pad (cons a p) = cons a (pad p)

padRead : ∀ {n} (p : Row n) x → eval (pad p) x ≈C eval p x
padRead nil x = singleRead A.zeroC x
padRead (cons a p) x = A.addCCongruent (C.≈C-refl _)
  (A.mulCCongruent (C.≈C-refl _) (padRead p x))

add : ∀ {n} → Row n → Row n → Row n
add nil nil = nil
add (cons a p) (cons b q) = cons (a +C b) (add p q)

addRead : ∀ {n} (p q : Row n) x → eval (add p q) x ≈C (eval p x +C eval q x)
addRead nil nil x = complexSym (L.complexAddRightIdentity A.zeroC)
addRead (cons a p) (cons b q) x =
  complexTrans (A.addCCongruent (C.≈C-refl _)
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (addRead p q x))
      (L.complexMultiplyDistributesLeft x (eval p x) (eval q x))))
    (Shift.addShuffle a b (x *C eval p x) (x *C eval q x))

scale : ∀ {n} → BishopComplex → Row n → Row n
scale r nil = nil
scale r (cons a p) = cons (r *C a) (scale r p)

commuteInner : ∀ x r z → (x *C (r *C z)) ≈C (r *C (x *C z))
commuteInner x r z = complexTrans (complexSym (L.complexMultiplyAssociative x r z))
  (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative x r) (C.≈C-refl _))
    (L.complexMultiplyAssociative r x z))

scaleRead : ∀ {n} r (p : Row n) x → eval (scale r p) x ≈C (r *C eval p x)
scaleRead r nil x = complexSym (L.complexMultiplyRightZero r)
scaleRead r (cons a p) x =
  complexTrans (A.addCCongruent (C.≈C-refl _)
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (scaleRead r p x))
      (commuteInner x r (eval p x))))
    (complexSym (L.complexMultiplyDistributesLeft r a (x *C eval p x)))

-- Exact degree lowering: (P(x)-P(r))/(x-r), represented without
-- inversion. The padding preserves the degree bound under addition.
quotient : ∀ {n} → BishopComplex → Row (suc n) → Row n
quotient r (cons a nil) = nil
quotient r (cons a (cons b p)) =
  add (cons b p) (pad (scale r (quotient r (cons b p))))

quotientRead : ∀ {n} r (p : Row (suc n)) x →
  (eval p x -C eval p r) ≈C ((x -C r) *C eval (quotient r p) x)
quotientRead r (cons a nil) x =
  complexTrans (A.subCCongruent (singleRead a x) (singleRead a r))
    (complexTrans (J.sameSub a) (complexSym (L.complexMultiplyRightZero (x -C r))))
quotientRead r (cons a (cons b p)) x =
  let tail = cons b p
      u = eval tail x
      v = eval tail r
      w = x -C r
      t = eval (quotient r tail) x
      qRead = complexTrans (addRead tail (pad (scale r (quotient r tail))) x)
        (A.addCCongruent (C.≈C-refl _)
          (complexTrans (padRead (scale r (quotient r tail)) x)
            (scaleRead r (quotient r tail) x)))
  in complexTrans (J.addStep a (x *C u) a (r *C v))
    (complexTrans (A.addCCongruent (J.sameSub a) (C.≈C-refl _))
      (complexTrans (L.complexAddLeftIdentity _)
        (complexTrans (J.mulStep x u r v)
          (complexTrans (A.addCCongruent (C.≈C-refl _)
            (A.mulCCongruent (C.≈C-refl _) (quotientRead r tail x)))
            (complexTrans (Cross.restFinish r w u t)
              (A.mulCCongruent (C.≈C-refl _) (complexSym qRead)))))))

-- Node geometry records exactly the apartness needed to cancel a
-- difference: no decidable equality of arbitrary complex numbers.
Apart : ∀ {n} → (Fin n → BishopComplex) → Set
Apart {zero} z = ⊤
Apart {suc n} z =
  (∀ i → Rec.BishopComplexNonzero (z (Fin.suc i) -C z Fin.zero)) ×
  Apart (λ i → z (Fin.suc i))

zeroEverywhere : ∀ {n} (p : Row n) (z : Fin n → BishopComplex) →
  Apart z → (∀ i → eval p (z i) ≈C A.zeroC) →
  ∀ x → eval p x ≈C A.zeroC
zeroEverywhere nil z apart roots x = C.≈C-refl _
zeroEverywhere (cons a p) z (apart , later) roots x =
  let r = z Fin.zero
      f = cons a p
      q = quotient r f
      tailRoots : ∀ i → eval q (z (Fin.suc i)) ≈C A.zeroC
      tailRoots i =
        let y = z (Fin.suc i)
            w = y -C r
        in Cancel.cancelLeft w (eval q y) A.zeroC (apart i)
          (complexTrans (complexSym (quotientRead r f y))
            (complexTrans (A.subCCongruent (roots (Fin.suc i)) (roots Fin.zero))
              (complexTrans (J.sameSub A.zeroC)
                (complexSym (L.complexMultiplyRightZero w)))))
      qZero = zeroEverywhere q (λ i → z (Fin.suc i)) later tailRoots x
      difference = complexTrans (quotientRead r f x)
        (complexTrans (A.mulCCongruent (C.≈C-refl _) qZero)
          (L.complexMultiplyRightZero (x -C r)))
  in complexTrans (Cross.zeroDifference (eval f x) (eval f r) difference)
    (roots Fin.zero)

-- Pointwise subtraction represented by the same degree-indexed row.
sub : ∀ {n} → Row n → Row n → Row n
sub nil nil = nil
sub (cons a p) (cons b q) = cons (a -C b) (sub p q)

subRead : ∀ {n} (p q : Row n) x → eval (sub p q) x ≈C (eval p x -C eval q x)
subRead nil nil x = complexSym (J.sameSub A.zeroC)
subRead (cons a p) (cons b q) x =
  complexTrans (A.addCCongruent (C.≈C-refl _)
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (subRead p q x))
      (Alg.mulSub x (eval p x) (eval q x))))
    (complexSym (J.addStep a (x *C eval p x) b (x *C eval q x)))

unique : ∀ {n} (p q : Row n) (z : Fin n → BishopComplex) →
  Apart z → (∀ i → eval p (z i) ≈C eval q (z i)) →
  ∀ x → eval p x ≈C eval q x
unique p q z apart nodes x = Cross.zeroDifference _ _
  (complexTrans (complexSym (subRead p q x))
    (zeroEverywhere (sub p q) z apart (λ i →
      complexTrans (subRead p q (z i))
        (complexTrans (A.subCCongruent (nodes i) (C.≈C-refl _))
          (J.sameSub _))) x))

-- Multiplication by an actual linear factor raises the row length
-- by exactly one. This produces the original finite product degree.
linear : ∀ {n} → BishopComplex → Row n → Row (suc n)
linear r p = sub (cons A.zeroC p) (pad (scale r p))

linearRead : ∀ {n} r (p : Row n) x →
  eval (linear r p) x ≈C ((x -C r) *C eval p x)
linearRead r p x =
  complexTrans (subRead (cons A.zeroC p) (pad (scale r p)) x)
    (complexTrans (A.subCCongruent (L.complexAddLeftIdentity _)
      (complexTrans (padRead (scale r p) x) (scaleRead r p x)))
      (complexTrans (A.subCCongruent (L.complexMultiplyCommutative x (eval p x))
        (L.complexMultiplyCommutative r (eval p x)))
        (complexTrans (J.subFactor (eval p x) x r)
          (L.complexMultiplyCommutative (eval p x) (x -C r)))))

productRow : ∀ {n} → (Fin n → BishopComplex) → Row (suc n)
productRow {zero} f = cons A.oneC nil
productRow {suc n} f = linear (f Fin.zero) (productRow (λ i → f (Fin.suc i)))

productRead : ∀ {n} (f : Fin n → BishopComplex) x →
  eval (productRow f) x ≈C Prod.product (λ i → x -C f i)
productRead {zero} f x = singleRead A.oneC x
productRead {suc n} f x = complexTrans (linearRead (f Fin.zero) _ x)
  (A.mulCCongruent (C.≈C-refl _) (productRead (λ i → f (Fin.suc i)) x))
