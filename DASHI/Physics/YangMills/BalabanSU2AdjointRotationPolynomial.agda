module DASHI.Physics.YangMills.BalabanSU2AdjointRotationPolynomial where

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver; oneCoefficient)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using
  (Polynomial; con; _:=_; _:+_; _:*_; :-_)
open import DASHI.Physics.YangMills.BalabanSU2AdjointRotationScalar using
  (rotationX; rotationY; rotationZ
  ; adjointXExpandedR; adjointYExpandedR; adjointZExpandedR)

oneP : ∀ {n : Nat} → Polynomial n
oneP = con oneCoefficient

twoP : ∀ {n : Nat} → Polynomial n
twoP = oneP :+ oneP

row00P row01P row02P row10P row11P row12P row20P row21P row22P :
  ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
row00P a b c d = (((a :* a) :+ (b :* b)) :+ (:- (c :* c))) :+ (:- (d :* d))
row01P a b c d = twoP :* ((b :* c) :+ (:- (a :* d)))
row02P a b c d = twoP :* ((b :* d) :+ (a :* c))
row10P a b c d = twoP :* ((b :* c) :+ (a :* d))
row11P a b c d = (((a :* a) :+ (:- (b :* b))) :+ (c :* c)) :+ (:- (d :* d))
row12P a b c d = twoP :* ((c :* d) :+ (:- (a :* b)))
row20P a b c d = twoP :* ((b :* d) :+ (:- (a :* c)))
row21P a b c d = twoP :* ((c :* d) :+ (a :* b))
row22P a b c d = (((a :* a) :+ (:- (b :* b))) :+ (:- (c :* c))) :+ (d :* d)

rotationXP rotationYP rotationZP :
  ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
rotationXP a b c d x y z =
  ((row00P a b c d :* x) :+ (row01P a b c d :* y)) :+ (row02P a b c d :* z)
rotationYP a b c d x y z =
  ((row10P a b c d :* x) :+ (row11P a b c d :* y)) :+ (row12P a b c d :* z)
rotationZP a b c d x y z =
  ((row20P a b c d :* x) :+ (row21P a b c d :* y)) :+ (row22P a b c d :* z)

inner0P inner1P inner2P inner3P :
  ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
inner0P a b c d x y z = ((:- (b :* x)) :+ (:- (c :* y))) :+ (:- (d :* z))
inner1P a b c d x y z = ((a :* x) :+ (c :* z)) :+ (:- (d :* y))
inner2P a b c d x y z = ((a :* y) :+ (:- (b :* z))) :+ (d :* x)
inner3P a b c d x y z = ((a :* z) :+ (b :* y)) :+ (:- (c :* x))

adjointXExpandedP adjointYExpandedP adjointZExpandedP :
  ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
adjointXExpandedP a b c d x y z =
  (((inner0P a b c d x y z :* (:- b)) :+ (inner1P a b c d x y z :* a))
    :+ (inner2P a b c d x y z :* (:- d)))
    :+ (:- (inner3P a b c d x y z :* (:- c)))
adjointYExpandedP a b c d x y z =
  (((inner0P a b c d x y z :* (:- c)) :+ (:- (inner1P a b c d x y z :* (:- d))))
    :+ (inner2P a b c d x y z :* a))
    :+ (inner3P a b c d x y z :* (:- b))
adjointZExpandedP a b c d x y z =
  (((inner0P a b c d x y z :* (:- d)) :+ (inner1P a b c d x y z :* (:- c)))
    :+ (:- (inner2P a b c d x y z :* (:- b))))
    :+ (inner3P a b c d x y z :* a)

adjointXPolynomial : ∀ a b c d x y z →
  rotationX a b c d x y z ≡ adjointXExpandedR a b c d x y z
adjointXPolynomial =
  solveComputed 7
    (λ a b c d x y z →
      rotationXP a b c d x y z := adjointXExpandedP a b c d x y z)
    computed

adjointYPolynomial : ∀ a b c d x y z →
  rotationY a b c d x y z ≡ adjointYExpandedR a b c d x y z
adjointYPolynomial =
  solveComputed 7
    (λ a b c d x y z →
      rotationYP a b c d x y z := adjointYExpandedP a b c d x y z)
    computed

adjointZPolynomial : ∀ a b c d x y z →
  rotationZ a b c d x y z ≡ adjointZExpandedR a b c d x y z
adjointZPolynomial =
  solveComputed 7
    (λ a b c d x y z →
      rotationZP a b c d x y z := adjointZExpandedP a b c d x y z)
    computed
