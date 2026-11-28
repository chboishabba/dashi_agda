module DASHI.Moonshine.JInvariantThetaRawHadamardTransportExact where

-- SOURCE-WRITTEN, kernel pending. Actual maps between the original raw
-- signed square labels and odd-coordinate labels, using the existing
-- integral chart equivalence. No equality of cardinalities is assumed.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)
open import Data.Product.Base using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import DASHI.Moonshine.JInvariantThetaHadamardIntegralChartExact as H
import DASHI.Moonshine.JInvariantThetaIntegralParityExact as P
import DASHI.Moonshine.JInvariantThetaRawCoordinateGradeExact as R

pairOf : H.Quad → R.Pairs
pairOf (H.quad a b c d) = (a , b) , (c , d)

pairQuad : ∀ x → pairOf (R.quadOf x) ≡ x
pairQuad ((a , b) , (c , d)) = refl

quadPair : ∀ x → R.quadOf (pairOf x) ≡ x
quadPair (H.quad a b c d) = refl

decodeParams : H.Quad → R.Pairs
decodeParams (H.quad a b c d) =
  (P.oddParam a , P.oddParam b) , (P.oddParam c , P.oddParam d)

decodeRead : ∀ x → P.FourOdd x → R.oddQuadOf (decodeParams x) ≡ x
decodeRead (H.quad a b c d) (ha , hb , hc , hd) =
  H.quadCong (P.oddParamRead a ha) (P.oddParamRead b hb)
    (P.oddParamRead c hc) (P.oddParamRead d hd)

decodeEncode : ∀ x → decodeParams (R.oddQuadOf x) ≡ x
decodeEncode ((a , b) , (c , d))
  rewrite P.oddParamExact a | P.oddParamExact b
    | P.oddParamExact c | P.oddParamExact d = refl

fourOdd : ∀ x → P.FourOdd (R.oddQuadOf x)
fourOdd ((a , b) , (c , d)) = (a , refl) , (b , refl) , (c , refl) , (d , refl)

evenOddCoords : ∀ q → P.FourOdd (H.halfEven q)
evenOddCoords (H.quad j u v w) =
  (u , refl) , (v , refl) , (w , refl) ,
    ((+ 2) * j - u - v - w - (+ 2) , H.halfEvenFourth j u v w)

oddOddCoords : ∀ q → P.FourOdd (H.halfOdd q)
oddOddCoords (H.quad j u v w) =
  (u , refl) , (v , refl) , (w , refl) ,
    ((+ 2) * j - u - v - w - (+ 1) , H.halfOddFourth j u v w)

integerTotal : ∀ q → H.total (H.integerOdd q) ≡ (+ 2) * H.a q + (+ 1)
integerTotal (H.quad k b c d) = solve 4
  (λ k b c d → (((con (+ 2) :* k :+ con (+ 1) :- b) :- c) :- d) :+ b :+ c :+ d
    := con (+ 2) :* k :+ con (+ 1)) refl k b c d

evenTotal : ∀ q → H.total (H.halfEven q) ≡ (+ 4) * H.a q
evenTotal (H.quad j u v w) = solve 4
  (λ j u v w →
    (con (+ 2) :* u :+ con (+ 1)) :+ (con (+ 2) :* v :+ con (+ 1)) :+
    (con (+ 2) :* w :+ con (+ 1)) :+
    (con (+ 4) :* j :+ con (+ 0) :- (con (+ 2) :* u :+ con (+ 1))
      :- (con (+ 2) :* v :+ con (+ 1)) :- (con (+ 2) :* w :+ con (+ 1)))
    := con (+ 4) :* j) refl j u v w

oddTotal : ∀ q → H.total (H.halfOdd q) ≡ (+ 4) * H.a q + (+ 2)
oddTotal (H.quad j u v w) = solve 4
  (λ j u v w →
    (con (+ 2) :* u :+ con (+ 1)) :+ (con (+ 2) :* v :+ con (+ 1)) :+
    (con (+ 2) :* w :+ con (+ 1)) :+
    (con (+ 4) :* j :+ con (+ 2) :- (con (+ 2) :* u :+ con (+ 1))
      :- (con (+ 2) :* v :+ con (+ 1)) :- (con (+ 2) :* w :+ con (+ 1)))
    := con (+ 4) :* j :+ con (+ 2)) refl j u v w

chart : H.Quad → H.Quad
chart x = H.integerChart x (P.oddParam (H.total x))

chartRead : ∀ x → P.Odd (H.total x) → H.integerOdd (chart x) ≡ x
chartRead x h = H.integerChartRead x (P.oddParam (H.total x))
  (sym (P.oddParamRead (H.total x) h))

chartReopen : ∀ q → chart (H.integerOdd q) ≡ q
chartReopen (H.quad k b c d)
  rewrite integerTotal (H.quad k b c d) | P.oddParamExact k = refl

-- The two orientation sheets are disjoint on the actual total.
sheetDisjoint : ∀ q r → H.halfEven q ≡ H.halfOdd r → ⊥
sheetDisjoint q r h =
  P.evenNotOdd ((+ 2) * H.a q)
    (H.a q , refl)
    (H.a r , P.cancelScale 1 _ _
      (trans (solve 1 (λ x → con (+ 2) :* (con (+ 2) :* x) := con (+ 4) :* x)
          refl (H.a q))
        (trans (sym (evenTotal q))
          (trans (cong H.total h)
            (trans (oddTotal r)
              (solve 1 (λ x → con (+ 4) :* x :+ con (+ 2)
                := con (+ 2) :* (con (+ 2) :* x :+ con (+ 1))) refl (H.a r))))))))

evenInject : ∀ {q r} → H.halfEven q ≡ H.halfEven r → q ≡ r
evenInject {H.quad j u v w} {H.quad j' u' v' w'} h =
  H.quadCong
    (P.cancelScale 3 j j' (trans (sym (evenTotal (H.quad j u v w)))
      (trans (cong H.total h) (evenTotal (H.quad j' u' v' w')))))
    (P.oddWitnessUnique u u' (cong H.a h))
    (P.oddWitnessUnique v v' (cong H.b h))
    (P.oddWitnessUnique w w' (cong H.c h))

oddInject : ∀ {q r} → H.halfOdd q ≡ H.halfOdd r → q ≡ r
oddInject {H.quad j u v w} {H.quad j' u' v' w'} h =
  H.quadCong
    (P.cancelScale 3 j j'
      (trans (solve 1 (λ j → con (+ 4) :* j := con (+ 4) :* j :+ con (+ 2) :- con (+ 2)) refl j)
        (trans (cong (_- (+ 2)) (trans (sym (oddTotal (H.quad j u v w)))
          (trans (cong H.total h) (oddTotal (H.quad j' u' v' w')))))
          (solve 1 (λ j → con (+ 4) :* j :+ con (+ 2) :- con (+ 2) := con (+ 4) :* j) refl j'))))
    (P.oddWitnessUnique u u' (cong H.a h))
    (P.oddWitnessUnique v v' (cong H.b h))
    (P.oddWitnessUnique w w' (cong H.c h))

forward : Bool × R.Pairs → R.Pairs
forward (false , x) = decodeParams (H.halfEven (H.encode (chart (R.quadOf x))))
forward (true , x) = decodeParams (H.halfOdd (H.flipToOdd (H.encode (chart (R.quadOf x)))))

forwardEvenRead : ∀ x →
  R.oddQuadOf (forward (false , x)) ≡ H.halfEven (H.encode (chart (R.quadOf x)))
forwardEvenRead x = decodeRead _ (evenOddCoords _)

forwardOddRead : ∀ x →
  R.oddQuadOf (forward (true , x)) ≡ H.halfOdd (H.flipToOdd (H.encode (chart (R.quadOf x))))
forwardOddRead x = decodeRead _ (oddOddCoords _)

forwardNorm : ∀ e x → P.Odd (H.total (R.quadOf x)) →
  H.normSq (R.oddQuadOf (forward (e , x))) ≡ (+ 4) * H.normSq (R.quadOf x)
forwardNorm false x hx =
  trans (cong H.normSq (forwardEvenRead x))
    (trans (H.encodeNorm _) (cong (λ q → (+ 4) * H.normSq q) (chartRead _ hx)))
forwardNorm true x hx =
  trans (cong H.normSq (forwardOddRead x))
    (trans (H.flipGrade _) (trans (H.encodeNorm _)
      (cong (λ q → (+ 4) * H.normSq q) (chartRead _ hx))))

chartInjectOn : ∀ x y → P.Odd (H.total (R.quadOf x)) → P.Odd (H.total (R.quadOf y)) →
  chart (R.quadOf x) ≡ chart (R.quadOf y) → x ≡ y
chartInjectOn x y hx hy e =
  trans (sym (pairQuad x))
    (trans (cong pairOf (trans (sym (chartRead _ hx))
      (trans (cong H.integerOdd e) (chartRead _ hy)))) (pairQuad y))

forwardInjectOn : ∀ e f x y →
  P.Odd (H.total (R.quadOf x)) → P.Odd (H.total (R.quadOf y)) →
  forward (e , x) ≡ forward (f , y) → (e , x) ≡ (f , y)
forwardInjectOn false false x y hx hy h =
  cong (false ,_) (chartInjectOn x y hx hy
    (trans (sym (H.decodeEncode _))
      (trans (cong H.decode (evenInject (trans (sym (forwardEvenRead x))
        (trans (cong R.oddQuadOf h) (forwardEvenRead y))))) (H.decodeEncode _))))
forwardInjectOn true true x y hx hy h =
  cong (true ,_) (chartInjectOn x y hx hy
    (trans (sym (H.decodeEncode _))
      (trans (cong H.decode (trans (sym (H.flipDecode _))
        (trans (cong H.flipToEven (oddInject (trans (sym (forwardOddRead x))
          (trans (cong R.oddQuadOf h) (forwardOddRead y))))) (H.flipDecode _))))
        (H.decodeEncode _))))
forwardInjectOn false true x y hx hy h = ⊥-elim
  (sheetDisjoint _ _ (trans (sym (forwardEvenRead x)) (trans (cong R.oddQuadOf h) (forwardOddRead y))))
forwardInjectOn true false x y hx hy h = ⊥-elim
  (sheetDisjoint _ _ (trans (sym (forwardEvenRead y)) (trans (cong R.oddQuadOf (sym h)) (forwardOddRead x))))

-- Construct a preimage for EVERY odd-coordinate vector, not just
-- points within a finite diagnostic radius.
record Preimage (y : R.Pairs) : Set where
  constructor preimage
  field
    side : Bool
    source : R.Pairs
    sourceOdd : P.Odd (H.total (R.quadOf source))
    roundTrip : forward (side , source) ≡ y
open Preimage public

sourceOf : H.Quad → R.Pairs
sourceOf q = pairOf (H.integerOdd q)

sourceOddRead : ∀ q → P.Odd (H.total (R.quadOf (sourceOf q)))
sourceOddRead q = H.a q , trans (cong H.total (quadPair (H.integerOdd q))) (integerTotal q)

sourceChart : ∀ q → chart (R.quadOf (sourceOf q)) ≡ q
sourceChart q = trans (cong chart (quadPair (H.integerOdd q))) (chartReopen q)

preimageAt : ∀ y → Preimage y
preimageAt y with P.halfChart (R.oddQuadOf y) (fourOdd y)
... | P.sheet0 q h =
  preimage false (sourceOf (H.decode q)) (sourceOddRead (H.decode q))
    (trans (cong decodeParams (cong H.halfEven
      (trans (cong H.encode (sourceChart (H.decode q))) (H.encodeDecode q))))
      (trans (cong decodeParams h) (decodeEncode y)))
... | P.sheet2 q h =
  preimage true (sourceOf (H.decode (H.flipToEven q))) (sourceOddRead (H.decode (H.flipToEven q)))
    (trans (cong decodeParams (cong H.halfOdd
      (trans (cong H.flipToOdd
        (trans (cong H.encode (sourceChart (H.decode (H.flipToEven q)))) (H.encodeDecode (H.flipToEven q))))
        (H.flipEncode q))))
      (trans (cong decodeParams h) (decodeEncode y)))
