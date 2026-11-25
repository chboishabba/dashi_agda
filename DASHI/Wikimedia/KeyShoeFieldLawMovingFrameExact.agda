module DASHI.Wikimedia.KeyShoeFieldLawMovingFrameExact where

-- H19e. Concrete finite decision certificates on original H19d Point.
-- Source-written; Agda kernel has not been run. No postulates.
open import DASHI.Core.Prelude
open import DASHI.Core.IndexedWeaveHyperfabricExact using (IndexedWeave)
import DASHI.Foundations.SSPTritCarrier as S
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as C
import DASHI.Wikimedia.KeyShoeIndexedTrigramWeaveExact as K
open import DASHI.Wikimedia.KeyShoeNativeFieldIncidenceExact

andB : Bool → Bool → Bool
andB false b = false
andB true b = b

andLeft : ∀ {a b} → andB a b ≡ true → a ≡ true
andLeft {false} ()
andLeft {true} p = refl

andRight : ∀ {a b} → andB a b ≡ true → b ≡ true
andRight {false} ()
andRight {true} p = p

eqT : S.SSPTrit → S.SSPTrit → Bool
eqT S.sspZero S.sspZero = true
eqT S.sspZero S.sspPosOne = false
eqT S.sspZero S.sspNegOne = false
eqT S.sspPosOne S.sspZero = false
eqT S.sspPosOne S.sspPosOne = true
eqT S.sspPosOne S.sspNegOne = false
eqT S.sspNegOne S.sspZero = false
eqT S.sspNegOne S.sspPosOne = false
eqT S.sspNegOne S.sspNegOne = true

eqTSound : (a b : S.SSPTrit) → eqT a b ≡ true → a ≡ b
eqTSound S.sspZero S.sspZero p = refl
eqTSound S.sspZero S.sspPosOne ()
eqTSound S.sspZero S.sspNegOne ()
eqTSound S.sspPosOne S.sspZero ()
eqTSound S.sspPosOne S.sspPosOne p = refl
eqTSound S.sspPosOne S.sspNegOne ()
eqTSound S.sspNegOne S.sspZero ()
eqTSound S.sspNegOne S.sspPosOne ()
eqTSound S.sspNegOne S.sspNegOne p = refl

eqTRefl : (a : S.SSPTrit) → eqT a a ≡ true
eqTRefl S.sspZero = refl
eqTRefl S.sspPosOne = refl
eqTRefl S.sspNegOne = refl

eqP : Point → Point → Bool
eqP (C.ternary27Point a b c) (C.ternary27Point d e f) =
  andB (eqT a d) (andB (eqT b e) (eqT c f))

pointCong : ∀ {a b c d e f : S.SSPTrit} →
  a ≡ d → b ≡ e → c ≡ f → C.ternary27Point a b c ≡ C.ternary27Point d e f
pointCong refl refl refl = refl

eqPSound : (a b : Point) → eqP a b ≡ true → a ≡ b
eqPSound (C.ternary27Point a b c) (C.ternary27Point d e f) p =
  pointCong (eqTSound a d (andLeft p))
    (eqTSound b e (andLeft (andRight p))) (eqTSound c f (andRight (andRight p)))

eqPRefl : (a : Point) → eqP a a ≡ true
eqPRefl (C.ternary27Point a b c)
  rewrite eqTRefl a | eqTRefl b | eqTRefl c = refl

eqPComplete : (a b : Point) → a ≡ b → eqP a b ≡ true
eqPComplete a .a refl = eqPRefl a

points : List Point
points = (C.ternary27Point S.sspZero S.sspZero S.sspZero) ∷
  (C.ternary27Point S.sspPosOne S.sspZero S.sspZero) ∷
  (C.ternary27Point S.sspNegOne S.sspZero S.sspZero) ∷
  (C.ternary27Point S.sspZero S.sspPosOne S.sspZero) ∷
  (C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero) ∷
  (C.ternary27Point S.sspNegOne S.sspPosOne S.sspZero) ∷
  (C.ternary27Point S.sspZero S.sspNegOne S.sspZero) ∷
  (C.ternary27Point S.sspPosOne S.sspNegOne S.sspZero) ∷
  (C.ternary27Point S.sspNegOne S.sspNegOne S.sspZero) ∷
  (C.ternary27Point S.sspZero S.sspZero S.sspPosOne) ∷
  (C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne) ∷
  (C.ternary27Point S.sspNegOne S.sspZero S.sspPosOne) ∷
  (C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne) ∷
  (C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne) ∷
  (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne) ∷
  (C.ternary27Point S.sspZero S.sspNegOne S.sspPosOne) ∷
  (C.ternary27Point S.sspPosOne S.sspNegOne S.sspPosOne) ∷
  (C.ternary27Point S.sspNegOne S.sspNegOne S.sspPosOne) ∷
  (C.ternary27Point S.sspZero S.sspZero S.sspNegOne) ∷
  (C.ternary27Point S.sspPosOne S.sspZero S.sspNegOne) ∷
  (C.ternary27Point S.sspNegOne S.sspZero S.sspNegOne) ∷
  (C.ternary27Point S.sspZero S.sspPosOne S.sspNegOne) ∷
  (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne) ∷
  (C.ternary27Point S.sspNegOne S.sspPosOne S.sspNegOne) ∷
  (C.ternary27Point S.sspZero S.sspNegOne S.sspNegOne) ∷
  (C.ternary27Point S.sspPosOne S.sspNegOne S.sspNegOne) ∷
  (C.ternary27Point S.sspNegOne S.sspNegOne S.sspNegOne) ∷ []

data Member (x : Point) : List Point → Set where
  here : ∀ {xs} → Member x (x ∷ xs)
  there : ∀ {y xs} → Member x xs → Member x (y ∷ xs)

pointMember : (x : Point) → Member x points
pointMember (C.ternary27Point S.sspZero S.sspZero S.sspZero) = here
pointMember (C.ternary27Point S.sspPosOne S.sspZero S.sspZero) = there (here)
pointMember (C.ternary27Point S.sspNegOne S.sspZero S.sspZero) = there (there (here))
pointMember (C.ternary27Point S.sspZero S.sspPosOne S.sspZero) = there (there (there (here)))
pointMember (C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero) = there (there (there (there (here))))
pointMember (C.ternary27Point S.sspNegOne S.sspPosOne S.sspZero) = there (there (there (there (there (here)))))
pointMember (C.ternary27Point S.sspZero S.sspNegOne S.sspZero) = there (there (there (there (there (there (here))))))
pointMember (C.ternary27Point S.sspPosOne S.sspNegOne S.sspZero) = there (there (there (there (there (there (there (here)))))))
pointMember (C.ternary27Point S.sspNegOne S.sspNegOne S.sspZero) = there (there (there (there (there (there (there (there (here))))))))
pointMember (C.ternary27Point S.sspZero S.sspZero S.sspPosOne) = there (there (there (there (there (there (there (there (there (here)))))))))
pointMember (C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne) = there (there (there (there (there (there (there (there (there (there (here))))))))))
pointMember (C.ternary27Point S.sspNegOne S.sspZero S.sspPosOne) = there (there (there (there (there (there (there (there (there (there (there (here)))))))))))
pointMember (C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne) = there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))
pointMember (C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))
pointMember (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))
pointMember (C.ternary27Point S.sspZero S.sspNegOne S.sspPosOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))))
pointMember (C.ternary27Point S.sspPosOne S.sspNegOne S.sspPosOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))))
pointMember (C.ternary27Point S.sspNegOne S.sspNegOne S.sspPosOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))))))
pointMember (C.ternary27Point S.sspZero S.sspZero S.sspNegOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))))))
pointMember (C.ternary27Point S.sspPosOne S.sspZero S.sspNegOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))))))))
pointMember (C.ternary27Point S.sspNegOne S.sspZero S.sspNegOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))))))))
pointMember (C.ternary27Point S.sspZero S.sspPosOne S.sspNegOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))))))))))
pointMember (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))))))))))
pointMember (C.ternary27Point S.sspNegOne S.sspPosOne S.sspNegOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))))))))))))
pointMember (C.ternary27Point S.sspZero S.sspNegOne S.sspNegOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))))))))))))
pointMember (C.ternary27Point S.sspPosOne S.sspNegOne S.sspNegOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))))))))))))))
pointMember (C.ternary27Point S.sspNegOne S.sspNegOne S.sspNegOne) = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))))))))))))))

allList : (Point → Bool) → List Point → Bool
allList f [] = true
allList f (x ∷ xs) = andB (f x) (allList f xs)

allAt : (f : Point → Bool) (xs : List Point) (x : Point) →
  Member x xs → allList f xs ≡ true → f x ≡ true
allAt f (x ∷ xs) .x here p = andLeft p
allAt f (y ∷ xs) x (there m) p = allAt f xs x m (andRight p)

allP : (Point → Bool) → Bool
allP f = allList f points

atP : (f : Point → Bool) → allP f ≡ true → (x : Point) → f x ≡ true
atP f p x = allAt f points x (pointMember x) p

all2 : (Point → Point → Bool) → Bool
all2 f = allP (λ x → allP (f x))

at2 : (f : Point → Point → Bool) → all2 f ≡ true →
  (x y : Point) → f x y ≡ true
at2 f p x y = atP (f x) (atP (λ a → allP (f a)) p x) y

all3 : (Point → Point → Point → Bool) → Bool
all3 f = allP (λ x → all2 (f x))

at3 : (f : Point → Point → Point → Bool) → all3 f ≡ true →
  (x y z : Point) → f x y z ≡ true
at3 f p x y z = at2 (f x) (atP (λ a → all2 (f a)) p x) y z

law2 : (l r : Point → Point → Point) →
  all2 (λ a b → eqP (l a b) (r a b)) ≡ true →
  (a b : Point) → l a b ≡ r a b
law2 l r p a b = eqPSound (l a b) (r a b)
  (at2 (λ x y → eqP (l x y) (r x y)) p a b)

law3 : (l r : Point → Point → Point → Point) →
  all3 (λ a b c → eqP (l a b c) (r a b c)) ≡ true →
  (a b c : Point) → l a b c ≡ r a b c
law3 l r p a b c = eqPSound (l a b c) (r a b c)
  (at3 (λ x y z → eqP (l x y z) (r x y z)) p a b c)

-- Closed finite certificates; not assumed as axioms.
addAssoc : (a b c : Point) → add (add a b) c ≡ add a (add b c)
addAssoc = law3 (λ a b c → add (add a b) c) (λ a b c → add a (add b c)) refl

mulAssoc : (a b c : Point) → mul (mul a b) c ≡ mul a (mul b c)
mulAssoc = law3 (λ a b c → mul (mul a b) c) (λ a b c → mul a (mul b c)) refl

distribLeft : (a b c : Point) → mul a (add b c) ≡ add (mul a b) (mul a c)
distribLeft = law3 (λ a b c → mul a (add b c)) (λ a b c → add (mul a b) (mul a c)) refl

addComm : (a b : Point) → add a b ≡ add b a
addComm = law2 add (λ a b → add b a) refl

mulComm : (a b : Point) → mul a b ≡ mul b a
mulComm = law2 mul (λ a b → mul b a) refl

addZero : (a : Point) → add a C.origin ≡ a
addZero a = eqPSound (add a C.origin) a (atP (λ x → eqP (add x C.origin) x) refl a)

addNegative : (a : Point) → add a (negative a) ≡ C.origin
addNegative a = eqPSound (add a (negative a)) C.origin
  (atP (λ x → eqP (add x (negative x)) C.origin) refl a)

mulOne : (a : Point) → mul a one ≡ a
mulOne a = eqPSound (mul a one) a (atP (λ x → eqP (mul x one) x) refl a)

mulZero : (a : Point) → mul a C.origin ≡ C.origin
mulZero a = eqPSound (mul a C.origin) C.origin
  (atP (λ x → eqP (mul x C.origin) C.origin) refl a)

subAdd : (a b : Point) → sub (add a b) a ≡ b
subAdd = law2 (λ a b → sub (add a b) a) (λ a b → b) refl

addSub : (a b : Point) → add a (sub b a) ≡ b
addSub = law2 (λ a b → add a (sub b a)) (λ a b → b) refl

Nonzero : Point → Set
Nonzero a = a ≡ C.origin → ⊥

guardNZ : Bool → Bool → Bool
guardNZ true b = true
guardNZ false b = b

guardSound : (a b : Bool) → (a ≡ true → ⊥) → guardNZ a b ≡ true → b ≡ true
guardSound true b n p = ⊥-elim (n refl)
guardSound false b n p = p

nzCert : (f : Point → Bool) →
  allP (λ a → guardNZ (eqP a C.origin) (f a)) ≡ true →
  (a : Point) → Nonzero a → f a ≡ true
nzCert f p a nz = guardSound (eqP a C.origin) (f a)
  (λ e → nz (eqPSound a C.origin e))
  (atP (λ x → guardNZ (eqP x C.origin) (f x)) p a)

slotInverseMultiplicative : (a : Point) → Nonzero a → mul a (inverse a) ≡ one
slotInverseMultiplicative a nz = eqPSound (mul a (inverse a)) one
  (nzCert (λ x → eqP (mul x (inverse x)) one) refl a nz)

-- Frames use a nonzero scale with a witness, not a default division by zero.
record Frame : Set where
  constructor frame
  field
    anchor scale : Point
    scaleNonzero : Nonzero scale

frameEncode frameDecode : Frame → Point → Point
frameEncode (frame o u nz) x = add o (mul u x)
frameDecode (frame o u nz) x = mul (inverse u) (sub x o)

scaleDecodeEncode : (u x : Point) → Nonzero u → mul (inverse u) (mul u x) ≡ x
scaleDecodeEncode u x nz =
  trans (sym (mulAssoc (inverse u) u x))
    (trans (cong (λ v → mul v x) (trans (mulComm (inverse u) u) (slotInverseMultiplicative u nz)))
      (trans (mulComm one x) (mulOne x)))

scaleEncodeDecode : (u x : Point) → Nonzero u → mul u (mul (inverse u) x) ≡ x
scaleEncodeDecode u x nz =
  trans (sym (mulAssoc u (inverse u) x))
    (trans (cong (λ v → mul v x) (slotInverseMultiplicative u nz))
      (trans (mulComm one x) (mulOne x)))

frameDecodeEncode : (f : Frame) (x : Point) → frameDecode f (frameEncode f x) ≡ x
frameDecodeEncode (frame o u nz) x
  rewrite subAdd o (mul u x) = scaleDecodeEncode u x nz

frameEncodeDecode : (f : Frame) (x : Point) → frameEncode f (frameDecode f x) ≡ x
frameEncodeDecode (frame o u nz) x
  rewrite scaleEncodeDecode u (sub x o) nz = addSub o x

frameWeave : IndexedWeave Frame (λ _ → Point)
frameWeave = K.chartWeave frameEncode frameDecode frameDecodeEncode frameEncodeDecode

frameTransport : Frame → Frame → Point → Point
frameTransport f g x = frameEncode g (frameDecode f x)

frameCovariance : (f g : Frame) (x : Point) →
  frameDecode g (frameTransport f g x) ≡ frameDecode f x
frameCovariance f g x = frameDecodeEncode g (frameDecode f x)

anchoredInverse : Frame → Point → Point
anchoredInverse f x = frameEncode f (inverse (frameDecode f x))

anchoredInverseCovariance : (f g : Frame) (x : Point) →
  frameTransport f g (anchoredInverse f x) ≡ anchoredInverse g (frameTransport f g x)
anchoredInverseCovariance f g x
  rewrite frameDecodeEncode f (inverse (frameDecode f x))
        | frameCovariance f g x = refl

-- Both normal and point must be nonzero for proper projective incidence.
ProperLine : Point → Point → Set
ProperLine n x = Nonzero n × LineAt n x

ProperConic : Point → Point → Set
ProperConic n x = Nonzero n × ConicAt n x

frameLine : Frame → Point → Point → Set
frameLine f n x = ProperLine n (frameDecode f x)

frameConic : Frame → Point → Point → Set
frameConic f n x = ProperConic n (frameDecode f x)

frameLineForward : (f g : Frame) (n x : Point) →
  frameLine f n x → frameLine g n (frameTransport f g x)
frameLineForward f g n x = subst (ProperLine n) (sym (frameCovariance f g x))

frameLineBackward : (f g : Frame) (n x : Point) →
  frameLine g n (frameTransport f g x) → frameLine f n x
frameLineBackward f g n x = subst (ProperLine n) (frameCovariance f g x)

frameConicForward : (f g : Frame) (n x : Point) →
  frameConic f n x → frameConic g n (frameTransport f g x)
frameConicForward f g n x = subst (ProperConic n) (sym (frameCovariance f g x))

frameConicBackward : (f g : Frame) (n x : Point) →
  frameConic g n (frameTransport f g x) → frameConic f n x
frameConicBackward f g n x = subst (ProperConic n) (frameCovariance f g x)

dualNormalCovariance : (n x : Point) → dot (dualNative n) (toNative x) ≡ dot n x
dualNormalCovariance n x = eqTSound (dot (dualNative n) (toNative x)) (dot n x)
  (at2 (λ a b → eqT (dot (dualNative a) (toNative b)) (dot a b)) refl n x)

cube : Point → Point
cube x = mul x (mul x x)

quadratic : Point → Point
quadratic x = mul (cube x) (cube (cube x))

eqB : Bool → Bool → Bool
eqB false false = true
eqB false true = false
eqB true false = false
eqB true true = true

eqBSound : (a b : Bool) → eqB a b ≡ true → a ≡ b
eqBSound false false p = refl
eqBSound false true ()
eqBSound true false ()
eqBSound true true p = refl

quadraticZeroTest : (n x : Point) →
  eqT (dot n (inverse x)) S.sspZero ≡ eqT (dot n (quadratic x)) S.sspZero
quadraticZeroTest n x = eqBSound (eqT (dot n (inverse x)) S.sspZero)
  (eqT (dot n (quadratic x)) S.sspZero)
  (at2 (λ a b → eqB (eqT (dot a (inverse b)) S.sspZero)
                     (eqT (dot a (quadratic b)) S.sspZero)) refl n x)

eqTComplete : (a b : S.SSPTrit) → a ≡ b → eqT a b ≡ true
eqTComplete a .a refl = eqTRefl a

quadraticForward : (n x : Point) → dot n (inverse x) ≡ S.sspZero → dot n (quadratic x) ≡ S.sspZero
quadraticForward n x h = eqTSound (dot n (quadratic x)) S.sspZero
  (trans (sym (quadraticZeroTest n x)) (eqTComplete (dot n (inverse x)) S.sspZero h))

quadraticBackward : (n x : Point) → dot n (quadratic x) ≡ S.sspZero → dot n (inverse x) ≡ S.sspZero
quadraticBackward n x h = eqTSound (dot n (inverse x)) S.sspZero
  (trans (quadraticZeroTest n x) (eqTComplete (dot n (quadratic x)) S.sspZero h))

-- Both sheets have mutually inverse completion functions, even on diagonal.
-- Distinctness is separately required for RatioRelation membership.
middleAfterRight : (s : RatioSheet) (a b : Point) →
  completeMiddle s a (completeRight s a b) ≡ b
middleAfterRight direct = law2 (λ a b → completeMiddle direct a (completeRight direct a b)) (λ a b → b) refl
middleAfterRight reflected = law2 (λ a b → completeMiddle reflected a (completeRight reflected a b)) (λ a b → b) refl

leftAfterRight : (s : RatioSheet) (a b : Point) →
  completeLeft s b (completeRight s a b) ≡ a
leftAfterRight direct = law2 (λ a b → completeLeft direct b (completeRight direct a b)) (λ a b → a) refl
leftAfterRight reflected = law2 (λ a b → completeLeft reflected b (completeRight reflected a b)) (λ a b → a) refl

rightAfterMiddle : (s : RatioSheet) (a c : Point) →
  completeRight s a (completeMiddle s a c) ≡ c
rightAfterMiddle direct = law2 (λ a c → completeRight direct a (completeMiddle direct a c)) (λ a c → c) refl
rightAfterMiddle reflected = law2 (λ a c → completeRight reflected a (completeMiddle reflected a c)) (λ a c → c) refl

rightAfterLeft : (s : RatioSheet) (b c : Point) →
  completeRight s (completeLeft s b c) b ≡ c
rightAfterLeft direct = law2 (λ b c → completeRight direct (completeLeft direct b c) b) (λ b c → c) refl
rightAfterLeft reflected = law2 (λ b c → completeRight reflected (completeLeft reflected b c) b) (λ b c → c) refl
