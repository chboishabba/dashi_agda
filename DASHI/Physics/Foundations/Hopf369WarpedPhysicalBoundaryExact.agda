module DASHI.Physics.Foundations.Hopf369WarpedPhysicalBoundaryExact where

-- BR34: actual BR14 normalized tensor -> BR33 D/E boundary rows.
-- The finite coefficient source is native; no continuum estimate is assumed.
-- Standard warped connection/Gauss/Codazzi/Israel identities: prior mathematics.
-- DASHI: signed two-chart allocation and same-source optical attachment.
open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C

data Wall : Set where
  t x y z : Wall

data Axis : Set where
  wall : Wall → Axis
  normal : Axis

data Allocation : Set where
  D E : Allocation

sameWall : Wall → Wall → Bool
sameWall t t = true
sameWall x x = true
sameWall y y = true
sameWall z z = true
sameWall _ _ = false

-- RealField's inverse operation alone has no inverse law. Require the
-- exact nonzero rational denominator laws, rather than assume them.
module At {r : Level} (F : C.RealField r)
  (halfLaw : C.multiply F
    (C.inverse F (C.add F (C.one F) (C.one F)))
    (C.add F (C.one F) (C.one F)) ≡ C.one F)
  (thirdLaw : C.multiply F
    (C.inverse F (C.add F (C.add F (C.one F) (C.one F)) (C.one F)))
    (C.add F (C.add F (C.one F) (C.one F)) (C.one F)) ≡ C.one F) where
  S : Set r
  S = C.Complex F

  infixl 6 _+_ _-_
  infixl 7 _*_

  _+_ _-_ _*_ : S → S → S
  _+_ = C.complexAdd
  _-_ = C.complexSubtract
  _*_ = C.complexMultiply

  neg : S → S
  neg = C.complexNegate

  O U two three four five half quarter third : S
  O = C.complexZero F
  U = C.complexOne F
  two = U + U
  three = two + U
  four = two + two
  five = four + U
  half = C.realEmbed F (C.inverse F (C.add F (C.one F) (C.one F)))
  quarter = half * half
  third = C.realEmbed F (C.inverse F (C.add F (C.add F (C.one F) (C.one F)) (C.one F)))

  sign : Wall → S
  sign t = neg U
  sign x = U
  sign y = U
  sign z = U

  eta : Wall → Wall → S
  eta a b with sameWall a b
  ... | true = sign a
  ... | false = O

  delta : Axis → Axis → S
  delta normal normal = U
  delta (wall a) (wall b) with sameWall a b
  ... | true = U
  ... | false = O
  delta normal (wall _) = O
  delta (wall _) normal = O

  metric : Axis → Axis → S
  metric normal normal = U
  metric (wall a) (wall b) = eta a b
  metric normal (wall _) = O
  metric (wall _) normal = O

  Vec : Set r
  Vec = Wall → S

  Cov : Set r
  Cov = Axis → S

  sum4 : (Wall → S) → S
  sum4 f = f t + f x + f y + f z

  trace4 : (Wall → Wall → S) → S
  trace4 h = sum4 (λ a → sign a * h a a)

  dot : Vec → Vec → S
  dot a b = sum4 (λ i → sign i * a i * b i)

  -- Exactly fifteen independent symmetric coordinates, no lost trace channel.
  record Tensor : Set r where
    constructor tensor
    field
      h00 h01 h02 h03 h04 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : S
  open Tensor public

  get : Tensor → Axis → Axis → S
  get p (wall t) (wall t) = h00 p
  get p (wall t) (wall x) = h01 p
  get p (wall t) (wall y) = h02 p
  get p (wall t) (wall z) = h03 p
  get p (wall t) normal = h04 p
  get p (wall x) (wall t) = h01 p
  get p (wall x) (wall x) = h11 p
  get p (wall x) (wall y) = h12 p
  get p (wall x) (wall z) = h13 p
  get p (wall x) normal = h14 p
  get p (wall y) (wall t) = h02 p
  get p (wall y) (wall x) = h12 p
  get p (wall y) (wall y) = h22 p
  get p (wall y) (wall z) = h23 p
  get p (wall y) normal = h24 p
  get p (wall z) (wall t) = h03 p
  get p (wall z) (wall x) = h13 p
  get p (wall z) (wall y) = h23 p
  get p (wall z) (wall z) = h33 p
  get p (wall z) normal = h34 p
  get p normal (wall t) = h04 p
  get p normal (wall x) = h14 p
  get p normal (wall y) = h24 p
  get p normal (wall z) = h34 p
  get p normal normal = h44 p

  tab : (Axis → Axis → S) → Tensor
  tab f = tensor
    (f (wall t) (wall t)) (f (wall t) (wall x))
    (f (wall t) (wall y)) (f (wall t) (wall z)) (f (wall t) normal)
    (f (wall x) (wall x)) (f (wall x) (wall y))
    (f (wall x) (wall z)) (f (wall x) normal)
    (f (wall y) (wall y)) (f (wall y) (wall z)) (f (wall y) normal)
    (f (wall z) (wall z)) (f (wall z) normal) (f normal normal)

  tabGet : (p : Tensor) → tab (get p) ≡ p
  tabGet (tensor a b c d e f g h i j k l m n o) = refl

  symmetric : (p : Tensor) (a b : Axis) → get p a b ≡ get p b a
  symmetric p normal normal = refl
  symmetric p normal (wall t) = refl
  symmetric p normal (wall x) = refl
  symmetric p normal (wall y) = refl
  symmetric p normal (wall z) = refl
  symmetric p (wall t) normal = refl
  symmetric p (wall x) normal = refl
  symmetric p (wall y) normal = refl
  symmetric p (wall z) normal = refl
  symmetric p (wall t) (wall t) = refl
  symmetric p (wall t) (wall x) = refl
  symmetric p (wall t) (wall y) = refl
  symmetric p (wall t) (wall z) = refl
  symmetric p (wall x) (wall t) = refl
  symmetric p (wall x) (wall x) = refl
  symmetric p (wall x) (wall y) = refl
  symmetric p (wall x) (wall z) = refl
  symmetric p (wall y) (wall t) = refl
  symmetric p (wall y) (wall x) = refl
  symmetric p (wall y) (wall y) = refl
  symmetric p (wall y) (wall z) = refl
  symmetric p (wall z) (wall t) = refl
  symmetric p (wall z) (wall x) = refl
  symmetric p (wall z) (wall y) = refl
  symmetric p (wall z) (wall z) = refl

  H : Tensor → Wall → Wall → S
  H p a b = get p (wall a) (wall b)

  beta : Tensor → Vec
  beta p a = get p (wall a) normal

  scale : Tensor → S
  scale p = half * h44 p

  tr : Tensor → S
  tr p = trace4 (H p)

  addT subT : Tensor → Tensor → Tensor
  addT a b = tab (λ i j → get a i j + get b i j)
  subT a b = tab (λ i j → get a i j - get b i j)

  mulT : S → Tensor → Tensor
  mulT a b = tab (λ i j → a * get b i j)

  sumT : (Wall → Tensor) → Tensor
  sumT f = tab (λ i j → sum4 (λ a → get (f a) i j))

  ins : Axis → Cov → Tensor
  ins a v = tab (λ i j → delta a i * v j + v i * delta a j)

  P : Tensor → Cov
  P p (wall a) = neg (two * beta p a)
  P p normal = tr p - four * h44 p

  L : Wall → Cov → Cov
  L a v normal = neg (v (wall a))
  L a v (wall b) with sameWall a b
  ... | true = sign a * v normal
  ... | false = O

  Lt : Wall → Tensor → Tensor
  Lt a p = tab (λ i j → L a (λ k → get p k j) i + L a (λ k → get p i k) j)

  R : Tensor → Tensor
  R p = addT (mulT three p) (ins normal (P p))

  J : Wall → Tensor → Tensor
  J a p = addT (mulT (two * sign a) (Lt a p)) (ins (wall a) (P p))

  W : Tensor → Tensor
  W p = sumT (λ a → addT (mulT (sign a) (Lt a (Lt a p))) (ins (wall a) (L a (P p))))

  C0 : Tensor → Tensor
  C0 p = tab (λ i j → two * (get p i j - metric i j * (tr p + h44 p)))

  tangCount : Axis → S
  tangCount normal = O
  tangCount (wall _) = U

  baseA : Wall → Tensor → Cov
  baseA a p (wall b) = (four * two * third) * H p b a - (two * third) * eta b a * tr p
  baseA a p normal = two * beta p a

  Vbase : Tensor → Tensor
  Vbase p = addT
    (tab (λ i j → (tangCount i + tangCount j) * get p i j))
    (sumT (λ a → ins (wall a) (baseA a p)))

  Vb Vh : Tensor → Tensor
  Vb p = subT (subT (addT (W p) (C0 p)) (mulT half (R p))) (mulT quarter (R (R p)))
  Vh p = addT (subT (subT (subT (R p) (mulT three p)) (W p)) (Vbase p))
                 (mulT quarter (R (R p)))

  -- BR15 spectral map; R eigenvalues -5, 1, 3, trace mixing retained.
  -- Call with b^(-5/2), b^(1/2), b^(3/2), respectively.
  spectral : S → S → S → Tensor → Tensor
  spectral a b c p = tab entry
    where
    entry : Axis → Axis → S
    entry (wall i) (wall j) = c * H p i j
    entry (wall i) normal = b * beta p i
    entry normal (wall i) = b * beta p i
    entry normal normal =
      a * (h44 p - quarter * tr p) + c * quarter * tr p

  -- BR15 actual matrix potential on the optical normal interval.
  -- E and Ei are the same spectral map with mutually reciprocal
  -- factors supplied by the positive warp profile, not independent matrices.
  metricPotential : S → S → S → Vec → S → S → S → S → S → S → Tensor → Tensor
  metricPotential b bk h2 q a e c ai ei ci u =
    spectral a e c (addT
      (mulT bk (sumT (λ i → mulT (q i) (J i p))))
      (addT (mulT (b * b) (Vb p)) (mulT h2 (Vh p))))
    where
    p : Tensor
    p = spectral ai ei ci u

  -- Actual BS4/5 coupled covector potential for orthonormal components.
  -- u=b^(3/2) C; proper normal to optical coordinate and Ric=-4.
  -- Sum eta L²=diag(-1,-1,-1,-1,-4); retain every component.
  gaugePotential : S → S → S → Vec → Cov → Cov
  gaugePotential b bk h2 q u i =
    two * bk * sum4 (λ a → sign a * q a * L a u i)
    + (bk * bk * (neg (diagS i) - three * three * quarter)
       - h2 * tangCount i - (four + three * half) * b * b) * u i
    where
    diagS : Axis → S
    diagS (wall _) = U
    diagS normal = four

  -- At b=1, u=p, p_x=u_x-k R p/2. These are not independent jets.
  opticalDerivative : S → Tensor → Tensor → Tensor
  opticalDerivative k p ux = subT ux (mulT (k * half) (R p))

  -- Actual metric boundary coefficients in BR14 harmonic Y reference chart.
  -- h=b² eta; lambda=b⁴; shift lower coefficient has exponent 3.
  -- No derivative-dependent gauge source; fixed reference source variation zero.
  extrinsic : S → Vec → Tensor → Tensor → Wall → Wall → S
  extrinsic k q p px a b =
    k * H p a b + half * (H px a b - q a * beta p b - beta p a * q b)
    - k * scale p * eta a b

  tau : S → Vec → Tensor → Tensor → S
  tau k q p px = half * tr px - dot q (beta p) - four * k * scale p

  gaugeTang : S → Vec → Tensor → Tensor → Vec
  gaugeTang k q p px a =
    sum4 (λ b → H p a b * sign b * q b) - half * q a * tr p
    - q a * scale p + beta px a + three * k * beta p a

  gaugeNorm : Vec → Tensor → Tensor → S
  gaugeNorm q p px = neg (half * tr px) + dot q (beta p) + scale px

  pack10 : (Wall → Wall → S) → List S
  pack10 f = f t t ∷ f t x ∷ f t y ∷ f t z ∷ f x x ∷ f x y ∷ f x z ∷ f y y ∷ f y z ∷ f z z ∷ []

  pack4 : Vec → List S
  pack4 f = f t ∷ f x ∷ f y ∷ f z ∷ []

  _++_ : List S → List S → List S
  [] ++ b = b
  (a ∷ as) ++ b = a ∷ (as ++ b)

  meanForce : S → Vec → Tensor → Tensor → Tensor → Tensor → S
  meanForce j q p px m mx = tau (half * j) q p px + tau (neg (half * j)) q m mx

  israel : S → Vec → Tensor → Tensor → Tensor → Tensor → Wall → Wall → S
  israel j q p px m mx a b =
    two * (extrinsic (half * j) q p px a b - extrinsic (neg (half * j)) q m mx a b)
    - j * (H p a b + H m a b)

  tangentJump : S → Vec → Tensor → Tensor → Tensor → Tensor → Vec
  tangentJump j q p px m mx a =
    gaugeTang (half * j) q p px a - gaugeTang (neg (half * j)) q m mx a

  -- Full thirty-row map, including the original value continuity rows.
  -- All source/normal-scale/mean-trace channels retained.
  metricPrefix : S → Vec → Tensor → Tensor → Tensor → Tensor → List S
  metricPrefix j q p px m mx =
    pack10 (λ a b → H p a b - H m a b) ++
    (pack4 (λ a → beta p a - beta m a) ++ pack10 (israel j q p px m mx))

  metricSuffix : Allocation → S → Vec → Tensor → Tensor → Tensor → Tensor → List S
  metricSuffix D j q p px m mx =
    pack4 (tangentJump j q p px m mx) ++
    (gaugeNorm q p px ∷ meanForce j q p px m mx ∷ [])
  metricSuffix E j q p px m mx =
    tangentJump j q p px m mx x ∷ tangentJump j q p px m mx y ∷
    tangentJump j q p px m mx z ∷ gaugeNorm q p px ∷ gaugeNorm q m mx ∷
    meanForce j q p px m mx ∷ []

  metricRows : Allocation → S → Vec → Tensor → Tensor → Tensor → Tensor → List S
  metricRows a j q p px m mx =
    metricPrefix j q p px m mx ++ metricSuffix a j q p px m mx

  attachMetric : Allocation → S → Vec → Tensor → Tensor → Tensor → Tensor → List S
  attachMetric a j q p ux m vx =
    metricRows a j q p (opticalDerivative (half * j) p ux)
      m (opticalDerivative (neg (half * j)) m vx)

  -- Covector optical equation: u=b^(3/2) C_frame; all five components.
  covOpticalDerivative : S → Cov → Cov → Cov
  covOpticalDerivative k p ux a = ux a - three * half * k * p a

  -- At arbitrary mean K the Codazzi term contains 2 M eta [C].
  -- At the AK reference M=0. Parallel derivative differs from coordinate
  -- derivative by k C on tangent components; do not double count the jump.
  gaugeCodazzi : S → Vec → Cov → Cov → Cov → Cov → Vec
  gaugeCodazzi j q p px m mx a =
    px (wall a) - mx (wall a) + q a * (p normal - m normal)
    - half * j * (p (wall a) + m (wall a))

  -- General mean-extrinsic correction to the coordinate Codazzi jump.
  -- M is symmetric covariant wall mean; the reference frame conversion
  -- above applies only at AK. For a general frame use coordinate jets.
  coordinateCodazzi : S → (Wall → Wall → S) → Vec → Cov → Cov → Cov → Cov → Vec
  coordinateCodazzi j M q p dp m dm a =
    dp (wall a) - dm (wall a) + q a * (p normal - m normal)
    - two * sum4 (λ b → M a b * sign b * (p (wall b) - m (wall b)))
    - j * (p (wall a) + m (wall a))

  gaugeGauss : S → Vec → Cov → Cov → Cov → Cov → S
  gaugeGauss j q p px m mx =
    px normal - mx normal - dot q (λ a → p (wall a) - m (wall a))
    - two * j * (p normal + m normal)

  gaugePrefix : Allocation → Cov → Cov → List S
  gaugePrefix D p m = p normal ∷ pack4 (λ a → p (wall a) - m (wall a))
  gaugePrefix E p m = p normal ∷ m normal ∷
    (p (wall x) - m (wall x)) ∷ (p (wall y) - m (wall y)) ∷
    (p (wall z) - m (wall z)) ∷ []

  gaugeRows : Allocation → S → Vec → Cov → Cov → Cov → Cov → List S
  gaugeRows a j q p px m mx =
    gaugePrefix a p m ++
    (pack4 (gaugeCodazzi j q p px m mx) ++ (gaugeGauss j q p px m mx ∷ []))

  attachGauge : Allocation → S → Vec → Cov → Cov → Cov → Cov → List S
  attachGauge a j q p ux m vx =
    gaugeRows a j q p (covOpticalDerivative (half * j) p ux)
      m (covOpticalDerivative (neg (half * j)) m vx)

  -- Native exact row-count and physical mean-force retention proof.
  open import Agda.Builtin.Nat using (Nat; zero; suc)
  length : List S → Nat
  length [] = zero
  length (_ ∷ as) = suc (length as)

  metricCount : (a : Allocation) (j : S) (q : Vec) (p px m mx : Tensor) →
    length (metricRows a j q p px m mx) ≡ 30
  metricCount D j q p px m mx = refl
  metricCount E j q p px m mx = refl

  gaugeCount : (a : Allocation) (j : S) (q : Vec) (p px m mx : Cov) →
    length (gaugeRows a j q p px m mx) ≡ 10
  gaugeCount D j q p px m mx = refl
  gaugeCount E j q p px m mx = refl

  last : List S → S
  last [] = O
  last (a ∷ []) = a
  last (_ ∷ b ∷ bs) = last (b ∷ bs)

  forceRetained : (a : Allocation) (j : S) (q : Vec) (p px m mx : Tensor) →
    last (metricRows a j q p px m mx) ≡ meanForce j q p px m mx
  forceRetained D j q p px m mx = refl
  forceRetained E j q p px m mx = refl
