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

  -- BR33 exact forced flat reference inverse on the homogeneous value
  -- continuity subspace. Reciprocal certificates are explicit; no
  -- uncontrolled division through q=0, z0=0 or normal transfer zeros.
  record Reciprocal (a : S) : Set r where
    constructor reciprocal
    field
      inv : S
      leftLaw : inv * a ≡ U
      rightLaw : a * inv ≡ U
  open Reciprocal public

  record MetricTracePair : Set r where
    constructor metricPair
    field
      plus minus : Tensor

  record GaugeTracePair : Set r where
    constructor gaugePair
    field
      plusC minusC : Cov

  commonMetricPair : (Wall → Wall → S) → Vec → S → S → MetricTracePair
  commonMetricPair h b a p = metricPair (mk (a + p)) (mk (a - p))
    where
    mk : S → Tensor
    mk nn = tab entry
      where
      entry : Axis → Axis → S
      entry (wall i) (wall j) = h i j
      entry (wall i) normal = half * b i
      entry normal (wall i) = half * b i
      entry normal normal = nn

  flatMetricD : (T Cn : S) → (q : Vec) → Reciprocal T →
    Reciprocal (dot q q) → (Wall → Wall → S) → Vec → S → S → MetricTracePair
  flatMetricD T Cn q Ti qi Rhs g rn f = commonMetricPair h b a p
    where
    h : Wall → Wall → S
    h i j = neg (half * inv Ti * Rhs i j)
    p : S
    p = inv qi * (T * f - dot q g)
    b : Vec
    b i = neg (inv Ti * (g i + q i * p))
    a : S
    a = trace4 h + inv Ti * (dot q b - Cn * p - two * rn)

  flatMetricE : (T Cn : S) → (q : Vec) → Reciprocal T →
    Reciprocal Cn → Reciprocal (q t) →
    (Wall → Wall → S) → Vec → S → S → S → MetricTracePair
  flatMetricE T Cn q Ti Ci zi Rhs g rp rm f = commonMetricPair h b a p
    where
    h : Wall → Wall → S
    h i j = neg (half * inv Ti * Rhs i j)
    p : S
    p = neg (inv Ci * (rp + rm + f))
    spatial : Wall → S
    spatial i = neg (inv Ti * (g i + q i * p))
    b : Vec
    b t = inv zi * (q x * spatial x + q y * spatial y + q z * spatial z + f)
    b x = spatial x
    b y = spatial y
    b z = spatial z
    a : S
    a = trace4 h + inv Ti * (rm - rp)

  flatMetricNormalPlus : S → S → Tensor → Tensor → Tensor
  flatMetricNormalPlus T Cn p m =
    mulT (neg half) (addT (mulT T (addT p m)) (mulT Cn (subT p m)))

  flatMetricNormalMinus : S → S → Tensor → Tensor → Tensor
  flatMetricNormalMinus T Cn p m =
    mulT half (subT (mulT T (addT p m)) (mulT Cn (subT p m)))

  flatGaugeD : (T j : S) → Vec → Reciprocal (T + j) →
    Reciprocal (T + two * j) → Vec → S → GaugeTracePair
  flatGaugeD T j q Ti Ni gt gn = gaugePair cp cm
    where
    ns : S
    ns = neg (inv Ni * gn)
    cs : Vec
    cs a = inv Ti * (neg (q a * ns) - gt a)
    cp cm : Cov
    cp normal = O
    cp (wall a) = half * cs a
    cm normal = ns
    cm (wall a) = half * cs a

  flatGaugeE : (T j : S) → (q : Vec) → Reciprocal (T + j) →
    Reciprocal (q t) → Vec → S → GaugeTracePair
  flatGaugeE T j q Ti zi gt gn = gaugePair cp cm
    where
    cj : Vec
    cj t = inv zi * gn
    cj x = O
    cj y = O
    cj z = O
    cs : Vec
    cs a = neg (inv Ti * gt a)
    cp cm : Cov
    cp normal = O
    cp (wall a) = half * (cs a + cj a)
    cm normal = O
    cm (wall a) = half * (cs a - cj a)

  -- BR36 complex Lorentz chart, acting on covectors (not conjugate vectors).
  -- q/ell=(a,v), v.v=a²-1. The two inverse certificates below are
  -- denominator guards, not a claim that the supplied q is on shell.
  spatialDot : Vec → Vec → S
  spatialDot p q = p x * q x + p y * q y + p z * q z

  boostEntry : (a : S) → Vec → Reciprocal (U + a) → Wall → Wall → S
  boostEntry a v ai t t = a
  boostEntry a v ai t x = v x
  boostEntry a v ai t y = v y
  boostEntry a v ai t z = v z
  boostEntry a v ai x t = v x
  boostEntry a v ai y t = v y
  boostEntry a v ai z t = v z
  boostEntry a v ai i j = delta (wall i) (wall j) + inv ai * v i * v j

  liftBoost : (Wall → Wall → S) → Axis → Axis → S
  liftBoost B normal normal = U
  liftBoost B normal (wall _) = O
  liftBoost B (wall _) normal = O
  liftBoost B (wall i) (wall j) = B i j

  sum5 : (Axis → S) → S
  sum5 f = sum4 (λ i → f (wall i)) + f normal

  transportCov : (Axis → Axis → S) → Cov → Cov
  transportCov B c i = sum5 (λ j → B i j * c j)

  transportTensor : (Axis → Axis → S) → Tensor → Tensor
  transportTensor B p = tab (λ i j →
    sum5 (λ a → sum5 (λ b → B i a * B j b * get p a b)))

  transportMetricPair : (Axis → Axis → S) → MetricTracePair → MetricTracePair
  transportMetricPair B (metricPair p m) =
    metricPair (transportTensor B p) (transportTensor B m)

  transportGaugePair : (Axis → Axis → S) → GaugeTracePair → GaugeTracePair
  transportGaugePair B (gaugePair p m) =
    gaugePair (transportCov B p) (transportCov B m)

  -- D-to-E uses the actual response to the released D row. In particular
  -- den is NOT replaced by its flat value. The linear row proof and
  -- nonvanishing proof are separate obligations of the actual DtN owner.
  updateMetricPair : MetricTracePair → MetricTracePair → S → MetricTracePair
  updateMetricPair (metricPair p m) (metricPair hp hm) a =
    metricPair (addT p (mulT a hp)) (addT m (mulT a hm))

  updateGaugePair : GaugeTracePair → GaugeTracePair → S → GaugeTracePair
  updateGaugePair (gaugePair p m) (gaugePair hp hm) a =
    gaugePair (λ i → p i + a * hp i) (λ i → m i + a * hm i)

  rowCorrection : (den : S) → Reciprocal den → S → S → S
  rowCorrection den di target current = inv di * (target - current)

  metricEFromD : (base response : MetricTracePair) →
    (row : MetricTracePair → S) → Reciprocal (row response) →
    S → MetricTracePair
  metricEFromD base response row ri target =
    updateMetricPair base response (rowCorrection (row response) ri target (row base))

  gaugeEFromD : (base response : GaugeTracePair) →
    (row : GaugeTracePair → S) → Reciprocal (row response) →
    S → GaugeTracePair
  gaugeEFromD base response row ri target =
    updateGaugePair base response (rowCorrection (row response) ri target (row base))

  ------------------------------------------------------------------------
  -- BR39 physical localizer: original optical jets, no new generic solver.
  -- These are algebraic SOURCE-SPECIFIC operators. The cutoff is required
  -- to have matching value and normal first jet on the Israel wall.
  -- Quantitative Sobolev estimates / glancing localisation are separate.
  ------------------------------------------------------------------------

  record ScalarJet : Set r where
    constructor scalarJet
    field
      value : S
      first : Axis → S
      second : Axis → Axis → S
  open ScalarJet public

  record TensorJet : Set r where
    constructor tensorJet
    field
      fieldValue : Tensor
      fieldFirst : Axis → Tensor
      fieldSecond : Axis → Axis → Tensor
  open TensorJet public

  record CovJet : Set r where
    constructor covJet
    field
      covValue : Cov
      covFirst : Axis → Cov
      covSecond : Axis → Axis → Cov
  open CovJet public

  -- Full five-coordinate nondivergence-form principal tensor:
  -- L u = a^ij ∂i∂j u + b^i ∂i u + V u.
  -- Keep every first/second cutoff derivative (including time/normal).
  -- The value potential commutes with scalar multiplication.
  record PrincipalJet : Set r where
    constructor principalJet
    field
      principal : Axis → Axis → S
      drift : Axis → S
  open PrincipalJet public

  localTensor : ScalarJet → TensorJet → TensorJet
  localTensor chi u = tensorJet
    (mulT (value chi) (fieldValue u))
    (λ i → addT (mulT (first chi i) (fieldValue u))
                (mulT (value chi) (fieldFirst u i)))
    (λ i j → addT (addT
      (mulT (second chi i j) (fieldValue u))
      (mulT (first chi i) (fieldFirst u j)))
      (addT (mulT (first chi j) (fieldFirst u i))
            (mulT (value chi) (fieldSecond u i j))))

  localCov : ScalarJet → CovJet → CovJet
  localCov chi u = covJet
    (λ a → value chi * covValue u a)
    (λ i a → first chi i * covValue u a + value chi * covFirst u i a)
    (λ i j a → second chi i j * covValue u a
      + first chi i * covFirst u j a
      + first chi j * covFirst u i a
      + value chi * covSecond u i j a)

  -- Nondivergence-form principal commutator, without asserting symmetry:
  -- [L,chi]u = a^ij(chi_ij u + chi_i u_j + chi_j u_i)
  --             + b^i chi_i u.
  -- This works even for a non-symmetric coefficient presentation.
  tensorCutoffResidual : PrincipalJet → ScalarJet → TensorJet → Tensor
  tensorCutoffResidual p chi u =
    addT (sumT (λ i → sumT (λ j →
      addT (mulT (principal p (wall i) (wall j) * second chi (wall i) (wall j))
                    (fieldValue u))
        (addT (mulT (principal p (wall i) (wall j) * first chi (wall i))
                    (fieldFirst u (wall j)))
              (mulT (principal p (wall i) (wall j) * first chi (wall j))
                    (fieldFirst u (wall i)))))))
      (sumT (λ i → mulT (drift p (wall i) * first chi (wall i))
                                      (fieldValue u)))

  -- Include the actual normal direction: no silent loss of mixed or
  -- normal/time jets in a physical 5D localization.
  fullTensorCutoffResidual : PrincipalJet → ScalarJet → TensorJet → Tensor
  fullTensorCutoffResidual p chi u =
    addT (tensorCutoffResidual p chi u)
      (addT
        (sumT (λ i → addT
          (mulT (principal p (wall i) normal * second chi (wall i) normal)
                (fieldValue u))
          (addT
            (mulT (principal p (wall i) normal * first chi (wall i))
                  (fieldFirst u normal))
            (mulT (principal p (wall i) normal * first chi normal)
                  (fieldFirst u (wall i))))))
        (addT
          (sumT (λ i → addT
            (mulT (principal p normal (wall i) * second chi normal (wall i))
                  (fieldValue u))
            (addT
              (mulT (principal p normal (wall i) * first chi normal)
                    (fieldFirst u (wall i)))
              (mulT (principal p normal (wall i) * first chi (wall i))
                    (fieldFirst u normal)))))
          (addT
            (mulT (principal p normal normal * second chi normal normal)
                  (fieldValue u))
            (addT
              (mulT (two * principal p normal normal * first chi normal)
                    (fieldFirst u normal))
              (mulT (drift p normal * first chi normal) (fieldValue u))))))

  -- Same physical cutoff on both faces: transform the NORMAL optical jet
  -- before the existing actual Israel/gauge rows.
  -- Every BR34 boundary condition is still imposed by attachMetric/attachGauge.
  localizedMetricRows : Allocation → S → Vec → ScalarJet →
    Tensor → Tensor → Tensor → Tensor → List S
  localizedMetricRows a j q chi p ux m vx =
    attachMetric a j q
      (mulT (value chi) p)
      (addT (mulT (value chi) ux) (mulT (first chi normal) p))
      (mulT (value chi) m)
      (addT (mulT (value chi) vx) (mulT (first chi normal) m))

  localizedGaugeRows : Allocation → S → Vec → ScalarJet →
    Cov → Cov → Cov → Cov → List S
  localizedGaugeRows a j q chi p ux m vx =
    attachGauge a j q
      (λ i → value chi * p i)
      (λ i → value chi * ux i + first chi normal * p i)
      (λ i → value chi * m i)
      (λ i → value chi * vx i + first chi normal * m i)

  -- The boundary collar owner must supply value=1, d_normal=0 for an
  -- exact no-new-boundary-defect weld. No proof of existence of such a
  -- cutoff in the relevant weighted global function space is claimed.

  -- The covector subsidiary gets the IDENTICAL five-direction product
  -- commutator, rather than being silently replaced by a scalar wave.
  covCutoffResidual : PrincipalJet → ScalarJet → CovJet → Cov
  covCutoffResidual p chi u k =
    sum5 (λ i → sum5 (λ j →
      principal p i j *
        (second chi i j * covValue u k
        + first chi i * covFirst u j k
        + first chi j * covFirst u i k)))
      + sum5 (λ i → drift p i * first chi i * covValue u k)

  -- Abstract source ledger is an actual finite carrier, not an
  -- assertion that analytic norms or subsidiary constraints close.
  record LocalizationDefects : Set r where
    constructor localizationDefects
    field
      metricBulk : Tensor
      gaugeBulk : Cov
      metricWallD metricWallE : List S
      gaugeWallD gaugeWallE : List S
  open LocalizationDefects public

  localizedDefects : PrincipalJet → PrincipalJet → ScalarJet →
    TensorJet → CovJet → S → Vec →
    Tensor → Tensor → Tensor → Tensor →
    Cov → Cov → Cov → Cov → LocalizationDefects
  localizedDefects mp gp chi tu cu j q p px m mx c cx d dx =
    localizationDefects
      (fullTensorCutoffResidual mp chi tu)
      (covCutoffResidual gp chi cu)
      (localizedMetricRows D j q chi p px m mx)
      (localizedMetricRows E j q chi p px m mx)
      (localizedGaugeRows D j q chi c cx d dx)
      (localizedGaugeRows E j q chi c cx d dx)

  -- To promote the ledger one must prove: actual principal coefficients
  -- and first-order drift reproduce BR14/BS4 in the same coordinates;
  -- estimates on derivatives of chi and all fields, trace lift,
  -- source compatibility and boundary collar. Neither finite signed
  -- ledgers nor this constructor supplies PDE existence.

  ------------------------------------------------------------------------
  -- BR39b: not merely a scalar proxy. Attach the ACTUAL BR15 spectral
  -- conjugated first-order metric matrices and BS4/5 covector generators
  -- to the diagonal optical wave principal part.
  ------------------------------------------------------------------------

  opticalPrincipal : PrincipalJet
  opticalPrincipal = principalJet diagonal (λ _ → O)
    where
    diagonal : Axis → Axis → S
    diagonal (wall a) (wall b) = eta a b
    diagonal normal normal = U
    diagonal normal (wall _) = O
    diagonal (wall _) normal = O

  metricFirstCutoff : S → S → S → S → S → S → S →
    ScalarJet → Tensor → Tensor
  metricFirstCutoff bk a e c ai ei ci chi u =
    spectral a e c
      (sumT (λ i → mulT (bk * first chi (wall i))
                    (J i (spectral ai ei ci u))))

  gaugeFirstCutoff : S → ScalarJet → Cov → Cov
  gaugeFirstCutoff bk chi u k =
    two * bk * sum4 (λ i → sign i * first chi (wall i) * L i u k)

  -- The second-order part and all first-order matrix terms now match the
  -- original frozen optical BR15 / BS4 coefficient OWNERS. Potential
  -- terms commute with a scalar chi. No estimate is hidden in this term.
  metricOpticalCutoffResidual : S → S → S → S → S → S → S →
    ScalarJet → TensorJet → Tensor
  metricOpticalCutoffResidual bk a e c ai ei ci chi u =
    addT (fullTensorCutoffResidual opticalPrincipal chi u)
         (metricFirstCutoff bk a e c ai ei ci chi (fieldValue u))

  gaugeOpticalCutoffResidual : S → ScalarJet → CovJet → Cov
  gaugeOpticalCutoffResidual bk chi u k =
    covCutoffResidual opticalPrincipal chi u k
      + gaugeFirstCutoff bk chi (covValue u) k

  record OpticalLocalizationDefects : Set r where
    constructor opticalLocalizationDefects
    field
      actualMetricBulk : Tensor
      actualGaugeBulk : Cov
      actualMetricD actualMetricE : List S
      actualGaugeD actualGaugeE : List S
  open OpticalLocalizationDefects public

  opticalLocalizedDefects : S → S → S → S → S → S → S →
    ScalarJet → TensorJet → CovJet → S → Vec →
    Tensor → Tensor → Tensor → Tensor →
    Cov → Cov → Cov → Cov → OpticalLocalizationDefects
  opticalLocalizedDefects bk a e c ai ei ci chi tu cu j q p px m mx gp gx gm gy =
    opticalLocalizationDefects
      (metricOpticalCutoffResidual bk a e c ai ei ci chi tu)
      (gaugeOpticalCutoffResidual bk chi cu)
      (localizedMetricRows D j q chi p px m mx)
      (localizedMetricRows E j q chi p px m mx)
      (localizedGaugeRows D j q chi gp gx gm gy)
      (localizedGaugeRows E j q chi gp gx gm gy)

  ------------------------------------------------------------------------
  -- BR40a: curved-chart scalar Hessian, not coordinate-Hessian promotion.
  -- For ∇_i∇_j chi the Christoffel subtraction is essential. The physical
  -- metric connection is an input constructed from the source background;
  -- this carrier cannot assert that a source metric is Einstein–Israel.
  ------------------------------------------------------------------------

  record ChartConnection : Set r where
    constructor chartConnection
    field
      christoffel : Axis → Axis → Axis → S
  open ChartConnection public

  covariantScalarHessian : ChartConnection → ScalarJet → Axis → Axis → S
  covariantScalarHessian g chi i j =
    second chi i j - sum5 (λ k → christoffel g k i j * first chi k)

  covariantScalarJet : ChartConnection → ScalarJet → ScalarJet
  covariantScalarJet g chi =
    scalarJet (value chi) (first chi) (covariantScalarHessian g chi)

  -- Treat TensorJet/CovJet.fieldFirst and .fieldSecond as covariant
  -- source jets here, not uncorrected partial jets.
  record MetricVariableCoefficients : Set r where
    constructor metricVariableCoefficients
    field
      metricSecondCoefficient : Axis → Axis → S
      metricFirstCoefficient : Axis → Tensor → Tensor
  open MetricVariableCoefficients public

  record GaugeVariableCoefficients : Set r where
    constructor gaugeVariableCoefficients
    field
      gaugeSecondCoefficient : Axis → Axis → S
      gaugeFirstCoefficient : Axis → Cov → Cov
  open GaugeVariableCoefficients public

  sum5T : (Axis → Tensor) → Tensor
  sum5T f = addT (sumT (λ i → f (wall i))) (f normal)

  metricVariableCutoffResidual : ChartConnection → MetricVariableCoefficients →
    ScalarJet → TensorJet → Tensor
  metricVariableCutoffResidual g c chi u =
    addT
      (sum5T (λ i → sum5T (λ j →
        addT
          (mulT (metricSecondCoefficient c i j * covariantScalarHessian g chi i j)
                (fieldValue u))
          (addT
            (mulT (metricSecondCoefficient c i j * first chi i)
                  (fieldFirst u j))
            (mulT (metricSecondCoefficient c i j * first chi j)
                  (fieldFirst u i))))))
      (sum5T (λ i →
        metricFirstCoefficient c i (mulT (first chi i) (fieldValue u))))

  gaugeVariableCutoffResidual : ChartConnection → GaugeVariableCoefficients →
    ScalarJet → CovJet → Cov
  gaugeVariableCutoffResidual g c chi u k =
    sum5 (λ i → sum5 (λ j →
      gaugeSecondCoefficient c i j *
        (covariantScalarHessian g chi i j * covValue u k
          + first chi i * covFirst u j k
          + first chi j * covFirst u i k)))
      + sum5 (λ i →
        gaugeFirstCoefficient c i
          (λ a → first chi i * covValue u a) k)

  -- Actual coordinate connection and physical matrix coefficients are
  -- still source-specific proof obligations. In particular, this carrier
  -- never replaces BR29 derivative Bianchi with componentwise scalar
  -- constraint propagation, nor assumes an inverse for a glancing symbol.

  -- Source Gaussian warp g=dn²+b(n)² eta, k=b'/b. This is the
  -- actual BR31 reference connection, with both tangent/normal signs.
  -- General variable backgrounds use their independent ChartConnection.
  warpedChristoffel : S → S → Axis → Axis → Axis → S
  warpedChristoffel b k normal (wall a) (wall c) =
    neg (b * b * k * eta a c)
  warpedChristoffel b k (wall a) (wall c) normal =
    k * eta a c * sign a
  warpedChristoffel b k (wall a) normal (wall c) =
    k * eta a c * sign a
  warpedChristoffel b k _ _ _ = O

  warpedConnection : S → S → ChartConnection
  warpedConnection b k = chartConnection (warpedChristoffel b k)

  -- Gaussian reference scalar collar: chi=1 and d_n chi=0 on n=0.
  -- The actual cutoffs and their supported weighted chart domain remain
  -- user-supplied jets. No artificial source profile is assumed.

  ------------------------------------------------------------------------
  -- BR40b: DIFFERENTIATED PHYSICAL SOURCE ROWS.
  -- Actual BR34 rows are homogeneous linear in their endpoint field
  -- jets and affine-linear in the background j,q (without j*q terms).
  -- The time derivative must retain both field and background jets.
  ------------------------------------------------------------------------

  zeroQ : Vec
  zeroQ _ = O

  rowAdd rowSub : List S → List S → List S
  rowAdd [] [] = []
  rowAdd (a ∷ as) (b ∷ bs) = (a + b) ∷ rowAdd as bs
  rowAdd [] (_ ∷ _) = []
  rowAdd (_ ∷ _) [] = []
  rowSub [] [] = []
  rowSub (a ∷ as) (b ∷ bs) = (a - b) ∷ rowSub as bs
  rowSub [] (_ ∷ _) = []
  rowSub (_ ∷ _) [] = []

  -- ∂_t metricRows(j,q;U) =
  -- metricRows(j,q;U_t) +
  -- metricRows(j_t,q_t;U) - metricRows(0,0;U).
  -- Source-side construction; an analytic time-derivative theorem still
  -- needs the true variable Einstein-Israel coefficient dependence.
  metricBackgroundDerivative : Allocation → S → Vec →
    Tensor → Tensor → Tensor → Tensor → List S
  metricBackgroundDerivative a dj dq p px m mx =
    rowSub (metricRows a dj dq p px m mx)
           (metricRows a O zeroQ p px m mx)

  metricTimeRows : Allocation → S → Vec → S → Vec →
    Tensor → Tensor → Tensor → Tensor →
    Tensor → Tensor → Tensor → Tensor → List S
  metricTimeRows a j q dj dq p px m mx pt pxt mt mxt =
    rowAdd (metricRows a j q pt pxt mt mxt)
           (metricBackgroundDerivative a dj dq p px m mx)

  gaugeBackgroundDerivative : Allocation → S → Vec →
    Cov → Cov → Cov → Cov → List S
  gaugeBackgroundDerivative a dj dq p px m mx =
    rowSub (gaugeRows a dj dq p px m mx)
           (gaugeRows a O zeroQ p px m mx)

  gaugeTimeRows : Allocation → S → Vec → S → Vec →
    Cov → Cov → Cov → Cov →
    Cov → Cov → Cov → Cov → List S
  gaugeTimeRows a j q dj dq p px m mx pt pxt mt mxt =
    rowAdd (gaugeRows a j q pt pxt mt mxt)
           (gaugeBackgroundDerivative a dj dq p px m mx)

  -- The physical mean force is the LAST ROW of BOTH differentiated
  -- metric allocations, including the derivative of the background k.
  metricTimeMeanForce : S → Vec → S → Vec →
    Tensor → Tensor → Tensor → Tensor →
    Tensor → Tensor → Tensor → Tensor → S
  metricTimeMeanForce j q dj dq p px m mx pt pxt mt mxt =
    tau (half * j) q pt pxt
    + tau (neg (half * j)) q mt mxt
    + half * dj * (neg (four * scale p) + four * scale m)
    - dot dq (beta p)
    - dot dq (beta m)

  -- General nonzero mean extrinsic curvature: differentiate the actual
  -- coordinate Codazzi jump. The mean and its time derivative are
  -- INDEPENDENT input tensors; never set M_t=0 as a flat shortcut.
  coordinateCodazziTime : S → S →
    (Wall → Wall → S) → (Wall → Wall → S) →
    Vec → Vec →
    Cov → Cov → Cov → Cov →
    Cov → Cov → Cov → Cov → Vec
  coordinateCodazziTime j dj M Mt q qt p px m mx pt pxt mt mxt a =
    coordinateCodazzi j M q pt pxt mt mxt a
    + coordinateCodazzi dj Mt qt p px m mx a
    - coordinateCodazzi O (λ _ _ → O) zeroQ p px m mx a

  -- A nonzero reduced source or differentiated wall geometry belongs in
  -- the forcing, not silently in the homogeneous BR34 boundary matrix.
  record DifferentiatedPhysicalForcing : Set r where
    constructor differentiatedPhysicalForcing
    field
      metricDTime metricETime : List S
      gaugeDTime gaugeETime : List S
      meanTime : S
      meanCodazziTime : Vec
  open DifferentiatedPhysicalForcing public

  physicalTimeForcing : S → Vec → S → Vec →
    (Wall → Wall → S) → (Wall → Wall → S) →
    Tensor → Tensor → Tensor → Tensor →
    Tensor → Tensor → Tensor → Tensor →
    Cov → Cov → Cov → Cov →
    Cov → Cov → Cov → Cov → DifferentiatedPhysicalForcing
  physicalTimeForcing j q dj dq M Mt p px m mx pt pxt mt mxt
                      c cx d dx ct cxt dt dxt =
    differentiatedPhysicalForcing
      (metricTimeRows D j q dj dq p px m mx pt pxt mt mxt)
      (metricTimeRows E j q dj dq p px m mx pt pxt mt mxt)
      (gaugeTimeRows D j q dj dq c cx d dx ct cxt dt dxt)
      (gaugeTimeRows E j q dj dq c cx d dx ct cxt dt dxt)
      (metricTimeMeanForce j q dj dq p px m mx pt pxt mt mxt)
      (coordinateCodazziTime j dj M Mt q dq c cx d dx ct cxt dt dxt)

  ------------------------------------------------------------------------
  -- BR40c: EXPLICIT PHYSICAL TRACE AND CONSTRAINT DERIVATIVE SOLVERS.
  -- Reuse the actual BR34 Israel, mean-force, Gauss and Codazzi owners.
  -- Unlike a guessed positive wall Hessian, these are exact signed
  -- reconstructions. They do NOT discard the normal-constant modes.
  ------------------------------------------------------------------------

  israelTrace : S → Vec → Tensor → Tensor → Tensor → Tensor → S
  israelTrace j q p px m mx = trace4 (israel j q p px m mx)

  betaSum betaJump : Tensor → Tensor → Vec
  betaSum p m a = beta p a + beta m a
  betaJump p m a = beta p a - beta m a

  -- trace J = [trace H_x] - 2 div[beta] - 4 j (l+ + l-).
  -- F = {trace H_x} - div{beta} - 2 j (l+ - l-).
  -- These solve BOTH one-sided normal trace derivatives at the actual
  -- interface without division by q, s or a characteristic root.
  normalTraceMean : S → Vec → Tensor → Tensor → Tensor → Tensor → S
  normalTraceMean j q p px m mx =
    meanForce j q p px m mx
    + dot q (betaSum p m)
    + two * j * (scale p - scale m)

  normalTraceJump : S → Vec → Tensor → Tensor → Tensor → Tensor → S
  normalTraceJump j q p px m mx =
    israelTrace j q p px m mx
    + two * dot q (betaJump p m)
    + four * j * (scale p + scale m)

  normalTracePlus normalTraceMinus :
    S → Vec → Tensor → Tensor → Tensor → Tensor → S
  normalTracePlus j q p px m mx =
    normalTraceMean j q p px m mx
    + half * normalTraceJump j q p px m mx
  normalTraceMinus j q p px m mx =
    normalTraceMean j q p px m mx
    - half * normalTraceJump j q p px m mx

  -- Unrestricted, nonzero mean extrinsic curvature is retained.
  -- Coordinate Codazzi solves tangent derivative jumps, while Gauss
  -- solves the normal derivative jump. No inverse Fourier factor.
  coordinateTangentDerivativeJump : S → (Wall → Wall → S) → Vec →
    Cov → Cov → Cov → Cov → Vec
  coordinateTangentDerivativeJump j M q p px m mx a =
    coordinateCodazzi j M q p px m mx a
    - q a * (p normal - m normal)
    + two * sum4 (λ b → M a b * sign b *
                           (p (wall b) - m (wall b)))
    + j * (p (wall a) + m (wall a))

  normalGaugeDerivativeJump : S → Vec →
    Cov → Cov → Cov → Cov → S
  normalGaugeDerivativeJump j q p px m mx =
    gaugeGauss j q p px m mx
    + dot q (λ a → p (wall a) - m (wall a))
    + two * j * (p normal + m normal)

  -- To turn these pointwise reconstructions into a physical wave energy
  -- estimate requires positivity/control of the remaining trace and
  -- normal energy work, and compatible differentiability of the source
  -- background. The indefinite Israel Hessian is deliberately retained.

  ------------------------------------------------------------------------
  -- BR40d: actual signed Israel contribution to variable BR4 normal work.
  -- For a common tangential velocity w_ab the normal-principal flux is
  -- <w,[H_x]>_eta. The equation J=2[K]-j(H+ +H-) gives
  -- [H_x]=J+q⊗[beta]+[beta]⊗q+j(l+ +l-)eta.
  -- This is NOT positive: retain trace and longitudinal cross terms.
  ------------------------------------------------------------------------

  wallPair : (Wall → Wall → S) → (Wall → Wall → S) → S
  wallPair a b = sum4 (λ i → sum4 (λ k →
    sign i * sign k * a i k * b i k))

  normalTensorJump : Tensor → Tensor → Wall → Wall → S
  normalTensorJump px mx a b = H px a b - H mx a b

  physicalNormalWork : (Wall → Wall → S) → Tensor → Tensor → S
  physicalNormalWork velocity px mx =
    wallPair velocity (normalTensorJump px mx)

  israelWallWork : S → Vec → (Wall → Wall → S) →
    Tensor → Tensor → Tensor → Tensor → S
  israelWallWork j q velocity p px m mx =
    wallPair velocity (israel j q p px m mx)

  longitudinalWallWork : Vec → (Wall → Wall → S) →
    Tensor → Tensor → S
  longitudinalWallWork q velocity p m =
    wallPair velocity (λ a b →
      q a * betaJump p m b + betaJump p m a * q b)

  scaleWallWork : S → (Wall → Wall → S) → Tensor → Tensor → S
  scaleWallWork j velocity p m =
    j * (scale p + scale m) * trace4 velocity

  -- The residual is zero under the BR34 tensor identities and ordinary
  -- complex ring laws; keep it explicit until kernel-checked. In
  -- particular the negative trace/shear Israel Hessian prevents the
  -- energy from becoming positive by merely discarding cross terms.
  signedWallWorkResidual : S → Vec → (Wall → Wall → S) →
    Tensor → Tensor → Tensor → Tensor → S
  signedWallWorkResidual j q velocity p px m mx =
    physicalNormalWork velocity px mx
      - israelWallWork j q velocity p px m mx
      - longitudinalWallWork q velocity p m
      - scaleWallWork j velocity p m

  ------------------------------------------------------------------------
  -- BR40f: the EXISTING BR19 moving-graph material jump, now attached
  -- to BR40b's differentiated physical source instead of being a
  -- disconnected symbolic geometry calculation.
  -- Original adapted wall point g=eta_5, n=unit normal; graphGrad_n=0.
  -- Full 15 components, including harmonic normal-normal and mixed.
  ------------------------------------------------------------------------

  normalUnit : Cov
  normalUnit normal = U
  normalUnit (wall _) = O

  tangentialGraphGradient : Vec → Cov
  tangentialGraphGradient a (wall i) = a i
  tangentialGraphGradient a normal = O

  graphMaterialJump : S → Vec → Tensor → Tensor
  graphMaterialJump j a p =
    tab (λ i k →
      two * j * get p i k
      + j * h44 p * metric i k
      + (three * three) * j * h44 p * normalUnit i * normalUnit k
      - (three * two) * j *
          (tangentialGraphGradient a i * normalUnit k
           + normalUnit i * tangentialGraphGradient a k))

  -- On a moving material wall, Q_material = Q_coordinate - f D_n Q_ref.
  -- Preserve both the normal transport and the graph displacement f;
  -- never identify a graph-fixed coordinate source with the original.
  materialGoodUnknown : S → Tensor → Tensor → Tensor
  materialGoodUnknown displacement coordinateJet sourceNormalJet =
    subT coordinateJet (mulT displacement sourceNormalJet)

  graphMaterialForcing : S → Vec → S →
    Tensor → Tensor → Tensor
  graphMaterialForcing j grad displacement perturbation
                       sourceNormalJet =
    subT (graphMaterialJump j grad perturbation)
         (mulT displacement sourceNormalJet)

  record PhysicalMaterialWeld : Set r where
    constructor physicalMaterialWeld
    field
      differentiatedRows : DifferentiatedPhysicalForcing
      movingGraphSource : Tensor
      originalMetricJet : Tensor
  open PhysicalMaterialWeld public

  physicalMovingWallWeld : S → Vec → S → Vec →
    (Wall → Wall → S) → (Wall → Wall → S) →
    Tensor → Tensor → Tensor → Tensor →
    Tensor → Tensor → Tensor → Tensor →
    Cov → Cov → Cov → Cov →
    Cov → Cov → Cov → Cov →
    Vec → S → Tensor → PhysicalMaterialWeld
  physicalMovingWallWeld j q dj dq M Mt p px m mx pt pxt mt mxt
                         c cx d dx ct cxt dt dxt graphGrad displacement
                         sourceNormalJet =
    physicalMaterialWeld
      (physicalTimeForcing j q dj dq M Mt p px m mx pt pxt mt mxt
                           c cx d dx ct cxt dt dxt)
      (graphMaterialForcing j graphGrad displacement p sourceNormalJet)
      (materialGoodUnknown displacement p sourceNormalJet)

  -- Original BR19/31 source geometry owns the material jump and graph
  -- shape; the BR34 rows own the linearized reference boundary operator.
  -- This record transports both but does not equate them without a
  -- variable-background harmonic-source and gauge proof.

  ------------------------------------------------------------------------
  -- BR41a/b: actual physical work budget and two-sided holonomy payments.
  --
  -- In the Lorentzian physical wallPair the metric signs are retained.
  -- Positive real trace bounds use Hermitian magnitudes in the analytic
  -- owner, never this complex-bilinear work as a positive quadratic form.
  ------------------------------------------------------------------------

  record PhysicalWallWorkSources : Set r where
    constructor mkPhysicalWallWorkSources
    field
      israelPower : S
      longitudinalPower : S
      tracePower : S
      physicalPower : S
      unallocatedPower : S
  open PhysicalWallWorkSources public

  assemblePhysicalWallWorkSources : S → Vec → (Wall → Wall → S) →
    Tensor → Tensor → Tensor → Tensor → PhysicalWallWorkSources
  assemblePhysicalWallWorkSources j q velocity p px m mx =
    mkPhysicalWallWorkSources
      (israelWallWork j q velocity p px m mx)
      (longitudinalWallWork q velocity p m)
      (scaleWallWork j velocity p m)
      (physicalNormalWork velocity px mx)
      (signedWallWorkResidual j q velocity p px m mx)

  -- BS11 normal holonomy in its original two-sided form:
  --
  -- xi' = -phi - 2 b² C, xi(0)=xi(L)=0
  -- U'  = b⁴(A-beta), U(0)=U(L)=0.
  --
  -- C = -Int(phi)/(2 Int(b²)); A = Int(b⁴ beta)/Int(b⁴).
  -- The source integral carries its original graph and time indices.
  -- The two denominator witnesses are supplied by the POSITIVE warp
  -- owner; this complex algebra does not assert positivity by itself.
  record NormalHolonomyMoments : Set r where
    constructor normalHolonomyMoments
    field
      scalarWarpIntegral : S
      vectorWarpIntegral : S
      scalarSourceIntegral : S
      vectorSourceIntegral : Vec
  open NormalHolonomyMoments public

  record NormalHolonomyResponse : Set r where
    constructor mkNormalHolonomyResponse
    field
      scalarConstant : S
      vectorConstant : Vec
      scalarZeroMode : S
      vectorZeroMode : Vec
  open NormalHolonomyResponse public

  solveNormalHolonomy : (m : NormalHolonomyMoments) →
    Reciprocal (scalarWarpIntegral m) →
    Reciprocal (vectorWarpIntegral m) →
    NormalHolonomyResponse
  solveNormalHolonomy m i2 i4 =
    mkNormalHolonomyResponse
      (neg (half * inv i2 * scalarSourceIntegral m))
      (λ k → inv i4 * vectorSourceIntegral m k)
      (scalarSourceIntegral m)
      (vectorSourceIntegral m)

  -- Do NOT drop original integral moments (or invent a zero-mode gauge
  -- fixing): they are retained in NormalHolonomyResponse for subsequent
  -- physical quotient detection. The actual BS13 curvature kernel and
  -- BR31 weighted exterior must supply the global analytic inequality.

  ------------------------------------------------------------------------
  -- BR42: ORIGINAL-PHYSICAL ENERGY/RESTART SOURCE, not a new PDE solver.
  --
  -- The BR4 first-order wave symmetrizer supplies the actual bulk energy
  -- identity, BR40d/41a supplies signed wall work, and BS11/13 supplies
  -- explicit scalar/vector normal-holonomy moments. These constructors
  -- keep all of those independent and include the unallocated residual.
  -- A complex ring alone cannot certify a positive Sobolev estimate.
  ------------------------------------------------------------------------

  record PhysicalSlabSource : Set r where
    constructor physicalSlabSource
    field
      initialEnergy : S
      slabDuration : S
      bulkGrowth : S
      bulkSourcePayment : S
      physicalWallSource : PhysicalWallWorkSources
      traceSourcePayment : S
      boundaryLocalizationError : S
      subsidiarySourcePayment : S
      normalHolonomySource : NormalHolonomyMoments
  open PhysicalSlabSource public

  -- This is the *exact signed* BR4 budget, prior to replacing the wall
  -- work with the real Hilbert-space estimate from BR41a.
  physicalSignedEnergyIncrement : PhysicalSlabSource → S
  physicalSignedEnergyIncrement d =
    slabDuration d *
      (bulkGrowth d * initialEnergy d
        + bulkSourcePayment d
        + two * physicalPower (physicalWallSource d)
        + traceSourcePayment d
        + boundaryLocalizationError d
        + subsidiarySourcePayment d)

  physicalSignedEnergyNext : PhysicalSlabSource → S
  physicalSignedEnergyNext d =
    initialEnergy d + physicalSignedEnergyIncrement d

  -- Keep the original four tangential + one scalar normal holonomy
  -- channels. The time source is NOT presumed zero at a restart.
  record PhysicalHolonomyAdvance : Set r where
    constructor physicalHolonomyAdvance
    field
      scalarBefore scalarTimeSource : S
      vectorBefore vectorTimeSource : Vec
  open PhysicalHolonomyAdvance public

  advanceScalarHolonomy : S → PhysicalHolonomyAdvance → S
  advanceScalarHolonomy dt d =
    scalarBefore d + dt * scalarTimeSource d

  advanceVectorHolonomy : S → PhysicalHolonomyAdvance → Vec
  advanceVectorHolonomy dt d a =
    vectorBefore d a + dt * vectorTimeSource d a

  record PhysicalSlabOutput : Set r where
    constructor physicalSlabOutput
    field
      signedEnergyAfter : S
      scalarHolonomyAfter : S
      vectorHolonomyAfter : Vec
      unpaidWallResidual : S
      unpaidLocalizationResidual : S
  open PhysicalSlabOutput public

  assemblePhysicalSlab : PhysicalSlabSource →
    PhysicalHolonomyAdvance → PhysicalSlabOutput
  assemblePhysicalSlab d h =
    physicalSlabOutput
      (physicalSignedEnergyNext d)
      (advanceScalarHolonomy (slabDuration d) h)
      (advanceVectorHolonomy (slabDuration d) h)
      (unallocatedPower (physicalWallSource d))
      (boundaryLocalizationError d)

  -- Physical *admission* is intentionally dependent on evidence for
  -- trace estimates, original Einstein-Israel source compatibility,
  -- positive quotient coercivity, Bianchi graph preservation, and
  -- nondegenerate reflecting-domain geometry. None can be constructed
  -- by setting a Boolean flag or by finite arithmetic above.
  record PhysicalAnalyticPayments (TraceEstimate
      BianchiCompatibility WeightedQuotient ReflectingDomain : Set r)
      : Set r where
    constructor physicalAnalyticPayments
    field
      tracePaid : TraceEstimate
      bianchiPaid : BianchiCompatibility
      quotientPaid : WeightedQuotient
      domainPaid : ReflectingDomain

  -- The payment record is deliberately PARAMETRIC in the actual
  -- physical propositions; there is no postulate or default inhabitant.
  -- Source ledger != accepted physical continuum theorem.

  ------------------------------------------------------------------------
  -- BR43: FULL PHYSICAL TWO-ENDED TRACE/PREMIUM CARRIER.
  --
  -- The 1D weighted H¹ trace theorem on a positive normal collar
  -- controls time-derivative endpoint traces by the normal H¹ norm
  -- of the time derivative. That normal derivative is an *extra*
  -- physical regularity currency, not a term in BR4's lowest energy.
  --
  -- Mathematical analytic owner (real/Hermitian) for w >= m > 0:
  -- |v(0)|²+|v(L)|² <= 4/(Lm) ∫ w|v|² + 2L/m ∫ w|∂n v|².
  -- This ring-level carrier stores the exact source slots, but does
  -- not falsely assign positivity to the complex-bilinear norm.
  ------------------------------------------------------------------------

  record PhysicalTraceCurrency : Set r where
    constructor physicalTraceCurrency
    field
      metricVelocityPlus metricVelocityMinus : Tensor
      gaugeVelocityPlus gaugeVelocityMinus : Cov
      metricNormalTimeDerivativePlus metricNormalTimeDerivativeMinus : Tensor
      gaugeNormalTimeDerivativePlus gaugeNormalTimeDerivativeMinus : Cov
      normalWeightedMetricMass : S
      normalWeightedMetricDerivative : S
      normalWeightedGaugeMass : S
      normalWeightedGaugeDerivative : S
      metricNormalDerivativePremium : S
      gaugeNormalDerivativePremium : S
  open PhysicalTraceCurrency public

  -- Distinct current and higher-energy sources. Do NOT unify them by a
  -- generic positive identifier: an independently proved normal H¹
  -- estimate and BR4 differentiated energy are needed for absorption.
  record PhysicalTraceEnergyPayment : Set r where
    constructor physicalTraceEnergyPayment
    field
      originalLowerEnergy : S
      originalNormalDifferentiatedEnergy : S
      metricBoundaryForcing : S
      subsidiaryBoundaryForcing : S
      metricTraceConstant : S
      normalTraceConstant : S
      residualUnpaidHigherEnergy : S
  open PhysicalTraceEnergyPayment public

  -- In an analytic weighted Hilbert-space instance the two trace
  -- constants can be 4/(L m) and 2L/m. Positivity and reciprocal laws
  -- must be supplied by the real ordered/weighted physical domain
  -- owner, not by the arbitrary Complex RealField here.
  traceEnergyBudget : PhysicalTraceEnergyPayment → S
  traceEnergyBudget p =
    metricTraceConstant p * originalLowerEnergy p
    + normalTraceConstant p * originalNormalDifferentiatedEnergy p
    + metricBoundaryForcing p + subsidiaryBoundaryForcing p
    + residualUnpaidHigherEnergy p

  -- The actual 15+5 transported channel slots and the normal-jet
  -- currency are retained. BR37 Q^4/Q² losses must be paid at
  -- tangential Sobolev orders s+4/s+2 separately from this normal H¹
  -- premium; nothing in this finite carrier promotes them to a
  -- uniform glancing estimate.

  ------------------------------------------------------------------------
  -- BR45/46: actual differentiated BR4 4+1-variable coefficient source,
  -- coupled to the existing BR40b physical time rows.
  --
  -- The original lower-order coefficient power on a physical real
  -- fixed-chart slice is:
  -- -At wt²/2 + Ct[grad v,grad v]/2 + wt Bt.grad v + v wt.
  -- Keep the material-normal spatial derivative and all three wall
  -- tangential derivatives. This COMPLEX algebra is not an order
  -- or positivity proof; real/Hermitian bounds are independent.
  ------------------------------------------------------------------------

  data BR4Space : Set where
    spaceX spaceY spaceZ spaceNormal : BR4Space

  spaceAxis : BR4Space → Axis
  spaceAxis spaceX = wall x
  spaceAxis spaceY = wall y
  spaceAxis spaceZ = wall z
  spaceAxis spaceNormal = normal

  sumBR4Space : (BR4Space → S) → S
  sumBR4Space f =
    f spaceX + f spaceY + f spaceZ + f spaceNormal

  record BR4DifferentiatedCoefficientJet : Set r where
    constructor br4DifferentiatedCoefficientJet
    field
      coefficientA coefficientAt : S
      coefficientB coefficientBt : BR4Space → S
      coefficientC coefficientCt : BR4Space → BR4Space → S
  open BR4DifferentiatedCoefficientJet public

  record BR4DifferentiatedFieldJet : Set r where
    constructor br4DifferentiatedFieldJet
    field
      differentiatedValue : S
      differentiatedTime : S
      differentiatedSpatial : BR4Space → S
  open BR4DifferentiatedFieldJet public

  br4SpatialSquare : (BR4Space → BR4Space → S) →
    (BR4Space → S) → S
  br4SpatialSquare c d =
    sumBR4Space (λ i →
      sumBR4Space (λ k → c i k * d i * d k))

  br4DifferentiatedEnergy : BR4DifferentiatedCoefficientJet →
    BR4DifferentiatedFieldJet → S
  br4DifferentiatedEnergy c u =
    half * (coefficientA c * differentiatedTime u * differentiatedTime u
      + br4SpatialSquare (coefficientC c) (differentiatedSpatial u)
      + differentiatedValue u * differentiatedValue u)

  br4CoefficientWork : BR4DifferentiatedCoefficientJet →
    BR4DifferentiatedFieldJet → S
  br4CoefficientWork c u =
    neg (half * coefficientAt c *
      differentiatedTime u * differentiatedTime u)
    + half * br4SpatialSquare (coefficientCt c) (differentiatedSpatial u)
    + differentiatedTime u *
        sumBR4Space (λ i → coefficientBt c i * differentiatedSpatial u i)
    + differentiatedValue u * differentiatedTime u

  -- Keep the original 15 metric and five subsidiary channel jets.
  -- Lower-order matrix couplings from BR15/BS4, commutator sources
  -- and BR40b/f wall time derivatives are separate, not discarded.
  record BR45PhysicalSourceOwner : Set r where
    constructor br45PhysicalSourceOwner
    field
      metricCoefficient : BR4DifferentiatedCoefficientJet
      metricFifteen : Tensor
      gaugeFive : Cov
      metricCoefficientPower : S
      gaugeCoefficientPower : S
      originalTimeRows : DifferentiatedPhysicalForcing
      materialBoundary : PhysicalMaterialWeld
      tracePremium : PhysicalTraceEnergyPayment
      leftoverBianchiSource : Cov
  open BR45PhysicalSourceOwner public

  -- A true variable Einstein–Israel estimate must instantiate both
  -- coefficient jets from the SAME background and prove A>=a0>0,
  -- C>=c0 I, bounded coefficient derivatives, compatible wall/corner
  -- source, and an H^1 normal trace paid by BR4 higher energies.
  -- BR46's contracted-Bianchi principal symbol determines the needed
  -- subsidiary source but cannot set leftoverBianchiSource to zero
  -- without the physical variable connection and source equations.

  ------------------------------------------------------------------------
  -- BR47: second physical boundary time derivative, native exact
  -- successor to BR40b first derivative. The executable source checker
  -- covers the same original 30+10 D/E rows through BR4 order eight.
  ------------------------------------------------------------------------

  rowScale : S → List S → List S
  rowScale k [] = []
  rowScale k (u ∷ us) = k * u ∷ rowScale k us

  metricSecondTimeRows : Allocation →
    S → Vec → S → Vec → S → Vec →
    Tensor → Tensor → Tensor → Tensor →
    Tensor → Tensor → Tensor → Tensor →
    Tensor → Tensor → Tensor → Tensor → List S
  metricSecondTimeRows a j q jt qt jtt qtt
    p px m mx pt pxt mt mxt ptt pxtt mtt mxtt =
    rowAdd
      (metricRows a j q ptt pxtt mtt mxtt)
      (rowAdd
        (rowScale two
          (metricBackgroundDerivative a jt qt pt pxt mt mxt))
        (metricBackgroundDerivative a jtt qtt p px m mx))

  gaugeSecondTimeRows : Allocation →
    S → Vec → S → Vec → S → Vec →
    Cov → Cov → Cov → Cov →
    Cov → Cov → Cov → Cov →
    Cov → Cov → Cov → Cov → List S
  gaugeSecondTimeRows a j q jt qt jtt qtt
    p px m mx pt pxt mt mxt ptt pxtt mtt mxtt =
    rowAdd
      (gaugeRows a j q ptt pxtt mtt mxtt)
      (rowAdd
        (rowScale two
          (gaugeBackgroundDerivative a jt qt pt pxt mt mxt))
        (gaugeBackgroundDerivative a jtt qtt p px m mx))

  -- BR47 formula in the original physical background coordinates:
  -- B^(r) = B(j,q;U^(r)) +
  --     sum_(k=1)^r binom(r,k) deltaB(j^(k),q^(k);U^(r-k)).
  -- This time-jet formula assumes the BR34 reference rows depend
  -- separately AFFINELY on j and q. Full moving-graph jets and
  -- nonlinear connection products are not claimed to be represented
  -- by these reference linear rows.

  ------------------------------------------------------------------------
  -- BR48: ACTUAL ADM PHYSICAL METRIC -> BR4 FOUR-SPATIAL COEFFICIENTS.
  --
  -- g=-N²dt²+H_ij(dx^i+v^i dt)(dx^j+v^j dt), i=x,y,z,n.
  -- D=N sqrt(det H)>0; the positive-volume witness and inverse spatial
  -- metric are supplied by the original physical source geometry.
  --
  -- A=D/N²; B^i=A v^i; C^ij=D H^ij-A v^i v^j.
  -- C+B Bᵀ/A=D H^ij >0, but positivity of C by itself requires
  -- the additional physical spacelike/shift guard |v|_H<N.
  -- No false inference that positive H automatically makes C positive.
  ------------------------------------------------------------------------

  record ADMPhysicalPoint : Set r where
    constructor admPhysicalPoint
    field
      lapse : S
      volumeDensity : S
      inverseLapseSquared : S
      spatialInverse : BR4Space → BR4Space → S
      fourShift : BR4Space → S
  open ADMPhysicalPoint public

  admBR4A : ADMPhysicalPoint → S
  admBR4A g = volumeDensity g * inverseLapseSquared g

  admBR4B : ADMPhysicalPoint → BR4Space → S
  admBR4B g i = admBR4A g * fourShift g i

  admBR4C : ADMPhysicalPoint → BR4Space → BR4Space → S
  admBR4C g i k =
    volumeDensity g * spatialInverse g i k
      - admBR4A g * fourShift g i * fourShift g k

  -- The primitive normal conormal current from the actual divergence
  -- operator contains both the material time velocity and all four
  -- spatial derivative components in general. The old BR34 normal
  -- derivative is only obtained after paying its Gaussian collar.
  admNormalFlux : ADMPhysicalPoint → S → (BR4Space → S) → S
  admNormalFlux g timeVelocity gradient =
    admBR4B g spaceNormal * timeVelocity
      + sumBR4Space (λ i →
          admBR4C g spaceNormal i * gradient i)

  -- BR48 source-preserving Gaussian fixed material collar:
  -- fourShift(n)=0 and H^na=0, H^nn=1; then the ADM conormal
  -- is volumeDensity * partial_n. Instead of an unsound universal
  -- assertion, the equalities below are required as explicit witness
  -- FIELDS on the same physical source.
  record ADMPhysicalNormalCollar (g : ADMPhysicalPoint) : Set r where
    constructor admPhysicalNormalCollar
    field
      normalShiftZero : fourShift g spaceNormal ≡ O
      normalInverseXZero : spatialInverse g spaceNormal spaceX ≡ O
      normalInverseYZero : spatialInverse g spaceNormal spaceY ≡ O
      normalInverseZZero : spatialInverse g spaceNormal spaceZ ≡ O
      normalInverseUnit : spatialInverse g spaceNormal spaceNormal ≡ U

  record BR48FluxMatchingSource : Set r where
    constructor br48FluxMatchingSource
    field
      originalADM : ADMPhysicalPoint
      normalVelocity : S
      fourSpatialJet : BR4Space → S
      conormalFlux : S
      sourceGaussianFlux : S
      uncorrectedMaterialFlux : S
  open BR48FluxMatchingSource public

  constructBR48FluxMatching : ADMPhysicalPoint → S →
    (BR4Space → S) → BR48FluxMatchingSource
  constructBR48FluxMatching g wt dx =
    br48FluxMatchingSource
      g wt dx
      (admNormalFlux g wt dx)
      (volumeDensity g * dx spaceNormal)
      (admNormalFlux g wt dx - volumeDensity g * dx spaceNormal)

  -- At nonzero normal shift or sheared normal spatial inverse, the
  -- residual is intentionally NONZERO. BR19 moving-material graph and
  -- normal-chart weld must consume it before BR41 wall work is asserted
  -- for the true PDE conormal. No inverse or positivity is assumed.

  ------------------------------------------------------------------------
  -- BR49: actual moving-material defining function F=n-f(t,x,y,z).
  -- Its physical conormal is g^(-1)dF. Using ∂n alone is valid ONLY at
  -- the compatible BR48 Gaussian collar. Retain the time/shift/graph
  -- coupling at a general moving Einstein–Israel wall.
  ------------------------------------------------------------------------

  record MaterialGraphGradient : Set r where
    constructor materialGraphGradient
    field
      graphTimeGradient : S
      graphTangentGradient : Wall → S
  open MaterialGraphGradient public

  materialDefiningCovector : MaterialGraphGradient → Cov
  materialDefiningCovector f normal = U
  materialDefiningCovector f (wall t) =
    neg (graphTimeGradient f)
  materialDefiningCovector f (wall x) =
    neg (graphTangentGradient f x)
  materialDefiningCovector f (wall y) =
    neg (graphTangentGradient f y)
  materialDefiningCovector f (wall z) =
    neg (graphTangentGradient f z)

  -- D g^{-1}(dF,du) for the ORIGINAL variable ADM source. Here the
  -- four spatial axes are x,y,z,normal; the wall time covector is
  -- carried separately by graphTimeGradient, never silently set zero.
  materialGraphSpaceNormal : MaterialGraphGradient → BR4Space → S
  materialGraphSpaceNormal f spaceX =
    neg (graphTangentGradient f x)
  materialGraphSpaceNormal f spaceY =
    neg (graphTangentGradient f y)
  materialGraphSpaceNormal f spaceZ =
    neg (graphTangentGradient f z)
  materialGraphSpaceNormal f spaceNormal = U

  -- g^(-1)(dF,dF)=H^ij F_i F_j-(F_t-v^iF_i)^2/N².
  graphAdvectiveTime : ADMPhysicalPoint → MaterialGraphGradient → S
  graphAdvectiveTime g f =
    neg (graphTimeGradient f)
      - sumBR4Space (λ i →
          fourShift g i * materialGraphSpaceNormal f i)

  graphNormSquared : ADMPhysicalPoint → MaterialGraphGradient → S
  graphNormSquared g f =
    sumBR4Space (λ i → sumBR4Space (λ k →
      spatialInverse g i k *
        materialGraphSpaceNormal f i * materialGraphSpaceNormal f k))
      - inverseLapseSquared g *
          graphAdvectiveTime g f * graphAdvectiveTime g f

  -- This raw densitized flux remains meaningful before an explicit
  -- positive graph-normalization certificate is available:
  --
  -- D g^(mu nu) F_mu u_nu =
  -- D [H^ij F_i u_j - N^-2(F_t-v.F)(u_t-v.grad u)].
  materialGraphFlux : ADMPhysicalPoint → MaterialGraphGradient →
    S → (BR4Space → S) → S
  materialGraphFlux g f ut du =
    volumeDensity g *
      (sumBR4Space (λ i → sumBR4Space (λ k →
        spatialInverse g i k * materialGraphSpaceNormal f i * du k))
        - inverseLapseSquared g * graphAdvectiveTime g f *
          (ut - sumBR4Space (λ i → fourShift g i * du i)))

  -- The exact conforming collar is a SPECIAL CASE; the material
  -- mismatch is a first-class source, not set to zero off shell.
  record MaterialConormalMismatch : Set r where
    constructor mkMaterialConormalMismatch
    field
      graphConormalWork : S
      coordinateNormalWork : S
      graphExtraWork : S
      graphSquaredNorm : S
  open MaterialConormalMismatch public

  materialConormalMismatch : ADMPhysicalPoint → MaterialGraphGradient →
    S → (BR4Space → S) → MaterialConormalMismatch
  materialConormalMismatch g f ut du =
    mkMaterialConormalMismatch
      (materialGraphFlux g f ut du)
      (volumeDensity g * du spaceNormal)
      (materialGraphFlux g f ut du
        - volumeDensity g * du spaceNormal)
      (graphNormSquared g f)

  -- A real geometric owner must prove graphNormSquared>0 and supply
  -- its positive square root to normalize the wall normal. This field
  -- cannot inhabit the unproved physical Bianchi or BR37 glancing
  -- certificate by algebraic projection alone.

  ------------------------------------------------------------------------
  -- BR50: same original ADM moving conormal on all 15 metric channels
  -- and five subsidiary channels. This is the physical correction to
  -- BR41's Gaussian-wall normal work, not an independent abstract PDE.
  ------------------------------------------------------------------------

  materialGraphTensorFlux : ADMPhysicalPoint → MaterialGraphGradient →
    Tensor → (BR4Space → Tensor) → Tensor
  materialGraphTensorFlux g f timeJet spatialJet =
    tab (λ i k →
      materialGraphFlux g f (get timeJet i k)
        (λ a → get (spatialJet a) i k))

  materialGraphGaugeFlux : ADMPhysicalPoint → MaterialGraphGradient →
    Cov → (BR4Space → Cov) → Cov
  materialGraphGaugeFlux g f timeJet spatialJet k =
    materialGraphFlux g f (timeJet k)
      (λ a → spatialJet a k)

  -- The two-face normal fields are kept independent, matching the
  -- original plus/minus BR34 Israel allocation and BR29 constraint.
  record OriginalMaterialPower : Set r where
    constructor originalMaterialPower
    field
      plusMovingPower : S
      minusMovingPower : S
      signedMovingPower : S
      gaussianBR41Power : S
      missingGraphPower : S
      plusMetricConormal : Tensor
      minusMetricConormal : Tensor
      plusGaugeConormal : Cov
      minusGaugeConormal : Cov
  open OriginalMaterialPower public

  assembleOriginalMaterialPower :
    ADMPhysicalPoint → ADMPhysicalPoint →
    MaterialGraphGradient → MaterialGraphGradient →
    (Wall → Wall → S) →
    Tensor → Tensor →
    (BR4Space → Tensor) → (BR4Space → Tensor) →
    Cov → Cov →
    (BR4Space → Cov) → (BR4Space → Cov) →
    OriginalMaterialPower
  assembleOriginalMaterialPower gp gm fp fm velocity
    pt mt ps ms ct dt cs ds =
    originalMaterialPower
      (wallPair velocity (H qp))
      (wallPair velocity (H qm))
      (wallPair velocity (λ a b → H qp a b - H qm a b))
      (wallPair velocity (λ a b →
        volumeDensity gp * H (ps spaceNormal) a b
          - volumeDensity gm * H (ms spaceNormal) a b))
      (wallPair velocity (λ a b →
        H qp a b - H qm a b
        - volumeDensity gp * H (ps spaceNormal) a b
        + volumeDensity gm * H (ms spaceNormal) a b))
      qp qm qcg qcm
    where
      qp : Tensor
      qp = materialGraphTensorFlux gp fp pt ps

      qm : Tensor
      qm = materialGraphTensorFlux gm fm mt ms

      qcg : Cov
      qcg = materialGraphGaugeFlux gp fp ct cs

      qcm : Cov
      qcm = materialGraphGaugeFlux gm fm dt ds

  -- For a fixed compatible Gaussian wall each graph correction vanishes
  -- and the conormal work reduces to the volume-weighted BR41 normal
  -- work. In the general moving/sheared chart the graph correction is
  -- an independent signed forcing in BR42/45, not an assumed positive
  -- multiple of the Israel Hessian. Its control needs actual metric
  -- regularity and timelike/spacelike material guard.

  ------------------------------------------------------------------------
  -- BR51: graph error as actual five differentiated physical components.
  -- This isolates the precise geometric factor needed for BR44 tame
  -- absorption; the inequality itself belongs to the REAL positive
  -- Hilbert-space owner, not arbitrary complex-bilinear arithmetic.
  ------------------------------------------------------------------------

  normalSpaceDelta : BR4Space → S
  normalSpaceDelta spaceNormal = U
  normalSpaceDelta spaceX = O
  normalSpaceDelta spaceY = O
  normalSpaceDelta spaceZ = O

  graphDefectTimeCoefficient : ADMPhysicalPoint →
    MaterialGraphGradient → S
  graphDefectTimeCoefficient g f =
    neg (inverseLapseSquared g * graphAdvectiveTime g f)

  graphDefectSpatialCoefficient : ADMPhysicalPoint →
    MaterialGraphGradient → BR4Space → S
  graphDefectSpatialCoefficient g f i =
    sumBR4Space (λ k →
      spatialInverse g k i * materialGraphSpaceNormal f k)
      - normalSpaceDelta i
      + inverseLapseSquared g * graphAdvectiveTime g f * fourShift g i

  scalarGraphDefect : ADMPhysicalPoint → MaterialGraphGradient →
    S → (BR4Space → S) → S
  scalarGraphDefect g f timeVelocity spatialVelocity =
    volumeDensity g *
      (graphDefectTimeCoefficient g f * timeVelocity
      + sumBR4Space (λ i →
          graphDefectSpatialCoefficient g f i * spatialVelocity i))

  record OriginalGraphDefectPayment : Set r where
    constructor mkOriginalGraphDefectPayment
    field
      actualGraphDefect : S
      coefficientResolvedDefect : S
      coefficientResidual : S
      originalTimeCoefficient : S
      originalSpatialCoefficients : BR4Space → S
  open OriginalGraphDefectPayment public

  originalGraphDefectPayment : ADMPhysicalPoint → MaterialGraphGradient →
    S → (BR4Space → S) → OriginalGraphDefectPayment
  originalGraphDefectPayment g f ut du =
    mkOriginalGraphDefectPayment
      (materialGraphFlux g f ut du
        - volumeDensity g * du spaceNormal)
      (scalarGraphDefect g f ut du)
      (materialGraphFlux g f ut du
        - volumeDensity g * du spaceNormal
        - scalarGraphDefect g f ut du)
      (graphDefectTimeCoefficient g f)
      (graphDefectSpatialCoefficient g f)

  -- The physical real-field Cauchy payment is
  -- |J_F-D ∂n u|² <= D² (|k_t|²+sum_i|k_i|²)
  --                         (|u_t|²+sum_i|u_i|²).
  -- It is pointwise and is independent of BR37 frequency/glancing
  -- tame losses; full high-order physical graph/source control remains.
