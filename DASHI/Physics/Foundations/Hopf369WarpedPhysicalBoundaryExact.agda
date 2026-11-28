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
