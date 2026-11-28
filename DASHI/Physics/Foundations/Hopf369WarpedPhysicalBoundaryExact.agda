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

  ------------------------------------------------------------------------
  -- BR52: DIVIDED TAYLOR JET ALGEBRA, all orders, same moving ADM wall.
  --
  -- The coefficients are u^(n)/n!, not raw derivatives: multiplying
  -- divided jets is ordinary Cauchy convolution. This prevents the
  -- combinatorial factor loss that would arise by multiplying BR47's
  -- raw derivative rows without their binomial coefficients.
  --
  -- Original ADM and graph coefficient series must be supplied from
  -- the ACTUAL physical source and its derivatives; this finite complex
  -- ring module cannot invent them.
  ------------------------------------------------------------------------

  DividedJet : Set r
  DividedJet = Nat → S

  splitConvolution : Nat → Nat → DividedJet → DividedJet → S
  splitConvolution zero j f g = f zero * g j
  splitConvolution (suc i) j f g =
    f (suc i) * g j + splitConvolution i (suc j) f g

  jetProduct : DividedJet → DividedJet → DividedJet
  jetProduct f g n = splitConvolution n zero f g

  jetSum : DividedJet → DividedJet → DividedJet
  jetSum f g n = f n + g n

  jetNeg : DividedJet → DividedJet
  jetNeg f n = neg (f n)

  jetScale : S → DividedJet → DividedJet
  jetScale a f n = a * f n

  record OriginalMaterialJetTower : Set r where
    constructor originalMaterialJetTower
    field
      admDensityTaylor : DividedJet
      graphTimeCoefficientTaylor : DividedJet
      graphSpaceCoefficientTaylor : BR4Space → DividedJet
      timeMetricTaylor : Nat → Tensor
      spatialMetricTaylor : BR4Space → Nat → Tensor
      timeGaugeTaylor : Nat → Cov
      spatialGaugeTaylor : BR4Space → Nat → Cov
      originalSourceADM : ADMPhysicalPoint
      originalSourceGraph : MaterialGraphGradient
  open OriginalMaterialJetTower public

  -- Coefficients below are the actual BR51 k_t,k_i, independently
  -- supplied by differentiating the source ADM/graph tensors. At order
  -- zero they must match BR51's primitive exact coefficient; higher
  -- identification is a separate source-jet compatibility proof.
  metricConormalDefectJet : OriginalMaterialJetTower → Nat → Tensor
  metricConormalDefectJet p n =
    tab (λ i j →
      splitConvolution n zero (admDensityTaylor p)
        (jetSum
          (jetProduct
            (graphTimeCoefficientTaylor p)
            (λ k → get (timeMetricTaylor p k) i j))
          (λ k → sumBR4Space (λ a →
            jetProduct (graphSpaceCoefficientTaylor p a)
              (λ l → get (spatialMetricTaylor p a l) i j) k))))

  gaugeConormalDefectJet : OriginalMaterialJetTower → Nat → Cov
  gaugeConormalDefectJet p n a =
    splitConvolution n zero (admDensityTaylor p)
      (jetSum
        (jetProduct (graphTimeCoefficientTaylor p)
          (λ k → timeGaugeTaylor p k a))
        (λ k → sumBR4Space (λ i →
          jetProduct (graphSpaceCoefficientTaylor p i)
            (λ l → spatialGaugeTaylor p i l a) k)))

  record TwoFaceMaterialJetTower : Set r where
    constructor twoFaceMaterialJetTower
    field
      plusMaterialTower minusMaterialTower : OriginalMaterialJetTower
  open TwoFaceMaterialJetTower public

  signedMetricDefectJet : TwoFaceMaterialJetTower → Nat → Tensor
  signedMetricDefectJet p n =
    subT
      (metricConormalDefectJet (plusMaterialTower p) n)
      (metricConormalDefectJet (minusMaterialTower p) n)

  signedGaugeDefectJet : TwoFaceMaterialJetTower → Nat → Cov
  signedGaugeDefectJet p n a =
    gaugeConormalDefectJet (plusMaterialTower p) n a
      - gaugeConormalDefectJet (minusMaterialTower p) n a

  -- The resulting derivative-order n wall source is n! times this
  -- divided coefficient. The ORIGINAL physical BR47 row, normal
  -- value continuity, BR19 material good unknown, and original
  -- BR29 Bianchi constraint are NOT replaced by this product algebra.

  ------------------------------------------------------------------------
  -- BR55: exact FIVE-AXIS source principal Bianchi symbol, sharing the
  -- original 15-component Einstein perturbation with BR45/46.
  --
  -- The reference signature is eta=(-,+,+,+,+), including n. No
  -- characteristic divisor z² is ever inverted; nonzero gauge mode
  -- on z²=0 is explicitly allowed. The underlying 5D contracted
  -- Bianchi / Weitzenböck curvature identity is original geometry,
  -- not a theorem obtained from BR29's finite projected Maxwell model.
  ------------------------------------------------------------------------

  raiseCov : Cov → Cov
  raiseCov z (wall a) = sign a * z (wall a)
  raiseCov z normal = z normal

  trace5 : Tensor → S
  trace5 p = tr p + h44 p

  waveSquare : Cov → S
  waveSquare z = sum5 (λ a → raiseCov z a * z a)

  contractedGaugeSymbol : Cov → Tensor → Cov
  contractedGaugeSymbol z p b =
    sum5 (λ a → raiseCov z a * get p a b)
      - half * z b * trace5 p

  linearRicciSymbol : Cov → Tensor → Tensor
  linearRicciSymbol z p =
    tab (λ a b →
      half *
        (z a * sum5 (λ k → raiseCov z k * get p k b)
        + z b * sum5 (λ k → raiseCov z k * get p k a)
        - waveSquare z * get p a b
        - z a * z b * trace5 p))

  reducedEinsteinRicciSymbol : Cov → Tensor → Tensor
  reducedEinsteinRicciSymbol z p =
    subT (linearRicciSymbol z p)
      (mulT half (tab (λ a b →
        z a * contractedGaugeSymbol z p b
        + z b * contractedGaugeSymbol z p a)))

  traceReverse5 : Tensor → Tensor
  traceReverse5 p =
    tab (λ a b →
      get p a b - half * metric a b * trace5 p)

  contractedTraceReverse5 : Cov → Tensor → Cov
  contractedTraceReverse5 z p a =
    sum5 (λ b → raiseCov z b * get (traceReverse5 p) b a)

  originalBianchiSourceResidual : Cov → Tensor → Cov
  originalBianchiSourceResidual z p a =
    contractedTraceReverse5 z (reducedEinsteinRicciSymbol z p) a
      + half * waveSquare z * contractedGaugeSymbol z p a

  -- The exact mathematical target is
  --   originalBianchiSourceResidual z p a == 0
  -- for all z,p,a, using ring identities. It is PRESENT AS A PROOF
  -- OBLIGATION rather than an untypechecked 'refl' or a postulate.
  record OriginalBianchiPrincipalCertificate
      (z : Cov) (p : Tensor) : Set r where
    constructor originalBianchiPrincipalCertificate
    field
      fiveAxisContractedBianchi :
        (a : Axis) → originalBianchiSourceResidual z p a ≡ O
  open OriginalBianchiPrincipalCertificate public

  -- General reduced metric: retain its actual Ricci action. On the
  -- AdS vacuum reference it specializes to Ric=-4g. Exact identity:
  --   div_g( symgrad C - half * g div C ) = (box_g C + Ric(C))/2.
  -- The extra Ric term and moving Israel Codazzi/Gauss residuals are
  -- not optional and are NOT recovered by the flat principal symbol.
  record PhysicalCurvedBianchiPayment : Set r where
    constructor physicalCurvedBianchiPayment
    field
      originalSourceMetric : ADMPhysicalPoint
      originalGraph : MaterialGraphGradient
      originalPhysicalMetricJets : Tensor
      originalPhysicalGaugeJets : Cov
      variableCurvaturePayment : Cov
      variableConnectionPayment : Cov
      nonlinearHarmonicPayment : Cov
      wallCodazziPayment : Cov
      wallGaussPayment : S
      remainingProjectedBianchi : Cov
  open PhysicalCurvedBianchiPayment public

  -- BR29's rank-nine projected Weyl kernel is a DIFFERENT 35D carrier.
  -- Its original projected-source factor is checked against original
  -- J,A,B,R in BR53. This Cov keeps precisely the five harmonic-gauge
  -- subsidiary sources; do not silently equate rank-five and rank-nine.

  ------------------------------------------------------------------------
  -- BR57: BS13 original ELECTRIC NORMAL CURVATURE transport.
  --
  -- E = -(b² S)'/b²+2 Q/b⁴. If p=b²S then
  -- p'=-b² E +2 Q/b². Both endpoints and the full original
  -- holonomy moment M=Int p remain independent; the primitive
  -- C=(M-Int_0^L (L-x)F(x)dx)/L is fixed by M.
  --
  -- The real analytic normal primitive and positive b²>=m>0
  -- are external proof-bearing data. There is no unjustified inverse
  -- of a 5D curvature tensor nor projection of BS13 kernel modes.
  ------------------------------------------------------------------------

  record ElectricNormalPrimitive : Set r where
    constructor electricNormalPrimitive
    field
      warpSquaredAtStart : S
      warpSquaredAtEnd : S
      positiveWarpLower : S
      physicalNormalLength : S
      integratedNormalElectricSource : S
      integratedMomentOfSource : S
      originalNormalHolonomyMoment : S
      reciprocalNormalLength : S
      reconstructedNormalConstant : S
  open ElectricNormalPrimitive public

  bs13NormalConstant : ElectricNormalPrimitive → S
  bs13NormalConstant d =
    reciprocalNormalLength d *
      (originalNormalHolonomyMoment d
        - integratedMomentOfSource d)

  -- For each original 4x4 electric curvature coordinate, keep the
  -- same physical source and all 16 components. The symmetric,
  -- trace-reduced constraints of BS13 remain independently enforced.
  record ElectricNormalShearTransport : Set r where
    constructor electricNormalShearTransport
    field
      normalShearStart : Wall → Wall → S
      normalShearEnd : Wall → Wall → S
      normalElectricSource : Wall → Wall → S
      normalQSource : Wall → Wall → S
      sourceHolonomy : Wall → Wall → S
      unallocatedWeightedQuotient : Wall → Wall → S
  open ElectricNormalShearTransport public

  ------------------------------------------------------------------------
  -- BR58: all-order ACTUAL D/E physical boundary operator receives the
  -- BR52 material conormal jets through its true normal derivative
  -- columns; background j/q Taylor coefficients remain independent.
  ------------------------------------------------------------------------

  zeroTensor : Tensor
  zeroTensor = tab (λ _ _ → O)

  zeroCov : Cov
  zeroCov _ = O

  record OriginalPhysicalReferenceTower : Set r where
    constructor originalPhysicalReferenceTower
    field
      backgroundIsraelTaylor : DividedJet
      backgroundFrequencyTaylor : Wall → DividedJet
      plusMetricValueTaylor plusMetricNormalTaylor : Nat → Tensor
      minusMetricValueTaylor minusMetricNormalTaylor : Nat → Tensor
      plusGaugeValueTaylor plusGaugeNormalTaylor : Nat → Cov
      minusGaugeValueTaylor minusGaugeNormalTaylor : Nat → Cov
      sourceMaterialTower : TwoFaceMaterialJetTower
  open OriginalPhysicalReferenceTower public

  towerFrequency : OriginalPhysicalReferenceTower → Nat → Vec
  towerFrequency t n a = backgroundFrequencyTaylor t a n

  metricReferenceAt : Allocation → OriginalPhysicalReferenceTower →
    Nat → List S
  metricReferenceAt a t n =
    metricRows a (backgroundIsraelTaylor t zero)
      (towerFrequency t zero)
      (plusMetricValueTaylor t n)
      (plusMetricNormalTaylor t n)
      (minusMetricValueTaylor t n)
      (minusMetricNormalTaylor t n)

  gaugeReferenceAt : Allocation → OriginalPhysicalReferenceTower →
    Nat → List S
  gaugeReferenceAt a t n =
    gaugeRows a (backgroundIsraelTaylor t zero)
      (towerFrequency t zero)
      (plusGaugeValueTaylor t n)
      (plusGaugeNormalTaylor t n)
      (minusGaugeValueTaylor t n)
      (minusGaugeNormalTaylor t n)

  -- The actual BR34 normal-derivative columns do not contain j or q.
  -- A moving material graph therefore enters by these same columns.
  -- This is reference *linearisation* only: the BR19 nonlinear normal
  -- and shape derivative remain separate original physical sources.
  metricMaterialCorrectionAt : Allocation →
    OriginalPhysicalReferenceTower → Nat → List S
  metricMaterialCorrectionAt a t n =
    metricRows a O zeroQ
      zeroTensor
      (metricConormalDefectJet (plusMaterialTower (sourceMaterialTower t)) n)
      zeroTensor
      (metricConormalDefectJet (minusMaterialTower (sourceMaterialTower t)) n)

  gaugeMaterialCorrectionAt : Allocation →
    OriginalPhysicalReferenceTower → Nat → List S
  gaugeMaterialCorrectionAt a t n =
    gaugeRows a O zeroQ
      zeroCov
      (gaugeConormalDefectJet (plusMaterialTower (sourceMaterialTower t)) n)
      zeroCov
      (gaugeConormalDefectJet (minusMaterialTower (sourceMaterialTower t)) n)

  -- Each Taylor order r also contains background derivative terms
  -- deltaB(j_k,q_k;U_(r-k)), k=1..r. The zero-frequency base is kept
  -- independent; this explicitly exposes every source payment to the
  -- BR47/58 summation rather than postulating a tame bound.
  metricBackgroundJetSource : Allocation →
    OriginalPhysicalReferenceTower → Nat → Nat → List S
  metricBackgroundJetSource a t coefficientOrder fieldOrder =
    rowSub
      (metricRows a
        (backgroundIsraelTaylor t coefficientOrder)
        (towerFrequency t coefficientOrder)
        (plusMetricValueTaylor t fieldOrder)
        (plusMetricNormalTaylor t fieldOrder)
        (minusMetricValueTaylor t fieldOrder)
        (minusMetricNormalTaylor t fieldOrder))
      (metricRows a O zeroQ
        (plusMetricValueTaylor t fieldOrder)
        (plusMetricNormalTaylor t fieldOrder)
        (minusMetricValueTaylor t fieldOrder)
        (minusMetricNormalTaylor t fieldOrder))

  gaugeBackgroundJetSource : Allocation →
    OriginalPhysicalReferenceTower → Nat → Nat → List S
  gaugeBackgroundJetSource a t coefficientOrder fieldOrder =
    rowSub
      (gaugeRows a
        (backgroundIsraelTaylor t coefficientOrder)
        (towerFrequency t coefficientOrder)
        (plusGaugeValueTaylor t fieldOrder)
        (plusGaugeNormalTaylor t fieldOrder)
        (minusGaugeValueTaylor t fieldOrder)
        (minusGaugeNormalTaylor t fieldOrder))
      (gaugeRows a O zeroQ
        (plusGaugeValueTaylor t fieldOrder)
        (plusGaugeNormalTaylor t fieldOrder)
        (minusGaugeValueTaylor t fieldOrder)
        (minusGaugeNormalTaylor t fieldOrder))

  -- Source compatibility is crucial: the normal Taylor jet on BR34
  -- must be the same normal derivative as in BR52's ADM field jet.
  -- The original source needs to inhabit these exact equalities; a
  -- free-record assembly cannot manufacture a physical solution.
  record PhysicalReferenceJetCompatibility
      (t : OriginalPhysicalReferenceTower) : Set r where
    constructor physicalReferenceJetCompatibility
    field
      plusMetricNormalOwnership :
        plusMetricNormalTaylor t zero ≡
          spatialMetricTaylor (plusMaterialTower (sourceMaterialTower t))
            spaceNormal zero
      minusMetricNormalOwnership :
        minusMetricNormalTaylor t zero ≡
          spatialMetricTaylor (minusMaterialTower (sourceMaterialTower t))
            spaceNormal zero
      plusGaugeNormalOwnership :
        plusGaugeNormalTaylor t zero ≡
          spatialGaugeTaylor (plusMaterialTower (sourceMaterialTower t))
            spaceNormal zero
      minusGaugeNormalOwnership :
        minusGaugeNormalTaylor t zero ≡
          spatialGaugeTaylor (minusMaterialTower (sourceMaterialTower t))
            spaceNormal zero
  open PhysicalReferenceJetCompatibility public

  -- The original source checked by BR58 must also identify the
  -- time-derivative and mixed-tangential jets of BR52 with the physical
  -- field, the curvature Bianchi source of BR55 with BR29's actual
  -- rank-nine projected wall graph, and preserve BR31's weighted domain.

  ------------------------------------------------------------------------
  -- BR52/58: native kernel-targeted low-order SPLIT identities.
  -- These use definitional reduction of the exact divided-Taylor
  -- recurrence, not an unchecked commutative-ring rewrite or postulate.
  -- Higher-order coefficients are constructed by the same recursion;
  -- analytic derivative/normal trace identities are separate.
  ------------------------------------------------------------------------

  jetProductAtZero : (f g : DividedJet) →
    jetProduct f g zero ≡ f zero * g zero
  jetProductAtZero f g = refl

  jetProductAtOne : (f g : DividedJet) →
    jetProduct f g (suc zero) ≡
      f (suc zero) * g zero + f zero * g (suc zero)
  jetProductAtOne f g = refl

  jetProductAtTwo : (f g : DividedJet) →
    jetProduct f g (suc (suc zero)) ≡
      f (suc (suc zero)) * g zero
        + (f (suc zero) * g (suc zero)
           + f zero * g (suc (suc zero)))
  jetProductAtTwo f g = refl

  -- Keep order-zero source ownership explicit. By reduction, the
  -- stored normal BR34 jet and the source ADM normal derivative are
  -- *identical* whenever the source supplies this indexed witness.
  originalPlusMetricNormalOwnership :
    (t : OriginalPhysicalReferenceTower) →
    PhysicalReferenceJetCompatibility t →
    plusMetricNormalTaylor t zero ≡
      spatialMetricTaylor (plusMaterialTower (sourceMaterialTower t))
        spaceNormal zero
  originalPlusMetricNormalOwnership t compat =
    plusMetricNormalOwnership compat

  originalMinusGaugeNormalOwnership :
    (t : OriginalPhysicalReferenceTower) →
    PhysicalReferenceJetCompatibility t →
    minusGaugeNormalTaylor t zero ≡
      spatialGaugeTaylor (minusMaterialTower (sourceMaterialTower t))
        spaceNormal zero
  originalMinusGaugeNormalOwnership t compat =
    minusGaugeNormalOwnership compat

  -- These are actual source-level Agda proof bodies. They do NOT
  -- discharge the pending variable-Bianchi kernel acceptance, the
  -- positive weighted physical energy norms, or nonlinear existence.

  ------------------------------------------------------------------------
  -- BR59–61: the ACTUAL nonlinear unit-normal moving Israel wall,
  -- not simply its Gaussian-reference derivative/conormal columns.
  --
  -- At original Gaussian g0=dn²+b²eta, b(0)=1, k=b'(0):
  -- delta h_ab = p_ab + 2k phi eta_ab.
  -- delta K_ab = -phi_ab + (k²+b''(0))phi eta_ab
  --              + 1/2 p_ab,n -1/2(∂a p_nb+∂b p_na)
  --              -1/2 k p_nn eta_ab.
  -- All ten original symmetric wall rows and both material sides stay.
  -- Their distinct p_nn normalisation and graph Hessians cannot be
  -- projected away by the linear BR34 reference normal derivative.
  ------------------------------------------------------------------------

  record OriginalMovingShapeData : Set r where
    constructor originalMovingShapeData
    field
      sourceReferenceWarpK : S
      sourceReferenceWarpSecond : S
      sourceGraphDisplacement : S
      sourceGraphHessian : Wall → Wall → S
      sourceMetricPerturbation : Tensor
      sourceMetricNormalDerivative : Tensor
      sourceMixedTangentDerivative : Wall → Wall → S
  open OriginalMovingShapeData public

  originalInducedVariation : OriginalMovingShapeData →
    Wall → Wall → S
  originalInducedVariation d a b =
    H (sourceMetricPerturbation d) a b
      + two * sourceReferenceWarpK d
        * sourceGraphDisplacement d * eta a b

  originalExtrinsicVariation : OriginalMovingShapeData →
    Wall → Wall → S
  originalExtrinsicVariation d a b =
    neg (sourceGraphHessian d a b)
      + (sourceReferenceWarpK d * sourceReferenceWarpK d
         + sourceReferenceWarpSecond d)
          * sourceGraphDisplacement d * eta a b
      + half * H (sourceMetricNormalDerivative d) a b
      - half * (sourceMixedTangentDerivative d a b
                 + sourceMixedTangentDerivative d b a)
      - half * sourceReferenceWarpK d
          * h44 (sourceMetricPerturbation d) * eta a b

  record TwoFaceMovingIsraelSource : Set r where
    constructor twoFaceMovingIsraelSource
    field
      plusMovingShape : OriginalMovingShapeData
      minusMovingShape : OriginalMovingShapeData
      originalIsraelJump : S
      derivativeIsraelJump : S
  open TwoFaceMovingIsraelSource public

  originalShapeJump : TwoFaceMovingIsraelSource → Wall → Wall → S
  originalShapeJump d a b =
    originalExtrinsicVariation (plusMovingShape d) a b
      - originalExtrinsicVariation (minusMovingShape d) a b

  -- Full non-linear Israel trace-reversed jump:
  -- I_ab=[K_ab]-h_ab tr_h[K]+3j h_ab.
  -- Its first variation contains both delta h and 3 delta j.
  -- Source matching is required below; an unmatched two-chart pair
  -- must NOT be treated as a single Israel hypersurface.
  originalIsraelShapeFrechet : TwoFaceMovingIsraelSource →
    Wall → Wall → S
  originalIsraelShapeFrechet d a b =
    originalShapeJump d a b
      - eta a b * trace4 (originalShapeJump d)
      - originalIsraelJump d *
          (originalInducedVariation (plusMovingShape d) a b
            - eta a b *
                trace4 (originalInducedVariation (plusMovingShape d)))
      + three * derivativeIsraelJump d * eta a b

  record OriginalTwoFaceShapeCompatibility
      (d : TwoFaceMovingIsraelSource) : Set r where
    constructor originalTwoFaceShapeCompatibility
    field
      inducedWallMatched :
        (a b : Wall) →
          originalInducedVariation (plusMovingShape d) a b ≡
          originalInducedVariation (minusMovingShape d) a b
      originalWarpJump :
          sourceReferenceWarpK (plusMovingShape d) ≡
          sourceReferenceWarpK (minusMovingShape d) + originalIsraelJump d
      sameGraphDisplacement :
          sourceGraphDisplacement (plusMovingShape d) ≡
          sourceGraphDisplacement (minusMovingShape d)
      sameGraphHessian :
        (a b : Wall) →
          sourceGraphHessian (plusMovingShape d) a b ≡
          sourceGraphHessian (minusMovingShape d) a b
  open OriginalTwoFaceShapeCompatibility public

  -- The actual nonlinear boundary source is now split into its
  -- original BR61 full 10-row geometric Israel variation, BR58 30/10
  -- reference D/E linearized derivative rows and the independent
  -- BR19/31 graph/corner/covariant connection compatibility.
  record FullMovingJunctionWeld : Set r where
    constructor fullMovingJunctionWeld
    field
      originalTwoFaceShape : TwoFaceMovingIsraelSource
      originalPhysicalReference : OriginalPhysicalReferenceTower
      nonlinearShapeIsraelRows : List S
      opticalReferenceMetricD opticalReferenceMetricE : List S
      opticalReferenceGaugeD opticalReferenceGaugeE : List S
      materialMetricD materialMetricE : List S
      materialGaugeD materialGaugeE : List S
      geometricWallSourceRemainder : List S
  open FullMovingJunctionWeld public

  assembleFullMovingJunction : TwoFaceMovingIsraelSource →
    OriginalPhysicalReferenceTower → FullMovingJunctionWeld
  assembleFullMovingJunction shape t =
    fullMovingJunctionWeld
      shape t (pack10 (originalIsraelShapeFrechet shape))
      (metricReferenceAt D t zero) (metricReferenceAt E t zero)
      (gaugeReferenceAt D t zero) (gaugeReferenceAt E t zero)
      (metricMaterialCorrectionAt D t zero)
      (metricMaterialCorrectionAt E t zero)
      (gaugeMaterialCorrectionAt D t zero)
      (gaugeMaterialCorrectionAt E t zero)
      (pack10 (originalIsraelShapeFrechet shape))

  -- The nonzero full-shape source is deliberate: until the actual
  -- BR34 reference Israel block is shown to equal this BR61 Fréchet
  -- after physical graph, gauge, coordinate, density and normal
  -- transport, it cannot be labelled a solved boundary condition.

  ------------------------------------------------------------------------
  -- BR62: ORIGINAL ten Israel rows -> FOUR wall Codazzi source slots.
  --
  -- For physical tangential covector q, the signed wall constraint is
  -- D_q(T)_b = q^a T_ab - q_b trace_eta(T).
  -- At q !=0 this is a rank-four map Sym²(R^4)->R^4, leaving SIX
  -- original shear/trace degrees; for q=0 it is rank zero.
  -- BR62's exact rational source checker supplies both null q²=0
  -- and non-null reverse solves, WITHOUT any inverse of q².
  ------------------------------------------------------------------------

  originalIsraelCodazziSymbol : Vec →
    (Wall → Wall → S) → Vec
  originalIsraelCodazziSymbol q j b =
    sum4 (λ a → sign a * q a * j a b)
       - q b * trace4 j

  record OriginalCodazziWallSource : Set r where
    constructor originalCodazziWallSource
    field
      originalTensorSource : Wall → Wall → S
      originalTangentialFrequency : Vec
      originalIsraelGradient : Vec
      originalRicciNormalJump : Vec
      originalConnectionCorrection : Vec
      unpaidCodazziResidual : Vec
  open OriginalCodazziWallSource public

  originalCodazziSourceResidual : OriginalCodazziWallSource → Vec
  originalCodazziSourceResidual d b =
    originalIsraelCodazziSymbol
      (originalTangentialFrequency d)
      (originalTensorSource d) b
      - three * originalIsraelGradient d b
      - originalRicciNormalJump d b
      - originalConnectionCorrection d b

  record OriginalCodazziFactorizationCertificate
      (d : OriginalCodazziWallSource) : Set r where
    constructor originalCodazziFactorizationCertificate
    field
      allFourWallSources :
        (b : Wall) → originalCodazziSourceResidual d b ≡ O
  open OriginalCodazziFactorizationCertificate public

  -- This source owner has no false rank-four claim at q=0:
  -- a certified inverse must choose a NONZERO coordinate of q,
  -- or explicitly retain the independent zero-frequency constraint.
  record OriginalNonzeroTangentialPivot (q : Vec) : Set r where
    constructor originalNonzeroTangentialPivot
    field
      pivot : Wall
      pivotReciprocal : Reciprocal (q pivot)
  open OriginalNonzeroTangentialPivot public

  record OriginalIsraelCodazziRightInverse
      (q target : Vec) : Set r where
    constructor originalIsraelCodazziRightInverse
    field
      actualTenWallSource : Wall → Wall → S
      sourceSymmetric :
        (a b : Wall) →
          actualTenWallSource a b ≡ actualTenWallSource b a
      fourSourceRightInverse :
        (b : Wall) →
          originalIsraelCodazziSymbol q actualTenWallSource b ≡ target b
  open OriginalIsraelCodazziRightInverse public

  -- At nonzero frequency the actual 10-row Israel system has four
  -- constrained Codazzi directions and six free physical wall
  -- directions. Existence is NOT proved by this record: it requires
  -- a right-inverse constructor, source-specific Bianchi factorization
  -- and compatible BR58/BR61 metric, gauge and graph jets.

  ------------------------------------------------------------------------
  -- BR63: FREQUENCY-FREE full nonlinear Israel trace-reversal inverse.
  --
  -- For an arbitrary compatible 4D induced metric h with true inverse,
  -- tr_h(K) = h^ab K_ab,
  -- I = [K]-h tr_h[K]+3j h.
  -- Set J=I-3j h. In FOUR wall dimensions,
  -- [K] = J-(1/3)h tr_h(J), without dividing by a Fourier q².
  --
  -- Original eta-index formula is a special case only. General moving
  -- walls use the same induced metric on both sides, as in BR61.
  ------------------------------------------------------------------------

  record ActualInducedWallInverse : Set r where
    constructor actualInducedWallInverse
    field
      inducedMetric : Wall → Wall → S
      inverseInducedMetric : Wall → Wall → S
      inducedLeftUnit :
        (a b : Wall) →
          sum4 (λ k → inverseInducedMetric a k * inducedMetric k b)
            ≡ delta (wall a) (wall b)
      inducedRightUnit :
        (a b : Wall) →
          sum4 (λ k → inducedMetric a k * inverseInducedMetric k b)
            ≡ delta (wall a) (wall b)
  open ActualInducedWallInverse public

  inducedTensorTrace : ActualInducedWallInverse →
    (Wall → Wall → S) → S
  inducedTensorTrace h j =
    sum4 (λ a → sum4 (λ b →
      inverseInducedMetric h a b * j b a))

  physicalIsraelTensor : ActualInducedWallInverse → S →
    (Wall → Wall → S) → Wall → Wall → S
  physicalIsraelTensor h j jump a b =
    jump a b
      - inducedMetric h a b * inducedTensorTrace h jump
      + three * j * inducedMetric h a b

  physicalIsraelInverse : ActualInducedWallInverse → S →
    (Wall → Wall → S) → Wall → Wall → S
  physicalIsraelInverse h j physicalJunction a b =
    (physicalJunction a b - three * j * inducedMetric h a b)
      - third * inducedMetric h a b *
          inducedTensorTrace h
            (λ x y →
              physicalJunction x y - three * j * inducedMetric h x y)

  record PhysicalFullIsraelInverseCertificate
      (h : ActualInducedWallInverse) (j : S)
      (junction : Wall → Wall → S) : Set r where
    constructor physicalFullIsraelInverseCertificate
    field
      actualNonlinearTraceReverse :
        (a b : Wall) →
          physicalIsraelTensor h j
            (physicalIsraelInverse h j junction) a b ≡ junction a b
      noDiscardedSymmetricModes :
        (a b : Wall) →
          physicalIsraelInverse h j junction a b
            ≡ physicalIsraelInverse h j junction b a
  open PhysicalFullIsraelInverseCertificate public

  -- BR62 still imposes FOUR physical Codazzi source equations on this
  -- ten-component geometric inverse. Inverting trace-reversal is NOT
  -- equivalent to solving the Einstein reduced boundary evolution.
  --
  -- The constructive rank-four right inverse of BR62 must be attached
  -- to a nonzero q pivot (NEVER q²), and the q=0 source compatibility
  -- survives independently. The full wall metric inverse here needs
  -- its ACTUAL positive/timelike physical chart proofs.

  ------------------------------------------------------------------------
  -- BR64: FULL ISRAEL FRECHET ↔ BR34 GEOMETRIC REFERENCE TEN ROWS.
  --
  -- With original two-face matching, R_ab=2[delta K_ab]-2j delta h_ab.
  -- The full nonlinear Israel shell derivative is exactly
  --   delta I=1/2 (R-eta tr_eta R)+3(delta j)eta.
  -- The bidirectional inverse (FOUR tangential dimensions) is
  --   R=2{delta I-3(delta j)eta
  --             -(1/3)eta tr_eta(delta I-3(delta j)eta)}.
  -- No frequency, zero-mode, glancing root or rank-nine projection
  -- appears in this finite geometric reversal.
  --
  -- The original BR34 10-row *reference operator* must still be
  -- identified with this R by the BR19/48/59 physical shape/coordinate
  -- and BR14 optical normalisation. That comparison is not automatic.
  ------------------------------------------------------------------------

  originalGeometricIsraelRows : TwoFaceMovingIsraelSource →
    Wall → Wall → S
  originalGeometricIsraelRows d a b =
    two * originalShapeJump d a b
      - two * originalIsraelJump d *
          originalInducedVariation (plusMovingShape d) a b

  originalTraceReverseFour :
    (Wall → Wall → S) → Wall → Wall → S
  originalTraceReverseFour p a b =
    p a b - eta a b * trace4 p

  originalTraceUnreverseFour :
    (Wall → Wall → S) → Wall → Wall → S
  originalTraceUnreverseFour p a b =
    p a b - third * eta a b * trace4 p

  originalFullShapeFromReference : TwoFaceMovingIsraelSource →
    Wall → Wall → S
  originalFullShapeFromReference d a b =
    half * originalTraceReverseFour (originalGeometricIsraelRows d) a b
      + three * derivativeIsraelJump d * eta a b

  originalReferenceFromFullShape : TwoFaceMovingIsraelSource →
    Wall → Wall → S
  originalReferenceFromFullShape d a b =
    two * originalTraceUnreverseFour
      (λ i k →
        originalIsraelShapeFrechet d i k
          - three * derivativeIsraelJump d * eta i k) a b

  record OriginalFullIsraelBidirectionalWeld
      (d : TwoFaceMovingIsraelSource) : Set r where
    constructor originalFullIsraelBidirectionalWeld
    field
      actualInducedAndGraphCompatible :
        OriginalTwoFaceShapeCompatibility d
      physicalToGeometricReference :
        (a b : Wall) →
          originalFullShapeFromReference d a b ≡
            originalIsraelShapeFrechet d a b
      geometricReferenceFromPhysical :
        (a b : Wall) →
          originalReferenceFromFullShape d a b ≡
            originalGeometricIsraelRows d a b
  open OriginalFullIsraelBidirectionalWeld public

  -- This is the exact remaining source-specific bridge to the native
  -- BR34 ten-row Israel block. Prove the BR14 optical jet/BR19 graph
  -- change-of-variables and the equality of the geometric ten rows
  -- to metricRows' original Israel indices. The freestanding record
  -- does not manufacture the two reverse proofs or a PDE solution.

  ------------------------------------------------------------------------
  -- BR65: exact ORIGINAL BR34 reference-Israel vs BR60/61 nonlinear
  -- geometric Israel under the SAME matched induced wall.
  --
  -- Given raw physical metric derivative
  --   (p_ab)'_physical = (px_ab)_BR34+2k p_ab,
  -- source tangent derivative d_a p_nb=q_a beta_b, and matched
  -- induced delta h_ab=H+_ab+2k+ phi eta_ab
  --                    =H-_ab+2k- phi eta_ab,
  -- k+ - k-=j, the true moving geometric reference R satisfies
  --
  --   R_ab = original BR34 israel_ab
  --          +2 (b+''(0)-b-''(0)) phi eta_ab.
  --
  -- It is INCORRECT to claim that original BR34 Israel is the true
  -- moving shape reference without paying this warp acceleration,
  -- and matching the induced metric. Both D/E metricRows share the
  -- SAME underlying ten Israel entries.
  ------------------------------------------------------------------------

  originalWarpSecondJump : TwoFaceMovingIsraelSource → S
  originalWarpSecondJump d =
    sourceReferenceWarpSecond (plusMovingShape d)
      - sourceReferenceWarpSecond (minusMovingShape d)

  originalBR65ShapePayment : TwoFaceMovingIsraelSource →
    Wall → Wall → S
  originalBR65ShapePayment d a b =
    two * originalWarpSecondJump d
      * sourceGraphDisplacement (plusMovingShape d) * eta a b

  originalBR65OpticalGeometryResidual : TwoFaceMovingIsraelSource →
    S → Vec → Tensor → Tensor → Tensor → Tensor →
    Wall → Wall → S
  originalBR65OpticalGeometryResidual d j q p px m mx a b =
    originalGeometricIsraelRows d a b
      - israel j q p px m mx a b
      - originalBR65ShapePayment d a b

  record OriginalBR65SourceCompatibility
    (d : TwoFaceMovingIsraelSource)
    (j : S) (q : Vec)
    (p px m mx : Tensor) : Set r where
    constructor originalBR65SourceCompatibility
    field
      physicalWallMatch : OriginalTwoFaceShapeCompatibility d
      originalReferenceJumpAgreement :
        originalIsraelJump d ≡ j
      physicalInducedReferenceMatch :
        (a b : Wall) →
          H p a b
            + two * sourceReferenceWarpK (plusMovingShape d)
                * sourceGraphDisplacement (plusMovingShape d)
                * eta a b
            ≡ H m a b
            + two * sourceReferenceWarpK (minusMovingShape d)
                * sourceGraphDisplacement (minusMovingShape d)
                * eta a b
      fullGeometricReferenceFromOriginalBR34 :
        (a b : Wall) →
          originalBR65OpticalGeometryResidual
            d j q p px m mx a b ≡ O
  open OriginalBR65SourceCompatibility public

  -- The certificate is not constructed from arbitrary free inputs.
  -- It requires the actual raw-to-optical derivative ownership,
  -- compatible tangential Fourier jets, physical shape, and source
  -- b'' on both sides. It also avoids silently claiming b+''=b-''.
  originalBR65FullIsraelFromBR34 :
    (d : TwoFaceMovingIsraelSource) →
    S → Vec → Tensor → Tensor → Tensor → Tensor →
    Wall → Wall → S
  originalBR65FullIsraelFromBR34 d j q p px m mx a b =
    half * originalTraceReverseFour
      (λ i k → israel j q p px m mx i k
        + originalBR65ShapePayment d i k) a b
      + three * derivativeIsraelJump d * eta a b

  -- The target equality of this formula with
  -- originalIsraelShapeFrechet d is an exact, source-dependent
  -- theorem once OriginalBR65SourceCompatibility is inhabited.
  -- The independent reference D/E gauge and mean force rows are not
  -- derived from this ten-component Israel identity.

  ------------------------------------------------------------------------
  -- BR66: NONZERO MEAN-curvature correction to BR65 BR34 source owner.
  --
  -- k+=m+j/2, k-=m-j/2. When the BR34 metric normal reference
  -- derivative is used on either side, the true physical delta K
  -- also has m H in its raw-normal pullback. Matching delta h on
  -- the same material graph gives H-=H++2j phi eta.
  --
  -- Thus R_full - J_BR34 =
  --    2(b+''-b-''-2m j) phi eta,
  -- not just the BR65 mean-free warp-acceleration term.
  --
  -- The nonzero mean is a physical background value, not a wall
  -- Fourier frequency. No characteristic divider appears.
  ------------------------------------------------------------------------

  record OriginalBR66MeanSource : Set r where
    constructor originalBR66MeanSource
    field
      fullTwoFaceShape : TwoFaceMovingIsraelSource
      originalMeanExtrinsic : S
      originalReferenceIsraelJump : S
      originalTangentialJet : Vec
      originalPlusMetric originalPlusNormal : Tensor
      originalMinusMetric originalMinusNormal : Tensor
  open OriginalBR66MeanSource public

  originalBR66MeanShapePayment : OriginalBR66MeanSource →
    Wall → Wall → S
  originalBR66MeanShapePayment d a b =
    two *
      (originalWarpSecondJump (fullTwoFaceShape d)
       - two * originalMeanExtrinsic d * originalReferenceIsraelJump d)
      * sourceGraphDisplacement
          (plusMovingShape (fullTwoFaceShape d)) * eta a b

  originalBR66SameSourceResidual : OriginalBR66MeanSource →
    Wall → Wall → S
  originalBR66SameSourceResidual d a b =
    originalGeometricIsraelRows (fullTwoFaceShape d) a b
      - israel (originalReferenceIsraelJump d)
          (originalTangentialJet d)
          (originalPlusMetric d) (originalPlusNormal d)
          (originalMinusMetric d) (originalMinusNormal d) a b
      - originalBR66MeanShapePayment d a b

  record OriginalBR66SourceEquality
      (d : OriginalBR66MeanSource) : Set r where
    constructor originalBR66SourceEquality
    field
      originalMeanJumpCompatible :
        sourceReferenceWarpK
          (plusMovingShape (fullTwoFaceShape d))
          ≡ originalMeanExtrinsic d
             + half * originalReferenceIsraelJump d
      originalMeanMinusCompatible :
        sourceReferenceWarpK
          (minusMovingShape (fullTwoFaceShape d))
          ≡ originalMeanExtrinsic d
             - half * originalReferenceIsraelJump d
      actualGraphMatched :
        OriginalTwoFaceShapeCompatibility (fullTwoFaceShape d)
      originalBR34ToFullPhysicalIsrael :
        (a b : Wall) → originalBR66SameSourceResidual d a b ≡ O
  open OriginalBR66SourceEquality public

  -- BR66's nonzero mean term must enter the BR41/44 signed wall work
  -- and the BR29 variable projected Bianchi connection source.
  -- Equality is a physical source-specific target, NOT a postulate or
  -- a declaration that the required background jets already match.

  ------------------------------------------------------------------------
  -- BR67: EIGHTH-ORDER NONZERO MEAN + SECOND-WARP SOURCE via BR52's
  -- existing DIVIDED jets (no duplicate Taylor machinery).
  --
  -- The exact BR66 physical correction at each time is
  --   T=2[(b+''-b-'')-2m*j] phi eta.
  -- At order n the coefficient is a triple Leibniz convolution,
  -- with arbitrary independent b'',m,j,phi jets. The original
  -- metricRows D/E Israel entries must receive this physical source.
  ------------------------------------------------------------------------

  record OriginalBR67EvolvingWallSource : Set r where
    constructor originalBR67EvolvingWallSource
    field
      evolvingPlusWarpAcceleration : DividedJet
      evolvingMinusWarpAcceleration : DividedJet
      evolvingMeanExtrinsic : DividedJet
      evolvingIsraelJump : DividedJet
      evolvingMaterialDisplacement : DividedJet
  open OriginalBR67EvolvingWallSource public

  originalBR67SecondWarpJump : OriginalBR67EvolvingWallSource →
    DividedJet
  originalBR67SecondWarpJump d n =
    evolvingPlusWarpAcceleration d n
      - evolvingMinusWarpAcceleration d n

  originalBR67CorrectionJet : OriginalBR67EvolvingWallSource →
    DividedJet
  originalBR67CorrectionJet d =
    jetScale two
      (jetProduct
        (λ n → originalBR67SecondWarpJump d n
          - two * jetProduct
              (evolvingMeanExtrinsic d) (evolvingIsraelJump d) n)
        (evolvingMaterialDisplacement d))

  originalBR67TenGeometricRows : OriginalBR67EvolvingWallSource →
    Nat → List S
  originalBR67TenGeometricRows d n =
    pack10 (λ a b → originalBR67CorrectionJet d n * eta a b)

  record OriginalBR67WallTimeCompatibility : Set r where
    constructor originalBR67WallTimeCompatibility
    field
      physicalReference : OriginalPhysicalReferenceTower
      actualEvolvingSource : OriginalBR67EvolvingWallSource
      fullMovingGeometricRows : Nat → Wall → Wall → S
      physicalBR34IsraelRows : Nat → Wall → Wall → S
      allOrderSourceEquality :
        (n : Nat) (a b : Wall) →
          fullMovingGeometricRows n a b ≡
          physicalBR34IsraelRows n a b
            + originalBR67CorrectionJet actualEvolvingSource n * eta a b
  open OriginalBR67WallTimeCompatibility public

  -- This record spells out the ENTIRE missing physical source equality,
  -- rather than assuming BR34's frozen ten-row Israel block is the
  -- nonlinear moving-wall source at nonzero mean. The kernel must
  -- verify all-order product proofs and actual source ownership before
  -- treating it as a proof of an evolving Einstein–Israel boundary.

  ------------------------------------------------------------------------
  -- BR68: actual BR34 nonzero-MEAN coordinate Codazzi and metric force.
  -- Reuse exact reference gaugeCodazzi, gaugeGauss, meanForce and
  -- distinct D/E prefixes. The general coordinate Codazzi differs
  -- from the reference parallel-frame form by the original mean M
  -- and HALF-jump terms; do not double count them.
  ------------------------------------------------------------------------

  originalBR68GaugeCorrection : S → (Wall → Wall → S) →
    Cov → Cov → Vec
  originalBR68GaugeCorrection j M p m a =
    neg (two * sum4 (λ b →
      M a b * sign b * (p (wall b) - m (wall b))))
      - half * j * (p (wall a) + m (wall a))

  originalBR68PhysicalGaugeCodazzi : S → (Wall → Wall → S) →
    Vec → Cov → Cov → Cov → Cov → Vec
  originalBR68PhysicalGaugeCodazzi j M q p px m mx a =
    gaugeCodazzi j q p px m mx a
      + originalBR68GaugeCorrection j M p m a

  originalBR68MeanForceCorrection : S → Tensor → Tensor → S
  originalBR68MeanForceCorrection mean p m =
    neg (four * mean * (scale p + scale m))

  originalBR68PhysicalMeanForce : S → S → Vec →
    Tensor → Tensor → Tensor → Tensor → S
  originalBR68PhysicalMeanForce mean j q p px m mx =
    meanForce j q p px m mx
      + originalBR68MeanForceCorrection mean p m

  -- The source correction ONLY changes the four gauge-Codazzi rows
  -- and the final metric mean-force row. The original BR34 normal
  -- Gauss row and the D/E-prefix allocations are retained as owned.
  record OriginalBR68BoundaryPayments : Set r where
    constructor originalBR68BoundaryPayments
    field
      originalGaugeD originalGaugeE : List S
      physicalGaugeCodazziFour : Vec
      physicalGaugeGauss : S
      originalMetricD originalMetricE : List S
      physicalMeanForce : S
      gaugeMeanResidual : Vec
      metricMeanResidual : S
  open OriginalBR68BoundaryPayments public

  assembleOriginalBR68BoundaryPayments :
    S → S → (Wall → Wall → S) → Vec →
    Tensor → Tensor → Tensor → Tensor →
    Cov → Cov → Cov → Cov → OriginalBR68BoundaryPayments
  assembleOriginalBR68BoundaryPayments mean j M q
    p px m mx c cx d dx =
    originalBR68BoundaryPayments
      (gaugeRows D j q c cx d dx)
      (gaugeRows E j q c cx d dx)
      (originalBR68PhysicalGaugeCodazzi j M q c cx d dx)
      (gaugeGauss j q c cx d dx)
      (metricRows D j q p px m mx)
      (metricRows E j q p px m mx)
      (originalBR68PhysicalMeanForce mean j q p px m mx)
      (originalBR68GaugeCorrection j M c d)
      (originalBR68MeanForceCorrection mean p m)

  ------------------------------------------------------------------------
  -- BR69: all-order PHYSICAL coordinate Codazzi/mean force derivatives,
  -- using the ORIGINAL BR52 divided Taylor jet product. Every
  -- nonzero mean M, Israel jump j, metric ell and covector channel
  -- retains its independent time jets through order eight.
  ------------------------------------------------------------------------

  record OriginalBR69SourceTower : Set r where
    constructor originalBR69SourceTower
    field
      coordinateMeanTensor : Wall → Wall → DividedJet
      coordinateMeanScalar : DividedJet
      coordinateIsraelJump : DividedJet
      plusGaugeValue minusGaugeValue : Wall → DividedJet
      plusScaleValue minusScaleValue : DividedJet
  open OriginalBR69SourceTower public

  originalBR69CodazziCorrection : OriginalBR69SourceTower →
    Nat → Vec
  originalBR69CodazziCorrection d n a =
    neg (two * sum4 (λ b →
      sign b * jetProduct
        (coordinateMeanTensor d a b)
        (λ k → plusGaugeValue d b k - minusGaugeValue d b k) n))
    - half * jetProduct
        (coordinateIsraelJump d)
        (λ k → plusGaugeValue d a k + minusGaugeValue d a k) n

  originalBR69MeanForceCorrection : OriginalBR69SourceTower →
    DividedJet
  originalBR69MeanForceCorrection d =
    jetScale (neg four)
      (jetProduct (coordinateMeanScalar d)
        (jetSum (plusScaleValue d) (minusScaleValue d)))

  record OriginalBR69NonlinearSourceDebt : Set r where
    constructor originalBR69NonlinearSourceDebt
    field
      originalPhysicalSources : OriginalBR69SourceTower
      graphShapeHessianDebt : Nat → Wall → Wall → S
      movingUnitNormalDebt : Nat → Cov
      curvedConnectionDebt : Nat → Cov
      originalPhysicalGaussDebt : Nat → S
      originalIsraelMeanDebt : Nat → S
  open OriginalBR69NonlinearSourceDebt public

  ------------------------------------------------------------------------
  -- BR70: actual moving material GAUGE tangent/normal frame.
  -- c_a=e_a^mu C_mu=C_a+f_a C_n.
  -- c_perp=n^mu C_mu, n^mu=g^{mu nu}F_nu/sqrt(z), z>0.
  -- C_n != c_perp on a general shifted/tilted ADM graph. The
  -- physical plus/minus gauge frame and its inverse are real
  -- geometric data, not postulated identities of coordinate traces.
  ------------------------------------------------------------------------

  materialGaugeTangent : MaterialGraphGradient → Cov → Vec
  materialGaugeTangent f c a =
    c (wall a)
      + (neg (materialDefiningCovector f (wall a))) * c normal

  record OriginalBR70UnitNormal : Set r where
    constructor originalBR70UnitNormal
    field
      sourceADM : ADMPhysicalPoint
      sourceGraph : MaterialGraphGradient
      sourceNormalSquared : S
      sourceNormalLength : S
      sourceNormalReciprocal : S
      originalContravariantNormal : Cov
      retainedSourceNormalResidual : S
  open OriginalBR70UnitNormal public

  materialGaugeNormal : OriginalBR70UnitNormal → Cov → S
  materialGaugeNormal n c =
    sum5 (λ a → originalContravariantNormal n a * c a)

  record OriginalBR70GaugePhysicalPair : Set r where
    constructor originalBR70GaugePhysicalPair
    field
      plusPhysicalNormal minusPhysicalNormal : OriginalBR70UnitNormal
      plusOriginalCovector minusOriginalCovector : Cov
      plusPhysicalTangent minusPhysicalTangent : Vec
      plusPhysicalNormalValue minusPhysicalNormalValue : S
      physicalTangentialJump : Vec
      physicalNormalJump : S
  open OriginalBR70GaugePhysicalPair public

  assembleOriginalBR70GaugePhysicalPair :
    OriginalBR70UnitNormal → OriginalBR70UnitNormal →
    Cov → Cov → OriginalBR70GaugePhysicalPair
  assembleOriginalBR70GaugePhysicalPair np nm cp cm =
    originalBR70GaugePhysicalPair np nm cp cm
      (materialGaugeTangent (sourceGraph np) cp)
      (materialGaugeTangent (sourceGraph nm) cm)
      (materialGaugeNormal np cp)
      (materialGaugeNormal nm cm)
      (λ a → materialGaugeTangent (sourceGraph np) cp a
        - materialGaugeTangent (sourceGraph nm) cm a)
      (materialGaugeNormal np cp - materialGaugeNormal nm cm)

  -- The positive normal-length law, inverse frame and actual
  -- nonlinear graph harmonic-gauge derivative remain separate
  -- evidence obligations. BR70 constructs the same-source data
  -- that must enter BR68/69 instead of pretending C_n=c_perp.

  ------------------------------------------------------------------------
  -- BR71: ONE COMPLETE ORIGINAL D/E 30+10 physical reference row map.
  -- Physically calculated sources replace ONLY their owned slots:
  -- metric 14:24 Israel (BR66), metric 29 mean force (BR68);
  -- gauge 5:9 coordinate Codazzi (BR68), gauge 9 Gauss unchanged.
  -- Original 14 value/shift and 5 D/E gauge/metric allocation rows
  -- are preserved, not normalized to an unverified common allocation.
  ------------------------------------------------------------------------

  originalBR71MetricPrefix : OriginalBR66MeanSource → List S
  originalBR71MetricPrefix d =
    pack10 (λ a b → H (originalPlusMetric d) a b
                      - H (originalMinusMetric d) a b) ++
    (pack4 (λ a → beta (originalPlusMetric d) a
                   - beta (originalMinusMetric d) a) ++
      pack10 (λ a b →
        israel (originalReferenceIsraelJump d) (originalTangentialJet d)
          (originalPlusMetric d) (originalPlusNormal d)
          (originalMinusMetric d) (originalMinusNormal d) a b
          + originalBR66MeanShapePayment d a b))

  originalBR71MetricSuffix : Allocation →
    OriginalBR66MeanSource → List S
  originalBR71MetricSuffix D d =
    pack4 (tangentJump (originalReferenceIsraelJump d)
      (originalTangentialJet d)
      (originalPlusMetric d) (originalPlusNormal d)
      (originalMinusMetric d) (originalMinusNormal d)) ++
      (gaugeNorm (originalTangentialJet d)
        (originalPlusMetric d) (originalPlusNormal d) ∷
        originalBR68PhysicalMeanForce (originalMeanExtrinsic d)
          (originalReferenceIsraelJump d) (originalTangentialJet d)
          (originalPlusMetric d) (originalPlusNormal d)
          (originalMinusMetric d) (originalMinusNormal d) ∷ [])
  originalBR71MetricSuffix E d =
    tangentJump (originalReferenceIsraelJump d) (originalTangentialJet d)
      (originalPlusMetric d) (originalPlusNormal d)
      (originalMinusMetric d) (originalMinusNormal d) x ∷
    tangentJump (originalReferenceIsraelJump d) (originalTangentialJet d)
      (originalPlusMetric d) (originalPlusNormal d)
      (originalMinusMetric d) (originalMinusNormal d) y ∷
    tangentJump (originalReferenceIsraelJump d) (originalTangentialJet d)
      (originalPlusMetric d) (originalPlusNormal d)
      (originalMinusMetric d) (originalMinusNormal d) z ∷
    gaugeNorm (originalTangentialJet d)
      (originalPlusMetric d) (originalPlusNormal d) ∷
    gaugeNorm (originalTangentialJet d)
      (originalMinusMetric d) (originalMinusNormal d) ∷
    originalBR68PhysicalMeanForce (originalMeanExtrinsic d)
      (originalReferenceIsraelJump d) (originalTangentialJet d)
      (originalPlusMetric d) (originalPlusNormal d)
      (originalMinusMetric d) (originalMinusNormal d) ∷ []

  originalBR71MetricRows : Allocation →
    OriginalBR66MeanSource → List S
  originalBR71MetricRows a d =
    originalBR71MetricPrefix d ++
      originalBR71MetricSuffix a d

  originalBR71GaugeRows : Allocation →
    S → (Wall → Wall → S) → Vec →
    Cov → Cov → Cov → Cov → List S
  originalBR71GaugeRows a j meanTensor q cp cx cm cmx =
    gaugePrefix a cp cm ++
      (pack4 (originalBR68PhysicalGaugeCodazzi j meanTensor q
        cp cx cm cmx) ++
        (gaugeGauss j q cp cx cm cmx ∷ []))

  record OriginalBR71UnifiedPhysicalBoundary : Set r where
    constructor originalBR71UnifiedPhysicalBoundary
    field
      originalMeanIsraelSource : OriginalBR66MeanSource
      actualMeanExtrinsicTensor : Wall → Wall → S
      plusGaugeValue plusGaugeNormal : Cov
      minusGaugeValue minusGaugeNormal : Cov
      physicalMetricD physicalMetricE : List S
      physicalGaugeD physicalGaugeE : List S
      originalNonlinearGraphUnpaid : List S
      originalHarmonicConnectionUnpaid : Cov
  open OriginalBR71UnifiedPhysicalBoundary public

  assembleOriginalBR71UnifiedBoundary :
    OriginalBR66MeanSource → (Wall → Wall → S) →
    Cov → Cov → Cov → Cov →
    List S → Cov → OriginalBR71UnifiedPhysicalBoundary
  assembleOriginalBR71UnifiedBoundary d M cp cx cm cmx graphDebt connectionDebt =
    originalBR71UnifiedPhysicalBoundary
      d M cp cx cm cmx
      (originalBR71MetricRows D d)
      (originalBR71MetricRows E d)
      (originalBR71GaugeRows D (originalReferenceIsraelJump d)
        M (originalTangentialJet d) cp cx cm cmx)
      (originalBR71GaugeRows E (originalReferenceIsraelJump d)
        M (originalTangentialJet d) cp cx cm cmx)
      graphDebt connectionDebt

  originalBR71MetricCount : (a : Allocation)
      (d : OriginalBR66MeanSource) →
      length (originalBR71MetricRows a d) ≡ 30
  originalBR71MetricCount D d = refl
  originalBR71MetricCount E d = refl

  originalBR71GaugeCount : (a : Allocation) (j : S)
    (M : Wall → Wall → S) (q : Vec) (p px m mx : Cov) →
    length (originalBR71GaugeRows a j M q p px m mx) ≡ 10
  originalBR71GaugeCount D j M q p px m mx = refl
  originalBR71GaugeCount E j M q p px m mx = refl

  -- Native source now owns ALL 40 physical reference boundary rows
  -- per allocation. The nonlinear graph, full harmonic connection,
  -- and rank-nine BR29 source factor remain present as UNPAID fields;
  -- this assembly alone cannot certify physical IBVP solvability.

  ------------------------------------------------------------------------
  -- BR73–78: source-specific REAL physical energy / curved wall
  -- constraint owners after BR71/72. Existing tensor/graph, original
  -- 30+10 D/E reference and BR29/BS13 curvature data are retained.
  --
  -- BR73 corrects the coordinate-symmetrizer overrestriction:
  -- H>0, N>0 => positive ADM normal-frame energy at ANY shift v.
  -- C itself can be indefinite; use A(u_t-v.grad u)^2+D H^-1[du,du].
  ------------------------------------------------------------------------

  originalADMNormalTime : ADMPhysicalPoint → S →
    (BR4Space → S) → S
  originalADMNormalTime g ut grad =
    ut - sumBR4Space (λ i → fourShift g i * grad i)

  originalADMNormalSpatialPower : ADMPhysicalPoint →
    (BR4Space → S) → S
  originalADMNormalSpatialPower g grad =
    volumeDensity g * sumBR4Space (λ i → sumBR4Space (λ k →
      spatialInverse g i k * grad i * grad k))

  originalADMNormalEnergy : ADMPhysicalPoint → S →
    (BR4Space → S) → S
  originalADMNormalEnergy g ut grad =
    half * (admBR4A g *
      originalADMNormalTime g ut grad *
      originalADMNormalTime g ut grad
      + originalADMNormalSpatialPower g grad)

  originalADMCoordinateEnergy : ADMPhysicalPoint → S →
    (BR4Space → S) → S
  originalADMCoordinateEnergy g ut grad =
    half * (admBR4A g * ut * ut
      + br4SpatialSquare (admBR4C g) grad)

  originalADMShiftCorrection : ADMPhysicalPoint → S →
    (BR4Space → S) → S
  originalADMShiftCorrection g ut grad =
    neg (sumBR4Space (λ i → admBR4B g i * grad i) * ut)
      + admBR4A g *
         (sumBR4Space (λ i → fourShift g i * grad i)) *
         (sumBR4Space (λ i → fourShift g i * grad i))

  -- Source-level equality to certify using the actual BR48 ADM
  -- identities and complex-ring distributive/commutative laws.
  record OriginalADMNormalEnergyWeld
      (g : ADMPhysicalPoint) (ut : S)
      (grad : BR4Space → S) : Set r where
    constructor originalADMNormalEnergyWeld
    field
      normalVsCoordinate :
        originalADMNormalEnergy g ut grad ≡
          originalADMCoordinateEnergy g ut grad
            + originalADMShiftCorrection g ut grad

  ------------------------------------------------------------------------
  -- BR74–75: full nonlinear GRAPH intrinsic Gauss/Codazzi algebra.
  -- In flat ambient eta5, at n=f(t,x,y,z):
  -- h_ab=eta_ab+f_a f_b, z=1+f^a f_a,
  -- K_ab=-f_ab/sqrt(z), Gamma^c_ab=f^c f_ab/z.
  -- The full 64 Codazzi components vanish by symmetric third jets;
  -- the complete 256 Gauss tensor is (H_ac H_bd-H_ad H_bc)/z.
  -- Curved AdS ambient Ricci/Weyl is an EXTERNAL nonzero source.
  ------------------------------------------------------------------------

  record OriginalNonlinearWallGraphJets : Set r where
    constructor originalNonlinearWallGraphJets
    field
      graphGradient : Vec
      graphHessian : Wall → Wall → S
      graphThirdDerivative : Wall → Wall → Wall → S
      graphNormalSquared : S
      reciprocalGraphNormalSquared : S
      hessianSymmetric :
        (a b : Wall) → graphHessian a b ≡ graphHessian b a
      thirdDerivativeSymmetric :
        (a b c : Wall) →
          graphThirdDerivative a b c ≡
          graphThirdDerivative b a c
      thirdDerivativeLastSymmetric :
        (a b c : Wall) →
          graphThirdDerivative a b c ≡
          graphThirdDerivative a c b
  open OriginalNonlinearWallGraphJets public

  originalGraphRaisedGradient : OriginalNonlinearWallGraphJets → Vec
  originalGraphRaisedGradient p a =
    sign a * graphGradient p a

  originalGraphHessianContraction :
    OriginalNonlinearWallGraphJets → Vec
  originalGraphHessianContraction p a =
    sum4 (λ i → originalGraphRaisedGradient p i *
      graphHessian p a i)

  originalGraphCodazziNumerator :
    OriginalNonlinearWallGraphJets → Wall → Wall → Wall → S
  originalGraphCodazziNumerator p c a b =
    neg (graphNormalSquared p *
      (graphThirdDerivative p c a b
        - graphThirdDerivative p a c b))
      + graphHessian p a b *
          originalGraphHessianContraction p c
      + graphHessian p c a *
          originalGraphHessianContraction p b
      + graphHessian p c b *
          originalGraphHessianContraction p a
      - graphHessian p c b *
          originalGraphHessianContraction p a
      - graphHessian p a c *
          originalGraphHessianContraction p b
      - graphHessian p a b *
          originalGraphHessianContraction p c

  originalGraphGaussNumerator :
    OriginalNonlinearWallGraphJets →
    Wall → Wall → Wall → Wall → S
  originalGraphGaussNumerator p a b c d =
    graphHessian p a c * graphHessian p b d
      - graphHessian p a d * graphHessian p b c

  record OriginalGraphCurvatureSourcePayment : Set r where
    constructor originalGraphCurvatureSourcePayment
    field
      originalWallGeometry : OriginalNonlinearWallGraphJets
      originalAmbientRicciNormal : Vec
      originalAmbientRiemannTangent :
        Wall → Wall → Wall → Wall → S
      originalWallStressDivergence : Vec
      originalGraphCodazziResidual : Wall → Wall → Wall → S
      originalGraphGaussResidual :
        Wall → Wall → Wall → Wall → S
  open OriginalGraphCurvatureSourcePayment public

  -- The polynomial flat-ambient source vanishes only after the
  -- symmetric hessian/third-jet/ring laws have been proved.
  -- For AdS and real curved Einstein g, retain ambient curvature
  -- and physical material graph unit-normal source.
  ------------------------------------------------------------------------
  -- BR76–77: signed physical stress through the true moving wall.
  -- T(t,s)=(t.du)(s.du)-1/2 g(t,s)g^-1(du,du).
  -- The scalar normal-slice energy controls this by
  -- |flux| <= (|chi|+sqrt(1+chi²)) E, chi=g(t,s).
  -- Positivity and absolute values belong to ordered REAL/Hermitian
  -- physical fields. Nothing makes Complex F ordered here.
  ------------------------------------------------------------------------

  record OriginalPhysicalEnergyFrames : Set r where
    constructor originalPhysicalEnergyFrames
    field
      sourcePhysicalADM : ADMPhysicalPoint
      sourcePhysicalWallGraph : MaterialGraphGradient
      unitSliceTimelike : Cov
      unitWallSpacelike : Cov
      sourcePhysicalMetric : Axis → Axis → S
      sourceInversePhysicalMetric : Axis → Axis → S
      originalWallTilt : S
      originalUnitNormalCompatibility : S
  open OriginalPhysicalEnergyFrames public

  originalEnergyFramePair : OriginalPhysicalEnergyFrames →
    Cov → Cov → S
  originalEnergyFramePair d u v =
    sum5 (λ a → sum5 (λ b →
      sourcePhysicalMetric d a b * u a * v b))

  originalInverseGradientNorm : OriginalPhysicalEnergyFrames →
    Cov → S
  originalInverseGradientNorm d du =
    sum5 (λ a → sum5 (λ b →
      sourceInversePhysicalMetric d a b * du a * du b))

  originalPhysicalStressFlux : OriginalPhysicalEnergyFrames →
    Cov → S
  originalPhysicalStressFlux d du =
    sum5 (λ a → unitSliceTimelike d a * du a)
      * sum5 (λ a → unitWallSpacelike d a * du a)
      - half * originalEnergyFramePair d
          (unitSliceTimelike d) (unitWallSpacelike d)
          * originalInverseGradientNorm d du

  record OriginalSharpMovingFluxPayment : Set r where
    constructor originalSharpMovingFluxPayment
    field
      originalPhysicalFrames : OriginalPhysicalEnergyFrames
      originalPositiveSliceEnergy : S
      originalPhysicalFlux : S
      originalGeometricTiltCoefficient : S
      residualUnpaidBoundaryTrace : S
      residualUnpaidWallIsrael : S
      residualUnpaidEinsteinConnection : S
  open OriginalSharpMovingFluxPayment public

  ------------------------------------------------------------------------
  -- BR78: nonlinear vacuum Einstein–Israel Bianchi / TENSION Ward.
  -- With one matched h and physical Israel I=[K]-h tr[K]+3j h-S:
  --   D^a I_ab = [Ric_g(n,e_b)]+3 D_b j-D^a S_ab.
  -- If both bulk Ric=-4g and S=0 and I=0, then D_b j=0
  -- on ALL FOUR tangent channels. Independent varying j(t) sources
  -- in BR67/69 are formal algebraic fixtures, not vacuum Einstein
  -- walls unless compensated by actual wall matter/flux.
  ------------------------------------------------------------------------

  record OriginalVacuumWallWardSource : Set r where
    constructor originalVacuumWallWardSource
    field
      originalJunctionDivergence : Vec
      originalBulkNormalRicciJump : Vec
      originalTensionTangentialGradient : Vec
      originalWallMatterDivergence : Vec
      remainingPhysicalWardDefect : Vec
  open OriginalVacuumWallWardSource public

  originalWallWardDefect : OriginalVacuumWallWardSource → Vec
  originalWallWardDefect d a =
    originalJunctionDivergence d a
      - originalBulkNormalRicciJump d a
      - three * originalTensionTangentialGradient d a
      + originalWallMatterDivergence d a

  record OriginalPhysicalEinsteinIsraelWardCertificate
      (d : OriginalVacuumWallWardSource) : Set r where
    constructor originalPhysicalEinsteinIsraelWardCertificate
    field
      genuineNonlinearCodazzi : (a : Wall) →
        originalWallWardDefect d a ≡ O
      originalPhysicalNoHiddenSource :
        (a : Wall) → remainingPhysicalWardDefect d a ≡ O
  open OriginalPhysicalEinsteinIsraelWardCertificate public

  -- The nonzero rank-nine BR29 projected Weyl wall system and
  -- the five harmonic source still need a SAME-solution factor.
  -- The Ward obstruction and shift-robust energy are added to the
  -- actual physical payment list; neither a placeholder record
  -- nor an algebraic test is accepted as a solved PDE.

  ------------------------------------------------------------------------
  -- BR79–81 RECONCILED ORIGINAL SPATIAL→SPACETIME BRIDGE.
  --
  -- The original P0BL/BM/BN owner is the complete FOUR-SPATIAL
  -- Riemannian scalar constraint on H3×S1. It is not the hyperbolic
  -- Einstein–Israel evolution. For Ric_g5=-4g5, Λ=-6, and initial
  -- K_ij=0, the 5D vacuum Hamiltonian is R(h)+12=0; momentum=0.
  --
  -- Nonzero K requires R+12=|K|²-(tr K)² and four independently
  -- proved momentum equations; never infer this from BN alone.
  ------------------------------------------------------------------------

  twelve : S
  twelve = four * three

  record OriginalP0BNTimeSymmetricInput : Set r where
    constructor originalP0BNTimeSymmetricInput
    field
      originalBNSpatialScalar : S
      originalBNActualSpatialMetric : BR4Space → BR4Space → S
      originalBNSpatialIsraelJump : Wall → Wall → S
      originalBNSourceSeamNormal : BR4Space → S
      originalBNScalarEquation : originalBNSpatialScalar + twelve ≡ O
  open OriginalP0BNTimeSymmetricInput public

  original5DTimeSymmetricHamiltonian :
    OriginalP0BNTimeSymmetricInput → S
  original5DTimeSymmetricHamiltonian d =
    originalBNSpatialScalar d + twelve

  originalP0BNPaysVacuumHamiltonian :
    (d : OriginalP0BNTimeSymmetricInput) →
    original5DTimeSymmetricHamiltonian d ≡ O
  originalP0BNPaysVacuumHamiltonian d =
    originalBNScalarEquation d

  -- This is a REAL same-equation geometric weld: no second scalar
  -- existence proof is demanded. Actual inhabited BN inputs
  -- require its source-specific classical PDE/interval certificates.
  -- The three-plus-one initial time/wall corners and regular
  -- physical gauge are separate proof obligations.
  record OriginalP0BNCauchyCornerPayment : Set r where
    constructor originalP0BNCauchyCornerPayment
    field
      originalBNTimeSymmetric : OriginalP0BNTimeSymmetricInput
      originalPhysicalTimeLapse : S
      originalPhysicalTimeShift : BR4Space → S
      originalPhysicalWallPair : OriginalBR71UnifiedPhysicalBoundary
      originalFourthNormalCorner : Tensor
      originalGaugeInitialZero : Cov
      originalTimeCornerResidual : Tensor
      originalBianchiCornerResidual : Cov
      originalExteriorCornerResidual : S
  open OriginalP0BNCauchyCornerPayment public

  ------------------------------------------------------------------------
  -- BR80: NONFROZEN ADM physical normal-frame multiplier current.
  -- The 5D stress divergence is the exact classical identity
  --   div_g(T(.,X)) = (box_g u) X(u) + T:Lie_X g/2.
  -- BR73 gives positive normal energy; BR76–77 give moving-wall
  -- flux and geometric tilt. The lapse/shift/metric deformation
  -- term T:Lie_X g/2 is necessarily retained.
  --
  -- This source owns each exact payment separately: 15 metric and
  -- five gauge channels share only the scalar principal part;
  -- their original Einstein connections and curved Bianchi
  -- lower-order terms are NOT declared zero.
  ------------------------------------------------------------------------

  record OriginalADMVariableEnergyCurrent : Set r where
    constructor originalADMVariableEnergyCurrent
    field
      originalVariableADM : ADMPhysicalPoint
      originalMaterialWall : MaterialGraphGradient
      originalFieldNormalTime : S
      originalFieldSpatialJet : BR4Space → S
      originalScalarWaveForcing : S
      originalPositiveSliceEnergy : S
      originalADMDeformationWork : S
      originalEnergyCurrentDivergence : S
      originalMovingWallFlux : S
      originalGeometryAndConnectionResidual : S
  open OriginalADMVariableEnergyCurrent public

  originalADMCurrentResidual : OriginalADMVariableEnergyCurrent → S
  originalADMCurrentResidual d =
    originalEnergyCurrentDivergence d
      - originalScalarWaveForcing d * originalFieldNormalTime d
      - originalADMDeformationWork d
      - originalGeometryAndConnectionResidual d

  record OriginalADMPhysicalCurrentCertificate
      (d : OriginalADMVariableEnergyCurrent) : Set r where
    constructor originalADMPhysicalCurrentCertificate
    field
      actualVariableEnergyCurrentWeld :
        originalADMCurrentResidual d ≡ O
  open OriginalADMPhysicalCurrentCertificate public

  ------------------------------------------------------------------------
  -- BR81: SOURCE-SPECIFIC P0AK reference, already an exact
  -- static AdS5 warped Einstein/pure-tension reference.
  --
  -- b=4/5 cosh(n-log2), L=2log2, h0=4/5.
  -- Spatial h=dn²+b² gamma_H3 has Ric_h=-3h and scalar -12.
  -- N=b/(h0 z_H3) obeys Hess_h N=N h and Delta_h N=4N.
  -- Thus -N²dt²+h solves Ric_g=-4g, and the wall time
  -- lapse jump [∂n log N]=[b'/b]=-6/5 matches the
  -- three physical spatial Israel directions.
  --
  -- P0BN's NONZERO scalar h need not have a static lapse:
  --     Hess_h N=N(Ric_h+4h)
  -- is overdetermined and not implied by R(h)=-12.
  -- The intended nonzero route is actual hyperbolic evolution
  -- with compatible initial wall corners, not a fictitious
  -- static-lapse inverse.
  ------------------------------------------------------------------------

  record OriginalP0AKReferenceStaticWeld : Set r where
    constructor originalP0AKReferenceStaticWeld
    field
      referenceSpatialScalar : S
      referencePhysicalLapse : S
      referenceSpatialRicciTrace : S
      referenceLapseHessianTrace : S
      referenceIsraelJump : S
      referenceTimeLapseJump : S
      referenceVacuumHamiltonian : S
      referenceStaticLapseResidual : S
      referenceWallTensionResidual : S
  open OriginalP0AKReferenceStaticWeld public

  record OriginalP0AKStaticSourceCertificate
      (d : OriginalP0AKReferenceStaticWeld) : Set r where
    constructor originalP0AKStaticSourceCertificate
    field
      sourceReferenceVacuum : referenceVacuumHamiltonian d ≡ O
      sourceReferenceLapse : referenceStaticLapseResidual d ≡ O
      sourceReferenceTension : referenceWallTensionResidual d ≡ O
      sourceReferenceTimeWallMatch :
        referenceTimeLapseJump d ≡ referenceIsraelJump d
  open OriginalP0AKStaticSourceCertificate public

  -- Reconciled theorem endpoint:
  -- (1) original BN classical spatial solution + existing BO/BQ
  -- higher corners; (2) BR71/72 physical wall source;
  -- (3) BR80 variable normal-frame current with a genuine high
  -- order positive boundary/Kreiss estimate; (4) BR29/55 same
  -- nonlinear Bianchi uniqueness; (5) BS13/BR57 weighted
  -- quotient and BR31 exterior; (6) construct an actual physical
  -- 5D solution and continuation. None may be silently inferred
  -- from the scalar Hamiltonian or the reference static lapse.


  -- BR92/93: actual reduced Ricci action, signed Gaussian fold.
  originalSameMetricGaugeWave : Cov → Cov → Cov
  originalSameMetricGaugeWave boxC ricC a = boxC a + ricC a

  originalFoldOdd : Cov → Cov → Cov
  originalFoldOdd p m (wall a) = p (wall a) - m (wall a)
  originalFoldOdd p m normal = p normal + m normal

  originalFoldEven : Cov → Cov → Cov
  originalFoldEven p m (wall a) = p (wall a) + m (wall a)
  originalFoldEven p m normal = p normal - m normal

  originalFoldOddRadial : Cov → Cov → Cov
  originalFoldOddRadial dp dm (wall a) = dp (wall a) + dm (wall a)
  originalFoldOddRadial dp dm normal = dp normal - dm normal

  originalFoldEvenRadial : Cov → Cov → Cov
  originalFoldEvenRadial dp dm (wall a) = dp (wall a) - dm (wall a)
  originalFoldEvenRadial dp dm normal = dp normal + dm normal

  originalFoldDNormalRobin : S → Cov → Cov → Cov → Cov → S
  originalFoldDNormalRobin j p m dp dm =
    originalFoldOddRadial dp dm normal - two * j * originalFoldOdd p m normal

  originalFoldDNormalRobinExact :
    (j : S) (p m dp dm : Cov) →
    originalFoldDNormalRobin j p m dp dm
      ≡ (dp normal - dm normal) - two * j * (p normal + m normal)
  originalFoldDNormalRobinExact j p m dp dm = refl

  originalFoldDTangentRobin : S → Cov → Cov → Cov → Cov → Vec
  originalFoldDTangentRobin j p m dp dm a =
    originalFoldEvenRadial dp dm (wall a) - j * originalFoldEven p m (wall a)

  originalFoldDTangentRobinExact :
    (j : S) (p m dp dm : Cov) (a : Wall) →
    originalFoldDTangentRobin j p m dp dm a
      ≡ (dp (wall a) - dm (wall a)) - j * (p (wall a) + m (wall a))
  originalFoldDTangentRobinExact j p m dp dm a = refl

  -- Robin residuals AFTER D's homogeneous value conditions vanish.
  -- Analytic cascade requires identical reflected operators, compatible
  -- boundary multiplier, zero initial/exterior data. Not asserted here.


  ------------------------------------------------------------------------
  -- BR97 candidate F: full geometric gauge continuity plus BR33
  -- mean force, preserving D/E and their existing source consumers.
  ------------------------------------------------------------------------
  originalMetricRowsF : S → Vec → Tensor → Tensor → Tensor → Tensor → List S
  originalMetricRowsF j q p px m mx =
    metricPrefix j q p px m mx ++
    (pack4 (tangentJump j q p px m mx) ++
      ((gaugeNorm q p px - gaugeNorm q m mx) ∷
        meanForce j q p px m mx ∷ []))

  originalGaugeRowsF : S → Vec → Cov → Cov → Cov → Cov → List S
  originalGaugeRowsF j q p px m mx =
    ((p normal - m normal) ∷ pack4 (λ a → p (wall a) - m (wall a))) ++
    (pack4 (gaugeCodazzi j q p px m mx) ++ (gaugeGauss j q p px m mx ∷ []))

  originalMetricCountF : (j : S) (q : Vec) (p px m mx : Tensor) →
    length (originalMetricRowsF j q p px m mx) ≡ 30
  originalMetricCountF j q p px m mx = refl

  originalGaugeCountF : (j : S) (q : Vec) (p px m mx : Cov) →
    length (originalGaugeRowsF j q p px m mx) ≡ 10
  originalGaugeCountF j q p px m mx = refl

  originalPhysicalGaugeRowsF : S → (Wall → Wall → S) → Vec →
    Cov → Cov → Cov → Cov → List S
  originalPhysicalGaugeRowsF j M q p dp m dm =
    ((p normal - m normal) ∷ pack4 (λ a → p (wall a) - m (wall a))) ++
    (pack4 (coordinateCodazzi j M q p dp m dm) ++
      (gaugeGauss j q p dp m dm ∷ []))

  originalPhysicalGaugeCountF : (j : S) (M : Wall → Wall → S)
    (q : Vec) (p dp m dm : Cov) →
    length (originalPhysicalGaugeRowsF j M q p dp m dm) ≡ 10
  originalPhysicalGaugeCountF j M q p dp m dm = refl

  -- These are reference/coordinate row constructors and exact
  -- count proofs only. BR98 requires the actual geometric F wall
  -- conditions and same reduced solution, not an inhabited count.


  -- BR100: explicit nonlinear F fixed-material normal-jet decoders.
  -- Inputs are actual h inverse, L_beta h and tangential geometric jets.
  originalFNormalH : S → (Wall → Wall → S) →
    (Wall → Wall → S) → Wall → Wall → S
  originalFNormalH l k lieH a b = two * l * k a b + lieH a b

  originalFNormalBeta : S → (Wall → Wall → S) →
    Vec → Vec → Vec → Vec → Vec → Vec
  originalFNormalBeta l hi adv c src gamma dlog a =
    adv a + (l * l) *
      sum4 (λ b → hi a b * (c b + src b - gamma b + dlog b))

  originalFNormalLambda : S → S → S → S → S → S
  originalFNormalLambda l adv c src tau =
    adv + (l * l) * (c + src + tau)

  originalFMeanShape : S → (Wall → Wall → S) →
    (Wall → Wall → S) → Wall → Wall → S
  originalFMeanShape f h m a b = m a b + (half * quarter * f) * h a b

  originalFPlusShape : S → S → (Wall → Wall → S) →
    (Wall → Wall → S) → (Wall → Wall → S) → Wall → Wall → S
  originalFPlusShape j f h m r a b =
    originalFMeanShape f h m a b + half * (j * h a b + r a b)

  originalFMinusShape : S → S → (Wall → Wall → S) →
    (Wall → Wall → S) → (Wall → Wall → S) → Wall → Wall → S
  originalFMinusShape j f h m r a b =
    originalFMeanShape f h m a b - half * (j * h a b + r a b)

  originalFPlusGauge : Cov → Cov → Cov
  originalFPlusGauge mean jump a = mean a + half * jump a

  originalFMinusGauge : Cov → Cov → Cov
  originalFMinusGauge mean jump a = mean a - half * jump a

  -- Decoders, not an assumed analytic F metric existence theorem.


  ------------------------------------------------------------------------
  -- BR104/105: material foliation source (actual signed contractions).
  -- The signed tangential shape square and tangential drift are
  -- supplied by the actual Lorentz leaf metric, not positive norms.
  ------------------------------------------------------------------------
  originalFNormalRicci :
    S → S → S → S → S
  originalFNormalRicci nTau shapeSquare leafBoxPsi leafGradSquare =
    neg nTau - shapeSquare - leafBoxPsi - leafGradSquare

  originalFScaleWaveSource :
    S → S → S → S → S → S → S
  originalFScaleWaveSource tau nPsi shapeSquare nHperp gaugeDrift reducedNN =
    tau * nPsi - shapeSquare + nHperp - gaugeDrift + four - reducedNN

  originalFWallScaleWaveSource : S → S → S → S → S
  originalFWallScaleWaveSource j gaugeNormal jumpNTau jumpReducedTrace =
    neg jumpNTau - four * j * gaugeNormal - jumpReducedTrace

  -- BR106 expanded divergence: B=Box psi-|dpsi|², V=∇_(grad psi)n.
  -- Box Q reduction on the same metric uses BR92, not vacuum Ricci.
  originalFMeanCurvatureWaveSource :
    S → S → S → S → S → S → S → S
  originalFMeanCurvatureWaveSource nB tau b divV boxQ gradPair qBoxPsi =
    nB + tau * b + two * divV - boxQ + gradPair + qBoxPsi

  -- BR107 exact source of the positive Dirichlet normal multiplier.
  originalFDirichletNormalStress : S → S
  originalFDirichletNormalStress normalDerivative =
    half * (normalDerivative * normalDerivative)

  -- No analytic trace, variable high-order tame or continuum existence
  -- witness is inferred from these algebraic expressions.


  ------------------------------------------------------------------------
  -- BR108/111: original F wave-adapted generator expressions.
  -- The scalar root reciprocal is supplied; no division by a
  -- characteristic zero is assumed. Graph displacement is retained.
  ------------------------------------------------------------------------
  originalFWaveLiftAmplitude : S → S → S
  originalFWaveLiftAmplitude inverseRoot scaleJump =
    neg (half * inverseRoot * scaleJump)

  originalFWaveLiftMixed : Vec → S → Vec
  originalFWaveLiftMixed q generatorValue a = q a * generatorValue

  originalFWaveLiftScale : S → S
  originalFWaveLiftScale normalGeneratorDerivative =
    normalGeneratorDerivative

  originalFGraphLieJump : S → S → (Wall → Wall → S) →
    Wall → Wall → S
  originalFGraphLieJump j v h a b = two * j * v * h a b

  -- BR111: gauge-preserving generator defect is the derivative
  -- of the fixed-source gauge map MINUS its covector Lie transport.
  originalFGaugeGeneratorDefect : Cov → Cov → Cov
  originalFGaugeGeneratorDefect variedGauge lieGauge a =
    variedGauge a - lieGauge a

  -- Analytic identity: D Ered(Lie_V g) = Lie_V Ered - symgrad(P_g V).
  -- These are source expressions, not an admitted inverse for P_g,
  -- nor the curved graph lift or variable glancing estimate.


  ------------------------------------------------------------------------
  -- BR112–115 scalar generator and F normal scale source attachments.
  -- These are geometric/source expressions, not analytic inverse proofs.
  ------------------------------------------------------------------------
  originalFGeneratorConormalTangential : S → Vec → Vec
  originalFGeneratorConormalTangential j w a = j * w a

  originalFOpticalGeneratorPotential : S → S → S
  originalFOpticalGeneratorPotential k derivativeK =
    (three * half) * derivativeK + (three * three * quarter) * (k * k)

  originalFOpticalGeneratorJump : S → S → S → S
  originalFOpticalGeneratorJump j a derivativeJump =
    derivativeJump - (three * half) * j * a

  originalFScaleNeumannPlus : S → S → S → S
  originalFScaleNeumannPlus j c src = two * j + c + src

  originalFScaleNeumannMinus : S → S → S → S
  originalFScaleNeumannMinus j c src = neg (two * j) + c + src

  originalFScaleNeumannJumpSource : S → S → S
  originalFScaleNeumannJumpSource j sourceJump = four * j + sourceJump

  -- BR114 finite scalar reference Green estimate and BR115 glancing
  -- loss are separate analytic acceptance obligations. No promotion.


  ------------------------------------------------------------------------
  -- BR116–119 structured scale source and defining-function variation.
  -- Algebraic contractions supplied by the original geometry. Not an
  -- analytic proof of the scalar inverse or nonzero curved evolution.
  ------------------------------------------------------------------------
  originalFAKScaleSource : S → S → S → S → S → S
  originalFAKScaleSource k normalL l gaugeNormal reducedNN =
    (three * two) * k * normalL + (four * two) * l
    + two * k * gaugeNormal - reducedNN

  originalFShapeVariationSource : S → S → S → S → S → S
  originalFShapeVariationSource tau nPsi deltaNPsi deltaQ shearPair =
    (nPsi + half * tau) * deltaNPsi
    - (nPsi - half * tau) * deltaQ - two * shearPair

  originalFDefiningScaleVariation : S → S → S → S
  originalFDefiningScaleVariation metricNN lambda normalSigma =
    half * metricNN - lambda * normalSigma

  originalFDefiningNormalTangentVariation : S → Vec → Vec → Vec
  originalFDefiningNormalTangentVariation lambda metricNormalTang gradSigma a =
    neg (metricNormalTang a) + lambda * gradSigma a

  originalFDefiningMeanVariation : S → S → S → S
  originalFDefiningMeanVariation lambda leafBoxSigma gradPair =
    lambda * (leafBoxSigma + two * gradPair)

  originalFAKScaleOpticalPotential : S → S → S
  originalFAKScaleOpticalPotential b kOpt =
    ((three * four + U) * half) * (b * b)
    + (three * three * quarter) * (kOpt * kOpt)

  -- For full foliation transport, delta phi=V(phi); for graph-only
  -- lift the normal jet is independent. Retain that distinction.


  ------------------------------------------------------------------------
  -- BR120–123: arbitrary contracted source jump and material chart BIDI.
  -- The ambient tangential shape extension and its intrinsic trace are
  -- supplied by actual geometry; lambda and n are the same defining jet.
  ------------------------------------------------------------------------
  originalFDerivativeJumpInverse : S → Tensor → S → Cov → Cov → Tensor
  originalFDerivativeJumpInverse l tangentB traceB n src =
    tab (λ i k → l * (two * get tangentB i k
      + two * traceB * n i * n k + n i * src k + src i * n k))

  originalFPureTensionSourceJump : S → S → Tensor → Cov → Cov → Tensor
  originalFPureTensionSourceJump l j g n src =
    tab (λ i k → l * (two * j * get g i k
      + (three * two) * j * n i * n k + n i * src k + src i * n k))

  originalFScaleValueJump : S → Cov → Tensor
  originalFScaleValueJump p n =
    tab (λ i k → two * p * n i * n k)

  originalFGeneratorValueJump : S → Tensor → S → Cov → Tensor
  originalFGeneratorValueJump f derivativeJump p n =
    addT (mulT f derivativeJump) (originalFScaleValueJump p n)

  originalFMovingMetricValueJump : S → Tensor → Tensor
  originalFMovingMetricValueJump f derivativeJump =
    mulT (neg f) derivativeJump

  originalFTransportedGaugeJump : Cov → Cov → Cov
  originalFTransportedGaugeJump plusP minusP i =
    minusP i - plusP i

  originalFScalarVectorCommutator : S → S → S
  originalFScalarVectorCommutator connectionHessianPair vectorCurvaturePair =
    two * connectionHessianPair + vectorCurvaturePair

  -- Jet expressions only: arbitrary h/source inverse requires the
  -- geometric hypotheses of BR120; a normally hyperbolic generator
  -- inverse and physical constrained curvature estimate remain open.


  ------------------------------------------------------------------------
  -- BR124–127: Gauss source, effective Weyl shape and Riccati transport.
  -- These are signed Lorentz contractions, not positive-energy norms.
  ------------------------------------------------------------------------
  originalFGaussMeanScalar : S → S → S → S
  originalFGaussMeanScalar j shapeSquare gaussDefect =
    neg (three * four) + three * j * j - shapeSquare + gaussDefect

  originalFGaussShearVariation : S → S → S → S → S
  originalFGaussShearVariation j deltaJ deltaScalar deltaDefect =
    deltaScalar - (three * two) * j * deltaJ - deltaDefect

  -- inverseJ must be an actual reciprocal of nonzero tension.
  originalFEffectiveMeanShape : S → Tensor → Tensor → Tensor
  originalFEffectiveMeanShape inverseJ meanTF defectTF =
    addT meanTF (mulT (third * inverseJ) defectTF)

  originalFWeylElectricJump : S → Tensor → Tensor
  originalFWeylElectricJump j effectiveShape =
    mulT (two * j) effectiveShape

  originalFWeylMeanInverse : S → Tensor → Tensor → Tensor
  originalFWeylMeanInverse inverseJ electricJump defectTF =
    subT (mulT (half * inverseJ) electricJump)
         (mulT (third * inverseJ) defectTF)

  originalFRiccatiLinearSource : S → S → S → S
  originalFRiccatiLinearSource electric leftShape rightShape =
    neg electric - leftShape - rightShape

  -- BR126 combines active AND zero-speed characteristic observations.
  -- The actual analytic trace/constraint propagation, normal chart
  -- regularity, and variable coupled curvature energy remain separate.
