module DASHI.Physics.YangMills.BalabanCMP109BishopPrincipalLogAdPolynomialExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Remove the rational-coefficient mismatch in the older CMP109 Jacobian lane.
-- The actual inverse-dexp Bernoulli coefficient is a Bishop real, so the
-- principal-log differential must not be forced through an ℚ-valued c2 socket.
--
-- On the literal three-dimensional su(2) coordinate carrier define
--
--   J_(c1,beta,X) v
--     = v + c1 [X,v] + beta [X,[X,v]].
--
-- This file proves the exact coefficient telescope directly over Bishop reals:
--
--   J_beta v - J_beta0 v
--     = (beta-beta0) [X,[X,v]].
--
-- The theorem is then specialized to the repository's ACTUAL constructive
-- inverse-dexp coefficient at the CMP109 source radius.  Thus the checked
-- endpoint modulus 0 <= beta-1/12 <= 1/14400 now controls the same Bishop-real
-- operator that enters the printed principal-log derivative.  No rational
-- surrogate for beta is introduced.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_; 0ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopProperties
import Inverse as BishopInverse
open import Data.Sum.Base using (inj₂)

import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
import DASHI.Physics.YangMills.BalabanCMP109BishopInverseDexpCoefficientEndpointModulusExact as Endpoint
import DASHI.Physics.YangMills.BalabanCMP109BishopSourceRadiusEndpointExact as Source
open import DASHI.Physics.YangMills.CompactLieProofLevel

record Vec3B : Set where
  constructor vec3B
  field x y z : BishopReal.ℝ
open Vec3B public

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

oneTwelfth : ℚᵘ
oneTwelfth = + 1 / 12

add3 : Vec3B → Vec3B → Vec3B
add3 (vec3B ax ay az) (vec3B bx by bz) =
  vec3B
    (BishopReal._+_ ax bx)
    (BishopReal._+_ ay by)
    (BishopReal._+_ az bz)

sub3 : Vec3B → Vec3B → Vec3B
sub3 (vec3B ax ay az) (vec3B bx by bz) =
  vec3B
    (BishopReal._-_ ax bx)
    (BishopReal._-_ ay by)
    (BishopReal._-_ az bz)

scale3 : BishopReal.ℝ → Vec3B → Vec3B
scale3 scalar (vec3B vx vy vz) =
  vec3B
    (BishopReal._*_ scalar vx)
    (BishopReal._*_ scalar vy)
    (BishopReal._*_ scalar vz)

bracket3 : Vec3B → Vec3B → Vec3B
bracket3 (vec3B x0 x1 x2) (vec3B v0 v1 v2) =
  vec3B
    (BishopReal._-_ (BishopReal._*_ x1 v2) (BishopReal._*_ x2 v1))
    (BishopReal._-_ (BishopReal._*_ x2 v0) (BishopReal._*_ x0 v2))
    (BishopReal._-_ (BishopReal._*_ x0 v1) (BishopReal._*_ x1 v0))

adSquare3 : Vec3B → Vec3B → Vec3B
adSquare3 generator value = bracket3 generator (bracket3 generator value)

principalLogAdApply :
  BishopReal.ℝ → BishopReal.ℝ → Vec3B → Vec3B → Vec3B
principalLogAdApply c1 beta generator value =
  add3 value
    (add3
      (scale3 c1 (bracket3 generator value))
      (scale3 beta (adSquare3 generator value)))

vec3Congruent : Vec3B → Vec3B → Set
vec3Congruent left right =
  BishopReal._≃_ (x left) (x right)
  × (BishopReal._≃_ (y left) (y right)
    × BishopReal._≃_ (z left) (z right))

principalLogCoefficientTelescope :
  ∀ c1 beta beta0 generator value →
  vec3Congruent
    (sub3
      (principalLogAdApply c1 beta generator value)
      (principalLogAdApply c1 beta0 generator value))
    (scale3 (BishopReal._-_ beta beta0) (adSquare3 generator value))
principalLogCoefficientTelescope c1 beta beta0
    (vec3B x0 x1 x2) (vec3B v0 v1 v2) =
  (let open BishopProperties.ℝ-Solver
   in solve 9
     (λ c b b0 x0 x1 x2 v0 v1 v2 →
       let
         a0 = (x1 ⊗ (x0 ⊗ v1 ⊖ x1 ⊗ v0))
              ⊖ (x2 ⊗ (x2 ⊗ v0 ⊖ x0 ⊗ v2))
       in
       ((v0 ⊕ ((c ⊗ (x1 ⊗ v2 ⊖ x2 ⊗ v1)) ⊕ (b ⊗ a0)))
        ⊖ (v0 ⊕ ((c ⊗ (x1 ⊗ v2 ⊖ x2 ⊗ v1)) ⊕ (b0 ⊗ a0))))
       ⊜ ((b ⊖ b0) ⊗ a0))
     BishopProperties.≃-refl
     c1 beta beta0 x0 x1 x2 v0 v1 v2)
  ,
  ((let open BishopProperties.ℝ-Solver
    in solve 9
      (λ c b b0 x0 x1 x2 v0 v1 v2 →
        let
          a1 = (x2 ⊗ (x1 ⊗ v2 ⊖ x2 ⊗ v1))
               ⊖ (x0 ⊗ (x0 ⊗ v1 ⊖ x1 ⊗ v0))
        in
        ((v1 ⊕ ((c ⊗ (x2 ⊗ v0 ⊖ x0 ⊗ v2)) ⊕ (b ⊗ a1)))
         ⊖ (v1 ⊕ ((c ⊗ (x2 ⊗ v0 ⊖ x0 ⊗ v2)) ⊕ (b0 ⊗ a1))))
        ⊜ ((b ⊖ b0) ⊗ a1))
      BishopProperties.≃-refl
      c1 beta beta0 x0 x1 x2 v0 v1 v2)
   ,
   (let open BishopProperties.ℝ-Solver
    in solve 9
      (λ c b b0 x0 x1 x2 v0 v1 v2 →
        let
          a2 = (x0 ⊗ (x2 ⊗ v0 ⊖ x0 ⊗ v2))
               ⊖ (x1 ⊗ (x1 ⊗ v2 ⊖ x2 ⊗ v1))
        in
        ((v2 ⊕ ((c ⊗ (x0 ⊗ v1 ⊖ x1 ⊗ v0)) ⊕ (b ⊗ a2)))
         ⊖ (v2 ⊕ ((c ⊗ (x0 ⊗ v1 ⊖ x1 ⊗ v0)) ⊕ (b0 ⊗ a2))))
        ⊜ ((b ⊖ b0) ⊗ a2))
      BishopProperties.≃-refl
      c1 beta beta0 x0 x1 x2 v0 v1 v2))

actualSourceInverseDexpCoefficient :
  ∀ {dataSet} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet Source.sourceRadiusValue →
  BishopReal.ℝ
actualSourceInverseDexpCoefficient inputs =
  Positive.inverseDexpCoefficientPositive inputs Source.sourceRadiusPositive

actualSourcePrincipalLogCoefficientTelescope :
  ∀ {dataSet}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs
      dataSet Source.sourceRadiusValue)
    c1 generator value →
  vec3Congruent
    (sub3
      (principalLogAdApply c1
        (actualSourceInverseDexpCoefficient inputs) generator value)
      (principalLogAdApply c1 (embed oneTwelfth) generator value))
    (scale3
      (Endpoint.coefficientEndpointDefect inputs Source.sourceRadiusPositive)
      (adSquare3 generator value))
actualSourcePrincipalLogCoefficientTelescope inputs c1 generator value =
  principalLogCoefficientTelescope
    c1
    (actualSourceInverseDexpCoefficient inputs)
    (embed oneTwelfth)
    generator value

cmp109BishopPrincipalLogAdPolynomialLevel : ProofLevel
cmp109BishopPrincipalLogAdPolynomialLevel = machineChecked

cmp109BishopActualCoefficientSameOperatorLevel : ProofLevel
cmp109BishopActualCoefficientSameOperatorLevel = machineChecked

-- The remaining CMP109 seam is now only identification of this literal
-- Bishop-real ad-polynomial with the paper's chosen left/right trivialized
-- product derivative.  The coefficient and its source-radius modulus are on
-- the correct carrier already.
cmp109PrintedBishopAdPolynomialTrivializationLevel : ProofLevel
cmp109PrintedBishopAdPolynomialTrivializationLevel = conditional

------------------------------------------------------------------------
-- Root-free inverse algebra for arbitrary coefficients (not a series axiom).
-- g is the ACTUAL ad generator: for pure quaternions g=2Y.
-- D=I+aX+bX², h=1-wb, d=h²+wa².
-- N=d I-aX+(a²-hb)X², ND=dI.
-- No nonzero hypothesis is needed for this denominator-cleared identity.
------------------------------------------------------------------------

generatorSq : Vec3B → BishopReal.ℝ
generatorSq (vec3B x0 x1 x2) =
  BishopReal._+_ (BishopReal._*_ x0 x0)
    (BishopReal._+_ (BishopReal._*_ x1 x1) (BishopReal._*_ x2 x2))

reducedH : Vec3B → BishopReal.ℝ → BishopReal.ℝ
reducedH g b = BishopReal._-_ BishopReal.1ℝ
  (BishopReal._*_ (generatorSq g) b)

reducedDelta : Vec3B → BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ
reducedDelta g a b =
  BishopReal._+_
    (BishopReal._*_ (reducedH g b) (reducedH g b))
    (BishopReal._*_ (generatorSq g) (BishopReal._*_ a a))

reducedNumerator : Vec3B → BishopReal.ℝ → BishopReal.ℝ → Vec3B → Vec3B
reducedNumerator g a b v =
  add3 (scale3 (reducedDelta g a b) v)
    (add3 (scale3 (BishopReal.- a) (bracket3 g v))
      (scale3
        (BishopReal._-_ (BishopReal._*_ a a)
          (BishopReal._*_ (reducedH g b) b))
        (adSquare3 g v)))

reducedScaledLeftInverse :
  ∀ g a b v →
  vec3Congruent
    (reducedNumerator g a b (principalLogAdApply a b g v))
    (scale3 (reducedDelta g a b) v)
reducedScaledLeftInverse (vec3B gx gy gz) a b (vec3B vx vy vz) =
  (let open BishopProperties.ℝ-Solver
   in solve 8
     (λ gx gy gz a b vx vy vz →
       let
         w = (gx ⊗ gx) ⊕ ((gy ⊗ gy) ⊕ (gz ⊗ gz))
         h = Κ (+ 1 / 1) ⊖ (w ⊗ b)
         d = (h ⊗ h) ⊕ (w ⊗ (a ⊗ a))
         k = (a ⊗ a) ⊖ (h ⊗ b)
         p0 = gy ⊗ vz ⊖ gz ⊗ vy
         p1 = gz ⊗ vx ⊖ gx ⊗ vz
         p2 = gx ⊗ vy ⊖ gy ⊗ vx
         q0 = gy ⊗ p2 ⊖ gz ⊗ p1
         q1 = gz ⊗ p0 ⊖ gx ⊗ p2
         q2 = gx ⊗ p1 ⊖ gy ⊗ p0
         r0 = vx ⊕ ((a ⊗ p0) ⊕ (b ⊗ q0))
         r1 = vy ⊕ ((a ⊗ p1) ⊕ (b ⊗ q1))
         r2 = vz ⊕ ((a ⊗ p2) ⊕ (b ⊗ q2))
         s0 = gy ⊗ r2 ⊖ gz ⊗ r1
         s1 = gz ⊗ r0 ⊖ gx ⊗ r2
         s2 = gx ⊗ r1 ⊖ gy ⊗ r0
         t0 = gy ⊗ s2 ⊖ gz ⊗ s1
         t1 = gz ⊗ s0 ⊖ gx ⊗ s2
         t2 = gx ⊗ s1 ⊖ gy ⊗ s0
       in
         ((d ⊗ r0) ⊕ (((⊝ a) ⊗ s0) ⊕ (k ⊗ t0)))
         ⊜ (d ⊗ vx))
     BishopProperties.≃-refl gx gy gz a b vx vy vz) ,
  ((let open BishopProperties.ℝ-Solver
   in solve 8
     (λ gx gy gz a b vx vy vz →
       let
         w = (gx ⊗ gx) ⊕ ((gy ⊗ gy) ⊕ (gz ⊗ gz))
         h = Κ (+ 1 / 1) ⊖ (w ⊗ b)
         d = (h ⊗ h) ⊕ (w ⊗ (a ⊗ a))
         k = (a ⊗ a) ⊖ (h ⊗ b)
         p0 = gy ⊗ vz ⊖ gz ⊗ vy
         p1 = gz ⊗ vx ⊖ gx ⊗ vz
         p2 = gx ⊗ vy ⊖ gy ⊗ vx
         q0 = gy ⊗ p2 ⊖ gz ⊗ p1
         q1 = gz ⊗ p0 ⊖ gx ⊗ p2
         q2 = gx ⊗ p1 ⊖ gy ⊗ p0
         r0 = vx ⊕ ((a ⊗ p0) ⊕ (b ⊗ q0))
         r1 = vy ⊕ ((a ⊗ p1) ⊕ (b ⊗ q1))
         r2 = vz ⊕ ((a ⊗ p2) ⊕ (b ⊗ q2))
         s0 = gy ⊗ r2 ⊖ gz ⊗ r1
         s1 = gz ⊗ r0 ⊖ gx ⊗ r2
         s2 = gx ⊗ r1 ⊖ gy ⊗ r0
         t0 = gy ⊗ s2 ⊖ gz ⊗ s1
         t1 = gz ⊗ s0 ⊖ gx ⊗ s2
         t2 = gx ⊗ s1 ⊖ gy ⊗ s0
       in
         ((d ⊗ r1) ⊕ (((⊝ a) ⊗ s1) ⊕ (k ⊗ t1)))
         ⊜ (d ⊗ vy))
     BishopProperties.≃-refl gx gy gz a b vx vy vz) ,
  (let open BishopProperties.ℝ-Solver
   in solve 8
     (λ gx gy gz a b vx vy vz →
       let
         w = (gx ⊗ gx) ⊕ ((gy ⊗ gy) ⊕ (gz ⊗ gz))
         h = Κ (+ 1 / 1) ⊖ (w ⊗ b)
         d = (h ⊗ h) ⊕ (w ⊗ (a ⊗ a))
         k = (a ⊗ a) ⊖ (h ⊗ b)
         p0 = gy ⊗ vz ⊖ gz ⊗ vy
         p1 = gz ⊗ vx ⊖ gx ⊗ vz
         p2 = gx ⊗ vy ⊖ gy ⊗ vx
         q0 = gy ⊗ p2 ⊖ gz ⊗ p1
         q1 = gz ⊗ p0 ⊖ gx ⊗ p2
         q2 = gx ⊗ p1 ⊖ gy ⊗ p0
         r0 = vx ⊕ ((a ⊗ p0) ⊕ (b ⊗ q0))
         r1 = vy ⊕ ((a ⊗ p1) ⊕ (b ⊗ q1))
         r2 = vz ⊕ ((a ⊗ p2) ⊕ (b ⊗ q2))
         s0 = gy ⊗ r2 ⊖ gz ⊗ r1
         s1 = gz ⊗ r0 ⊖ gx ⊗ r2
         s2 = gx ⊗ r1 ⊖ gy ⊗ r0
         t0 = gy ⊗ s2 ⊖ gz ⊗ s1
         t1 = gz ⊗ s0 ⊖ gx ⊗ s2
         t2 = gx ⊗ s1 ⊖ gy ⊗ s0
       in
         ((d ⊗ r2) ⊕ (((⊝ a) ⊗ s2) ⊕ (k ⊗ t2)))
         ⊜ (d ⊗ vz))
     BishopProperties.≃-refl gx gy gz a b vx vy vz))

-- An actual inverse from denominator positivity alone.  No analytic
-- operator-cancellation hypothesis is accepted by this construction.
reducedInverse : ∀ g a b →
  BishopReal._<_ BishopReal.0ℝ (reducedDelta g a b) →
  Vec3B → Vec3B
reducedInverse g a b positive v =
  scale3
    (BishopInverse._⁻¹ (reducedDelta g a b) (inj₂ positive))
    (reducedNumerator g a b v)

cancelPositiveScale : ∀ d → (positive : BishopReal._<_ BishopReal.0ℝ d) →
  ∀ u v → BishopReal._≃_ u (BishopReal._*_ d v) →
  BishopReal._≃_
    (BishopReal._*_ (BishopInverse._⁻¹ d (inj₂ positive)) u) v
cancelPositiveScale d positive u v equal =
  let
    dinv = BishopInverse._⁻¹ d (inj₂ positive)
    inverseLeft =
      BishopProperties.≃-trans
        (BishopProperties.*-comm dinv d)
        (BishopInverse.*-inverseʳ d (inj₂ positive))
  in
  BishopProperties.≃-trans
    (BishopProperties.*-congˡ equal)
    (BishopProperties.≃-trans
      (BishopProperties.≃-symm (BishopProperties.*-assoc dinv d v))
      (BishopProperties.≃-trans
        (BishopProperties.*-congʳ inverseLeft)
        (BishopProperties.*-identityˡ v)))

reducedLeftInverse :
  ∀ g a b (positive : BishopReal._<_ BishopReal.0ℝ (reducedDelta g a b)) v →
  vec3Congruent
    (reducedInverse g a b positive (principalLogAdApply a b g v)) v
reducedLeftInverse g a b positive v
  with reducedScaledLeftInverse g a b v
... | ex , (ey , ez) =
  let d = reducedDelta g a b
      u = reducedNumerator g a b (principalLogAdApply a b g v)
  in
  cancelPositiveScale d positive (x u) (x v) ex ,
  (cancelPositiveScale d positive (y u) (y v) ey ,
   cancelPositiveScale d positive (z u) (z v) ez)

-- Small-radius denominator floor. A positive coefficient is not needed;
-- its nonnegativity suffices for the square term. These bounds are the
-- elementary alternating factorial-series bounds on 0 <= w <= 1/4.
reducedHLower :
  ∀ g b →
  BishopReal._≤_ BishopReal.0ℝ (generatorSq g) →
  BishopReal._≤_ (generatorSq g) (embed (+ 1 / 4)) →
  BishopReal._≤_ BishopReal.0ℝ b →
  BishopReal._≤_ b (embed (+ 1 / 6)) →
  BishopReal._≤_ (embed (+ 23 / 24)) (reducedH g b)
reducedHLower g b wn wu bn bu =
  let
    productBound = BishopProperties.*-mono-≤
      (BishopProperties.0≤x⇒nonNegx wn)
      (BishopProperties.0≤x⇒nonNegx bn) wu bu
    shifted = BishopProperties.+-monoʳ-≤ BishopReal.1ℝ
      (BishopProperties.neg-mono-≤ productBound)
  in
  BishopProperties.≤-respˡ-≃
    (BishopProperties.≃-symm
      (let open BishopProperties.ℝ-Solver
       in solve 0
         (Κ (+ 23 / 24) ⊜ Κ (+ 1 / 1) ⊕
           (⊝ (Κ (+ 1 / 4) ⊗ Κ (+ 1 / 6))))
         BishopProperties.≃-refl))
    (BishopProperties.≤-respʳ-≃
      (let open BishopProperties.ℝ-Solver
       in solve 2 (λ w b → Κ (+ 1 / 1) ⊕ (⊝ (w ⊗ b))
                         ⊜ Κ (+ 1 / 1) ⊖ (w ⊗ b))
         BishopProperties.≃-refl (generatorSq g) b)
      shifted)

reducedDeltaLower :
  ∀ g a b →
  BishopReal._≤_ BishopReal.0ℝ (generatorSq g) →
  BishopReal._≤_ (generatorSq g) (embed (+ 1 / 4)) →
  BishopReal._≤_ BishopReal.0ℝ a →
  BishopReal._≤_ BishopReal.0ℝ b →
  BishopReal._≤_ b (embed (+ 1 / 6)) →
  BishopReal._≤_ (embed (+ 529 / 576)) (reducedDelta g a b)
reducedDeltaLower g a b wn wu an bn bu =
  let
    h = reducedH g b
    hl = reducedHLower g b wn wu bn bu
    cPositive = Positive.positiveTwentyThreeTwentyFourth
    cNonnegative = BishopProperties.pos⇒nonNeg
      (BishopProperties.0<x⇒posx cPositive)
    hSqFloor = BishopProperties.≤-respˡ-≃
      (BishopProperties.≃-symm
        (let open BishopProperties.ℝ-Solver
         in solve 0
           (Κ (+ 529 / 576) ⊜ Κ (+ 23 / 24) ⊗ Κ (+ 23 / 24))
           BishopProperties.≃-refl))
      (BishopProperties.*-mono-≤ cNonnegative cNonnegative hl hl)
    tailNN = BishopProperties.nonNegx,y⇒nonNegx*y
      (BishopProperties.0≤x⇒nonNegx wn)
      (BishopProperties.nonNegx,y⇒nonNegx*y
        (BishopProperties.0≤x⇒nonNegx an)
        (BishopProperties.0≤x⇒nonNegx an))
    hSqBelowDelta = BishopProperties.≤-respˡ-≃
      (BishopProperties.+-identityʳ (BishopReal._*_ h h))
      (BishopProperties.+-monoʳ-≤ (BishopReal._*_ h h)
        (BishopProperties.nonNegx⇒0≤x tailNN))
  in BishopProperties.≤-trans hSqFloor hSqBelowDelta

reducedDeltaPositiveFromBounds :
  ∀ g a b →
  BishopReal._≤_ BishopReal.0ℝ (generatorSq g) →
  BishopReal._≤_ (generatorSq g) (embed (+ 1 / 4)) →
  BishopReal._≤_ BishopReal.0ℝ a →
  BishopReal._≤_ BishopReal.0ℝ b →
  BishopReal._≤_ b (embed (+ 1 / 6)) →
  BishopReal._<_ BishopReal.0ℝ (reducedDelta g a b)
reducedDeltaPositiveFromBounds g a b wn wu an bn bu =
  BishopProperties.<-≤-trans
    (BishopProperties.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 529 / 576)
      (ℚP.positive⁻¹ (+ 529 / 576)))
    (reducedDeltaLower g a b wn wu an bn bu)
