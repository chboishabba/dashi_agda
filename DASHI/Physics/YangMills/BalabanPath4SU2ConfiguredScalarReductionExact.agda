module DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredScalarReductionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
  using (side4; average0123)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using
    ( ScalarBondField4
    ; literalPeriodicDivergenceScalar
    ; literalNegativeForwardGradientScalar
    ; backwardForwardDifferenceCommutes
    ; axis0
    ; axis1
    ; axis2
    ; axis3
    )
open import DASHI.Physics.YangMills.BalabanConfiguredSide4ScalarWilsonOperatorExact
  using (scalarPlaneCurl; scalarWilsonOperator)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using (componentScalarBondField)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredMatrixActionExact
  using
    ( literalGaugePenalty
    ; configuredGaugeFixedMatrixPointwise
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact
  using (fineProjection)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact
  using (configuredGaugeFixedMatrix)

subtractSiteField : SiteField side4 → SiteField side4 → SiteField side4
subtractSiteField left right site = left site - right site

diffSubRaw : ∀ a1 a2 b1 b2 → (a1 - b1) - (a2 - b2) ≡ (a1 - a2) - (b1 - b2)
diffSubRaw = ℚRing.solve-∀

backwardDifferenceSubtract : ∀ axis left right site →
  backwardDifference4 axis (subtractSiteField left right) site
  ≡ backwardDifference4 axis left site
    - backwardDifference4 axis right site
backwardDifferenceSubtract axis left right site =
  diffSubRaw
    (left site)
    (left (shiftBackward4 axis site))
    (right site)
    (right (shiftBackward4 axis site))

backwardPlaneCurlExpand : ∀ backwardAxis plane fld site →
  backwardDifference4 backwardAxis (scalarPlaneCurl plane fld) site
  ≡ backwardDifference4 backwardAxis
      (forwardDifference4 (positivePlaneFirst plane)
        (fld (positivePlaneSecond plane))) site
    - backwardDifference4 backwardAxis
      (forwardDifference4 (positivePlaneSecond plane)
        (fld (positivePlaneFirst plane))) site
backwardPlaneCurlExpand backwardAxis plane fld =
  backwardDifferenceSubtract backwardAxis
    (forwardDifference4 (positivePlaneFirst plane)
      (fld (positivePlaneSecond plane)))
    (forwardDifference4 (positivePlaneSecond plane)
      (fld (positivePlaneFirst plane)))

scalarGaugePenalty : ScalarBondField4 → ScalarBondField4
scalarGaugePenalty fld =
  literalNegativeForwardGradientScalar
    (literalPeriodicDivergenceScalar fld)

scalarForwardBackwardLaplacian : ScalarBondField4 → ScalarBondField4
scalarForwardBackwardLaplacian fld componentAxis site =
  - sumRational (allCyclicIndices four)
      (λ derivativeAxis →
        forwardDifference4 derivativeAxis
          (backwardDifference4 derivativeAxis (fld componentAxis)) site)

addSubSplitRaw : ∀ a1 a2 b1 b2 → (a1 + a2) - (b1 + b2) ≡ (a1 - b1) + (a2 - b2)
addSubSplitRaw = ℚRing.solve-∀

subZeroRaw : ∀ a b → (a + 0ℚ) - (b + 0ℚ) ≡ (a - b) + 0ℚ
subZeroRaw = ℚRing.solve-∀

fourSumSubSplit : ∀ a0 b0 a1 b1 a2 b2 a3 b3 →
  (a0 + (a1 + (a2 + (a3 + 0ℚ)))) - (b0 + (b1 + (b2 + (b3 + 0ℚ))))
  ≡ (a0 - b0) + ((a1 - b1) + ((a2 - b2) + ((a3 - b3) + 0ℚ)))
fourSumSubSplit a0 b0 a1 b1 a2 b2 a3 b3 =
  trans
    (addSubSplitRaw a0 (a1 + (a2 + (a3 + 0ℚ))) b0 (b1 + (b2 + (b3 + 0ℚ))))
    (cong ((a0 - b0) +_)
      (trans
        (addSubSplitRaw a1 (a2 + (a3 + 0ℚ)) b1 (b2 + (b3 + 0ℚ)))
        (cong ((a1 - b1) +_)
          (trans
            (addSubSplitRaw a2 (a3 + 0ℚ) b2 (b3 + 0ℚ))
            (cong ((a2 - b2) +_) (subZeroRaw a3 b3))))))

tail0Raw : ∀ d2 d3 l2 l3 →
  (d2 - l2) + ((d3 - l3) + (0ℚ + (0ℚ + (0ℚ + 0ℚ))))
  ≡ (d2 + (d3 + 0ℚ)) - (l2 + (l3 + 0ℚ))
tail0Raw = ℚRing.solve-∀

collapse0CoreRaw : ∀ d0 d1 d23 l1 l23 →
  ((d1 - l1) + (d23 - l23)) + (- (d0 + (d1 + d23)))
  ≡ - (d0 + (l1 + l23))
collapse0CoreRaw = ℚRing.solve-∀

collapse0Raw : ∀ d00f d00s d10f d10s d20f d20s d30f d30s l1 l2 l3 →
  (((d10f - d10s) - l1)
   + (((d20f - d20s) - l2)
   + (((d30f - d30s) - l3)
   + (0ℚ + (0ℚ + (0ℚ + 0ℚ))))))
  + (- ((d00f + (d10f + (d20f + (d30f + 0ℚ))))
        - (d00s + (d10s + (d20s + (d30s + 0ℚ))))))
  ≡ - ((d00f - d00s) + (l1 + (l2 + (l3 + 0ℚ))))
collapse0Raw d00f d00s d10f d10s d20f d20s d30f d30s l1 l2 l3 =
  trans
    (cong₂ _+_
      (cong (((d10f - d10s) - l1) +_)
        (tail0Raw (d20f - d20s) (d30f - d30s) l2 l3))
      (cong -_
        (fourSumSubSplit d00f d00s d10f d10s d20f d20s d30f d30s)))
    (collapse0CoreRaw
      (d00f - d00s)
      (d10f - d10s)
      ((d20f - d20s) + ((d30f - d30s) + 0ℚ))
      l1
      (l2 + (l3 + 0ℚ)))

tail1Raw : ∀ d2 d3 l2 l3 →
  0ℚ + (0ℚ + ((d2 - l2) + ((d3 - l3) + (0ℚ + 0ℚ))))
  ≡ (d2 + (d3 + 0ℚ)) - (l2 + (l3 + 0ℚ))
tail1Raw = ℚRing.solve-∀

collapse1CoreRaw : ∀ d0 d1 d23 l0 l23 →
  ((- (l0 - d0)) + (d23 - l23)) + (- (d0 + (d1 + d23)))
  ≡ - (l0 + (d1 + l23))
collapse1CoreRaw = ℚRing.solve-∀

collapse1Raw : ∀ d01f d01s d11f d11s d21f d21s d31f d31s l0 l2 l3 →
  ((- (l0 - (d01f - d01s)))
   + (0ℚ
   + (0ℚ
   + (((d21f - d21s) - l2)
   + (((d31f - d31s) - l3)
   + (0ℚ + 0ℚ))))))
  + (- ((d01f + (d11f + (d21f + (d31f + 0ℚ))))
        - (d01s + (d11s + (d21s + (d31s + 0ℚ))))))
  ≡ - (l0 + ((d11f - d11s) + (l2 + (l3 + 0ℚ))))
collapse1Raw d01f d01s d11f d11s d21f d21s d31f d31s l0 l2 l3 =
  trans
    (cong₂ _+_
      (cong ((- (l0 - (d01f - d01s))) +_)
        (tail1Raw (d21f - d21s) (d31f - d31s) l2 l3))
      (cong -_
        (fourSumSubSplit d01f d01s d11f d11s d21f d21s d31f d31s)))
    (collapse1CoreRaw
      (d01f - d01s)
      (d11f - d11s)
      ((d21f - d21s) + ((d31f - d31s) + 0ℚ))
      l0
      (l2 + (l3 + 0ℚ)))

tail2Raw : ∀ d1 d3 l1 l3 →
  0ℚ + ((- (l1 - d1)) + (0ℚ + ((d3 - l3) + 0ℚ)))
  ≡ (d1 + (d3 + 0ℚ)) - (l1 + (l3 + 0ℚ))
tail2Raw = ℚRing.solve-∀

collapse2CoreRaw : ∀ d0 d2 d13 l0 l13 →
  (0ℚ + ((- (l0 - d0)) + (d13 - l13))) + (- (d0 + (d2 + d13)))
  ≡ - (l0 + (d2 + l13))
collapse2CoreRaw = ℚRing.solve-∀

swapMidRaw : ∀ a b c → a + (b + c) ≡ b + (a + c)
swapMidRaw = ℚRing.solve-∀

threeAssocLeftRaw : ∀ a b c → a + (b + c) ≡ (a + b) + c
threeAssocLeftRaw = ℚRing.solve-∀

collapse2Raw : ∀ d02f d02s d12f d12s d22f d22s d32f d32s l0 l1 l3 →
  (0ℚ
   + ((- (l0 - (d02f - d02s)))
   + (0ℚ
   + ((- (l1 - (d12f - d12s)))
   + (0ℚ
   + (((d32f - d32s) - l3) + 0ℚ))))))
  + (- ((d02f + (d12f + (d22f + (d32f + 0ℚ))))
        - (d02s + (d12s + (d22s + (d32s + 0ℚ))))))
  ≡ - (l0 + (l1 + ((d22f - d22s) + (l3 + 0ℚ))))
collapse2Raw d02f d02s d12f d12s d22f d22s d32f d32s l0 l1 l3 =
  trans
    (cong₂ _+_
      (cong (0ℚ +_)
        (cong ((- (l0 - (d02f - d02s))) +_)
          (tail2Raw (d12f - d12s) (d32f - d32s) l1 l3)))
      (cong -_
        (trans
          (fourSumSubSplit d02f d02s d12f d12s d22f d22s d32f d32s)
          (cong ((d02f - d02s) +_)
            (swapMidRaw (d12f - d12s) (d22f - d22s) ((d32f - d32s) + 0ℚ))))))
    (trans
      (collapse2CoreRaw
        (d02f - d02s)
        (d22f - d22s)
        ((d12f - d12s) + ((d32f - d32s) + 0ℚ))
        l0
        (l1 + (l3 + 0ℚ)))
      (cong (λ u → - (l0 + u))
        (swapMidRaw (d22f - d22s) l1 (l3 + 0ℚ))))

tail3Raw : ∀ d1 d2 l1 l2 →
  0ℚ + ((- (l1 - d1)) + ((- (l2 - d2)) + 0ℚ))
  ≡ (d1 + d2) - (l1 + l2)
tail3Raw = ℚRing.solve-∀

collapse3CoreRaw : ∀ d0 d12 d3 l0 l12 →
  (0ℚ + (0ℚ + ((- (l0 - d0)) + (d12 - l12)))) + (- (d0 + (d12 + (d3 + 0ℚ))))
  ≡ - (l0 + (l12 + (d3 + 0ℚ)))
collapse3CoreRaw = ℚRing.solve-∀

collapse3Raw : ∀ d03f d03s d13f d13s d23f d23s d33f d33s l0 l1 l2 →
  (0ℚ
   + (0ℚ
   + ((- (l0 - (d03f - d03s)))
   + (0ℚ
   + ((- (l1 - (d13f - d13s)))
   + ((- (l2 - (d23f - d23s))) + 0ℚ))))))
  + (- ((d03f + (d13f + (d23f + (d33f + 0ℚ))))
        - (d03s + (d13s + (d23s + (d33s + 0ℚ))))))
  ≡ - (l0 + (l1 + (l2 + ((d33f - d33s) + 0ℚ))))
collapse3Raw d03f d03s d13f d13s d23f d23s d33f d33s l0 l1 l2 =
  trans
    (cong₂ _+_
      (cong (0ℚ +_)
        (cong (0ℚ +_)
          (cong ((- (l0 - (d03f - d03s))) +_)
            (tail3Raw (d13f - d13s) (d23f - d23s) l1 l2))))
      (cong -_
        (trans
          (fourSumSubSplit d03f d03s d13f d13s d23f d23s d33f d33s)
          (cong ((d03f - d03s) +_)
            (threeAssocLeftRaw (d13f - d13s) (d23f - d23s) ((d33f - d33s) + 0ℚ))))))
    (trans
      (collapse3CoreRaw
        (d03f - d03s)
        ((d13f - d13s) + (d23f - d23s))
        (d33f - d33s)
        l0
        (l1 + l2))
      (cong (λ u → - (l0 + u))
        (sym (threeAssocLeftRaw l1 l2 ((d33f - d33s) + 0ℚ)))))

planeCurlTermPositive : ∀ bAxis pFirst pSecond (fld : ScalarBondField4) site plane →
  positivePlaneFirst plane ≡ pFirst →
  positivePlaneSecond plane ≡ pSecond →
  backwardDifference4 bAxis (scalarPlaneCurl plane fld) site
  ≡ (backwardDifference4 bAxis (fld pSecond) (shiftForward4 pFirst site)
     - backwardDifference4 bAxis (fld pSecond) site)
    - forwardDifference4 pSecond (backwardDifference4 bAxis (fld pFirst)) site
planeCurlTermPositive bAxis pFirst pSecond fld site plane refl refl =
  trans
    (backwardPlaneCurlExpand bAxis plane fld site)
    (cong₂ _-_
      (backwardForwardDifferenceCommutes bAxis pFirst (fld pSecond) site)
      (backwardForwardDifferenceCommutes bAxis pSecond (fld pFirst) site))

scalarWilsonGaugeCollapse : ∀ (fld : ScalarBondField4) (componentAxis : Axis4) site →
  scalarWilsonOperator fld componentAxis site
    + scalarGaugePenalty fld componentAxis site
  ≡ scalarForwardBackwardLaplacian fld componentAxis site
scalarWilsonGaugeCollapse fld zeroᵢ site =
  trans
    (cong (_+ scalarGaugePenalty fld zeroᵢ site)
      (cong₂ _+_
        (planeCurlTermPositive axis1 axis0 axis1 fld site plane01 refl refl)
        (cong₂ _+_
          (planeCurlTermPositive axis2 axis0 axis2 fld site plane02 refl refl)
          (cong (_+ (0ℚ + (0ℚ + (0ℚ + 0ℚ))))
            (planeCurlTermPositive axis3 axis0 axis3 fld site plane03 refl refl)))))
    (collapse0Raw
      (backwardDifference4 axis0 (fld axis0) (shiftForward4 axis0 site))
      (backwardDifference4 axis0 (fld axis0) site)
      (backwardDifference4 axis1 (fld axis1) (shiftForward4 axis0 site))
      (backwardDifference4 axis1 (fld axis1) site)
      (backwardDifference4 axis2 (fld axis2) (shiftForward4 axis0 site))
      (backwardDifference4 axis2 (fld axis2) site)
      (backwardDifference4 axis3 (fld axis3) (shiftForward4 axis0 site))
      (backwardDifference4 axis3 (fld axis3) site)
      (forwardDifference4 axis1 (backwardDifference4 axis1 (fld axis0)) site)
      (forwardDifference4 axis2 (backwardDifference4 axis2 (fld axis0)) site)
      (forwardDifference4 axis3 (backwardDifference4 axis3 (fld axis0)) site))
scalarWilsonGaugeCollapse fld (sucᵢ zeroᵢ) site =
  trans
    (cong (_+ scalarGaugePenalty fld (sucᵢ zeroᵢ) site)
      (cong₂ _+_
        (cong -_ (planeCurlTermPositive axis0 axis0 axis1 fld site plane01 refl refl))
        (cong (λ u → 0ℚ + (0ℚ + u))
          (cong₂ _+_
            (planeCurlTermPositive axis2 axis1 axis2 fld site plane12 refl refl)
            (cong (_+ (0ℚ + 0ℚ))
              (planeCurlTermPositive axis3 axis1 axis3 fld site plane13 refl refl))))))
    (collapse1Raw
      (backwardDifference4 axis0 (fld axis0) (shiftForward4 axis1 site))
      (backwardDifference4 axis0 (fld axis0) site)
      (backwardDifference4 axis1 (fld axis1) (shiftForward4 axis1 site))
      (backwardDifference4 axis1 (fld axis1) site)
      (backwardDifference4 axis2 (fld axis2) (shiftForward4 axis1 site))
      (backwardDifference4 axis2 (fld axis2) site)
      (backwardDifference4 axis3 (fld axis3) (shiftForward4 axis1 site))
      (backwardDifference4 axis3 (fld axis3) site)
      (forwardDifference4 axis0 (backwardDifference4 axis0 (fld axis1)) site)
      (forwardDifference4 axis2 (backwardDifference4 axis2 (fld axis1)) site)
      (forwardDifference4 axis3 (backwardDifference4 axis3 (fld axis1)) site))
scalarWilsonGaugeCollapse fld (sucᵢ (sucᵢ zeroᵢ)) site =
  trans
    (cong (_+ scalarGaugePenalty fld (sucᵢ (sucᵢ zeroᵢ)) site)
      (cong (0ℚ +_)
        (cong₂ _+_
          (cong -_ (planeCurlTermPositive axis0 axis0 axis2 fld site plane02 refl refl))
          (cong (0ℚ +_)
            (cong₂ _+_
              (cong -_ (planeCurlTermPositive axis1 axis1 axis2 fld site plane12 refl refl))
              (cong (0ℚ +_)
                (cong (_+ 0ℚ)
                  (planeCurlTermPositive axis3 axis2 axis3 fld site plane23 refl refl))))))))
    (collapse2Raw
      (backwardDifference4 axis0 (fld axis0) (shiftForward4 axis2 site))
      (backwardDifference4 axis0 (fld axis0) site)
      (backwardDifference4 axis1 (fld axis1) (shiftForward4 axis2 site))
      (backwardDifference4 axis1 (fld axis1) site)
      (backwardDifference4 axis2 (fld axis2) (shiftForward4 axis2 site))
      (backwardDifference4 axis2 (fld axis2) site)
      (backwardDifference4 axis3 (fld axis3) (shiftForward4 axis2 site))
      (backwardDifference4 axis3 (fld axis3) site)
      (forwardDifference4 axis0 (backwardDifference4 axis0 (fld axis2)) site)
      (forwardDifference4 axis1 (backwardDifference4 axis1 (fld axis2)) site)
      (forwardDifference4 axis3 (backwardDifference4 axis3 (fld axis2)) site))
scalarWilsonGaugeCollapse fld (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong (_+ scalarGaugePenalty fld (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site)
      (cong (λ u → 0ℚ + (0ℚ + u))
        (cong₂ _+_
          (cong -_ (planeCurlTermPositive axis0 axis0 axis3 fld site plane03 refl refl))
          (cong (0ℚ +_)
            (cong₂ _+_
              (cong -_ (planeCurlTermPositive axis1 axis1 axis3 fld site plane13 refl refl))
              (cong (_+ 0ℚ)
                (cong -_ (planeCurlTermPositive axis2 axis2 axis3 fld site plane23 refl refl))))))))
    (collapse3Raw
      (backwardDifference4 axis0 (fld axis0) (shiftForward4 axis3 site))
      (backwardDifference4 axis0 (fld axis0) site)
      (backwardDifference4 axis1 (fld axis1) (shiftForward4 axis3 site))
      (backwardDifference4 axis1 (fld axis1) site)
      (backwardDifference4 axis2 (fld axis2) (shiftForward4 axis3 site))
      (backwardDifference4 axis2 (fld axis2) site)
      (backwardDifference4 axis3 (fld axis3) (shiftForward4 axis3 site))
      (backwardDifference4 axis3 (fld axis3) site)
      (forwardDifference4 axis0 (backwardDifference4 axis0 (fld axis3)) site)
      (forwardDifference4 axis1 (backwardDifference4 axis1 (fld axis3)) site)
      (forwardDifference4 axis2 (backwardDifference4 axis2 (fld axis3)) site))

shiftBackwardAfterForward : ∀ axis site →
  shiftBackward4 axis (shiftForward4 axis site) ≡ site
shiftBackwardAfterForward zeroᵢ (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x0 = refl
shiftBackwardAfterForward (sucᵢ zeroᵢ)
    (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x1 = refl
shiftBackwardAfterForward (sucᵢ (sucᵢ zeroᵢ))
    (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x2 = refl
shiftBackwardAfterForward (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x3 = refl

stencilRaw : ∀ f s b → - ((f - s) - (s - b)) ≡ (s + s) - (f + b)
stencilRaw = ℚRing.solve-∀

negativeForwardBackwardStencil : ∀ (axis : Axis4) (fld : SiteField side4) site →
  - forwardDifference4 axis (backwardDifference4 axis fld) site
  ≡ (fld site + fld site)
      - (fld (shiftForward4 axis site)
        + fld (shiftBackward4 axis site))
negativeForwardBackwardStencil axis fld site =
  trans
    (cong
      (λ u → - ((fld (shiftForward4 axis site) - u) - (fld site - fld (shiftBackward4 axis site))))
      (cong fld (shiftBackwardAfterForward axis site)))
    (stencilRaw
      (fld (shiftForward4 axis site))
      (fld site)
      (fld (shiftBackward4 axis site)))

scalarLocalLaplacian : ScalarBondField4 → ScalarBondField4
scalarLocalLaplacian fld componentAxis site =
  sumRational (allCyclicIndices four)
    (λ derivativeAxis →
      (fld componentAxis site + fld componentAxis site)
      - (fld componentAxis (shiftForward4 derivativeAxis site)
        + fld componentAxis (shiftBackward4 derivativeAxis site)))

fourTermCong : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : ℚ} →
  a0 ≡ b0 → a1 ≡ b1 → a2 ≡ b2 → a3 ≡ b3 →
  a0 + (a1 + (a2 + a3)) ≡ b0 + (b1 + (b2 + b3))
fourTermCong refl refl refl refl = refl

negFourSumRaw : ∀ a0 a1 a2 a3 →
  - (a0 + (a1 + (a2 + (a3 + 0ℚ)))) ≡ (- a0) + ((- a1) + ((- a2) + (- a3)))
negFourSumRaw = ℚRing.solve-∀

fourSumZeroRightRaw : ∀ b0 b1 b2 b3 →
  b0 + (b1 + (b2 + b3)) ≡ b0 + (b1 + (b2 + (b3 + 0ℚ)))
fourSumZeroRightRaw = ℚRing.solve-∀

scalarForwardBackwardEqualsLocal : ∀ (fld : ScalarBondField4) (componentAxis : Axis4) site →
  scalarForwardBackwardLaplacian fld componentAxis site
  ≡ scalarLocalLaplacian fld componentAxis site
scalarForwardBackwardEqualsLocal fld componentAxis site =
  trans
    (negFourSumRaw
      (forwardDifference4 axis0 (backwardDifference4 axis0 (fld componentAxis)) site)
      (forwardDifference4 axis1 (backwardDifference4 axis1 (fld componentAxis)) site)
      (forwardDifference4 axis2 (backwardDifference4 axis2 (fld componentAxis)) site)
      (forwardDifference4 axis3 (backwardDifference4 axis3 (fld componentAxis)) site))
    (trans
      (fourTermCong
        (negativeForwardBackwardStencil axis0 (fld componentAxis) site)
        (negativeForwardBackwardStencil axis1 (fld componentAxis) site)
        (negativeForwardBackwardStencil axis2 (fld componentAxis) site)
        (negativeForwardBackwardStencil axis3 (fld componentAxis) site))
      (fourSumZeroRightRaw
        ((fld componentAxis site + fld componentAxis site) - (fld componentAxis (shiftForward4 axis0 site) + fld componentAxis (shiftBackward4 axis0 site)))
        ((fld componentAxis site + fld componentAxis site) - (fld componentAxis (shiftForward4 axis1 site) + fld componentAxis (shiftBackward4 axis1 site)))
        ((fld componentAxis site + fld componentAxis site) - (fld componentAxis (shiftForward4 axis2 site) + fld componentAxis (shiftBackward4 axis2 site)))
        ((fld componentAxis site + fld componentAxis site) - (fld componentAxis (shiftForward4 axis3 site) + fld componentAxis (shiftBackward4 axis3 site)))))

configuredGaugeFixedMatrixEqualsLaplacianPlusMean :
  ∀ tangent component site bondAxis →
  configuredGaugeFixedMatrix tangent component (pair site bondAxis)
  ≡ scalarLocalLaplacian
      (componentScalarBondField tangent component) bondAxis site
    + average0123
      (componentScalarBondField tangent component bondAxis) site
configuredGaugeFixedMatrixEqualsLaplacianPlusMean tangent component1 site bondAxis =
  trans
    (threeAssocLeftRaw
      (scalarWilsonOperator (componentScalarBondField tangent component1) bondAxis site)
      (scalarGaugePenalty (componentScalarBondField tangent component1) bondAxis site)
      (fineProjection tangent component1 (pair site bondAxis)))
    (trans
      (cong
        (λ wilsonGauge → wilsonGauge
          + fineProjection tangent component1 (pair site bondAxis))
        (scalarWilsonGaugeCollapse
          (componentScalarBondField tangent component1) bondAxis site))
      (cong
        (λ laplacian → laplacian
          + average0123
              (componentScalarBondField tangent component1 bondAxis) site)
        (scalarForwardBackwardEqualsLocal
          (componentScalarBondField tangent component1) bondAxis site)))
configuredGaugeFixedMatrixEqualsLaplacianPlusMean tangent component2 site bondAxis =
  trans
    (threeAssocLeftRaw
      (scalarWilsonOperator (componentScalarBondField tangent component2) bondAxis site)
      (scalarGaugePenalty (componentScalarBondField tangent component2) bondAxis site)
      (fineProjection tangent component2 (pair site bondAxis)))
    (trans
      (cong
        (λ wilsonGauge → wilsonGauge
          + fineProjection tangent component2 (pair site bondAxis))
        (scalarWilsonGaugeCollapse
          (componentScalarBondField tangent component2) bondAxis site))
      (cong
        (λ laplacian → laplacian
          + average0123
              (componentScalarBondField tangent component2 bondAxis) site)
        (scalarForwardBackwardEqualsLocal
          (componentScalarBondField tangent component2) bondAxis site)))
configuredGaugeFixedMatrixEqualsLaplacianPlusMean tangent component3 site bondAxis =
  trans
    (threeAssocLeftRaw
      (scalarWilsonOperator (componentScalarBondField tangent component3) bondAxis site)
      (scalarGaugePenalty (componentScalarBondField tangent component3) bondAxis site)
      (fineProjection tangent component3 (pair site bondAxis)))
    (trans
      (cong
        (λ wilsonGauge → wilsonGauge
          + fineProjection tangent component3 (pair site bondAxis))
        (scalarWilsonGaugeCollapse
          (componentScalarBondField tangent component3) bondAxis site))
      (cong
        (λ laplacian → laplacian
          + average0123
              (componentScalarBondField tangent component3 bondAxis) site)
        (scalarForwardBackwardEqualsLocal
          (componentScalarBondField tangent component3) bondAxis site)))

scalarWilsonGaugeOperatorHodgeLevel : ProofLevel
scalarWilsonGaugeOperatorHodgeLevel = machineChecked

configuredLaplacianPlusMeanReductionLevel : ProofLevel
configuredLaplacianPlusMeanReductionLevel = machineChecked
