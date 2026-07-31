module DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact SU(2) trace/chordal identity over the repository rational carrier.
--
-- A unit quaternion q = a + bi + cj + dk represents an SU(2) plaquette.
-- Its normalized real trace is a.  The literal squared chordal distance to the
-- identity is (a-1)^2+b^2+c^2+d^2, and on the unit sphere this equals
-- 2(1-a).  Thus the Wilson trace deficit is exactly one half of the chordal
-- distance squared; no trigonometry or asymptotic expansion enters.
------------------------------------------------------------------------

record RationalUnitQuaternion : Set where
  constructor rationalUnitQuaternion
  field
    realPart imagI imagJ imagK : ℚ
    unitNormExact :
      realPart * realPart
      + imagI * imagI
      + imagJ * imagJ
      + imagK * imagK
      ≡ 1ℚ

open RationalUnitQuaternion public

twoℚ halfℚ : ℚ
twoℚ = 1ℚ + 1ℚ
halfℚ = + 1 / 2

squareℚ : ℚ → ℚ
squareℚ value = value * value

quaternionNormSq : RationalUnitQuaternion → ℚ
quaternionNormSq q =
  squareℚ (realPart q)
  + squareℚ (imagI q)
  + squareℚ (imagJ q)
  + squareℚ (imagK q)

literalChordalDistanceSq : RationalUnitQuaternion → ℚ
literalChordalDistanceSq q =
  squareℚ (realPart q - 1ℚ)
  + squareℚ (imagI q)
  + squareℚ (imagJ q)
  + squareℚ (imagK q)

wilsonTraceDeficit : RationalUnitQuaternion → ℚ
wilsonTraceDeficit q = 1ℚ - realPart q

chordalExpandedThroughNorm : ∀ q →
  literalChordalDistanceSq q
  ≡ quaternionNormSq q - twoℚ * realPart q + 1ℚ
chordalExpandedThroughNorm q =
  regroup (realPart q) (imagI q) (imagJ q) (imagK q)
  where
  regroup : (w x y zVal : ℚ) →
    (w - 1ℚ) * (w - 1ℚ) + x * x + y * y + zVal * zVal
    ≡ (w * w + x * x + y * y + zVal * zVal) - twoℚ * w + 1ℚ
  regroup = ℚRing.solve-∀

quaternionNormMatchesUnit : ∀ q → quaternionNormSq q ≡ 1ℚ
quaternionNormMatchesUnit q = unitNormExact q

unitChordalEqualsTwiceTraceDeficit : ∀ q →
  literalChordalDistanceSq q ≡ twoℚ * wilsonTraceDeficit q
unitChordalEqualsTwiceTraceDeficit q =
  trans
    (chordalExpandedThroughNorm q)
    (trans
      (cong
        (λ normValue → normValue - twoℚ * realPart q + 1ℚ)
        (quaternionNormMatchesUnit q))
      (regroup (realPart q)))
  where
  regroup : ∀ w → 1ℚ - twoℚ * w + 1ℚ ≡ twoℚ * (1ℚ - w)
  regroup = ℚRing.solve-∀

traceDeficitEqualsHalfTwice : ∀ value →
  value ≡ halfℚ * (twoℚ * value)
traceDeficitEqualsHalfTwice = ℚRing.solve-∀

wilsonPlaquetteAction : ℚ → RationalUnitQuaternion → ℚ
wilsonPlaquetteAction beta q = beta * wilsonTraceDeficit q

wilsonActionEqualsHalfBetaChordal : ∀ beta q →
  wilsonPlaquetteAction beta q
  ≡ (halfℚ * beta) * literalChordalDistanceSq q
wilsonActionEqualsHalfBetaChordal beta q =
  trans
    (cong (beta *_)
      (traceDeficitEqualsHalfTwice (wilsonTraceDeficit q)))
    (trans
      (cong
        (λ value → beta * (halfℚ * value))
        (sym (unitChordalEqualsTwiceTraceDeficit q)))
      (regroup beta (literalChordalDistanceSq q)))
  where
  regroup : ∀ b d → b * (halfℚ * d) ≡ (halfℚ * b) * d
  regroup = ℚRing.solve-∀

------------------------------------------------------------------------
-- Ordered consequence.  Only monotonicity of multiplication by a certified
-- nonnegative scalar is required.  The trace/chordal and normalization parts
-- above are fully concrete.
------------------------------------------------------------------------

record RationalWilsonGapOrder : Set₁ where
  field
    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper
    nonnegativeScaleMonotone : ∀ coefficient {left right} →
      0ℚ ≤ coefficient → left ≤ right →
      coefficient * left ≤ coefficient * right

open RationalWilsonGapOrder public

localWilsonActionGap :
  (order : RationalWilsonGapOrder) →
  ∀ beta epsilon q →
  0ℚ ≤ halfℚ * beta →
  squareℚ epsilon ≤ literalChordalDistanceSq q →
  (halfℚ * beta) * squareℚ epsilon
  ≤ wilsonPlaquetteAction beta q
localWilsonActionGap order beta epsilon q coefficientNonnegative bad =
  subst
    (λ right → (halfℚ * beta) * squareℚ epsilon ≤ right)
    (sym (wilsonActionEqualsHalfBetaChordal beta q))
    (nonnegativeScaleMonotone order
      (halfℚ * beta) coefficientNonnegative bad)

------------------------------------------------------------------------
-- A duplicate-free witness selection converts the local plaquette gap into a
-- polymer action gap.  Geometry is isolated to the single statement that the
-- selected witness sum is bounded by the total action; the summation argument
-- itself is proved here by list induction.
------------------------------------------------------------------------

sumMap : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumMap [] term = 0ℚ
sumMap (value ∷ values) term = term value + sumMap values term

natScale : Nat → ℚ → ℚ
natScale zero value = 0ℚ
natScale (suc n) value = value + natScale n value

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ values) = suc (length values)

sumMapConstant : ∀ {A : Set} (values : List A) constant →
  sumMap values (λ _ → constant) ≡ natScale (length values) constant
sumMapConstant [] constant = refl
sumMapConstant (_ ∷ values) constant
  rewrite sumMapConstant values constant = refl

sumMapMonotone :
  (order : RationalWilsonGapOrder) →
  ∀ {A : Set} (values : List A) (lower upper : A → ℚ) →
  (∀ value → lower value ≤ upper value) →
  sumMap values lower ≤ sumMap values upper
sumMapMonotone order [] lower upper pointwise = reflexive order 0ℚ
sumMapMonotone order (value ∷ values) lower upper pointwise =
  addMonotone order
    (pointwise value)
    (sumMapMonotone order values lower upper pointwise)

record LargeFieldWitnessSystem (Block Plaquette : Set) : Set₁ where
  field
    order : RationalWilsonGapOrder
    badBlocks : List Block
    witnessPlaquette : Block → Plaquette
    localAction : Plaquette → ℚ
    totalAction : ℚ
    localGap : ℚ

    witnessHasGap : ∀ block →
      localGap ≤ localAction (witnessPlaquette block)

    -- This field is exactly where duplicate-free witness geometry is consumed.
    witnessActionSumBelowTotal :
      sumMap badBlocks (λ block → localAction (witnessPlaquette block))
      ≤ totalAction

open LargeFieldWitnessSystem public

largeFieldActionLowerBoundFromWitnesses :
  ∀ {Block Plaquette}
    (dataSet : LargeFieldWitnessSystem Block Plaquette) →
  natScale (length (badBlocks dataSet)) (localGap dataSet)
  ≤ totalAction dataSet
largeFieldActionLowerBoundFromWitnesses dataSet =
  transitive (order dataSet)
    (subst
      (λ left → left ≤
        sumMap (badBlocks dataSet)
          (λ block → localAction dataSet (witnessPlaquette dataSet block)))
      (sumMapConstant (badBlocks dataSet) (localGap dataSet))
      (sumMapMonotone (order dataSet)
        (badBlocks dataSet)
        (λ _ → localGap dataSet)
        (λ block → localAction dataSet (witnessPlaquette dataSet block))
        (witnessHasGap dataSet)))
    (witnessActionSumBelowTotal dataSet)

su2TraceChordalIdentityLevel : ProofLevel
su2TraceChordalIdentityLevel = machineChecked

su2LocalWilsonGapReductionLevel : ProofLevel
su2LocalWilsonGapReductionLevel = machineChecked

largeFieldWitnessSummationLevel : ProofLevel
largeFieldWitnessSummationLevel = machineChecked

largeFieldDuplicateFreeWitnessGeometryLevel : ProofLevel
largeFieldDuplicateFreeWitnessGeometryLevel = conditional
