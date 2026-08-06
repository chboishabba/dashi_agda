module DASHI.Physics.YangMills.BalabanP33LiteralFiveMechanismFamiliesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the five signed local Hessian families on the literal side-four
-- positive-bond carrier.  For every mechanism i and bond cell c,
--
--   R_i,c(A,v) = kappa_i(A,c) q_c(v),
--   q_c(v)     = v(c)^2.
--
-- The primitive operator-norm development supplies
--
--   -C_i rho <= kappa_i(A,c) <= C_i rho,
--
-- while positivity of q_c and exact finite Fubini give
--
--   -C_i rho q_c(v) <= R_i,c(A,v) <= C_i rho q_c(v),
--   sum_c q_c(v) = ||v||^2.
--
-- Thus all five pointwise and incidence fields required by the P33 coercivity
-- theorem are constructed here rather than postulated globally.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; NonNegative; NonPositive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Cells
import DASHI.Physics.YangMills.BalabanP33PrimitiveOperatorNormLocalBoundsExact as Primitive
import DASHI.Physics.YangMills.BalabanP33FiniteSignedRemainderSummationExact as Signed
import DASHI.Physics.YangMills.BalabanP33FiveChannelPath4CoercivityExact as Five
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge

------------------------------------------------------------------------
-- Elementary rational positivity and sign transport.
------------------------------------------------------------------------

squareNonnegative : ∀ value → 0ℚ ≤ value * value
squareNonnegative value with ℚP.≤-total 0ℚ value
... | inj₁ valueNonnegative =
  let
    instance
      valueNN : NonNegative value
      valueNN = ℚ.nonNegative valueNonnegative

      productNN : NonNegative (value * value)
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg value value
  in
  ℚP.nonNegative⁻¹ (value * value)
... | inj₂ valueNonpositive =
  let
    instance
      valueNP : NonPositive value
      valueNP = ℚ.nonPositive valueNonpositive

      productNN : NonNegative (value * value)
      productNN = ℚP.nonPos*nonPos⇒nonNeg value value
  in
  ℚP.nonNegative⁻¹ (value * value)

negTimesRight : ∀ budget charge →
  (- budget) * charge ≡ - (budget * charge)
negTimesRight = ℚRing.solve-∀

multiplyTwoSidedByNonnegative :
  ∀ coefficient budget charge →
  Primitive.TwoSided coefficient budget →
  0ℚ ≤ charge →
  Primitive.TwoSided
    (coefficient * charge)
    (budget * charge)
multiplyTwoSidedByNonnegative coefficient budget charge bound chargeNonnegative =
  let
    instance
      chargeNN : NonNegative charge
      chargeNN = ℚ.nonNegative chargeNonnegative
  in
  record
    { Primitive.TwoSided.lower =
        subst
          (λ left → left ≤ coefficient * charge)
          (negTimesRight budget charge)
          (ℚP.*-monoʳ-≤-nonNeg charge
            (Primitive.lower bound))
    ; Primitive.TwoSided.upper =
        ℚP.*-monoʳ-≤-nonNeg charge
          (Primitive.upper bound)
    }

productNonnegative :
  ∀ left right →
  NonNegative left →
  0ℚ ≤ right →
  0ℚ ≤ left * right
productNonnegative left right leftNonnegative rightNonnegative =
  let
    instance
      leftNN : NonNegative left
      leftNN = leftNonnegative

      rightNN : NonNegative right
      rightNN = ℚ.nonNegative rightNonnegative

      productNN : NonNegative (left * right)
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

------------------------------------------------------------------------
-- A fixed one-point background carrier.  The configured-radius equality is a
-- theorem argument, rather than being hidden in the background universe.
------------------------------------------------------------------------

data ConfiguredBackground : Set where
  configuredBackground : ConfiguredBackground

localCharge : Hodge.RationalBondField4 → Cells.BondCell4 → ℚ
localCharge state cell = Cells.bondCellCharge state cell

localChargeNonnegative : ∀ state cell →
  0ℚ ≤ localCharge state cell
localChargeNonnegative state cell =
  squareNonnegative (Cells.bondCellValue state cell)

------------------------------------------------------------------------
-- A common constructor for literal local Hessian channels.
------------------------------------------------------------------------

literalSignedFamily :
  ∀ (dataSet : Primitive.PrimitivePhysicalOperatorNorms Cells.BondCell4)
    (configuredCoefficient : ℚ)
    (configuredCoefficientNonnegative : NonNegative configuredCoefficient)
    (localCoefficient : Cells.BondCell4 → ℚ) →
  (∀ cell →
    Primitive.TwoSided
      (localCoefficient cell)
      (configuredCoefficient * Primitive.radius dataSet)) →
  Signed.FiniteSignedRemainderFamily
    ConfiguredBackground
    Hodge.RationalBondField4
    Cells.BondCell4
literalSignedFamily dataSet configuredCoefficient coefficientNN
    localCoefficient coefficientBound = record
  { Signed.FiniteSignedRemainderFamily.cells =
      λ _ → Cells.bondCells4
  ; Signed.FiniteSignedRemainderFamily.localRemainder =
      λ _ state cell → localCoefficient cell * localCharge state cell
  ; Signed.FiniteSignedRemainderFamily.localNormCharge =
      λ _ state cell → localCharge state cell
  ; Signed.FiniteSignedRemainderFamily.weight =
      λ _ _ → configuredCoefficient * Primitive.radius dataSet
  ; Signed.FiniteSignedRemainderFamily.globalNormSq =
      λ _ state → Hodge.bondNormSq state
  ; Signed.FiniteSignedRemainderFamily.weightNonnegative =
      λ _ _ →
        productNonnegative
          configuredCoefficient
          (Primitive.radius dataSet)
          coefficientNN
          (Primitive.radiusNonnegative dataSet)
  ; Signed.FiniteSignedRemainderFamily.pointwiseUpper =
      λ _ state cell →
        Primitive.upper
          (multiplyTwoSidedByNonnegative
            (localCoefficient cell)
            (configuredCoefficient * Primitive.radius dataSet)
            (localCharge state cell)
            (coefficientBound cell)
            (localChargeNonnegative state cell))
  ; Signed.FiniteSignedRemainderFamily.pointwiseLower =
      λ _ state cell →
        Primitive.lower
          (multiplyTwoSidedByNonnegative
            (localCoefficient cell)
            (configuredCoefficient * Primitive.radius dataSet)
            (localCharge state cell)
            (coefficientBound cell)
            (localChargeNonnegative state cell))
  ; Signed.FiniteSignedRemainderFamily.incidenceNormBound =
      λ _ state → Cells.bondCellIncidenceBound state
  }

------------------------------------------------------------------------
-- The five literal local functions R_i,c(A,v).
------------------------------------------------------------------------

curvatureFamily :
  ∀ dataSet →
  Signed.FiniteSignedRemainderFamily
    ConfiguredBackground Hodge.RationalBondField4 Cells.BondCell4
curvatureFamily dataSet =
  literalSignedFamily
    dataSet
    Constants.configuredCurvatureCoefficient
    Primitive.thirtyTwoNonnegative
    (Primitive.curvatureCoefficient dataSet)
    (Primitive.curvatureCoefficientBound dataSet)

transportFamily :
  ∀ dataSet →
  Signed.FiniteSignedRemainderFamily
    ConfiguredBackground Hodge.RationalBondField4 Cells.BondCell4
transportFamily dataSet =
  literalSignedFamily
    dataSet
    Constants.configuredTransportCoefficient
    Primitive.sixtyFourNonnegative
    (Primitive.transportCoefficient dataSet)
    (Primitive.transportCoefficientBound dataSet)

chartFamily :
  ∀ dataSet →
  Signed.FiniteSignedRemainderFamily
    ConfiguredBackground Hodge.RationalBondField4 Cells.BondCell4
chartFamily dataSet =
  literalSignedFamily
    dataSet
    Constants.configuredChartCoefficient
    Primitive.thirtyTwoNonnegative
    (Primitive.chartCoefficient dataSet)
    (Primitive.chartCoefficientBound dataSet)

gaugeFamily :
  ∀ dataSet →
  Signed.FiniteSignedRemainderFamily
    ConfiguredBackground Hodge.RationalBondField4 Cells.BondCell4
gaugeFamily dataSet =
  literalSignedFamily
    dataSet
    Constants.configuredGaugeCoefficient
    Primitive.sixtyFourNonnegative
    (Primitive.gaugeCoefficient dataSet)
    (Primitive.gaugeCoefficientBound dataSet)

constraintFamily :
  ∀ dataSet →
  Signed.FiniteSignedRemainderFamily
    ConfiguredBackground Hodge.RationalBondField4 Cells.BondCell4
constraintFamily dataSet =
  literalSignedFamily
    dataSet
    Constants.configuredConstraintCoefficient
    Primitive.sixtyFourNonnegative
    (Primitive.constraintCoefficient dataSet)
    (Primitive.constraintCoefficientBound dataSet)

------------------------------------------------------------------------
-- Assemble the five concrete families and consume the P33 coercivity theorem.
------------------------------------------------------------------------

literalFiveChannelData :
  ∀ (dataSet : Primitive.PrimitivePhysicalOperatorNorms Cells.BondCell4) →
  Primitive.radius dataSet ≡ P33.p33SmallFieldRadius →
  Five.FiveChannelPath4Data
    ConfiguredBackground
    Cells.BondCell4 Cells.BondCell4 Cells.BondCell4
    Cells.BondCell4 Cells.BondCell4
literalFiveChannelData dataSet radiusExact = record
  { Five.FiveChannelPath4Data.curvature = curvatureFamily dataSet
  ; Five.FiveChannelPath4Data.transport = transportFamily dataSet
  ; Five.FiveChannelPath4Data.chart = chartFamily dataSet
  ; Five.FiveChannelPath4Data.gauge = gaugeFamily dataSet
  ; Five.FiveChannelPath4Data.constraint = constraintFamily dataSet
  ; Five.FiveChannelPath4Data.radius =
      λ _ _ → Primitive.radius dataSet
  ; Five.FiveChannelPath4Data.curvatureWeightExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.transportWeightExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.chartWeightExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.gaugeWeightExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.constraintWeightExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.curvatureNormExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.transportNormExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.chartNormExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.gaugeNormExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.constraintNormExact = λ _ _ → refl
  ; Five.FiveChannelPath4Data.radiusIsConfigured =
      λ _ _ → radiusExact
  }

literalFiveMechanismsGivePath4PhysicalCoercivity :
  ∀ (dataSet : Primitive.PrimitivePhysicalOperatorNorms Cells.BondCell4)
    (radiusExact : Primitive.radius dataSet ≡ P33.p33SmallFieldRadius)
    state gaugeFixingEnergy blockPenaltyEnergy →
  Hodge.BondComponentMeanZero state →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  P33.p33PhysicalFloor * Hodge.bondNormSq state
  ≤ P33.physicalHessianEnergy
      (Hodge.referenceHodgeEnergy
        state gaugeFixingEnergy blockPenaltyEnergy)
      (Five.totalSignedRemainder
        (literalFiveChannelData dataSet radiusExact)
        configuredBackground state)
literalFiveMechanismsGivePath4PhysicalCoercivity
    dataSet radiusExact state gaugeFixingEnergy blockPenaltyEnergy
    meanZero gaugeNonnegative blockNonnegative =
  Five.fiveLocalChannelsGivePath4PhysicalCoercivity
    (literalFiveChannelData dataSet radiusExact)
    configuredBackground state gaugeFixingEnergy blockPenaltyEnergy
    meanZero gaugeNonnegative blockNonnegative

literalFiveLocalFunctionsLevel : ProofLevel
literalFiveLocalFunctionsLevel = machineChecked

literalFivePointwiseBoundsLevel : ProofLevel
literalFivePointwiseBoundsLevel = machineChecked

literalFiveIncidenceBoundsLevel : ProofLevel
literalFiveIncidenceBoundsLevel = machineChecked

primitiveNormsToConcreteP33FloorLevel : ProofLevel
primitiveNormsToConcreteP33FloorLevel = machineChecked
