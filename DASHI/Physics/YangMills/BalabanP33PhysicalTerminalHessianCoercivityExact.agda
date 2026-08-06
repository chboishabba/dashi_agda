module DASHI.Physics.YangMills.BalabanP33PhysicalTerminalHessianCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Close the terminal coefficient arithmetic against the literal three-
-- component side-four Hessian, rather than merely recording a scalar budget.
-- The exact flat physical Poincare floor is 1/16.  The separately allocated
-- Wilson and gauge losses are
--
--   epsilon_W  = (13/24) rho,
--   epsilon_gf = 64 rho,
--   rho        = 1/8192,
--
-- hence
--
--   1/16 - epsilon_W - epsilon_gf
--     = 10739/196608
--     = 1/32 + 4595/196608.
--
-- The main theorem consumes the actual coupled Wilson-plus-gauge remainder of
-- `LiteralPhysicalSecondVariation`, the actual componentwise mean-zero
-- predicate, and exact residual-background evidence.  It returns the stronger
-- 10739/196608 lower bound on the literal total Hessian.  A second theorem
-- weakens this to the requested 1/32 floor.  No anonymous Hessian scalar or
-- dimension witness is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as PhysicalHodge
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact as Cancel
import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact as Budget

terminalPhysicalCoefficient : ℚ
terminalPhysicalCoefficient =
  LDL.oneSixteenth - Budget.sharpWilsonGaugeBudget

terminalPhysicalCoefficientExact :
  terminalPhysicalCoefficient ≡ + 10739 / 196608
terminalPhysicalCoefficientExact = ℚRing.solve []

terminalPhysicalSlack : ℚ
terminalPhysicalSlack = + 4595 / 196608

terminalPhysicalSlackNonnegative : 0ℚ ≤ terminalPhysicalSlack
terminalPhysicalSlackNonnegative = ℚP.nonNegative⁻¹ terminalPhysicalSlack

terminalCoefficientSplitsAtOneThirtySecond :
  terminalPhysicalCoefficient
  ≡ P33.p33PhysicalFloor + terminalPhysicalSlack
terminalCoefficientSplitsAtOneThirtySecond = ℚRing.solve []

oneThirtySecondBelowTerminalCoefficient :
  P33.p33PhysicalFloor ≤ terminalPhysicalCoefficient
oneThirtySecondBelowTerminalCoefficient =
  let
    instance
      slackNN : NonNegative terminalPhysicalSlack
      slackNN = ℚ.nonNegative terminalPhysicalSlackNonnegative

    beforeRewrite :
      P33.p33PhysicalFloor
      ≤ P33.p33PhysicalFloor + terminalPhysicalSlack
    beforeRewrite =
      ℚP.p≤p+q P33.p33PhysicalFloor terminalPhysicalSlack
  in
  subst
    (λ upper → P33.p33PhysicalFloor ≤ upper)
    (sym terminalCoefficientSplitsAtOneThirtySecond)
    beforeRewrite

terminalCoefficientScaledSplit : ∀ normSq →
  terminalPhysicalCoefficient * normSq
  ≡ LDL.oneSixteenth * normSq
    + - (Budget.sharpWilsonGaugeBudget * normSq)
terminalCoefficientScaledSplit = ℚRing.solve-∀

literalHessianCoerciveAtTerminalCoefficient :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  PhysicalHodge.PhysicalBondComponentMeanZero field →
  Jets.ExactResidualBackground (Jets.gaugeResidual dataSet) →
  Jets.ExactResidualBackground (Jets.constraintResidual dataSet) →
  - (Budget.sharpWilsonGaugeBudget
      * Physical.physicalSU2BondNormSq field)
  ≤ Jets.wilsonSecondVariation dataSet
      + Cancel.gaugeFirstEnergy dataSet
      - PhysicalHodge.physicalReferenceDifferenceEnergy field →
  terminalPhysicalCoefficient * Physical.physicalSU2BondNormSq field
  ≤ Jets.literalTotalSecondVariation dataSet
literalHessianCoerciveAtTerminalCoefficient
    field dataSet meanZero gaugeExact constraintExact coupledLower =
  let
    normSq = Physical.physicalSU2BondNormSq field

    matchedLower :
      - (Budget.sharpWilsonGaugeBudget * normSq)
      ≤ Cancel.matchedSignedRemainder field dataSet
    matchedLower =
      subst
        (λ remainder →
          - (Budget.sharpWilsonGaugeBudget * normSq) ≤ remainder)
        (sym
          (Cancel.constraintCancellationLeavesWilsonGaugeHodgeExact
            field dataSet))
        coupledLower

    referenceLower :
      LDL.oneSixteenth * normSq
      ≤ Cancel.matchedReferenceEnergy field dataSet
    referenceLower =
      PhysicalHodge.physicalReferenceHodgeCoercivity
        field (Cancel.constraintFirstEnergy dataSet)
        meanZero (Cancel.constraintFirstEnergyNonnegative dataSet)

    summedLower :
      LDL.oneSixteenth * normSq
        + - (Budget.sharpWilsonGaugeBudget * normSq)
      ≤ Cancel.matchedReferenceEnergy field dataSet
        + Cancel.matchedSignedRemainder field dataSet
    summedLower = ℚP.+-mono-≤ referenceLower matchedLower

    terminalLower :
      terminalPhysicalCoefficient * normSq
      ≤ Cancel.matchedReferenceEnergy field dataSet
        + Cancel.matchedSignedRemainder field dataSet
    terminalLower =
      subst
        (λ lower →
          lower
          ≤ Cancel.matchedReferenceEnergy field dataSet
            + Cancel.matchedSignedRemainder field dataSet)
        (sym (terminalCoefficientScaledSplit normSq))
        summedLower

    exactHessianLower :
      terminalPhysicalCoefficient * normSq
      ≤ Cancel.matchedExactHessian dataSet
    exactHessianLower =
      subst
        (λ upper → terminalPhysicalCoefficient * normSq ≤ upper)
        (Cancel.matchedReferenceRecomposesExactHessian field dataSet)
        terminalLower
  in
  subst
    (λ upper → terminalPhysicalCoefficient * normSq ≤ upper)
    (sym
      (Cancel.literalTotalEqualsMatchedExactHessian
        dataSet gaugeExact constraintExact))
    exactHessianLower

literalHessianCoerciveAtOneThirtySecond :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  PhysicalHodge.PhysicalBondComponentMeanZero field →
  Jets.ExactResidualBackground (Jets.gaugeResidual dataSet) →
  Jets.ExactResidualBackground (Jets.constraintResidual dataSet) →
  - (Budget.sharpWilsonGaugeBudget
      * Physical.physicalSU2BondNormSq field)
  ≤ Jets.wilsonSecondVariation dataSet
      + Cancel.gaugeFirstEnergy dataSet
      - PhysicalHodge.physicalReferenceDifferenceEnergy field →
  P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field
  ≤ Jets.literalTotalSecondVariation dataSet
literalHessianCoerciveAtOneThirtySecond
    field dataSet meanZero gaugeExact constraintExact coupledLower =
  let
    normSq = Physical.physicalSU2BondNormSq field

    scaledFloor :
      P33.p33PhysicalFloor * normSq
      ≤ terminalPhysicalCoefficient * normSq
    scaledFloor =
      let
        instance
          normNN : NonNegative normSq
          normNN = ℚ.nonNegative (Budget.physicalBondNormSqNonnegative field)
      in
      ℚP.*-monoʳ-≤-nonNeg normSq oneThirtySecondBelowTerminalCoefficient
  in
  ℚP.≤-trans scaledFloor
    (literalHessianCoerciveAtTerminalCoefficient
      field dataSet meanZero gaugeExact constraintExact coupledLower)

terminalPhysicalCoefficientLevel : ProofLevel
terminalPhysicalCoefficientLevel = machineChecked

terminalPhysicalSlackLevel : ProofLevel
terminalPhysicalSlackLevel = machineChecked

literalTerminalHessianCoefficientLevel : ProofLevel
literalTerminalHessianCoefficientLevel = machineChecked

literalTerminalOneThirtySecondLevel : ProofLevel
literalTerminalOneThirtySecondLevel = machineChecked
