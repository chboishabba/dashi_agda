module DASHI.Physics.Closure.NSTriadKNDirectCompanionThreeOrbitSignedRowBidiExact where

------------------------------------------------------------------------
-- DIRECT R496 COMPANION ROW -> THREE-ORBIT SIGNED FORCE CROSS
--
-- The existing direct/nested row weld places four times the canonical R496
-- direct-companion row on the exact scalar
--
--   2 ( Re <nestedForce_beta , D_beta>
--       + Re <fourA_beta , G_beta> ).
--
-- The weighted signed-three-orbit owner now proves that the FIRST scalar cross,
-- on the actual nestedWeightedCompanionCell carrier, is exactly a sum of only
-- three signed Bony-orbit channels: 2*LH + HH->low + comparable.  This file
-- substitutes that equality into the already-canonical direct-companion row.
--
-- The amplitude/product-rule half remains explicit.  No norm, absolute value,
-- Cauchy/Young/Schur estimate, time integration or cutoff-uniform bound is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNDirectCompanionSpectatorNestedRowBidiExact as DirectNested
import DASHI.Physics.Closure.NSTriadKNWeightedNestedSignedCrossThreeOrbitBidiExact as ThreeOrbit

F : C3.RealField _
F = Rational.rationalRealField

module DirectThreeOrbitRow
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module DN = DirectNested.DirectNestedRow
    physicalSystem S L H velocityTransverse
  module Row = R545.Row physicalSystem S
  module Spec = R541.Spectator physicalSystem S

  system = Field30.finiteSystem physicalSystem

  module Three (beta : Physical.PhysicalTriadIncidence) =
    ThreeOrbit.SignedThreeOrbit
      (Spec.spectatorWeight beta)
      S L H system velocityTransverse

  outputItems : Z3.FourierMode → List Physical.PhysicalTriadIncidence
  outputItems output = Output.physicalOutputFiber (Audit.cutoff system) output

  threeOrbitForceCross :
    Z3.FourierMode → Physical.PhysicalTriadIncidence → ℚ
  threeOrbitForceCross output beta =
    Three.threeOrbitCrossSum beta
      (outputItems output)
      (Row.doubleCell beta)

  amplitudeCross :
    Z3.FourierMode → Physical.PhysicalTriadIncidence → ℚ
  amplitudeCross output beta =
    let
      items = outputItems output
      A = R224.foldVector (Row.Weighted.Amp.amplitude beta) items
      fourA = C3.complex3Add
        (C3.complex3Add A A) (C3.complex3Add A A)
    in
    R179.realHermitianCross fourA (Row.D.doubleForcing beta)

  fourDirectCompanionRowIsThreeOrbitSignedRow :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    (positives : DN.PositiveAgainst beta (outputItems output)) →
    R299.four * DN.directCompanionRow beta (outputItems output) positives
    ≡ R291.two *
        (threeOrbitForceCross output beta + amplitudeCross output beta)
  fourDirectCompanionRowIsThreeOrbitSignedRow output beta positives =
    trans
      (DN.fourDirectCompanionRowIsNestedForceScalarRow
        output beta positives)
      (cong
        (R291.two *_)
        (cong₂ _+_
          (Three.foldedNestedWeightedCrossIsThreeOrbitSum beta
            (outputItems output) (Row.doubleCell beta))
          refl))

------------------------------------------------------------------------
-- Status / no-promotion boundary.
------------------------------------------------------------------------

directCompanionForceHalfThreeOrbitSignedReductionClosed : Bool
directCompanionForceHalfThreeOrbitSignedReductionClosed = true

directCompanionForceHalfNormedBeforeThreeOrbitReduction : Bool
directCompanionForceHalfNormedBeforeThreeOrbitReduction = false

directCompanionAmplitudeHalfStillExplicit : Bool
directCompanionAmplitudeHalfStillExplicit = true

directCompanionThreeOrbitCutoffUniformBudgetClosed : Bool
directCompanionThreeOrbitCutoffUniformBudgetClosed = false

directCompanionThreeOrbitClayPromotion : Bool
directCompanionThreeOrbitClayPromotion = false

directCompanionForceHalfThreeOrbitSignedReductionClosedIsTrue :
  directCompanionForceHalfThreeOrbitSignedReductionClosed ≡ true
directCompanionForceHalfThreeOrbitSignedReductionClosedIsTrue = refl

directCompanionForceHalfNormedBeforeThreeOrbitReductionIsFalse :
  directCompanionForceHalfNormedBeforeThreeOrbitReduction ≡ false
directCompanionForceHalfNormedBeforeThreeOrbitReductionIsFalse = refl

directCompanionThreeOrbitClayPromotionIsFalse :
  directCompanionThreeOrbitClayPromotion ≡ false
directCompanionThreeOrbitClayPromotionIsFalse = refl
