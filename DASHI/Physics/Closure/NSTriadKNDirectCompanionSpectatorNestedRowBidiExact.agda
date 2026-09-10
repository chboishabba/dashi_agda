module DASHI.Physics.Closure.NSTriadKNDirectCompanionSpectatorNestedRowBidiExact where

------------------------------------------------------------------------
-- R496 DIRECT COMPANION <-> R545/R573 SPECTATOR NESTED ROW BIDI
--
-- R538's symmetric pair scalar is the literal resolvent-weighted nonlinear
-- Gram remainder.  R496 proves that the SAME R290 weighted remainder is four
-- times the canonical direct resolvent pair companion.  Hence, under the
-- already-required positive pair-rate authority,
--
--   R538.pairScalar(alpha,beta) = 4 * R496.directCompanion(alpha,beta).
--
-- Finite row aggregation then welds the R545 spectator row to four times the
-- R496 direct-companion row.  Composing with the preceding nested-force row
-- factorization places the R573 signed nested carrier on the SAME scalar route
-- that later feeds R497-R500-R503.
--
-- This file introduces no estimate, norm, absolute value, time integration or
-- cutoff-uniform theorem.  In particular it does NOT pay R503.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairCompanionRound496Exact as R496
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNSpectatorNestedRowFactorizationBidiExact as NestedRowWeld
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as SpectatorWeld

module DirectNestedRow
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R496.F)
    (S : Helical.HelicalModeScalars R496.F)
    (L : Helical.PeriodicHelicalProjectorLaws R496.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Direct = R496.DirectPair physicalSystem S
  module Swap = R538.PairSwap physicalSystem S
  module Row = R545.Row physicalSystem S
  module Nested = NestedRowWeld.NestedRow
    physicalSystem S L H velocityTransverse
  module Spectator = SpectatorWeld.SpectatorNested
    physicalSystem S L H velocityTransverse

  system = Field30.finiteSystem physicalSystem

  pairScalarIsFourDirectCompanion :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (positive : Positive (R291.pairRate (Swap.Q alpha beta))) →
    Swap.symmetricWeightedRemainder alpha beta
    ≡ R291.two * R291.two *
        Direct.directResolventPairCompanion alpha beta positive
  pairScalarIsFourDirectCompanion alpha beta positive =
    trans
      (sym
        (Swap.literalR290WeightedRemainderIsSymmetricScalar
          alpha beta positive))
      (Direct.weightedRemainderIsFourDirectCompanion alpha beta positive)

  PositiveAgainst :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → Set
  PositiveAgainst beta items =
    (alpha : Physical.PhysicalTriadIncidence) →
    Positive (R291.pairRate (Swap.Q alpha beta))

  directCompanionRow :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    PositiveAgainst beta items → ℚ
  directCompanionRow beta [] positives = 0ℚ
  directCompanionRow beta (alpha ∷ rest) positives =
    Direct.directResolventPairCompanion alpha beta (positives alpha)
    + directCompanionRow beta rest positives

  spectatorRowIsFourDirectCompanionRow :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    (positives : PositiveAgainst beta items) →
    Row.spectatorRow beta items
    ≡ R291.two * R291.two * directCompanionRow beta items positives
  spectatorRowIsFourDirectCompanionRow beta [] positives = refl
  spectatorRowIsFourDirectCompanionRow beta (alpha ∷ rest) positives
    rewrite pairScalarIsFourDirectCompanion alpha beta (positives alpha)
          | spectatorRowIsFourDirectCompanionRow beta rest positives =
    solve
      (Direct.directResolventPairCompanion alpha beta (positives alpha)
        ∷ directCompanionRow beta rest positives ∷ [])

  -- Canonical fixed-output consequence: the same finite scalar row that is
  -- four times R496 is also the R545 row whose force half has been normalized
  -- into the R573 nested signed fold.
  fourDirectCompanionRowIsNestedForceScalarRow :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    (positives : PositiveAgainst beta
      (Output.physicalOutputFiber (Audit.cutoff system) output)) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        module N = Spectator.Nested beta
        nestedForce =
          R545.R224.foldVector N.nestedWeightedCompanionCell items
        A = R545.R224.foldVector (Row.Weighted.Amp.amplitude beta) items
        fourA =
          R545.C3.complex3Add
            (R545.C3.complex3Add A A)
            (R545.C3.complex3Add A A)
    in
    R291.two * R291.two * directCompanionRow beta items positives
    ≡ R291.two *
        (R545.R179.realHermitianCross nestedForce (Row.doubleCell beta)
        + R545.R179.realHermitianCross fourA (Row.D.doubleForcing beta))
  fourDirectCompanionRowIsNestedForceScalarRow output beta positives =
    trans
      (sym
        (spectatorRowIsFourDirectCompanionRow
          beta
          (Output.physicalOutputFiber (Audit.cutoff system) output)
          positives))
      (Nested.fixedOutputSpectatorRowFactorsThroughNestedForce output beta)

------------------------------------------------------------------------
-- Status / WrongType firewalls.
------------------------------------------------------------------------

directCompanionToNestedSpectatorSameScalarCarrierClosed : Bool
directCompanionToNestedSpectatorSameScalarCarrierClosed = true

directCompanionNestedRowUsesNormBeforeCancellation : Bool
directCompanionNestedRowUsesNormBeforeCancellation = false

directCompanionNestedRowUsesAbsoluteValueBeforeCancellation : Bool
directCompanionNestedRowUsesAbsoluteValueBeforeCancellation = false

directCompanionNestedRowTimeIntegrationClosed : Bool
directCompanionNestedRowTimeIntegrationClosed = false

directCompanionNestedRowR503BudgetClosed : Bool
directCompanionNestedRowR503BudgetClosed = false

directCompanionNestedRowClayPromotion : Bool
directCompanionNestedRowClayPromotion = false

directCompanionToNestedSpectatorSameScalarCarrierClosedIsTrue :
  directCompanionToNestedSpectatorSameScalarCarrierClosed ≡ true
directCompanionToNestedSpectatorSameScalarCarrierClosedIsTrue = refl

directCompanionNestedRowR503BudgetClosedIsFalse :
  directCompanionNestedRowR503BudgetClosed ≡ false
directCompanionNestedRowR503BudgetClosedIsFalse = refl

directCompanionNestedRowClayPromotionIsFalse :
  directCompanionNestedRowClayPromotion ≡ false
directCompanionNestedRowClayPromotionIsFalse = refl
