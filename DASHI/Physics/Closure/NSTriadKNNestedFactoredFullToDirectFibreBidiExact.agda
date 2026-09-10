module DASHI.Physics.Closure.NSTriadKNNestedFactoredFullToDirectFibreBidiExact where

------------------------------------------------------------------------
-- NESTED SIGNED FACTORED FULL -> CANONICAL R497 DIRECT FIBRE BIDI
--
-- R547 already proves, before absolute values,
--
--   FactoredFull = Diagonal + 2 * LiteralWeightedRemainder.
--
-- R497 proves on the same R396 unordered pair enumeration
--
--   LiteralWeightedRemainder = 4 * DirectFibreCompanion.
--
-- The preceding spectator-nested weld proves that each R547 spectator row may
-- replace its force-side four-commutator aggregate by the exact R573 nested
-- four-sign fold.  This module lifts that replacement over all spectators and
-- composes the two existing equalities.  Thus the nested signed carrier lands
-- directly on the canonical R497 -> R500 -> R503 scalar route while the
-- diagonal remains explicit.
--
-- No estimate, norm, absolute value, time integration or cutoff-uniform bound
-- is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact as R547
import DASHI.Physics.Closure.NSTriadKNDirectResolventFibreCompanionRound497Exact as R497
import DASHI.Physics.Closure.NSTriadKNSpectatorNestedRowFactorizationBidiExact as NestedRowWeld
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as SpectatorWeld

module NestedDirectFibre
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R547.F)
    (S : Helical.HelicalModeScalars R547.F)
    (L : Helical.PeriodicHelicalProjectorLaws R547.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Row = R545.Row physicalSystem S
  module Normal = R547.NormalForm physicalSystem S
  module Direct = R497.DirectFibre physicalSystem S
  module Local = R396.LocalEnumerate physicalSystem S
  module NestedRow = NestedRowWeld.NestedRow
    physicalSystem S L H velocityTransverse
  module Spectator = SpectatorWeld.SpectatorNested
    physicalSystem S L H velocityTransverse

  system = Field30.finiteSystem physicalSystem

  nestedFactoredRow :
    Z3.FourierMode → Physical.PhysicalTriadIncidence → ℚ
  nestedFactoredRow output beta =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      module N = Spectator.Nested beta
      nestedForce = R224.foldVector N.nestedWeightedCompanionCell items
      A = R224.foldVector (Row.Weighted.Amp.amplitude beta) items
      fourA = C3.complex3Add (C3.complex3Add A A) (C3.complex3Add A A)
    in
    R291.two *
      (R179.realHermitianCross nestedForce (Row.doubleCell beta)
      + R179.realHermitianCross fourA (Row.D.doubleForcing beta))

  nestedFactoredFull :
    Z3.FourierMode → List Physical.PhysicalTriadIncidence → ℚ
  nestedFactoredFull output [] = 0ℚ
  nestedFactoredFull output (beta ∷ rest) =
    nestedFactoredRow output beta + nestedFactoredFull output rest

  factoredRowIsNestedFactoredRow :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    Normal.factoredRow output beta ≡ nestedFactoredRow output beta
  factoredRowIsNestedFactoredRow output beta =
    trans
      (sym (Row.fixedOutputSpectatorRowFactorsThroughR294 output beta))
      (NestedRow.fixedOutputSpectatorRowFactorsThroughNestedForce output beta)

  factoredFullIsNestedFactoredFull :
    (output : Z3.FourierMode) →
    (betas : List Physical.PhysicalTriadIncidence) →
    Normal.factoredFull output betas ≡ nestedFactoredFull output betas
  factoredFullIsNestedFactoredFull output [] = refl
  factoredFullIsNestedFactoredFull output (beta ∷ rest) =
    cong₂ _+_
      (factoredRowIsNestedFactoredRow output beta)
      (factoredFullIsNestedFactoredFull output rest)

  -- This is the canonical finite-fibre composition.  It keeps the diagonal
  -- visible and substitutes only existing exact equalities.
  nestedFactoredFullIsDiagonalPlusDirectFibre :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    (positive : Local.PairRatePositiveOn items) →
    nestedFactoredFull output items
    ≡ R547.R543.diagonalSum Row.pairScalar items
      + R539.two *
          (R299.four * Direct.directFibreCompanion items positive)
  nestedFactoredFullIsDiagonalPlusDirectFibre output positive =
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    trans
      (sym (factoredFullIsNestedFactoredFull output items))
      (trans
        (Normal.factoredFullIsDiagonalPlusTwoLiteralRemainder output positive)
        (cong
          (R547.R543.diagonalSum Row.pairScalar items +_)
          (cong (R539.two *_)
            (Direct.allRemainderIsFourCompanion items positive))))

------------------------------------------------------------------------
-- Status / no-promotion boundary.
------------------------------------------------------------------------

nestedFactoredFullToCanonicalR497CarrierClosed : Bool
nestedFactoredFullToCanonicalR497CarrierClosed = true

nestedFactoredFullDiagonalErased : Bool
nestedFactoredFullDiagonalErased = false

nestedFactoredFullAbsoluteValueIntroduced : Bool
nestedFactoredFullAbsoluteValueIntroduced = false

nestedFactoredFullTimeIntegrationClosed : Bool
nestedFactoredFullTimeIntegrationClosed = false

nestedFactoredFullR503CutoffUniformBudgetClosed : Bool
nestedFactoredFullR503CutoffUniformBudgetClosed = false

nestedFactoredFullClayPromotion : Bool
nestedFactoredFullClayPromotion = false

nestedFactoredFullToCanonicalR497CarrierClosedIsTrue :
  nestedFactoredFullToCanonicalR497CarrierClosed ≡ true
nestedFactoredFullToCanonicalR497CarrierClosedIsTrue = refl

nestedFactoredFullR503CutoffUniformBudgetClosedIsFalse :
  nestedFactoredFullR503CutoffUniformBudgetClosed ≡ false
nestedFactoredFullR503CutoffUniformBudgetClosedIsFalse = refl

nestedFactoredFullClayPromotionIsFalse :
  nestedFactoredFullClayPromotion ≡ false
nestedFactoredFullClayPromotionIsFalse = refl
