{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveBondSelectedCutFederbushRound184Exact where

------------------------------------------------------------------------
-- ROUND184 A1 BIDI: POSITIVE COARSE BOND + SELECTED BACKGROUND/CUT +
-- EXISTING FEDERBUSH FAMILY -> EQ. (119)
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories",
-- Commun. Math. Phys. 102 (1985), 605--636. DOI: 10.1007/BF01229381.
--
-- R178 already gives the shortest literal selected-cut/Federbush producer, but
-- its source still entered through R158 where axis and orientation were exposed
-- as separate fields. R182 proves those are not independent data: an actual
-- positive coarse bond already owns its axis, and positivity owns orientation.
--
-- This round composes those facts directly. The actual positive bond generates
-- the canonical L=13 CMP98 coarse segment; the selected variational background
-- supplies the positive-link small-field estimate; the already-owned selected
-- cut supplies principal-image admission; and the existing Federbush family
-- supplies D+/D-/J+/J-/Ad at the literal principal Y values.
--
-- In particular this strongest route needs NO dyadic transported-relative weld.
-- The dyadic R180-R183 lane remains useful as an independent same-object audit
-- against the printed CMP109 equation-(0.12) carrier, but it is not logically
-- required to construct CMP98 equation (119).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedExistingCutRound175Exact as R175
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182

positiveBondSelectedCutFederbushOneStepDerivative :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source))
    (cutInputs : R175.SelectedExistingCutInputs
      (R182.asCanonicalL13Equation119Source source) weld) →
  R177.ExistingFederbushConventionFamily →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
positiveBondSelectedCutFederbushOneStepDerivative
    source weld cutInputs family =
  R178.federbushSelectedCutOneStepDerivative
    (R182.asCanonicalL13Equation119Source source)
    weld cutInputs family

positiveBondSelectedCutFederbushMultiscaleDerivative :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source))
    (cutInputs : R175.SelectedExistingCutInputs
      (R182.asCanonicalL13Equation119Source source) weld) →
  R177.ExistingFederbushConventionFamily →
  Nat → R126.Operator R178.su2AdditiveCarrier
positiveBondSelectedCutFederbushMultiscaleDerivative
    source weld cutInputs family =
  R178.federbushSelectedCutMultiscaleDerivative
    (R182.asCanonicalL13Equation119Source source)
    weld cutInputs family

cmp98Equation119PositiveBondSelectedCutFederbushRound184Level : ProofLevel
cmp98Equation119PositiveBondSelectedCutFederbushRound184Level = machineChecked

-- BIDI frontier on this route is now upstream of Eq. (119): instantiate the
-- selected variational background bridge and selected principal cut on the
-- actual periodic realization.  The coarse-bond axis/orientation, literal
-- relative path, Y_x, block-average Y, principal-log admission, differential
-- calculus and Eq. (119) assembly are all downstream constructions.
literalCMP98SelectedBackgroundAndCutInstantiationRound184Level : ProofLevel
literalCMP98SelectedBackgroundAndCutInstantiationRound184Level = conditional
