module DASHI.Physics.Closure.Ternary27TrinificationTwoVEVGeneralMassSpectrumExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.Ternary27TrinificationTwoVEVMassSpectrumExact as EqualUnit
import DASHI.Physics.Closure.Ternary27TrinificationTwoNeutralVEVBreakingExact as Breaking

------------------------------------------------------------------------
-- GENERAL COUPLING/VEV FACTORISATION OF THE TWO-NEUTRAL-VEV MASS FORM
--
-- The earlier owner quoted the equal-unit specialization
--
--   gL=gR=v32=v33=1
--
-- with positive spectrum (1/4)^4,(1/2)^7,(5/6)^1.  The new local analytic
-- probe keeps gL,gR,v32,v33 independent and diagonalises the same 16x16 Gram
-- form.  Four zero modes persist (su2_L + Y) and twelve modes are positive for
-- positive nonzero parameters.
--
-- Ten massive modes are already diagonal:
--
--   gL^2 (v32^2+v33^2)/4          multiplicity 4
--   gR^2 v32^2/4                  multiplicity 2
--   gR^2 v33^2/4                  multiplicity 2
--   gR^2 (v32^2+v33^2)/4          multiplicity 2.
--
-- The remaining neutral 3x3 block has one exact hypercharge zero mode and two
-- roots lambda_-,lambda_+ of
--
--   12 lambda^2 - 4 S lambda + C = 0,
--
-- where
--
--   S = (gL^2+gR^2)(v32^2+v33^2),
--   C = gR^2(4gL^2+gR^2)v32^2 v33^2,
--
-- hence
--
--   lambda_± = (S ± sqrt(S^2-3C))/6.
--
-- At equal unit parameters these are 1/2 and 5/6, reproducing the prior
-- receipt.  This removes an accidental-normalisation ambiguity but still does
-- not derive physical couplings, VEVs, running, scalar normalization or masses.
------------------------------------------------------------------------

persistentZeroModeCount : Nat
persistentZeroModeCount = 4

persistentPositiveRank : Nat
persistentPositiveRank = 12

generalSpectrumFormula : String
generalSpectrumFormula =
  "0^4; [gL^2(v32^2+v33^2)/4]^4; [gR^2 v32^2/4]^2; [gR^2 v33^2/4]^2; [gR^2(v32^2+v33^2)/4]^2; lambda_-,lambda_+"

neutralQuadraticFormula : String
neutralQuadraticFormula =
  "12 lambda^2 - 4 S lambda + C = 0, S=(gL^2+gR^2)(v32^2+v33^2), C=gR^2(4gL^2+gR^2)v32^2 v33^2"

neutralRootFormula : String
neutralRootFormula = "lambda_±=(S±sqrt(S^2-3C))/6"

record TwoVEVGeneralMassSpectrumLocalReceipt : Set where
  constructor two-vev-general-mass-spectrum-local-receipt
  field
    sameE32E33DirectionsUsed : Bool
    sameGellMannHalfNormalizationUsed : Bool
    gLAndgRKeptIndependent : Bool
    v32Andv33KeptIndependent : Bool
    fourZeroModesPersist : Bool
    zeroKernelStillSU2LPlusHypercharge : Bool
    positiveRankTwelvePersists : Bool
    tenSimpleMassModesFactorised : Bool
    neutralThreeByThreeBlockIsolated : Bool
    exactHyperchargeZeroModeInNeutralBlock : Bool
    twoNeutralEigenvalueFormulaDerivedLocally : Bool
    equalUnitSpectrumRecovered : Bool
    randomNumericMatricesMatchAnalyticFormula : Bool
    physicalCouplingsDerived : Bool
    physicalVEVMagnitudesDerived : Bool
    physicalMassesPredicted : Bool
    runningAndMixingDerived : Bool
    boundary : String
open TwoVEVGeneralMassSpectrumLocalReceipt public

canonicalGeneralMassSpectrumLocalReceipt : TwoVEVGeneralMassSpectrumLocalReceipt
canonicalGeneralMassSpectrumLocalReceipt =
  two-vev-general-mass-spectrum-local-receipt
    true true true true true true true true true true true true true
    false false false false
    "The same two-neutral-VEV Gram form has now been diagonalised with independent gL,gR,v32,v33. Four zero modes (su2_L+Y) and rank 12 persist, ten positive sectors factorise directly, and the remaining neutral pair has the displayed analytic quadratic. The old equal-unit spectrum is only a specialization. Local analytic/numerical diagonalisation does not derive physical gauge couplings, VEVs, renormalization-group running, scalar normalization or observed masses."

priorEqualUnitReceipt : EqualUnit.TwoVEVMassSpectrumLocalReceipt
priorEqualUnitReceipt = EqualUnit.canonicalTwoVEVMassSpectrumLocalReceipt

breakingReceipt : Breaking.TrinificationTwoNeutralVEVLocalReceipt
breakingReceipt = Breaking.canonicalTrinificationTwoNeutralVEVLocalReceipt
