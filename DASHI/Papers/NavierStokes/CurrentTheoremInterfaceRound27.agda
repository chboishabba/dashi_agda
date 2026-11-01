module DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound27 where

------------------------------------------------------------------------
-- Current normalized paper-facing Navier--Stokes interface after Round 27.
--
-- Round 26 remains the signed physical ledger and duplicate-free tax base.
-- Round 27 adds concrete finite projector, involution, state/dual commutator,
-- centred-probe, maximal-core and Plucker geometry.  The actual cutoff-uniform
-- PDE estimates and Clay theorem remain fail-closed.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound26 as R26
import DASHI.Papers.NavierStokes.ProjectorOperatorCoreRound27 as R27

record CurrentNSPaperTheoremInterfaceRound27 : Setω where
  field
    round26Interface : R26.CurrentNSPaperTheoremInterfaceRound26
    round26InterfaceIsCanonical :
      round26Interface ≡ R26.canonicalCurrentNSPaperTheoremInterfaceRound26

    round27Status : R27.ProjectorOperatorCoreRound27Status
    round27StatusIsCanonical :
      round27Status ≡ R27.canonicalProjectorOperatorCoreRound27Status

    sharpFiniteShellProjectorsChecked :
      R27.sharpFiniteShellProjectors round27Status ≡ true

    realityInvolutionChecked :
      R27.realityInvolution round27Status ≡ true

    signedTranslationMultiplierCommutatorChecked :
      R27.signedTranslationMultiplierCommutator round27Status ≡ true

    maximalUniformViscosityCoreChecked :
      R27.maximalUniformViscosityCore round27Status ≡ true

    physicalVectorFieldEquivarianceStillOpen :
      R27.fullPhysicalVectorFieldEquivariance round27Status ≡ false

    finitePicardLindelofStillOpen :
      R27.finitePicardLindelof round27Status ≡ false

    cutoffUniformOperatorTaxStillOpen :
      R27.cutoffUniformSignedOperatorTax round27Status ≡ false

    strictMarginStillOpen :
      R27.strictTotalViscosityMargin round27Status ≡ false

    clayPromotionStillFalse :
      R27.unconditionalClayTheorem round27Status ≡ false

open CurrentNSPaperTheoremInterfaceRound27 public

canonicalCurrentNSPaperTheoremInterfaceRound27 :
  CurrentNSPaperTheoremInterfaceRound27
canonicalCurrentNSPaperTheoremInterfaceRound27 = record
  { round26Interface = R26.canonicalCurrentNSPaperTheoremInterfaceRound26
  ; round26InterfaceIsCanonical = refl
  ; round27Status = R27.canonicalProjectorOperatorCoreRound27Status
  ; round27StatusIsCanonical = refl
  ; sharpFiniteShellProjectorsChecked = R27.finiteProjectorOperatorCoreAdvanced
  ; realityInvolutionChecked = refl
  ; signedTranslationMultiplierCommutatorChecked = R27.signedCommutatorAdvanced
  ; maximalUniformViscosityCoreChecked = R27.maximalCoreAdvanced
  ; physicalVectorFieldEquivarianceStillOpen = R27.physicalVectorFieldStillOpen
  ; finitePicardLindelofStillOpen = refl
  ; cutoffUniformOperatorTaxStillOpen = R27.uniformOperatorTaxStillOpen
  ; strictMarginStillOpen = R27.strictMarginStillOpen
  ; clayPromotionStillFalse = R27.clayPromotionStillFalse
  }

currentRound27SignedCommutatorChecked :
  R27.signedTranslationMultiplierCommutator
    (round27Status canonicalCurrentNSPaperTheoremInterfaceRound27)
  ≡ true
currentRound27SignedCommutatorChecked = R27.signedCommutatorAdvanced

currentRound27ClayPromotionFalse :
  R27.unconditionalClayTheorem
    (round27Status canonicalCurrentNSPaperTheoremInterfaceRound27)
  ≡ false
currentRound27ClayPromotionFalse = R27.clayPromotionStillFalse
