module DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound28 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound27
import DASHI.Papers.NavierStokes.PhysicalCarrierPartitionRound28 as Round28

record CurrentNSPaperTheoremInterfaceRound28 : Set where
  constructor current-ns-paper-theorem-interface-round28
  field
    literalPeriodicClayTargetImplemented : Bool
    exhaustivePhysicalSupportChecked : Bool
    sharpFiniteProjectorsChecked : Bool
    commutingCarrierSelectorChecked : Bool
    conjugateOutputFibreChecked : Bool
    finiteRationalLocalLipschitzChecked : Bool
    continuumRealPicardLindelof : Bool
    dependentOwnerPartitionChecked : Bool
    signedConstituentGroupingChecked : Bool
    signedInteractionFibreChecked : Bool
    divisionFreePluckerScalingChecked : Bool
    admissibleNineOwnerAlgebraChecked : Bool
    finiteGlobalGalerkinFlow : Bool
    physicalSignedShellBalance : Bool
    cutoffUniformOperatorTax : Bool
    physicalNineOwnerEstimates : Bool
    strictTotalViscosityMargin : Bool
    shellAndGalerkinLimits : Bool
    unconditionalPeriodicRegularity : Bool

open CurrentNSPaperTheoremInterfaceRound28 public

canonicalCurrentNSPaperTheoremInterfaceRound28 :
  CurrentNSPaperTheoremInterfaceRound28
canonicalCurrentNSPaperTheoremInterfaceRound28 =
  current-ns-paper-theorem-interface-round28
    true true true true true true false
    true true true true true
    false false false false false false false

round28ExactArchitectureAdvanced :
  admissibleNineOwnerAlgebraChecked
    canonicalCurrentNSPaperTheoremInterfaceRound28 ≡ true
round28ExactArchitectureAdvanced = refl

finiteLocalLipschitzChecked :
  finiteRationalLocalLipschitzChecked
    canonicalCurrentNSPaperTheoremInterfaceRound28 ≡ true
finiteLocalLipschitzChecked = refl

continuumPicardLindelofStillOpen :
  continuumRealPicardLindelof
    canonicalCurrentNSPaperTheoremInterfaceRound28 ≡ false
continuumPicardLindelofStillOpen = refl

finiteGlobalFlowStillOpen :
  finiteGlobalGalerkinFlow
    canonicalCurrentNSPaperTheoremInterfaceRound28 ≡ false
finiteGlobalFlowStillOpen = refl

physicalOwnerTaxesStillOpen :
  physicalNineOwnerEstimates
    canonicalCurrentNSPaperTheoremInterfaceRound28 ≡ false
physicalOwnerTaxesStillOpen = refl

currentRound28ClayPromotionFalse :
  unconditionalPeriodicRegularity
    canonicalCurrentNSPaperTheoremInterfaceRound28 ≡ false
currentRound28ClayPromotionFalse = refl
