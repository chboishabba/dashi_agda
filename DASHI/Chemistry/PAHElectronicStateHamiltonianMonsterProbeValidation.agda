module DASHI.Chemistry.PAHElectronicStateHamiltonianMonsterProbeValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Chemistry.PAHElectronicStateHamiltonianMonsterProbeExact as Probe

literalStateCarrierWithoutFabricatedHamiltonian :
  Probe.literalCatalyticStateCarrierPaid Probe.canonicalPAHElectronicMonsterBoundary ≡ true
  × Probe.literalElectronicHamiltonianPaid Probe.canonicalPAHElectronicMonsterBoundary ≡ false
  × Probe.literalElectronicWavefunctionPaid Probe.canonicalPAHElectronicMonsterBoundary ≡ false
literalStateCarrierWithoutFabricatedHamiltonian = refl , (refl , refl)

bacterialFerrylDoesNotBecomeHumanSameObjectByAnalogy :
  Probe.sourceBackedHighSpinFeIVStatePaid Probe.canonicalPAHElectronicMonsterBoundary ≡ true
  × Probe.bacterialFeIVAutomaticallyEqualsHumanFeIVSameObject Probe.canonicalPAHElectronicMonsterBoundary ≡ false
bacterialFerrylDoesNotBecomeHumanSameObjectByAnalogy = refl , refl

finiteOperatorTypeDoesNotCreateMatrixOrEigenvector :
  Probe.sourceBackedNumericalHamiltonianMatrixPaid Probe.canonicalPAHFiniteHamiltonianProbe ≡ false
  × Probe.numericalDiagonalizationPaid Probe.canonicalPAHFiniteHamiltonianProbe ≡ false
  × Probe.eigenvectorCoefficientsPaid Probe.canonicalPAHFiniteHamiltonianProbe ≡ false
finiteOperatorTypeDoesNotCreateMatrixOrEigenvector = refl , (refl , refl)

pahD2DoesNotManufactureMonsterC3 :
  Probe.sameObjectC3CoordinatePaid Probe.canonicalPAHMonster3BProbe ≡ false
  × Probe.canonicalD2ToMonsterC3IntertwinerPaid Probe.canonicalPAHMonster3BProbe ≡ false
  × Probe.nontrivialMonsterActionOnPAHStatePaid Probe.canonicalPAHMonster3BProbe ≡ false
pahD2DoesNotManufactureMonsterC3 = refl , (refl , refl)

trivialActionIsExplicitlyNonDiagnostic :
  Probe.trivialGroupActionMathematicallyAvailable Probe.canonicalPAHMonster3BProbe ≡ true
  × Probe.trivialActionCountsAsPhysicalMonsterEvidence Probe.canonicalPAHMonster3BProbe ≡ false
trivialActionIsExplicitlyNonDiagnostic = refl , refl

microscopicDepthStillDoesNotPayAllocation :
  Probe.microscopicPromotionPaysBH4AllocationFlux Probe.canonicalPAHElectronicMonsterBoundary ≡ false
microscopicDepthStillDoesNotPayAllocation = refl
