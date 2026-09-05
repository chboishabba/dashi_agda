module DASHI.Law.FascismAtrocitySourceValidation where

open import DASHI.Core.Prelude

import DASHI.Law.GazaGenocideHerzogZionismSourceReceiptsExact as Source
import DASHI.Law.FascismAtrocitySourceCrossPollinationExact as FascismBridge
import DASHI.Law.HerzogCommandIdeologyProvenanceBidiExact as Herzog

commissionGenocideFindingKeepsCommissionRole :
  Source.role Source.commissionGenocideFinding ≡ Source.unIndependentCommissionFinding
commissionGenocideFindingKeepsCommissionRole = refl

herzogFindingKeepsCommissionRole :
  Source.role Source.commissionHerzogIncitementFinding ≡ Source.unIndependentCommissionFinding
herzogFindingKeepsCommissionRole = refl

zionism3379KeepsGeneralAssemblyRole :
  Source.role Source.unga3379Receipt ≡ Source.generalAssemblyResolution
zionism3379KeepsGeneralAssemblyRole = refl

commissionFindingDoesNotCloseNSWPoliceMotive :
  Herzog.firstIdeologyCommandResidual
    Herzog.nswCommandWasZionistIdeologyMotivated
    Herzog.canonicalCommissionOnlyCutset
  ≡ Herzog.motiveResidual
commissionFindingDoesNotCloseNSWPoliceMotive =
  Herzog.commissionFindingDoesNotCloseMotive

commissionFindingDoesNotCloseCoordination :
  Herzog.firstIdeologyCommandResidual
    Herzog.nswPoliceCoordinatedWithHerzogOrIsraeliOfficials
    Herzog.canonicalCommissionOnlyCutset
  ≡ Herzog.coordinationResidual
commissionFindingDoesNotCloseCoordination =
  Herzog.commissionFindingDoesNotCloseCoordination

sourceOnlyFascismAssessmentKeepsContractionOpen :
  FascismBridge.empiricalClosure
    (FascismBridge.contractionReceipt FascismBridge.canonicalSourceOnlyAssessment)
  ≡ false
sourceOnlyFascismAssessmentKeepsContractionOpen = refl
