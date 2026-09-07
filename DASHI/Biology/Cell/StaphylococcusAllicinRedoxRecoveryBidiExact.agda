module DASHI.Biology.Cell.StaphylococcusAllicinRedoxRecoveryBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Cell.CellRecoveryBoundary as CellRecovery
import DASHI.Biology.Protein.StaphylococcusAllicinThiolomeExact as Thiolome

------------------------------------------------------------------------
-- S. AUREUS ALLICIN STRESS <-> CELLULAR RECOVERY BIDI
--
-- Direct source anchor:
--   Loi VV, Huyen NTT, Busche T, Tung QN, Gruhlke MCH, Kalinowski J,
--   Bernhardt J, Slusarenko AJ, Antelmann H.
--   "Staphylococcus aureus responds to allicin by global S-thioallylation ..."
--   Free Radic Biol Med. 2019;139:55-69.
--   DOI 10.1016/j.freeradbiomed.2019.05.018 / PMID 31121222.
--
-- The source supports a dynamic competition between allicin-mediated thiol
-- modification and BSH/BrxAB/YpdA/MerA-associated recovery.  This module maps
-- that evidence into the pre-existing generic CellRecoveryBoundary seam.
------------------------------------------------------------------------

data AllicinDisturbance : Set where
  allicinExposure : AllicinDisturbance

data MolecularDamageState : Set where
  proteinSThioallylation : MolecularDamageState
  lowMolecularWeightThiolShift : MolecularDamageState
  mixedDisulfideStress : MolecularDamageState
  regulatorModification : MolecularDamageState


data RecoveryAction : Set where
  bacillithiolBuffering : RecoveryAction
  brxDependentDethioallylation : RecoveryAction
  ypdAReduction : RecoveryAction
  merADisulfideReduction : RecoveryAction
  combinedThiolHomeostasis : RecoveryAction


data RegulatoryResponse : Set where
  hypRResponse : RegulatoryResponse
  mgrASarAContext : RegulatoryResponse
  oxidativeStressResponse : RegulatoryResponse
  unresolvedRegulatoryResponse : RegulatoryResponse


damageFromAllicin : AllicinDisturbance → MolecularDamageState
damageFromAllicin allicinExposure = proteinSThioallylation

recoveryForDamage : MolecularDamageState → RecoveryAction
recoveryForDamage proteinSThioallylation = brxDependentDethioallylation
recoveryForDamage lowMolecularWeightThiolShift = ypdAReduction
recoveryForDamage mixedDisulfideStress = merADisulfideReduction
recoveryForDamage regulatorModification = combinedThiolHomeostasis

regulatoryForDamage : MolecularDamageState → RegulatoryResponse
regulatoryForDamage proteinSThioallylation = hypRResponse
regulatoryForDamage lowMolecularWeightThiolShift = oxidativeStressResponse
regulatoryForDamage mixedDisulfideStress = hypRResponse
regulatoryForDamage regulatorModification = mgrASarAContext

record StaphylococcusCellRecoveryWeld
  (C : CellRecovery.CellRecoveryBoundary) : Set₁ where
  constructor staphylococcusCellRecoveryWeld
  field
    genericBridge : CellRecovery.ChemicalStressRecoveryBridge C

    allicinThiolomeReference : String
    bacillithiolReference : String
    brxABReference : String
    ypdAReference : String
    merAReference : String

    damageLaneMatchesDirectEvidence : Bool
    damageLaneMatchesDirectEvidenceIsTrue :
      damageLaneMatchesDirectEvidence ≡ true

    recoveryLaneMatchesDirectEvidence : Bool
    recoveryLaneMatchesDirectEvidenceIsTrue :
      recoveryLaneMatchesDirectEvidence ≡ true

    completeViabilityRecoveryMeasured : Bool
    completeViabilityRecoveryMeasuredIsFalse :
      completeViabilityRecoveryMeasured ≡ false

open StaphylococcusCellRecoveryWeld public

------------------------------------------------------------------------
-- Explicit receipts imported from the protein owner.  These make the direction
-- reciprocal: the cell-recovery model consumes the molecular evidence rather
-- than the thiolome terminating at a protein-level list.
------------------------------------------------------------------------

bshRecoveryReceipt : Thiolome.ThiolHomeostasisReceipt
bshRecoveryReceipt = Thiolome.bacillithiolReceipt

yPdARecoveryReceipt : Thiolome.ThiolHomeostasisReceipt
yPdARecoveryReceipt = Thiolome.ypdAReceipt

brxRecoveryReceipt : Thiolome.ThiolHomeostasisReceipt
brxRecoveryReceipt = Thiolome.brxReceipt

merARecoveryReceipt : Thiolome.ThiolHomeostasisReceipt
merARecoveryReceipt = Thiolome.merAReceipt

record RedoxRecoveryInterpretationBoundary : Set where
  constructor redoxRecoveryInterpretationBoundary
  field
    detoxificationResponseProvesNoMolecularDamage : Bool
    detoxificationResponseProvesNoMolecularDamageIsFalse :
      detoxificationResponseProvesNoMolecularDamage ≡ false

    reversalOfSomeSThioallylationProvesFullProteomeRestoration : Bool
    reversalOfSomeSThioallylationProvesFullProteomeRestorationIsFalse :
      reversalOfSomeSThioallylationProvesFullProteomeRestoration ≡ false

    survivalProvesNoRegulatoryPerturbation : Bool
    survivalProvesNoRegulatoryPerturbationIsFalse :
      survivalProvesNoRegulatoryPerturbation ≡ false

    proteinAndRecoveryReceiptsCanFeedCellViabilityModel : Bool
    proteinAndRecoveryReceiptsCanFeedCellViabilityModelIsTrue :
      proteinAndRecoveryReceiptsCanFeedCellViabilityModel ≡ true

canonicalRedoxRecoveryInterpretationBoundary : RedoxRecoveryInterpretationBoundary
canonicalRedoxRecoveryInterpretationBoundary =
  redoxRecoveryInterpretationBoundary false refl false refl false refl true refl
