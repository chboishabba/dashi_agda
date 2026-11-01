module DASHI.Culture.MissingDeceasedMaterialsProcessOperatorExact where

open import DASHI.Core.Prelude
open import DASHI.Core.ScientificOperatorFamilyExact as O

rezaMaterialsProcess : O.OperatorFactorisation
rezaMaterialsProcess = O.operator-factorisation
  "Monica Jacinto / Monica Reza"
  "DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact"
  O.materialsProcessShape
  "alloy composition + melt/remelt/work history -> microstructure/strength/burn-response vector"
  "The reusable operator is process-to-property mapping; patent examples do not define a universal constitutive law."

zhouMaterialsProcess : O.OperatorFactorisation
zhouMaterialsProcess = O.operator-factorisation
  "Zhou Guangyuan"
  "DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelBidiExact"
  O.materialsProcessShape
  "monomer/synthesis/process -> aerogel network/shrinkage/porosity -> thermal-property vector"
  "A source property portfolio constrains but does not close a manufacturing/scale-up process window."

fangMaterialsProcess : O.OperatorFactorisation
fangMaterialsProcess = O.operator-factorisation
  "Fang Daining"
  "DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact"
  O.materialsProcessShape
  "unit-cell/material design -> energy/eigenmode structure -> dispersion/property output"
  "Inverse structural design shares design-to-property geometry while preserving its mechanics and band-structure semantics."

materialsProcessFactorisations : List O.OperatorFactorisation
materialsProcessFactorisations = rezaMaterialsProcess ∷ zhouMaterialsProcess ∷ fangMaterialsProcess ∷ []
