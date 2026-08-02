module DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalEquation012Exact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PhysicalScaleGeometryExact as Physical
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed

------------------------------------------------------------------------
-- Equation (0.12) at the minimal source-admissible physical scale.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The block list and coefficient are no longer arbitrary:
--
--   L = 13, r = 6, |B_r| = 28561, blockWeight = 1/28561.
--
-- The remaining fields are exactly the group-valued averaged contour variables
-- from equation (0.11), the crossing and reverse-bond values, and the selected
-- logarithm/exponential chart.
------------------------------------------------------------------------

record MinimalEquation012Inputs
    (Field Group Lie : Set) : Set₁ where
  field
    geometry : Physical.CMP109PhysicalScaleGeometry
      Minimal.radius Minimal.RepositoryFineSite
      Minimal.RepositoryCoarseSite Nat

    zeroLie : Lie
    addLie : Lie → Lie → Lie
    scaleLie : ℚ → Lie → Lie

    multiplyGroup : Group → Group → Group

    sourceAveragedContour :
      Field → Minimal.RepositoryCoarseBond →
      Minimal.RepositoryFineSite → Group

    crossingValue :
      Field → Minimal.RepositoryCoarseBond →
      Minimal.RepositoryFineSite → Group

    targetAveragedContourReverse :
      Field → Minimal.RepositoryCoarseBond →
      Minimal.RepositoryFineSite → Group

    reversedCoarseBondValue :
      Field → Minimal.RepositoryCoarseBond → Group

    coarseBondValue :
      Field → Minimal.RepositoryCoarseBond → Group

    antiHermitianLogCoordinate : Group → Lie
    outerExponential : Lie → Group

open MinimalEquation012Inputs public

minimalEquation012PrintedData :
  ∀ {Field Group Lie} →
  MinimalEquation012Inputs Field Group Lie →
  Printed.PrintedCMP109Equation012Data
    Field Minimal.RepositoryCoarseBond Minimal.RepositoryFineSite
    Group Lie ℚ
minimalEquation012PrintedData inputs = record
  { Printed.PrintedCMP109Equation012Data.blockSites =
      λ coarseBond →
        Physical.physicalBlockElements
          (geometry inputs) (Carrier.first coarseBond)
  ; Printed.PrintedCMP109Equation012Data.blockWeight =
      λ coarseBond → Minimal.siteWeightℚ
  ; Printed.PrintedCMP109Equation012Data.zeroLie = zeroLie inputs
  ; Printed.PrintedCMP109Equation012Data.addLie = addLie inputs
  ; Printed.PrintedCMP109Equation012Data.scaleLie = scaleLie inputs
  ; Printed.PrintedCMP109Equation012Data.multiplyGroup =
      multiplyGroup inputs
  ; Printed.PrintedCMP109Equation012Data.sourceAveragedContour =
      sourceAveragedContour inputs
  ; Printed.PrintedCMP109Equation012Data.crossingValue =
      crossingValue inputs
  ; Printed.PrintedCMP109Equation012Data.targetAveragedContourReverse =
      targetAveragedContourReverse inputs
  ; Printed.PrintedCMP109Equation012Data.reversedCoarseBondValue =
      reversedCoarseBondValue inputs
  ; Printed.PrintedCMP109Equation012Data.coarseBondValue =
      coarseBondValue inputs
  ; Printed.PrintedCMP109Equation012Data.antiHermitianLogCoordinate =
      antiHermitianLogCoordinate inputs
  ; Printed.PrintedCMP109Equation012Data.outerExponential =
      outerExponential inputs
  }

minimalEquation012Map :
  ∀ {Field Group Lie} →
  MinimalEquation012Inputs Field Group Lie →
  Field → Minimal.RepositoryCoarseBond → Group
minimalEquation012Map inputs =
  Printed.printedEquation012Map (minimalEquation012PrintedData inputs)

minimalEquation012UsesPrintedOrder :
  ∀ {Field Group Lie}
    (inputs : MinimalEquation012Inputs Field Group Lie) →
  minimalEquation012Map inputs
  ≡ Printed.implementedEquation012Map
      (minimalEquation012PrintedData inputs)
minimalEquation012UsesPrintedOrder inputs = refl

minimalEquation012BlockCardinality :
  ∀ {Field Group Lie}
    (inputs : MinimalEquation012Inputs Field Group Lie)
    coarseBond →
  length
    (Printed.blockSites
      (minimalEquation012PrintedData inputs) coarseBond)
  ≡ Minimal.volume
minimalEquation012BlockCardinality inputs coarseBond =
  trans
    (Physical.physicalBlockEnumerationLength
      (geometry inputs) (Carrier.first coarseBond))
    Minimal.volumeExact

minimalEquation012BlockWeight :
  ∀ {Field Group Lie}
    (inputs : MinimalEquation012Inputs Field Group Lie)
    coarseBond →
  Printed.blockWeight
    (minimalEquation012PrintedData inputs) coarseBond
  ≡ Minimal.siteWeightℚ
minimalEquation012BlockWeight inputs coarseBond = refl

cmp109MinimalEquation012InstantiationLevel : ProofLevel
cmp109MinimalEquation012InstantiationLevel = machineChecked

cmp109MinimalEquation012WeightAndCardinalityLevel : ProofLevel
cmp109MinimalEquation012WeightAndCardinalityLevel = machineChecked

physicalCMP109Equation011AveragedContourInputsLevel : ProofLevel
physicalCMP109Equation011AveragedContourInputsLevel = conditional

physicalCMP109PrincipalLogChartInputsLevel : ProofLevel
physicalCMP109PrincipalLogChartInputsLevel = conditional
