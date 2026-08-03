module DASHI.Physics.YangMills.BalabanClayGate4CountingAndLocalizationReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRationalConstantsExact as BishopConstants
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geometric
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as ExistingRG

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- The first two papers are the primary candidates for the connected-family and
-- localization-norm estimates used by the later R-operation proof. Exact
-- theorem-number attribution remains pending direct primary-text verification.
-- The DASHI theorems below reuse existing in-repository quantitative owners and
-- do not claim that the remaining representation bridge has been proved.
------------------------------------------------------------------------

record RootedComponentFamilyCounting
    (Scale Volume Root : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root
    componentFamilyMass : Scale → Volume → Root → Nat → ℚ
    componentFamilyEmbedsInRootedShell : ∀ scale volume root depth →
      componentFamilyMass scale volume root depth
      ≤ Shell.rootedShell shellData scale volume root depth

open RootedComponentFamilyCounting public

componentFamilyCountingBound :
  ∀ {Scale Volume Root}
    (dataSet : RootedComponentFamilyCounting Scale Volume Root)
    scale volume root depth →
  componentFamilyMass dataSet scale volume root depth
  ≤ BishopConstants.quarter * Geometric.halfPower depth
componentFamilyCountingBound dataSet scale volume root depth =
  Shell.transitive (shellData dataSet)
    (componentFamilyEmbedsInRootedShell dataSet scale volume root depth)
    (Shell.rootedShellBelowQuarterHalfPower
      (shellData dataSet) scale volume root depth)

record ExactRootedFamilyRepresentation
    (Scale Volume Root : Set)
    (shellData : Shell.TraversalShellData Scale Volume Root) : Set₁ where
  field
    Family : Set
    scaleOf : Family → Scale
    volumeOf : Family → Volume
    rootOf : Family → Root
    depthOf : Family → Nat
    familyMass : Family → ℚ
    familyMassDefinition : ∀ family →
      familyMass family
      ≡ Shell.rootedShell shellData
          (scaleOf family) (volumeOf family) (rootOf family) (depthOf family)

open ExactRootedFamilyRepresentation public

exactRootedFamilyCounting :
  ∀ {Scale Volume Root}
    {shellData : Shell.TraversalShellData Scale Volume Root}
    (representation : ExactRootedFamilyRepresentation
      Scale Volume Root shellData)
    family →
  familyMass representation family
  ≤ BishopConstants.quarter * Geometric.halfPower (depthOf representation family)
exactRootedFamilyCounting {shellData = shellData} representation family =
  subst
    (λ lower → lower
      ≤ BishopConstants.quarter * Geometric.halfPower (depthOf representation family))
    (sym (familyMassDefinition representation family))
    (Shell.rootedShellBelowQuarterHalfPower shellData
      (scaleOf representation family)
      (volumeOf representation family)
      (rootOf representation family)
      (depthOf representation family))

existingLocalizationBudgetBound :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density)
    region →
  ExistingRG.LessEqual rg
    (ExistingRG.localizationContribution rg region)
    (ExistingRG.localizationBudget rg region)
existingLocalizationBudgetBound rg = ExistingRG.localizationBudgetBound rg

existingLocalizationPreservesSupport :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density) →
  ExistingRG.LocalizationPreservesSupport rg
existingLocalizationPreservesSupport rg =
  ExistingRG.localizationPreservesSupport rg

existingLocalizationPreservesExponentialWeight :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density) →
  ExistingRG.LocalizationPreservesExponentialWeight rg
existingLocalizationPreservesExponentialWeight rg =
  ExistingRG.localizationPreservesExponentialWeight rg

record RLocalizationNormInterpretation
    {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density)
    (RExpression : Set) : Set₁ where
  field
    regionOf : RExpression → Region
    localizedNorm localizationNormUpper : RExpression → Bound
    localizedNormMeaning : ∀ expression →
      localizedNorm expression
      ≡ ExistingRG.localizationContribution rg (regionOf expression)
    localizationUpperMeaning : ∀ expression →
      localizationNormUpper expression
      ≡ ExistingRG.localizationBudget rg (regionOf expression)

open RLocalizationNormInterpretation public

rLocalizationBudgetFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density RExpression}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    (interpretation : RLocalizationNormInterpretation rg RExpression)
    expression →
  ExistingRG.LessEqual rg
    (localizedNorm interpretation expression)
    (localizationNormUpper interpretation expression)
rLocalizationBudgetFromExistingRG {rg = rg} interpretation expression =
  subst
    (λ lower → ExistingRG.LessEqual rg lower
      (localizationNormUpper interpretation expression))
    (sym (localizedNormMeaning interpretation expression))
    (subst
      (λ upper → ExistingRG.LessEqual rg
        (ExistingRG.localizationContribution rg
          (regionOf interpretation expression)) upper)
      (sym (localizationUpperMeaning interpretation expression))
      (ExistingRG.localizationBudgetBound rg
        (regionOf interpretation expression)))

rootedComponentFamilyCountingReuseLevel : ProofLevel
rootedComponentFamilyCountingReuseLevel = machineChecked

exactRootedFamilyRepresentationCountingLevel : ProofLevel
exactRootedFamilyRepresentationCountingLevel = machineChecked

existingRGLocalizationBudgetReuseLevel : ProofLevel
existingRGLocalizationBudgetReuseLevel = machineChecked

existingRGLocalizationSupportWeightReuseLevel : ProofLevel
existingRGLocalizationSupportWeightReuseLevel = machineChecked

rComponentFamilyToRootedTraversalIdentificationLevel : ProofLevel
rComponentFamilyToRootedTraversalIdentificationLevel = conditional

rLocalizationNormInterpretationInputsLevel : ProofLevel
rLocalizationNormInterpretationInputsLevel = conditional
