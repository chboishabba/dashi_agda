module DASHI.Physics.YangMills.BalabanClayT3ConfiguredCommonRadiusCertificateExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Propagators and Renormalization Transformations for
-- Lattice Gauge Theories. II", Communications in Mathematical Physics 96
-- (1984), 223--250. DOI: 10.1007/BF01240221
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
--
-- Relationship: the source papers motivate the small-field restriction.  The
-- radius 1/2048 and the exact scalar equality below are DASHI-owned conservative
-- arithmetic for the total configured coefficient 256.
------------------------------------------------------------------------

configuredRadius configuredReferenceCoercivity configuredHalfReference : ℚ
configuredRadius = + 1 / 2048
configuredReferenceCoercivity = + 1 / 4
configuredHalfReference = + 1 / 8

configuredHalfReferenceExact :
  configuredHalfReference + configuredHalfReference
  ≡ configuredReferenceCoercivity
configuredHalfReferenceExact = ℚRing.solve

configuredRadiusBudgetExact :
  Constants.configuredTotalCoefficient * configuredRadius
  ≡ configuredHalfReference
configuredRadiusBudgetExact = ℚRing.solve

configuredRadiusBudgetScaledExact : ∀ norm →
  (Constants.configuredTotalCoefficient * configuredRadius) * norm
  ≡ configuredHalfReference * norm
configuredRadiusBudgetScaledExact = ℚRing.solve-∀

record ConfiguredCommonRadiusPhysicalInput
    (Background State : Set) : Set₁ where
  field
    domination : Constants.ConfiguredFiveRemainderDomination Background State

    radiusIsConfigured : ∀ background state →
      Constants.radius domination background state ≡ configuredRadius

    referenceEnergy physicalEnergy : Background → State → ℚ

    referenceCoercive : ∀ background state →
      configuredReferenceCoercivity
        * Constants.normSq domination background state
      ≤ referenceEnergy background state

    physicalEnergyDefinition : ∀ background state →
      physicalEnergy background state
      ≡ referenceEnergy background state
        + Constants.totalRemainder domination background state

    physicalEnergyLowerFromAbsoluteRemainder : ∀ background state →
      Constants.totalRemainder domination background state
      ≤ configuredHalfReference
        * Constants.normSq domination background state →
      configuredHalfReference
        * Constants.normSq domination background state
      ≤ physicalEnergy background state

open ConfiguredCommonRadiusPhysicalInput public

configuredFiveBackgroundRemaindersBelowHalf :
  ∀ {Background State}
    (dataSet : ConfiguredCommonRadiusPhysicalInput Background State)
    background state →
  Constants.BackgroundInConfiguredRadius (domination dataSet) background →
  Constants.totalRemainder (domination dataSet) background state
  ≤ configuredHalfReference
      * Constants.normSq (domination dataSet) background state
configuredFiveBackgroundRemaindersBelowHalf dataSet background state inRadius =
  subst
    (λ upper →
      Constants.totalRemainder (domination dataSet) background state ≤ upper)
    (trans
      (cong
        (λ radiusValue →
          Constants.configuredTotalCoefficient * radiusValue
          * Constants.normSq (domination dataSet) background state)
        (radiusIsConfigured dataSet background state))
      (configuredRadiusBudgetScaledExact
        (Constants.normSq (domination dataSet) background state)))
    (Constants.configuredFiveRemainderSumBound
      (domination dataSet) background state inRadius)

configuredPhysicalSmallFieldCoercive :
  ∀ {Background State}
    (dataSet : ConfiguredCommonRadiusPhysicalInput Background State)
    background state →
  Constants.BackgroundInConfiguredRadius (domination dataSet) background →
  configuredHalfReference
    * Constants.normSq (domination dataSet) background state
  ≤ physicalEnergy dataSet background state
configuredPhysicalSmallFieldCoercive dataSet background state inRadius =
  physicalEnergyLowerFromAbsoluteRemainder dataSet background state
    (configuredFiveBackgroundRemaindersBelowHalf
      dataSet background state inRadius)

configuredCommonRadiusArithmeticLevel : ProofLevel
configuredCommonRadiusArithmeticLevel = machineChecked

configuredFiveRemaindersBelowHalfLevel : ProofLevel
configuredFiveRemaindersBelowHalfLevel = machineChecked

configuredPhysicalRemainderEstimateInputsLevel : ProofLevel
configuredPhysicalRemainderEstimateInputsLevel = conditional
