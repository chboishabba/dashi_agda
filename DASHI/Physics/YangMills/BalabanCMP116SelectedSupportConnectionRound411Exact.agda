{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact where

------------------------------------------------------------------------
-- ROUND411 / TWO SOURCE MARKS FORCE CONNECTING-DOMAIN GEOMETRY
--
-- The remaining B proof needs the source-geometric implication
--
--   selected differentiated term survives
--       -> its localization domain connects both selected source supports
--       -> selected support distance <= domain/tree distance.
--
-- R390 already proves that a lower bound on distance is all a decreasing
-- geometric/exponential consumer observes.  This owner isolates that geometry
-- from the differentiated analytic estimate itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanCMP116PhysicalDistanceLowerRound390Exact as R390

record SelectedSupportConnectionGeometry
    (Domain Term : Set) : Set₁ where
  field
    selectedConnectingDistance : Nat
    domainTreeDistance : Domain → Nat

    selectedDifferentiatedTermSurvives : Domain → Term → Set
    domainConnectsBothSupports : Domain → Set

    survivingTermForcesSupportConnection :
      ∀ domain term →
      selectedDifferentiatedTermSurvives domain term →
      domainConnectsBothSupports domain

    supportConnectionForcesDistanceLower :
      ∀ domain →
      domainConnectsBothSupports domain →
      selectedConnectingDistance Nat.≤ domainTreeDistance domain

open SelectedSupportConnectionGeometry public

survivingTermForcesSelectedDistanceLower :
  ∀ {Domain Term}
    (geometry : SelectedSupportConnectionGeometry Domain Term)
    domain term →
  selectedDifferentiatedTermSurvives geometry domain term →
  selectedConnectingDistance geometry Nat.≤ domainTreeDistance geometry domain
survivingTermForcesSelectedDistanceLower geometry domain term survives =
  supportConnectionForcesDistanceLower geometry domain
    (survivingTermForcesSupportConnection geometry domain term survives)

domainDecayBelowSelectedDecay :
  ∀ {Domain Term}
    (geometry : SelectedSupportConnectionGeometry Domain Term)
    domain →
  domainConnectsBothSupports geometry domain →
  Geo.halfPower (domainTreeDistance geometry domain)
    ≤ Geo.halfPower (selectedConnectingDistance geometry)
domainDecayBelowSelectedDecay geometry domain connects =
  R390.halfPowerAntitone
    (supportConnectionForcesDistanceLower geometry domain connects)

record ConnectedDomainGeometricMajorant
    {Domain Term : Set}
    (geometry : SelectedSupportConnectionGeometry Domain Term) : Set₁ where
  field
    amplitude : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude
    domainMajorant : Domain → ℚ

    domainMajorantBelowTreeDecay :
      ∀ domain →
      domainMajorant domain
      ≤ amplitude * Geo.halfPower (domainTreeDistance geometry domain)

open ConnectedDomainGeometricMajorant public

connectedDomainMajorantBelowSelectedDecay :
  ∀ {Domain Term}
    {geometry : SelectedSupportConnectionGeometry Domain Term}
    (majorant : ConnectedDomainGeometricMajorant geometry)
    domain →
  domainConnectsBothSupports geometry domain →
  domainMajorant majorant domain
    ≤ amplitude majorant * Geo.halfPower (selectedConnectingDistance geometry)
connectedDomainMajorantBelowSelectedDecay {geometry = geometry}
    majorant domain connects =
  ℚP.≤-trans
    (domainMajorantBelowTreeDecay majorant domain)
    (Norm.scaleNonnegative
      (amplitude majorant)
      (amplitudeNonnegative majorant)
      (domainDecayBelowSelectedDecay geometry domain connects))

survivingTermDomainMajorantBelowSelectedDecay :
  ∀ {Domain Term}
    {geometry : SelectedSupportConnectionGeometry Domain Term}
    (majorant : ConnectedDomainGeometricMajorant geometry)
    domain term →
  selectedDifferentiatedTermSurvives geometry domain term →
  domainMajorant majorant domain
    ≤ amplitude majorant * Geo.halfPower (selectedConnectingDistance geometry)
survivingTermDomainMajorantBelowSelectedDecay {geometry = geometry}
    majorant domain term survives =
  connectedDomainMajorantBelowSelectedDecay majorant domain
    (survivingTermForcesSupportConnection geometry domain term survives)

round411SupportConnectionCompilerLevel : ProofLevel
round411SupportConnectionCompilerLevel = machineChecked

round411DistanceDecayTransportLevel : ProofLevel
round411DistanceDecayTransportLevel = machineChecked

-- Genuine selected-source geometry still to instantiate:
-- a nonzero/surviving twice-marked CMP116 term must live on a localization
-- domain connecting both selected source supports, and that connection must
-- dominate the selected physical/tree separation.
literalSelectedTwoJSupportConnectionLevel : ProofLevel
literalSelectedTwoJSupportConnectionLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
