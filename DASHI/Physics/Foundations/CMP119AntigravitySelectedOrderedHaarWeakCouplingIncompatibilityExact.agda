{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedOrderedHaarWeakCouplingIncompatibilityExact where

------------------------------------------------------------------------
-- SAME-PHYSICAL-MEASURE FIREWALL
--
-- The existing selected ordered-Haar branch obtains negative diagonal active
-- stress under its SU(2) trace closure inputs. The finite CMP109 inverse-
-- square history, Lorentzian E/B continuation, and weak-coupling threshold
-- obtain NONNEGATIVE active stress.  On identifying their actual stress
-- observables these conclusions are incompatible.
--
-- No false equivalence between the two source objects is introduced here:
-- an explicit same-measure/same-tensor equality is precisely the remaining
-- physical comparison. Thus a candidate selected source must establish
-- which hypothesis of the two source packages fails, or add a genuinely
-- different stress contribution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119AntigravitySelectedMetricFamilyOrderedHaarClosureExact as Haar
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonGibbsMinimalAnchorExact as Minimal
import DASHI.Physics.Foundations.CMP119AntigravityActiveScaleInverseCouplingNoGoExact as Active
import DASHI.Physics.Foundations.CMP119AntigravityLorentzianF2ContinuationExact as Lorentz
import DASHI.Physics.Foundations.CMP119AntigravityWeakCouplingTraceEnergyNoGoExact as YM
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson

module _
  {G X Cutoff Configuration Observable Position
   CurvaturePolynomial LocalOperator OPECoefficient StressTensor
   HilbertSpace Hamiltonian VacuumState : Set}
  where

  C : Top.LiteralYangMillsCarriers
  C = Physical.physicalLiteralCarriers
    G X Cutoff Configuration ℚ Observable Position
    CurvaturePolynomial LocalOperator OPECoefficient StressTensor
    HilbertSpace Hamiltonian VacuumState

  module _
    {trajectory split}
    {inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
    (realization : Basis.SymmetricMetricBasisRealization domain)
    (representation : StressRep.CanonicalMetricStressRepresentation domain)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate)
    (measureWeld :
      R124.BalabanDensityLiteralFiniteMeasureWeld
        {trajectory = trajectory} {split = split} {inputs = inputs}
        Y group)
    (wilsonInsertion :
      Wilson.ClassicalWilsonSelectedInsertion Configuration)
    where

    orderedHaarAndWeakYMExcludeOneAnother :
      ∀ {Mode Atom betaData}
      {history : History.FiniteModeInverseSquareTerminalHistoryData
        trajectory Mode Atom betaData}
      (continuation : Lorentz.LorentzianF2ContinuationReceipt)
      (threshold : Active.ActiveScaleTraceThresholdCertificate history)
      (scale : Nat) (active : History.ActiveScale history scale)
      (ordered :
        Haar.SelectedMetricFamilyOrderedHaarClosureInput
          domain realization representation selected measureWeld
          wilsonInsertion)
      (background : Chain.Background activity)
      (sameSelectedStress :
        Minimal.selectedDiagonalActiveSum
          domain realization representation selected
          measureWeld wilsonInsertion background
        ≡
        YM.activeStress (Active.activeScaleNoGoData
          continuation threshold scale active)) →
      ⊥
    orderedHaarAndWeakYMExcludeOneAnother
      continuation threshold scale active ordered background sameSelectedStress =
      ℚP.<⇒≱
        (subst (_< 0ℚ) sameSelectedStress
          (Haar.selectedMetricFamilyOrderedHaarDiagonalActiveSumNegative
            domain realization representation selected measureWeld
            wilsonInsertion ordered background))
        (Active.activeCMP119ScaleTraceAnomalyNoGo
          continuation threshold scale active)
