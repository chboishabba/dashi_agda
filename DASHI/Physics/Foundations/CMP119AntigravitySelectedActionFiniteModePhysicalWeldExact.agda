{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedActionFiniteModePhysicalWeldExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (_+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact as FinitePlaquette
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- Selected physical one-step action -> SAME finite-mode CMP109 beta.
--
-- Unlike a separate "source beta is selected effective action" axiom,
-- the beta/action equality is here DERIVED from the preexisting finite-mode
-- CMP109 split plus five componentwise projector identities.
--
-- The five same-object identities must be established on the actual selected
-- Wilson/FP/Haar one-step action. A synthetically fitted action is insufficient.
------------------------------------------------------------------------

record SelectedActionFiniteModePlaquetteIdentification
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    (finiteMode : FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom)
    (oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat)
    (remainder : Plaquette.PlaquetteRemainderData Nat)
    (selectedAction : Plaquette.ExactOneStepEffectiveActionData Nat) : Set₁ where
  field
    finiteModePlaquette :
      FinitePlaquette.FiniteModePlaquetteBetaSameObject
        finiteMode oneLoop remainder

    background : ∀ k →
      Plaquette.backgroundSubstitutionPlaquetteCoefficient selectedAction k
      ≡ Plaquette.backgroundRemainder remainder k
    haar : ∀ k →
      Plaquette.haarJacobianPlaquetteCoefficient selectedAction k
      ≡ Plaquette.jacobianRemainder remainder k
    determinant : ∀ k →
      Plaquette.fluctuationDeterminantPlaquetteCoefficient selectedAction k
      ≡ Plaquette.determinantRemainder remainder k
    connected : ∀ k →
      Plaquette.connectedCumulantPlaquetteCoefficient selectedAction k
      ≡ Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop k
        + Plaquette.bchRemainder remainder k
    localization : ∀ k →
      Plaquette.localizationRemainderPlaquetteCoefficient selectedAction k
      ≡ Plaquette.localizationRemainder remainder k

open SelectedActionFiniteModePlaquetteIdentification public

selectedActionCoefficientIsLiteral :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder selectedAction} →
  SelectedActionFiniteModePlaquetteIdentification
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    finiteMode oneLoop remainder selectedAction →
  ∀ k →
  Plaquette.plaquetteCoefficientProjector
    (Plaquette.effectiveAction selectedAction k)
  ≡ Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop k
    + Plaquette.totalRemainder remainder k
selectedActionCoefficientIsLiteral
    {oneLoop = oneLoop} {remainder = remainder}
    {selectedAction = selectedAction} source k =
  trans
    (Plaquette.localizedPlaquetteCoefficientOfExactRGStep
      selectedAction k)
    termwise
  where
    termwise :
      Plaquette.backgroundSubstitutionPlaquetteCoefficient selectedAction k
      + (Plaquette.haarJacobianPlaquetteCoefficient selectedAction k
      + (Plaquette.fluctuationDeterminantPlaquetteCoefficient selectedAction k
      + (Plaquette.connectedCumulantPlaquetteCoefficient selectedAction k
      + Plaquette.localizationRemainderPlaquetteCoefficient selectedAction k)))
      ≡ Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop k
        + Plaquette.totalRemainder remainder k
    termwise
      rewrite background source k
            | haar source k
            | determinant source k
            | connected source k
            | localization source k
            | Plaquette.totalRemainderDefinition remainder k
      = ℚRing.solve []

sourceBetaIsSelectedActionCoefficient :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder selectedAction} →
  SelectedActionFiniteModePlaquetteIdentification
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    finiteMode oneLoop remainder selectedAction →
  ∀ k →
  Flow.beta trajectory (suc k)
  ≡ Plaquette.plaquetteCoefficientProjector
      (Plaquette.effectiveAction selectedAction k)
sourceBetaIsSelectedActionCoefficient source k =
  trans
    (FinitePlaquette.sourceBetaIsLiteralPlaquetteCoefficient
      (finiteModePlaquette source) k)
    (sym (selectedActionCoefficientIsLiteral source k))

asCMP109CoefficientWeld :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder selectedAction} →
  SelectedActionFiniteModePlaquetteIdentification
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    finiteMode oneLoop remainder selectedAction →
  Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory
asCMP109CoefficientWeld source =
  FinitePlaquette.asCMP109LiteralPlaquetteCoefficientWeld
    (finiteModePlaquette source)
