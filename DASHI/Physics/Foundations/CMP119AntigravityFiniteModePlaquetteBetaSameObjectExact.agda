{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- FINITE-MODE BETA = LITERAL PLAQUETTE BETA, COMPONENTWISE
--
-- The existing finite-mode source theorem owns
--
--   beta_(k+1) = betaZ_k + betaInt_k.
--
-- The literal plaquette producer owns
--
--   beta_lit,k = vacuumPolarizationPlaquetteCoefficient_k
--                  + totalRemainder_k.
--
-- Thus the full source-beta/plaquette weld should not be paid independently.
-- It is compiled from the two physically meaningful same-object equalities:
--
--   betaZ_k   = one-loop plaquette coefficient_k
--   betaInt_k = literal plaquette remainder_k.
------------------------------------------------------------------------

record FiniteModePlaquetteBetaSameObject
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    (finiteMode :
      FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom)
    (oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat)
    (remainder : Plaquette.PlaquetteRemainderData Nat) : Set₁ where
  field
    gaussianBetaZSame :
      ∀ step →
      Local.betaZ (FiniteMode.gaussianAt finiteMode step)
      ≡ Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop step

    interactionBetaSame :
      ∀ step →
      Local.betaInt (FiniteMode.interactionAt finiteMode step)
      ≡ Plaquette.totalRemainder remainder step

open FiniteModePlaquetteBetaSameObject public

sourceBetaIsLiteralPlaquetteCoefficient :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder}
    (weld :
      FiniteModePlaquetteBetaSameObject
        {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
        finiteMode oneLoop remainder)
    step →
  Flow.beta trajectory (suc step)
  ≡
  Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop step
    + Plaquette.totalRemainder remainder step
sourceBetaIsLiteralPlaquetteCoefficient
    {finiteMode = finiteMode} weld step =
  trans
    (FiniteMode.sourceBetaSplitExact finiteMode step)
    (cong₂
      _+_
      (gaussianBetaZSame weld step)
      (interactionBetaSame weld step))

asCMP109LiteralPlaquetteCoefficientWeld :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder} →
  FiniteModePlaquetteBetaSameObject
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    finiteMode oneLoop remainder →
  Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory
asCMP109LiteralPlaquetteCoefficientWeld
    {oneLoop = oneLoop} {remainder = remainder} weld = record
  { Constructor.CMP109LiteralPlaquetteCoefficientWeld.oneLoop =
      oneLoop
  ; Constructor.CMP109LiteralPlaquetteCoefficientWeld.remainder =
      remainder
  ; Constructor.CMP109LiteralPlaquetteCoefficientWeld.sourceBetaIsLiteralPlaquetteCoefficient =
      sourceBetaIsLiteralPlaquetteCoefficient weld
  }

fullSourceBetaPlaquetteIdentityStillRequired : Bool
fullSourceBetaPlaquetteIdentityStillRequired = false

gaussianBetaZSameObjectStillRequired : Bool
gaussianBetaZSameObjectStillRequired = true

interactionBetaSameObjectStillRequired : Bool
interactionBetaSameObjectStillRequired = true

fullSourceBetaPlaquetteIdentityStillRequiredIsFalse :
  fullSourceBetaPlaquetteIdentityStillRequired ≡ false
fullSourceBetaPlaquetteIdentityStillRequiredIsFalse = refl

gaussianBetaZSameObjectStillRequiredIsTrue :
  gaussianBetaZSameObjectStillRequired ≡ true
gaussianBetaZSameObjectStillRequiredIsTrue = refl

interactionBetaSameObjectStillRequiredIsTrue :
  interactionBetaSameObjectStillRequired ≡ true
interactionBetaSameObjectStillRequiredIsTrue = refl

finiteModePlaquetteBetaSameObjectCompilerLevel : ProofLevel
finiteModePlaquetteBetaSameObjectCompilerLevel = machineChecked

literalFiniteModePlaquetteComponentIdentificationLevel : ProofLevel
literalFiniteModePlaquetteComponentIdentificationLevel = conditional
