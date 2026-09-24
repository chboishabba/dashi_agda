{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCylinderMeasureRepresentationMaxCutRound495Exact where

------------------------------------------------------------------------
-- ROUND495 / COUNTABLY-ADDITIVE CONTINUUM REPRESENTATION MAX-CUT
--
-- Do not call a positive normalized expectation functional a measure.
--
-- For the selected cylinder algebra, the representation wall is split into:
--
--   M1 finite/projective cylinder probability premeasure;
--   M2 continuity at the empty event for decreasing cylinder events;
--      (the genuine premeasure / countable-additivity input);
--   M3 standard Caratheodory extension from that premeasure;
--   M4 selected cylinder expectations agree with integration against the
--      extended measure.
--
-- M3 is standard measure theory.  M1/M2/M4 are the YM/source-facing payments.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476

record CylinderProbabilityPremeasure
    (Event Mass : Set) : Set₁ where
  field
    empty whole : Event
    complement : Event → Event
    union : Event → Event → Event
    Disjoint : Event → Event → Set

    zero one : Mass
    add : Mass → Mass → Mass
    mass : Event → Mass

    emptyMass : mass empty ≡ zero
    wholeMass : mass whole ≡ one

    finiteAdditivity :
      ∀ left right →
      Disjoint left right →
      mass (union left right)
      ≡ add (mass left) (mass right)

open CylinderProbabilityPremeasure public

record ProjectiveCylinderProbability
    (Index Event Mass : Set) : Set₂ where
  field
    levelPremeasure :
      Index → CylinderProbabilityPremeasure Event Mass

    Restricts : Index → Index → Set
    restrictEvent : ∀ lower upper → Restricts lower upper → Event → Event

    projectiveMassConsistency :
      ∀ lower upper
        (restriction : Restricts lower upper)
        event →
      mass (levelPremeasure lower)
        (restrictEvent lower upper restriction event)
      ≡
      mass (levelPremeasure upper) event

open ProjectiveCylinderProbability public

record ContinuityAtEmpty
    {Event Mass : Set}
    (premeasure : CylinderProbabilityPremeasure Event Mass) : Set₁ where
  field
    ConvergesMass : (Nat → Mass) → Mass → Set
    Decreasing : (Nat → Event) → Set
    HasEmptyIntersection : (Nat → Event) → Set

    decreasingEmptyMassVanishes :
      ∀ events →
      Decreasing events →
      HasEmptyIntersection events →
      ConvergesMass
        (λ n → mass premeasure (events n))
        (zero premeasure)

open ContinuityAtEmpty public

------------------------------------------------------------------------
-- Standard extension authority.
--
-- This is deliberately generic.  The authority states the classical theorem:
-- finite additivity + continuity at empty on the cylinder algebra gives a
-- sigma-additive extension.  It does NOT contain YM-specific physics.
------------------------------------------------------------------------

record MeasureExtensionAuthority
    (Event Mass Observable Scalar : Set) : Set₂ where
  field
    SigmaMeasure : Set
    IsCountablyAdditive : SigmaMeasure → Set

    extend :
      (premeasure : CylinderProbabilityPremeasure Event Mass) →
      ContinuityAtEmpty premeasure →
      SigmaMeasure

    extensionCountablyAdditive :
      ∀ premeasure continuity →
      IsCountablyAdditive (extend premeasure continuity)

    integrate :
      SigmaMeasure → Observable → Scalar

open MeasureExtensionAuthority public

------------------------------------------------------------------------
-- YM representation specialization.
------------------------------------------------------------------------

record CylinderRepresentationInputs
    (Index Event Mass Observable Scalar : Set)
    (sourceExpectation : Observable → Scalar)
    : Set₂ where
  field
    projective :
      ProjectiveCylinderProbability Index Event Mass

    selectedIndex : Index

    continuity :
      ContinuityAtEmpty
        (levelPremeasure projective selectedIndex)

    extensionAuthority :
      MeasureExtensionAuthority Event Mass Observable Scalar

    -- Genuine YM/source identification: the selected E_infty on the cylinder
    -- observables equals integration against the sigma-additive extension.
    sourceExpectationIsExtendedIntegral :
      ∀ observable →
      sourceExpectation observable
      ≡
      integrate extensionAuthority
        (extend extensionAuthority
          (levelPremeasure projective selectedIndex)
          continuity)
        observable

open CylinderRepresentationInputs public

asSourceLimitRepresentation :
  ∀ {Index Event Mass Observable}
    {sourceExpectation : Observable → ℝ} →
  CylinderRepresentationInputs
    Index Event Mass Observable
    ℝ
    sourceExpectation →
  R476.SourceLimitRepresentation Observable sourceExpectation
asSourceLimitRepresentation inputs = record
  { R476.SourceLimitRepresentation.represented = record
      { R476.RepresentedContinuum.MeasureObject =
          SigmaMeasure (extensionAuthority inputs)
      ; R476.RepresentedContinuum.IsCountablyAdditive =
          IsCountablyAdditive (extensionAuthority inputs)
      ; R476.RepresentedContinuum.measure =
          extend (extensionAuthority inputs)
            (levelPremeasure (projective inputs) (selectedIndex inputs))
            (continuity inputs)
      ; R476.RepresentedContinuum.integrate =
          integrate (extensionAuthority inputs)
      ; R476.RepresentedContinuum.countablyAdditive =
          extensionCountablyAdditive (extensionAuthority inputs)
            (levelPremeasure (projective inputs) (selectedIndex inputs))
            (continuity inputs)
      }
  ; R476.SourceLimitRepresentation.sourceLimitIsIntegral =
      sourceExpectationIsExtendedIntegral inputs
  }

finiteProjectiveConsistencyAloneImpliesSigmaAdditivity : Bool
finiteProjectiveConsistencyAloneImpliesSigmaAdditivity = false

continuityAtEmptyIsRealMeasureTheoreticPayment : Bool
continuityAtEmptyIsRealMeasureTheoreticPayment = true

caratheodoryExtensionIsYMPhysics : Bool
caratheodoryExtensionIsYMPhysics = false

sourceExpectationIntegralIdentificationStillRequired : Bool
sourceExpectationIntegralIdentificationStillRequired = true

round495RepresentationCompilerLevel : ProofLevel
round495RepresentationCompilerLevel = machineChecked

round495CaratheodoryExtensionAuthorityLevel : ProofLevel
round495CaratheodoryExtensionAuthorityLevel = standardImported

literalRound495FiniteProjectivePremeasureLevel : ProofLevel
literalRound495FiniteProjectivePremeasureLevel = conditional

literalRound495ContinuityAtEmptyLevel : ProofLevel
literalRound495ContinuityAtEmptyLevel = conditional

literalRound495CylinderExpectationIdentificationLevel : ProofLevel
literalRound495CylinderExpectationIdentificationLevel = conditional
