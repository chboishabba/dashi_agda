{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND534:
-- PROJECTIVE CYLINDER FAMILY -> COUNTABLY-ADDITIVE CONTINUUM REPRESENTATION
--
-- Correction to the older R495 specialization:
--
-- Extending one selected finite-cutoff premeasure is not enough to construct
-- the continuum/projective measure.  The extension theorem must consume the
-- WHOLE projective cylinder family.
--
-- The preferred representation boundary is therefore:
--
--   projective finite cylinder probabilities
--   + projective continuity at empty
--   + standard projective/Caratheodory-Kolmogorov extension authority
--       -> countably-additive continuum measure
--   + selected expectation = integral on the selected observable class.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsCylinderMeasureRepresentationMaxCutRound495Exact as R495
import DASHI.Physics.YangMills.YangMillsPositiveProjectiveCylinderProbabilityRound538Exact as R538
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476

record ProjectiveContinuityAtEmpty
    {Index Event Mass : Set}
    (projective : R538.ProjectivePositiveCylinderProbability Index Event)
    : Set₂ where
  field
    CylinderSequence : Set
    eventAt : CylinderSequence → Nat → Event
    indexAt : CylinderSequence → Nat → Index

    Decreasing : CylinderSequence → Set
    HasEmptyIntersection : CylinderSequence → Set

    ConvergesMass : (Nat → Mass) → Mass → Set

    zero : Mass

    decreasingEmptyMassVanishes :
      ∀ sequence →
      Decreasing sequence →
      HasEmptyIntersection sequence →
      ConvergesMass
        (λ n →
          R495.mass
            (R538.premeasure
              (R538.levelProbability projective (indexAt sequence n)))
            (eventAt sequence n))
        zero

open ProjectiveContinuityAtEmpty public

record ProjectiveMeasureExtensionAuthority
    (Index Event Mass Observable Scalar : Set) : Set₂ where
  field
    SigmaMeasure : Set
    IsCountablyAdditive : SigmaMeasure → Set

    extendProjective :
      (projective :
        R538.ProjectivePositiveCylinderProbability Index Event) →
      ProjectiveContinuityAtEmpty projective →
      SigmaMeasure

    extensionCountablyAdditive :
      ∀ projective continuity →
      IsCountablyAdditive
        (extendProjective projective continuity)

    integrate :
      SigmaMeasure → Observable → Scalar

    -- Standard extension compatibility with every finite cylinder level.
    indicatorAt : Index → Event → Observable
    massAsScalar : Mass → Scalar

    extensionAgreesWithCylinderMass :
      ∀ projective continuity index event →
      integrate
        (extendProjective projective continuity)
        (indicatorAt index event)
      ≡
      massAsScalar
        (R495.mass
          (R538.premeasure
            (R538.levelProbability projective index))
          event)

open ProjectiveMeasureExtensionAuthority public

record ProjectiveCylinderRepresentationInputs
    (Index Event Mass Observable Scalar : Set)
    (sourceExpectation : Observable → Scalar)
    : Set₂ where
  field
    projective :
      R538.ProjectivePositiveCylinderProbability Index Event

    continuity :
      ProjectiveContinuityAtEmpty projective

    extensionAuthority :
      ProjectiveMeasureExtensionAuthority
        Index Event Mass Observable Scalar

    -- Genuine YM/source identification on the observable class consumed by
    -- the Clay construction.
    sourceExpectationIsExtendedIntegral :
      ∀ observable →
      sourceExpectation observable
      ≡
      integrate extensionAuthority
        (extendProjective extensionAuthority
          projective continuity)
        observable

open ProjectiveCylinderRepresentationInputs public

asSourceLimitRepresentation :
  ∀ {Index Event Mass Observable}
    {sourceExpectation : Observable → ℝ} →
  ProjectiveCylinderRepresentationInputs
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
          extendProjective
            (extensionAuthority inputs)
            (projective inputs)
            (continuity inputs)
      ; R476.RepresentedContinuum.integrate =
          integrate (extensionAuthority inputs)
      ; R476.RepresentedContinuum.countablyAdditive =
          extensionCountablyAdditive
            (extensionAuthority inputs)
            (projective inputs)
            (continuity inputs)
      }
  ; R476.SourceLimitRepresentation.sourceLimitIsIntegral =
      sourceExpectationIsExtendedIntegral inputs
  }

selectedSingleCutoffExtensionIsPreferredContinuumRoute : Bool
selectedSingleCutoffExtensionIsPreferredContinuumRoute = false

wholeProjectiveFamilyRequiredForPreferredExtension : Bool
wholeProjectiveFamilyRequiredForPreferredExtension = true

round534ProjectiveRepresentationCompilerLevel : ProofLevel
round534ProjectiveRepresentationCompilerLevel = machineChecked

round534ProjectiveExtensionAuthorityLevel : ProofLevel
round534ProjectiveExtensionAuthorityLevel = standardImported

literalRound534ProjectiveContinuityAtEmptyLevel : ProofLevel
literalRound534ProjectiveContinuityAtEmptyLevel = conditional

literalRound534SourceExpectationIntegralIdentificationLevel : ProofLevel
literalRound534SourceExpectationIntegralIdentificationLevel = conditional
