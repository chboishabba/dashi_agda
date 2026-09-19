{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2OPECoefficientCoordinateWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact as OPE

------------------------------------------------------------------------
-- LEVEL-2 D2: OPE COEFFICIENT / RG COORDINATE WELD
--
-- Global AF / beta-history dynamics are already owned elsewhere.  The OPE
-- coefficient recurrence theorem also already owns the exact induction:
--
--   same UV normalization
--   + same deterministic one-step mixing map
--       -> coefficient equality at every depth.
--
-- What was still only prose in the Level-2 frontier is the physical SAME-OBJECT
-- attachment saying that the literal OPE coefficient coordinate is really the
-- coefficient coordinate selected from the already-existing RG/composite state,
-- and that its one-step update is the same mixing coordinate.
--
-- This record deliberately contains NO new beta theorem and NO all-depth
-- equality field.  Those are upstream/downstream respectively.
------------------------------------------------------------------------

record OPECoefficientRGCoordinateWeld
    (Coefficient RGCoordinate PhysicalCoefficient : Set)
    (recurrence : OPE.CoefficientRGRecurrence Coefficient) : Set₁ where
  field
    rgCoordinateAt : Nat → RGCoordinate

    physicalCoefficientOfRGCoordinate :
      RGCoordinate → PhysicalCoefficient

    recurrenceCoefficientToPhysical :
      Coefficient → PhysicalCoefficient

    literalOPECoefficientAt :
      Nat → PhysicalCoefficient

    -- SAME physical coordinate: the literal OPE coefficient is the selected
    -- projection of the existing RG/composite coordinate at each depth.
    literalCoefficientIsRGProjection :
      ∀ depth →
      literalOPECoefficientAt depth
      ≡ physicalCoefficientOfRGCoordinate (rgCoordinateAt depth)

    -- SAME recurrence coordinate: the physical coefficient appearing in the
    -- recurrence theorem is the same projected coefficient used by the literal
    -- OPE semantics.
    recurrencePhysicalCoefficientIsLiteral :
      ∀ depth →
      recurrenceCoefficientToPhysical
        (OPE.physicalCoefficient recurrence depth)
      ≡ literalOPECoefficientAt depth

    -- The projection used at the terminal/literal layer is fixed once and for
    -- all; no independent all-depth comparison theorem is requested here.
    projection :
      OPE.MatchedCoefficientProjection
        {PhysicalCoefficient = PhysicalCoefficient} recurrence

    projectionIsDeclaredPhysicalProjection :
      OPE.project projection ≡ recurrenceCoefficientToPhysical

open OPECoefficientRGCoordinateWeld public

literalOPECoefficientMatchesProjectedAFAtEveryDepth :
  ∀ {Coefficient RGCoordinate PhysicalCoefficient}
    {recurrence : OPE.CoefficientRGRecurrence Coefficient} →
  (weld : OPECoefficientRGCoordinateWeld
    Coefficient RGCoordinate PhysicalCoefficient recurrence) →
  ∀ depth →
  literalOPECoefficientAt weld depth
  ≡ OPE.project (projection weld)
      (OPE.asymptoticFreedomCoefficient recurrence depth)
literalOPECoefficientMatchesProjectedAFAtEveryDepth
    {recurrence = recurrence} weld depth =
  let
    physicalToLiteral :
      OPE.project (projection weld)
        (OPE.physicalCoefficient recurrence depth)
      ≡ literalOPECoefficientAt weld depth
    physicalToLiteral =
      subst
        (λ selectedProjection →
          selectedProjection
            (OPE.physicalCoefficient recurrence depth)
          ≡ literalOPECoefficientAt weld depth)
        (projectionIsDeclaredPhysicalProjection weld)
        (recurrencePhysicalCoefficientIsLiteral weld depth)

    projectedMatch :
      OPE.project (projection weld)
        (OPE.physicalCoefficient recurrence depth)
      ≡
      OPE.project (projection weld)
        (OPE.asymptoticFreedomCoefficient recurrence depth)
    projectedMatch =
      OPE.projectedCoefficientMatch (projection weld) depth
  in
  trans
    (sym physicalToLiteral)
    projectedMatch

------------------------------------------------------------------------
-- Frontier classification.
------------------------------------------------------------------------

newGlobalAFTheoremRequiredByD2 : Bool
newGlobalAFTheoremRequiredByD2 = false

newGlobalAFTheoremRequiredByD2IsFalse :
  newGlobalAFTheoremRequiredByD2 ≡ false
newGlobalAFTheoremRequiredByD2IsFalse = refl

newAllDepthCoefficientTheoremRequiredByD2 : Bool
newAllDepthCoefficientTheoremRequiredByD2 = false

newAllDepthCoefficientTheoremRequiredByD2IsFalse :
  newAllDepthCoefficientTheoremRequiredByD2 ≡ false
newAllDepthCoefficientTheoremRequiredByD2IsFalse = refl

sameCoordinateAttachmentStillPhysical : Bool
sameCoordinateAttachmentStillPhysical = true

sameCoordinateAttachmentStillPhysicalIsTrue :
  sameCoordinateAttachmentStillPhysical ≡ true
sameCoordinateAttachmentStillPhysicalIsTrue = refl

coordinateWeldCompilerLevel : ProofLevel
coordinateWeldCompilerLevel = machineChecked

physicalCoordinateAttachmentLevel : ProofLevel
physicalCoordinateAttachmentLevel =
  OPE.physicalSameFamilyOPECoefficientOneStepAFIdentificationLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
