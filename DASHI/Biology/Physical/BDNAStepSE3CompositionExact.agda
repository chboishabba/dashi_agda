module DASHI.Biology.Physical.BDNAStepSE3CompositionExact where

------------------------------------------------------------------------
-- SOURCE-FACING GEOMETRY
-- Wilma K. Olson, Manju Bansal, Stephen K. Burley, Richard E. Dickerson,
-- Mark Gerstein, Stephen C. Harvey, Udo Heinemann, Xiang-Jun Lu,
-- Stephen Neidle, Zippora Shakked, Helen Sklenar, Masami Suzuki,
-- Charon Tung, Eric Westhof and Clive Wolberger,
-- "A standard reference frame for the description of nucleic acid base-pair
-- geometry", Journal of Molecular Biology 313 (2001), 229--237.
-- DOI: 10.1006/jmbi.2001.4987.
--
-- DASHI CONTRIBUTION
-- Sequence/environment-dependent six-parameter base-pair steps are realized in
-- an arbitrary exact rigid-motion semidirect-product model and accumulated by
-- group composition.  Thus the earlier Phase4 carrier is no longer the owner of
-- physical DNA frame composition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Biology.Physical.BDNACalibratedHelicalGeometryExact as B
import DASHI.Geometry.RigidMotionSemidirectProductExact as SE3

record BDNARigidStepCalibration (model : SE3.RigidMotionModel) : Set₁ where
  field
    stepLaw : B.SequenceDependentStepLaw
    realizeStep : B.BasePairStep6 → SE3.RigidMotion model

open BDNARigidStepCalibration public

realizeDinucleotide :
  ∀ {model} →
  BDNARigidStepCalibration model →
  B.HelixEnvironment → DNA.DNABase → DNA.DNABase →
  SE3.RigidMotion model
realizeDinucleotide calibration env left right =
  realizeStep calibration
    (B.stepFor (stepLaw calibration) env left right)

------------------------------------------------------------------------
-- Ordered frame product along a sequence tail.
------------------------------------------------------------------------

accumulateFrames :
  ∀ {model} →
  (calibration : BDNARigidStepCalibration model) →
  B.HelixEnvironment →
  DNA.DNABase → List DNA.DNABase →
  SE3.RigidMotion model
accumulateFrames {model} calibration env current [] = SE3.identity model
accumulateFrames {model} calibration env current (next ∷ rest) =
  SE3.compose model
    (realizeDinucleotide calibration env current next)
    (accumulateFrames calibration env next rest)

emptyTailIsIdentity :
  ∀ {model}
    (calibration : BDNARigidStepCalibration model)
    (env : B.HelixEnvironment) (base : DNA.DNABase) →
  accumulateFrames calibration env base [] ≡ SE3.identity model
emptyTailIsIdentity calibration env base = refl

singleStepIsRealizedDinucleotide :
  ∀ {model}
    (calibration : BDNARigidStepCalibration model)
    (env : B.HelixEnvironment) (left right : DNA.DNABase) →
  accumulateFrames calibration env left (right ∷ [])
  ≡ realizeDinucleotide calibration env left right
singleStepIsRealizedDinucleotide {model} calibration env left right =
  SE3.rightIdentity model (realizeDinucleotide calibration env left right)

------------------------------------------------------------------------
-- Rebracketing of a three-transform frame product is licensed by the actual
-- semidirect-product associativity theorem, rather than by a feed-forward
-- sequence metaphor.
------------------------------------------------------------------------

threeFrameReassociation :
  ∀ {model} (a b c : SE3.RigidMotion model) →
  SE3.compose model (SE3.compose model a b) c
  ≡ SE3.compose model a (SE3.compose model b c)
threeFrameReassociation {model} = SE3.associative model

record BDNASE3AuthorityBoundary : Set where
  field
    sixParameterSlotsAreAlreadyEmpiricalSE3Matrices : Bool
    sixParameterSlotsAreAlreadyEmpiricalSE3MatricesIsFalse :
      sixParameterSlotsAreAlreadyEmpiricalSE3Matrices ≡ false
    sequenceSymbolIsPhysicalFrame : Bool
    sequenceSymbolIsPhysicalFrameIsFalse : sequenceSymbolIsPhysicalFrame ≡ false

canonicalBDNASE3AuthorityBoundary : BDNASE3AuthorityBoundary
canonicalBDNASE3AuthorityBoundary = record
  { sixParameterSlotsAreAlreadyEmpiricalSE3Matrices = false
  ; sixParameterSlotsAreAlreadyEmpiricalSE3MatricesIsFalse = refl
  ; sequenceSymbolIsPhysicalFrame = false
  ; sequenceSymbolIsPhysicalFrameIsFalse = refl
  }
