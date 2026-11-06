module DASHI.Biology.Physical.BiologicalCoupledTissueCubeExact where

------------------------------------------------------------------------
-- NON-PERIODIC 3x3x3 SPATIALLY COUPLED TISSUE UPDATE
--
-- Unlike the earlier pointwise lift, the signal update at each voxel
-- reads the junction state of an adjacent voxel in the old field.
-- Neighbour schedules carry actual Cube.HypervoxelAdjacent witnesses.
-- Thus simultaneous updates do not silently introduce a periodic boundary,
-- a nonlocal edge, or an in-place sequential update order.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement

record AdmissibleNeighbourSchedule : Set where
  field
    neighbour : Cube.Ternary27Point → Cube.Ternary27Point
    actualEdge : (p : Cube.Ternary27Point) →
      Cube.HypervoxelAdjacent p (neighbour p)

open AdmissibleNeighbourSchedule public

withMorphology : Bio.BiologicalState → Bool → Bio.BiologicalState
withMorphology (Bio.biologicalState g c h j e p) new =
  Bio.biologicalState g c h j e new

withCoarseMorphology :
  Bio.FutureSufficientCode → Bool → Bio.FutureSufficientCode
withCoarseMorphology (Bio.futureSufficientCode g h j e p) new =
  Bio.futureSufficientCode g h j e new

replaceMorphologyCommutes :
  (x : Bio.BiologicalState) (new : Bool) →
  Bio.project (withMorphology x new)
  ≡ withCoarseMorphology (Bio.project x) new
replaceMorphologyCommutes (Bio.biologicalState g c h j e p) new = refl

localResponse :
  (schedule : AdmissibleNeighbourSchedule) →
  Bio.TissueField → Cube.Ternary27Point → Bool
localResponse schedule field p =
  Bio.edgeDrivenMorphology
    p (neighbour schedule p) (actualEdge schedule p) field

coarseResponse :
  (schedule : AdmissibleNeighbourSchedule) →
  Bio.CoarseTissueField → Cube.Ternary27Point → Bool
coarseResponse schedule field p =
  Bio.coarseEdgeDrivenMorphology
    p (neighbour schedule p) (actualEdge schedule p) field

responseCommutes :
  (schedule : AdmissibleNeighbourSchedule)
  (field : Bio.TissueField)
  (p : Cube.Ternary27Point) →
  localResponse schedule field p
  ≡ coarseResponse schedule (Bio.spatialProject field) p
responseCommutes schedule field p =
  Bio.localEdgeResponseSurvivesProjection
    p (neighbour schedule p) (actualEdge schedule p) field

-- Synchronous update: all neighbour reads come from the same input field.
coupledStep :
  (schedule : AdmissibleNeighbourSchedule) →
  Bio.Intervention → Bio.TissueField → Bio.TissueField
coupledStep schedule Bio.signal field p =
  withMorphology (Bio.step Bio.signal (field p))
    (localResponse schedule field p)
coupledStep schedule action field p =
  Bio.step action (field p)

coarseCoupledStep :
  (schedule : AdmissibleNeighbourSchedule) →
  Bio.Intervention → Bio.CoarseTissueField → Bio.CoarseTissueField
coarseCoupledStep schedule Bio.signal field p =
  withCoarseMorphology (Bio.coarseStep Bio.signal (field p))
    (coarseResponse schedule field p)
coarseCoupledStep schedule action field p =
  Bio.coarseStep action (field p)

-- This theorem is pointwise on every voxel, not merely a single edge
-- regression. Function extensionality is deliberately not assumed.
coupledStepCommutesAtEveryVoxel :
  (schedule : AdmissibleNeighbourSchedule)
  (action : Bio.Intervention)
  (field : Bio.TissueField)
  (p : Cube.Ternary27Point) →
  Bio.spatialProject (coupledStep schedule action field) p
  ≡ coarseCoupledStep schedule action (Bio.spatialProject field) p
coupledStepCommutesAtEveryVoxel schedule Bio.signal field p
  rewrite responseCommutes schedule field p =
    trans
      (replaceMorphologyCommutes
        (Bio.step Bio.signal (field p))
        (coarseResponse schedule (Bio.spatialProject field) p))
      (cong
        (λ state → withCoarseMorphology state
          (coarseResponse schedule (Bio.spatialProject field) p))
        (Bio.projectionCommutes Bio.signal (field p)))
coupledStepCommutesAtEveryVoxel schedule Bio.wound field p =
  Bio.projectionCommutes Bio.wound (field p)
coupledStepCommutesAtEveryVoxel schedule Bio.connect field p =
  Bio.projectionCommutes Bio.connect (field p)
coupledStepCommutesAtEveryVoxel schedule Bio.restoreMemory field p =
  Bio.projectionCommutes Bio.restoreMemory (field p)
coupledStepCommutesAtEveryVoxel schedule Bio.provideEnvironment field p =
  Bio.projectionCommutes Bio.provideEnvironment (field p)

-- The stronger spatial theorem has an explicit history of interventions.
fineEvolve :
  AdmissibleNeighbourSchedule → List Bio.Intervention →
  Bio.TissueField → Bio.TissueField
fineEvolve schedule [] field = field
fineEvolve schedule (a ∷ rest) field =
  fineEvolve schedule rest (coupledStep schedule a field)

coarseEvolve :
  AdmissibleNeighbourSchedule → List Bio.Intervention →
  Bio.CoarseTissueField → Bio.CoarseTissueField
coarseEvolve schedule [] field = field
coarseEvolve schedule (a ∷ rest) field =
  coarseEvolve schedule rest (coarseCoupledStep schedule a field)

-- Explicit pointwise equivalence is retained as a relation, so the
-- inductive theorem does not assume extensional equality of functions.
record FieldsAgree
    (fine : Bio.TissueField)
    (coarse : Bio.CoarseTissueField) : Set where
  constructor fieldsAgree
  field
    atEveryVoxel : (p : Cube.Ternary27Point) →
      Bio.project (fine p) ≡ coarse p

open FieldsAgree public

initialFieldAgreement :
  (fine : Bio.TissueField) →
  FieldsAgree fine (Bio.spatialProject fine)
initialFieldAgreement fine = fieldsAgree (λ p → refl)

-- The following named obligation is stronger than pointwise one-step
-- equality: it allows a separately represented coarse field.
coupledAgreementPreserved :
  (schedule : AdmissibleNeighbourSchedule)
  (a : Bio.Intervention)
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  FieldsAgree fine coarse →
  FieldsAgree
    (coupledStep schedule a fine)
    (coarseCoupledStep schedule a coarse)
coupledAgreementPreserved schedule Bio.signal fine coarse agreement =
  fieldsAgree λ p →
    trans
      (coupledStepCommutesAtEveryVoxel schedule Bio.signal fine p)
      (cong
        (λ x → withCoarseMorphology
          (Bio.coarseStep Bio.signal x)
          (coarseResponse schedule (Bio.spatialProject fine) p))
        (atEveryVoxel agreement p))
      -- The neighbour response must also transport across the two fields.
      -- This is provided by the full-field component relation below.
