module DASHI.Core.QueryIndexedProjectionSpineAdapterRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Indexed
import DASHI.Core.CoarseFineFabricCalculusExact as Coarse
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.QueryIndexedProjectionSpineAdapterExact as Adapter

data QueryKey : Set where hiddenQuery : QueryKey

record HiddenState : Set where
  constructor hiddenState
  field visible hidden : Bool
open HiddenState public

hiddenProject : HiddenState → Bool
hiddenProject = visible

hiddenAnswer : QueryKey → HiddenState → Bool
hiddenAnswer hiddenQuery = hidden

hiddenSemantics : Indexed.QuerySemantics HiddenState QueryKey Bool
hiddenSemantics = Indexed.querySemantics hiddenAnswer

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

queryDefect : Indexed.QueryAdequacyDefect hiddenProject hiddenSemantics hiddenQuery
queryDefect = Indexed.queryAdequacyDefect
  (hiddenState false true)
  (hiddenState false false)
  refl
  trueNotFalse

canonicalCollision : Coarse.ProjectionCollision hiddenProject (Indexed.answer hiddenSemantics hiddenQuery)
canonicalCollision = Adapter.queryAdequacyDefectToProjectionCollision queryDefect

queryDefectRoundTrip : Indexed.QueryAdequacyDefect hiddenProject hiddenSemantics hiddenQuery
queryDefectRoundTrip = Adapter.projectionCollisionToQueryAdequacyDefect canonicalCollision

repairMustSeparateSelectedQuery :
  ∀ {Refinement : Set}
    (refine : HiddenState → Refinement) →
  Repair.RefinementRepairs hiddenProject refine (Indexed.answer hiddenSemantics hiddenQuery) →
  refine (hiddenState false true) ≡ refine (hiddenState false false) →
  ⊥
repairMustSeparateSelectedQuery refine =
  Adapter.queryAdequacyDefectRepairRequiresSeparation queryDefect
