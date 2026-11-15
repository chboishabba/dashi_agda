{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechLayerErrorTransportExact where

-- F07: exact CONDITIONAL compositional error bound for a finite sequence
-- of teacher/student steps. Reuse the established metric/parallelogram
-- programme in DASHI/Geometry/* rather than assuming a numeric constant.
--
-- The user-observed layer-1 CE collapse motivates this result, but this
-- theorem DOES NOT certify the actual PyTorch layers as Lipschitz with
-- any particular coefficient, and does not derive cross-entropy bounds.
-- Numeric CE refinement is the distinct F08 obligation.
--
-- Original Leech-LILA: Anatolii Kornienko,
-- DOI 10.5281/zenodo.18784424.

open import Agda.Builtin.List using (List; []; _∷_)

record ErrorCalculus (State Bound : Set) : Set₁ where
  field
    distance : State → State → Bound
    _≼_ : Bound → Bound → Set
    _⊕_ : Bound → Bound → Bound
    scale : Bound → Bound → Bound

    orderTrans : ∀ {a b c : Bound} → _≼_ a b → _≼_ b c → _≼_ a c
    addMonoLeft : ∀ {a b : Bound} (c : Bound) →
      _≼_ a b → _≼_ (_⊕_ a c) (_⊕_ b c)
    scaleMono : (constant : Bound) → ∀ {a b : Bound} →
      _≼_ a b → _≼_ (scale constant a) (scale constant b)
    triangle : (a b c : State) →
      _≼_ (distance a c) (_⊕_ (distance a b) (distance b c))

open ErrorCalculus public

record ErrorLayer
       (State Bound : Set)
       (calc : ErrorCalculus State Bound) : Set where
  field
    teacher : State → State
    student : State → State
    lip : Bound
    lipBound : ∀ (s t : State) →
      _≼_ calc (distance calc (student s) (student t))
                (scale calc lip (distance calc s t))

open ErrorLayer public

oneStepErrorBound :
  ∀ {State Bound : Set}
    (calc : ErrorCalculus State Bound)
    (layer : ErrorLayer State Bound calc)
    (studentState teacherState : State) →
  _≼_ calc
    (distance calc
      (student layer studentState)
      (teacher layer teacherState))
    (_⊕_ calc
      (scale calc (lip layer)
        (distance calc studentState teacherState))
      (distance calc
        (student layer teacherState)
        (teacher layer teacherState)))
oneStepErrorBound calc layer s t =
  orderTrans calc
    (triangle calc (student layer s) (student layer t)
                   (teacher layer t))
    (addMonoLeft calc
      (distance calc (student layer t) (teacher layer t))
      (lipBound layer s t))

runStudent :
  ∀ {State Bound : Set} {calc : ErrorCalculus State Bound} →
  List (ErrorLayer State Bound calc) → State → State
runStudent [] initial = initial
runStudent (layer ∷ later) initial =
  runStudent later (student layer initial)

runTeacher :
  ∀ {State Bound : Set} {calc : ErrorCalculus State Bound} →
  List (ErrorLayer State Bound calc) → State → State
runTeacher [] initial = initial
runTeacher (layer ∷ later) initial =
  runTeacher later (teacher layer initial)

-- Explicit finite telescoping recipe, based ONLY on actual teacher
-- intermediate states and declared layer-specific Lipschitz evidence.
teacherPathMajorant :
  ∀ {State Bound : Set}
    (calc : ErrorCalculus State Bound) →
  List (ErrorLayer State Bound calc) → State → Bound → Bound
teacherPathMajorant calc [] teacherState previous = previous
teacherPathMajorant calc (layer ∷ later) teacherState previous =
  teacherPathMajorant calc later (teacher layer teacherState)
    (_⊕_ calc
      (scale calc (lip layer) previous)
      (distance calc (student layer teacherState)
                     (teacher layer teacherState)))

traceErrorBound :
  ∀ {State Bound : Set}
    (calc : ErrorCalculus State Bound) →
  (layers : List (ErrorLayer State Bound calc)) →
  (studentState teacherState : State) (prior : Bound) →
  _≼_ calc (distance calc studentState teacherState) prior →
  _≼_ calc
    (distance calc
      (runStudent layers studentState)
      (runTeacher layers teacherState))
    (teacherPathMajorant calc layers teacherState prior)
traceErrorBound calc [] s t prior initialBound = initialBound
traceErrorBound calc (layer ∷ later) s t prior initialBound =
  traceErrorBound calc later
    (student layer s) (teacher layer t)
    (_⊕_ calc
      (scale calc (lip layer) prior)
      (distance calc (student layer t) (teacher layer t)))
    (orderTrans calc
      (oneStepErrorBound calc layer s t)
      (addMonoLeft calc
        (distance calc (student layer t) (teacher layer t))
        (scaleMono calc (lip layer) initialBound)))

-- Neither a finite calibration sample nor a 240-root router gives the
-- concrete lipBound witness automatically. The exact torch nonlinear
-- FFN, normalization, sparse top-k discontinuities and historical
-- transitions must be accounted for before using this inequality as
-- a useful numeric CE certificate.
