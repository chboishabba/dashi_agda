module DASHI.Core.ProjectionConstructor where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC

----------------------------------------------------------------------
-- ProjectionConstructor: a method that produces an inhabitant of a
-- projection category.
--
-- A morphism π : A → B in 𝓟Γ can arise by many methods:
--
--   • learning (SGD, gradient descent)
--   • proof (theorem, derivation, type inference)
--   • analytic construction (McKay–Thompson, Hecke, Fourier)
--   • evolution (biological, genetic algorithm)
--   • engineering (human design, architecture search)
--   • measurement (assay, experiment)
--   • optimisation (calibration, minimisation)
--
-- The learner is therefore NOT fundamental.  It is one constructor
-- among many.  This unifies Prot2Prop (learning), Moonshine
-- (proof/construction), Translation (evolution/engineering), and
-- Hecke (analytic) under the same abstraction.
----------------------------------------------------------------------

record ProjectionConstructor (PCat : PC.ProjectionCategory) : Set₁ where
  open PC.ProjectionCategory PCat

  field
    -- The carrier that drives construction (training data, proof
    -- hypotheses, evolutionary pressure, engineering spec, ...)
    MethodCarrier : Set

    -- Construct a morphism A → B from the method carrier
    construct : ∀ {A B} → MethodCarrier → Hom A B

    -- Semantic classification: what kind of constructor?
    methodKind : String

open ProjectionConstructor public

----------------------------------------------------------------------
-- Canonical constructor (trivial)
----------------------------------------------------------------------

canonicalProjectionConstructor : ProjectionConstructor PC.canonicalProjectionCategory
canonicalProjectionConstructor = record
  { MethodCarrier = ⊤
  ; construct     = λ _ → tt
  ; methodKind    = "trivial"
  }

----------------------------------------------------------------------
-- Constructor instances
----------------------------------------------------------------------

-- Learning constructor
record LearningConstructor (PCat : PC.ProjectionCategory) : Set₁ where
  field
    projectionConstructor : ProjectionConstructor PCat
    lossSurface           : Set
    learningReading       : String

-- Proof constructor
record ProofConstructor (PCat : PC.ProjectionCategory) : Set₁ where
  field
    projectionConstructor : ProjectionConstructor PCat
    theoremStatement      : String
    proofReading          : String

-- Analytic constructor
record AnalyticConstructor (PCat : PC.ProjectionCategory) : Set₁ where
  field
    projectionConstructor : ProjectionConstructor PCat
    analyticDomain        : String
    analyticReading       : String
