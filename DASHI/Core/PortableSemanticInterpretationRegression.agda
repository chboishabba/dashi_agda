module DASHI.Core.PortableSemanticInterpretationRegression where

open import DASHI.Core.Prelude
import DASHI.Core.PortableSemanticInterpretationExact as Portable

problemSurfaceExists : Set₁
problemSurfaceExists = Portable.SemanticInterpretationProblem

refinementSurfaceExists :
  (problem : Portable.SemanticInterpretationProblem) →
  (backend : Portable.SemanticInterpretationProblem.Backend problem) →
  (syntax : Portable.SemanticInterpretationProblem.Syntax problem) →
  (query : Portable.SemanticInterpretationProblem.Query problem) →
  Set
refinementSurfaceExists problem backend syntax query =
  Portable.SemanticRefinement problem backend syntax query

boundarySurfaceExists : Portable.PortableSemanticInterpretationBoundary
boundarySurfaceExists = Portable.canonicalPortableSemanticInterpretationBoundary
