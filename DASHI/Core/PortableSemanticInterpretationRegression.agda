module DASHI.Core.PortableSemanticInterpretationRegression where

open import DASHI.Core.Prelude
import DASHI.Core.PortableSemanticInterpretationExact as Portable

problemSurfaceExists : Set₁
problemSurfaceExists = Portable.SemanticInterpretationProblem

refinementSurfaceExists :
  (problem : Portable.SemanticInterpretationProblem) →
  (backend : Portable.Backend problem) →
  (syntax : Portable.Syntax problem) →
  (query : Portable.Query problem) →
  Set₁
refinementSurfaceExists problem backend syntax query =
  Portable.SemanticRefinement problem backend syntax query

boundarySurfaceExists : Portable.PortableSemanticInterpretationBoundary
boundarySurfaceExists = Portable.canonicalPortableSemanticInterpretationBoundary
