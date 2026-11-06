module DASHI.Unified.TSFVPhysicalR445AllWordRegression where

-- Separate original-Wilson physical/axiomatic regression.
-- The existing DASHI.Unified.TSFVUnifiedRegression uses --safe and
-- must not import this non-safe RealAnalysisAxioms-dependent owner.
-- Run with parallel_checker without --safe and independently audit
-- transitive axioms/physical identification.
import DASHI.Physics.Foundations.TSVFOriginalR445AllWordActualPushforwardExact
  as OriginalR445AllWord

-- Original native Wilson reflected all-word Gram, same physical finite Gibbs.
import DASHI.Physics.Foundations.TSVFOriginalR445ReflectedAllWordGramExact
  as OriginalR445ReflectedGram
