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

-- Published Osterwalder--Seiler / Menotti--Pelissetto RP route,
-- attached to the same native finite Wilson word Gram.
import DASHI.Physics.Foundations.TSVFOriginalR445PublishedWilsonRPWordWeldExact
  as OriginalR445PublishedWordRP

-- Source-selected ORIGINAL TSVF forward-ket observer -> physical
-- Wilson/R445 all-word Gram. The complex observer's real readout is
-- calibrated explicitly, not equated to Wilson ℝ by definitional fiat.
-- Source-facing cylinder Born equality/product/adjoint are physical
-- producer obligations, not a second assumed Gram.
import DASHI.Physics.Foundations.TSVFOriginalForwardToNativeWilsonWordGramExact
  as OriginalObserverWilsonGram

-- Original same-instrument forward-ket measured Wilson/R445 *finite cyclic
-- real-span* equality and two-way Gram-observational quotient transport.
import DASHI.Physics.Foundations.TSVFOriginalMeasuredFiniteSpanR445Exact
  as OriginalObserverNativeFiniteSpan
