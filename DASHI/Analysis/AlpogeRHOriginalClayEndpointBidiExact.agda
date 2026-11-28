module DASHI.Analysis.AlpogeRHOriginalClayEndpointBidiExact where

-- Same-original RH endpoint transport: ANALYTIC SUBSTRATE <-> the existing
-- RiemannZetaProgramBoundary.RiemannHypothesisWitness (Clay-facing witness).
-- This file does not postulate RH, import Lean bytecode or forge an external
-- proof. Actual same-function/zero/critical-line transport must be supplied.
-- The external source proof is admitted through AlpogeGRHGeometricTransportExact.
--
-- Steelman/BIDI/reverse solve: reuse both original endpoint definitions
-- rather than inventing a third critical-line proposition.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Analysis.RiemannAnalyticSubstrate
import DASHI.Analysis.RiemannZetaProgramBoundary as Clay
import DASHI.Analysis.AlpogeGRHGeometricTransportExact as External

private
  module A = AnalyticSubstrate
  module C = ComplexAnalyticCarrier
  module Z = CompletedRiemannZeta
  module S = Clay.CriticalStripWitness
  module W = Clay.RiemannHypothesisWitness

-- Every direction is a proof-relevant source-object identification.
-- Even an exact set bijection is insufficient without both predicates.
record OriginalRHClayEndpointWeld
    (analytic : AnalyticSubstrate)
    (strip : Clay.CriticalStripWitness) : Set₁ where
  field
    toStrip : C.Complex (A.carrier analytic) → S.Complex strip
    fromStrip : S.Complex strip → C.Complex (A.carrier analytic)

    analyticZeroToStrip :
      (s : C.Complex (A.carrier analytic)) →
      Z.nontrivialZero (A.completed analytic) s →
      S.nontrivialZero strip (toStrip s)

    stripZeroToAnalytic :
      (s : S.Complex strip) →
      S.nontrivialZero strip s →
      Z.nontrivialZero (A.completed analytic) (fromStrip s)

    stripLineToAnalytic :
      (s : C.Complex (A.carrier analytic)) →
      S.criticalLine strip (toStrip s) →
      Z.criticalLine (A.completed analytic) s

    analyticLineToStrip :
      (s : S.Complex strip) →
      Z.criticalLine (A.completed analytic) (fromStrip s) →
      S.criticalLine strip s

-- Forward: the original analytic RH pays the ORIGINAL Clay-facing strip.
analyticRHToClayWitness :
  (analytic : AnalyticSubstrate)
  (strip : Clay.CriticalStripWitness) →
  OriginalRHClayEndpointWeld analytic strip →
  RiemannHypothesisFor analytic →
  Clay.RiemannHypothesisWitness
analyticRHToClayWitness analytic strip weld h =
  record
    { strip = strip
    ; everyNontrivialZeroOnCriticalLine = λ s z →
        OriginalRHClayEndpointWeld.analyticLineToStrip weld s
          (h (OriginalRHClayEndpointWeld.fromStrip weld s)
            (OriginalRHClayEndpointWeld.stripZeroToAnalytic weld s z))
    }

-- Reverse: the existing Clay witness gives back RH on the SAME analytic
-- substrate only when the original predicate reflection is actually paid.
clayWitnessToAnalyticRH :
  (analytic : AnalyticSubstrate)
  (strip : Clay.CriticalStripWitness) →
  OriginalRHClayEndpointWeld analytic strip →
  ((s : S.Complex strip) →
    S.nontrivialZero strip s → S.criticalLine strip s) →
  RiemannHypothesisFor analytic
clayWitnessToAnalyticRH analytic strip weld h s z =
  OriginalRHClayEndpointWeld.stripLineToAnalytic weld s
    (h (OriginalRHClayEndpointWeld.toStrip weld s)
      (OriginalRHClayEndpointWeld.analyticZeroToStrip weld s z))

-- Source external Lean proof → original analytic RH → original Clay witness.
-- A closed inhabitant STILL requires real external proof admission and
-- the actual same-object analytic/strip predicate weld.
alpogeExternalToOriginalClayWitness :
  (analytic : AnalyticSubstrate)
  (strip : Clay.CriticalStripWitness) →
  External.ExternalRHGeometricTransport analytic →
  OriginalRHClayEndpointWeld analytic strip →
  Clay.RiemannHypothesisWitness
alpogeExternalToOriginalClayWitness analytic strip ext weld =
  analyticRHToClayWitness analytic strip weld
    (External.externalRHImpliesDashiRH analytic ext)


-- COMPLETE original Clay-record reverse direction. The pre-existing
-- clayWitnessToAnalyticRH demanded the witness's predicate function
-- separately. Here consume the REAL original Clay witness projection:
-- no new strip, synthetic zeta, or replacement critical-line predicate.
--
-- This is an RH-only same-target weld. A Clay RH witness does NOT
-- establish GRH for every nontrivial Dirichlet character. That P0
-- authority must come from the original all-character external proof.
originalClayWitnessToAnalyticRH :
  (analytic : AnalyticSubstrate)
  (witness : Clay.RiemannHypothesisWitness) →
  OriginalRHClayEndpointWeld analytic (W.strip witness) →
  RiemannHypothesisFor analytic
originalClayWitnessToAnalyticRH analytic witness weld =
  clayWitnessToAnalyticRH analytic (W.strip witness) weld
    (W.everyNontrivialZeroOnCriticalLine witness)

-- Existing external theorem, once EXACT original proof/zero carriers are
-- admitted, already projects to both analytical RH and original Clay RH.
-- This is the literal typed reverse consumer for an original Clay record;
-- it is NOT a reverse implication ordinary RH -> all-character GRH.
originalClayWitnessToSameOriginalRH :
  (analytic : AnalyticSubstrate)
  (strip : Clay.CriticalStripWitness)
  (weld : OriginalRHClayEndpointWeld analytic strip)
  (witness : Clay.RiemannHypothesisWitness) →
  W.strip witness ≡ strip →
  RiemannHypothesisFor analytic
originalClayWitnessToSameOriginalRH analytic strip weld witness refl =
  originalClayWitnessToAnalyticRH analytic witness weld


-- Canonical same-object strip on the original analytic carrier. The only
-- extra semantic datum is the ACTUAL real half and its critical-line law.
-- No rational approximation or coercion of arbitrary real coordinates.
analyticOwnedStrip :
  (analytic : AnalyticSubstrate) →
  (half : C.Real (A.carrier analytic)) →
  ((s : C.Complex (A.carrier analytic)) →
    Z.criticalLine (A.completed analytic) s →
    C.realPart (A.carrier analytic) s ≡ half) →
  Clay.CriticalStripWitness
analyticOwnedStrip analytic half lineMeansHalf =
  record
    { Complex = C.Complex (A.carrier analytic)
    ; zeta = C.apply (A.carrier analytic) (Z.zeta (A.completed analytic))
    ; zero = C.zeroC (A.carrier analytic)
    ; Real = C.Real (A.carrier analytic)
    ; realPart = C.realPart (A.carrier analytic)
    ; oneHalf = half
    ; nontrivialZero = Z.nontrivialZero (A.completed analytic)
    ; criticalLine = Z.criticalLine (A.completed analytic)
    ; criticalLineMeansHalf = lineMeansHalf
    }

analyticOwnedStripWeld :
  (analytic : AnalyticSubstrate) →
  (half : C.Real (A.carrier analytic)) →
  (lineMeansHalf : (s : C.Complex (A.carrier analytic)) →
    Z.criticalLine (A.completed analytic) s →
    C.realPart (A.carrier analytic) s ≡ half) →
  OriginalRHClayEndpointWeld analytic (analyticOwnedStrip analytic half lineMeansHalf)
analyticOwnedStripWeld analytic half lineMeansHalf =
  record
    { toStrip = λ s → s
    ; fromStrip = λ s → s
    ; analyticZeroToStrip = λ s z → z
    ; stripZeroToAnalytic = λ s z → z
    ; stripLineToAnalytic = λ s h → h
    ; analyticLineToStrip = λ s h → h
    }

-- Ingress still requires the actual external transport, not a receipt string.
externalToOwnedClayWitness :
  (analytic : AnalyticSubstrate) →
  (half : C.Real (A.carrier analytic)) →
  (lineMeansHalf : (s : C.Complex (A.carrier analytic)) →
    Z.criticalLine (A.completed analytic) s →
    C.realPart (A.carrier analytic) s ≡ half) →
  External.ExternalRHGeometricTransport analytic →
  Clay.RiemannHypothesisWitness
externalToOwnedClayWitness analytic half lineMeansHalf ext =
  alpogeExternalToOriginalClayWitness analytic
    (analyticOwnedStrip analytic half lineMeansHalf) ext
    (analyticOwnedStripWeld analytic half lineMeansHalf)

ownedClayWitnessRecoversAnalytic :
  (analytic : AnalyticSubstrate) →
  (half : C.Real (A.carrier analytic)) →
  (lineMeansHalf : (s : C.Complex (A.carrier analytic)) →
    Z.criticalLine (A.completed analytic) s →
    C.realPart (A.carrier analytic) s ≡ half) →
  (witness : Clay.RiemannHypothesisWitness) →
  W.strip witness ≡ analyticOwnedStrip analytic half lineMeansHalf →
  RiemannHypothesisFor analytic
ownedClayWitnessRecoversAnalytic analytic half lineMeansHalf witness same =
  originalClayWitnessToSameOriginalRH analytic
    (analyticOwnedStrip analytic half lineMeansHalf)
    (analyticOwnedStripWeld analytic half lineMeansHalf) witness same
