module DASHI.Moonshine.Y443JMDConcretePairPowerCompilerExact where

------------------------------------------------------------------------
-- SOURCE-EXACT JMD TWO-GENERATOR INITIAL SEGMENT
-- x0..x11 / three Coxeter paths directly from original Lean source:
-- AxiomMath/CFSGCorollary/Sporadic/Monster/Y443.lean,
-- y443_paths / closure_pair_eq_top_of_paths.
--
-- Proved here:
-- * Literal u,v,beta,w (not unconstrained formal labels).
-- * w is explicitly the u/v word u^-1 v, by group identities.
-- * Given the genuine path theorem premises x4=w^5, beta=w^6,
--   construct actual words representing both group elements.
--
-- Do not equate source-written conditional compiler with Agda replay
-- of Lean's path-Coxeter-element theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDTracePowerExact as Trace
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as Source

record JMDConcretePowers
  {G : Set}
  (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G) : Set where
  field
    -- The Lean path theorem proves these in Y443, using that x4
    -- commutes with beta, x4^2=1 and beta^5=1.
    sourceX4Fifth :
      nodes Source.x4 ≡
      Trace.groupPower gi (Source.wElement gi nodes) 5
    sourceBetaSixth :
      Source.betaElement gi nodes ≡
      Trace.groupPower gi (Source.wElement gi nodes) 6

open JMDConcretePowers public

concreteTrace :
  ∀ {G} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G) →
  JMDConcretePowers gi nodes →
  Trace.JMDStepsTwoToFour
    gi (Source.uElement gi nodes) (Source.vElement gi nodes)
concreteTrace gi nodes powers = record
  { Trace.w = Source.wElement gi nodes
  ; Trace.x4 = nodes Source.x4
  ; Trace.beta = Source.betaElement gi nodes
  ; Trace.wIsProduct = Source.wIsX4Beta gi nodes
  ; Trace.wFromPair = Source.jmdWFromPair gi nodes
  ; Trace.x4IsFifthPower = sourceX4Fifth powers
  ; Trace.betaIsSixthPower = sourceBetaSixth powers
  }

sourceX4Word :
  ∀ {G} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G) →
  (powers : JMDConcretePowers gi nodes) →
  Pair.RepresentedByPair gi
    (Source.uElement gi nodes) (Source.vElement gi nodes)
    (nodes Source.x4)
sourceX4Word gi nodes powers =
  Trace.traceStepThreeX4 gi
    (Source.uElement gi nodes) (Source.vElement gi nodes)
    (concreteTrace gi nodes powers)

sourceBetaWord :
  ∀ {G} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G) →
  (powers : JMDConcretePowers gi nodes) →
  Pair.RepresentedByPair gi
    (Source.uElement gi nodes) (Source.vElement gi nodes)
    (Source.betaElement gi nodes)
sourceBetaWord gi nodes powers =
  Trace.traceStepFourBeta gi
    (Source.uElement gi nodes) (Source.vElement gi nodes)
    (concreteTrace gi nodes powers)
