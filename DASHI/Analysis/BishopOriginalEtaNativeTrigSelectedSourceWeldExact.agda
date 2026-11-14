module DASHI.Analysis.BishopOriginalEtaNativeTrigSelectedSourceWeldExact where

------------------------------------------------------------------------
-- ACTUAL ROUND11 ETA / ZETA FINITE SOURCE FROM NATIVE REAL EXP ADD.
--
-- Provenance: Bishop/Bridges (1985); Zachary Murray (2022),
-- arXiv:2205.08354; DASHI original Round11 eta source,
-- BishopExponentialCauchyProductExact and native setoid expC.
--
-- This new SAME-SOURCE consumer composes the actual existing finite
-- eta identity from BishopOriginalEtaDyadicSourceLawReductionExact
-- with the new original native expC addition algebra:
--
--   existing real exp-add + native cosine-add + native sine-add
--     -> exact original Bishop expC addition
--     -> dyadic a_s(2k+1) = a_s(1) a_s(k)
--     -> original Round11 finite eta/zeta identity for every n.
--
-- Uninhabited analytical leaves are explicit parameters, not a new
-- oracle/postulate. Original Nat-log law and two true trigonometric
-- addition laws remain. Uniform eta convergence, RH, Agda 2.9
-- acceptance and original nonzero divisor arguments remain OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as Analytic
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Analysis.BishopOriginalEtaPairBlockTelescopingExact as Shifted
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopOriginalEtaDyadicSourceLawReductionExact as Dyadic
import DASHI.Analysis.BishopOriginalNativeComplexExpAdditionFromTrigExact as Native
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

module OriginalRound11 (inputs : Round11.Round11BishopCutset) where

  private
    T = Route.round11MachinTranscendentals inputs
    L = Terms.sourceCanonicalNatLogCandidate

  module Selected = Eta.OriginalRound11DirichletEta inputs
  module Existing = Dyadic.OriginalRound11 inputs

  -- EXACT original finite all-cutoff source as already stated in
  -- Dyadic.OriginalRound11.originalRound11EtaZetaFiniteFromTwoLaws.
  -- This is a genuine theorem application, not a separately defined
  -- eta family, and has no full complex-exp-add premise.
  originalRound11FiniteEtaZetaFromNativeTrigAddition :
    (s : Analytic.BishopComplex) →
    Dyadic.OriginalDyadicNatLogLaw L →
    Native.OriginalCosineAddition T →
    Native.OriginalSineAddition T →
    (n : Nat) →
    Eta._≈C_
      (Analytic._+C_
        (Eta.originalEtaPrefix (Selected.sourceTerms s) n)
        (Analytic._+C_
          (Analytic._*C_ (Selected.sourceTerms s (suc zero))
            (Dirichlet.dirichletPartial (Selected.sourceTerms) s n))
          (Analytic._*C_ (Selected.sourceTerms s (suc zero))
            (Dirichlet.dirichletPartial (Selected.sourceTerms) s n))))
      (Dirichlet.dirichletPartial Selected.sourceTerms s (Eta.twice n))
  originalRound11FiniteEtaZetaFromNativeTrigAddition
    s logLaw cosAdd sinAdd n =
    Existing.originalRound11EtaZetaFiniteFromTwoLaws
      s logLaw
      (Native.originalBishopAnalyticExpAddFromNativeRealExpAndTrig
        T cosAdd sinAdd)
      n


  -- Actual ALL n,m original Round11 selected finite eta shifted-tail
  -- identity, now directly consumed on the SAME source term family.
  -- This pays the summation-by-parts indexing precursor, not the
  -- missing analytic derivative, FTC or uniform Cauchy estimate.
  module OriginalShiftedTail = Shifted.OriginalRound11 inputs

  originalRound11EtaAllShiftedPairTailFromSelectedTerms :
    (s : Analytic.BishopComplex) (n m : Nat) →
    Eta._≈C_
      (Eta.originalEtaPrefix (Selected.sourceTerms s)
        (n + m))
      (Analytic._+C_
        (Eta.originalEtaPrefix (Selected.sourceTerms s) n)
        (Shifted.originalShiftedEtaPairs
          (Selected.sourceTerms s) n m))
  originalRound11EtaAllShiftedPairTailFromSelectedTerms s n m =
    OriginalShiftedTail.actualOriginalRound11ShiftedEtaTailExact s n m
