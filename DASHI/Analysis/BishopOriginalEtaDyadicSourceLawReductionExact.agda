module DASHI.Analysis.BishopOriginalEtaDyadicSourceLawReductionExact where

------------------------------------------------------------------------
-- ORIGINAL ETA P2 DYADIC SOURCE LAW: TWO ANALYTIC LEAVES -> FINITE WELD.
--
-- These are ORIGINAL Bishop analytic source terms:
--   a_s(k) = expC(-s * canonicalNatLog(k+1)).
-- The original even-positive source a_s(2*k+1) indexes 2*(k+1).
--
-- Unlike the generic OriginalDyadicSourceScale input, this module
-- derives that exact SCALE equality from exactly TWO interpretable
-- analytic laws, on the actual Riemann/Bishop carrier:
--
--   (L) L(2*(k+1)) ~= L(2) + L(k+1), the original logNat candidate;
--   (E) expC(z+w) ~= expC(z)*expC(w), the original Bishop expC.
--
-- The distributive step -s*(L2+Lk) = -s*L2 + -s*Lk
-- is proved coordinatewise using Bishop REAL distributivity.
-- Then P2's ORIGINAL finite eta/zeta theorem follows at EVERY cutoff,
-- with scale literally the original source term a_s(1)=expC(-s*L2).
--
-- IMPORTANT: (L) and (E) are the remaining analytic LEAVES and are
-- explicit arguments, NOT record instances, postulates, or proofs.
-- This does NOT establish either leaf or compact-uniform eta
-- convergence; it makes the original dyadic maximum cut exact.
--
-- Source-written, original pinned Agda 2.9 kernel acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as Analytic
import DASHI.Analysis.BishopRiemannAnalyticSetoidExpReuseExact as ExpBridge
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Analysis.BishopOriginalEtaEvenSourceScaleFiniteWeldExact as Scale
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- Natural multiplication has already been normalized into the
-- original indexing equation: source index 2k+1 means integer 2k+2.
OriginalDyadicNatLogLaw : Terms.NatLogCandidate → Set
OriginalDyadicNatLogLaw logNat =
  (k : Nat) →
  BishopReal._≃_
    (logNat (suc (Eta.twice k)))
    (BishopReal._+_ (logNat (suc zero)) (logNat k))

-- The *actual* expC transported by the original analytic/setoid
-- equivalence, rather than an unrelated abstract complex exp.
OriginalBishopAnalyticExpAddLaw :
  Cartesian.BishopSetoidComplexTranscendentals → Set
OriginalBishopAnalyticExpAddLaw T =
  (z w : Analytic.BishopComplex) →
  Eta._≈C_
    (ExpBridge.bishopAnalyticComplexExp T (Analytic._+C_ z w))
    (Analytic._*C_
      (ExpBridge.bishopAnalyticComplexExp T z)
      (ExpBridge.bishopAnalyticComplexExp T w))

-- The only algebraic bridge from the real log statement to
-- complex -s*log. Both original Bishop coordinates are included.
originalDyadicNegativeSLogIsSum :
  (logNat : Terms.NatLogCandidate) →
  OriginalDyadicNatLogLaw logNat →
  (s : Analytic.BishopComplex) (k : Nat) →
  Eta._≈C_
    (Terms.bishopNegativeSLn logNat s (suc (Eta.twice k)))
    (Analytic._+C_
      (Terms.bishopNegativeSLn logNat s (suc zero))
      (Terms.bishopNegativeSLn logNat s k))
originalDyadicNegativeSLogIsSum logNat logLaw s k =
  BishopP.≃-trans
    (BishopP.*-congˡ (logLaw k))
    (BishopP.*-distribˡ-+
      (BishopReal.- (Analytic.re s))
      (logNat (suc zero))
      (logNat k))
  ,
  BishopP.≃-trans
    (BishopP.*-congˡ (logLaw k))
    (BishopP.*-distribˡ-+
      (BishopReal.- (Analytic.im s))
      (logNat (suc zero))
      (logNat k))

-- ACTUAL SOURCE SCALE, not an uninterpreted 2^{-s} constant.
-- It is exactly a_s(1)=expC(-s*L(2)) from the original eta family.
originalEtaTwoToNegativeS :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  (logNat : Terms.NatLogCandidate) →
  Analytic.BishopComplex → Analytic.BishopComplex
originalEtaTwoToNegativeS T logNat s =
  Terms.bishopDirichletExponentialTerm T logNat s (suc zero)

-- This closes the entire FINITE source-specific dyadic premise,
-- CONDITIONAL ONLY on (L) and (E).  It is not a hypothesis of its own.
originalEtaDyadicScaleFromLogAndExp :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  (logNat : Terms.NatLogCandidate) →
  (s : Analytic.BishopComplex) →
  OriginalDyadicNatLogLaw logNat →
  OriginalBishopAnalyticExpAddLaw T →
  Scale.OriginalDyadicSourceScale
    (Terms.bishopDirichletExponentialTerm T logNat s)
    (originalEtaTwoToNegativeS T logNat s)
originalEtaDyadicScaleFromLogAndExp T logNat s logLaw expLaw k =
  let
    sourceSum =
      originalDyadicNegativeSLogIsSum logNat logLaw s k
    realSame = proj₁ sourceSum
    imaginarySame = proj₂ sourceSum
    first = Terms.bishopNegativeSLn logNat s (suc zero)
    second = Terms.bishopNegativeSLn logNat s k
  in
  Eta.≈C-trans
    (ExpBridge.bishopAnalyticExpCongruent
      T realSame imaginarySame)
    (expLaw first second)

-- The selected Round11 Machin/Bishop eta source is the SAME object
-- already used in BishopOriginalDirichletEtaFinitePairingExact.
-- There is no new analytic family, witness function or source scale.
module OriginalRound11
  (inputs : Round11.Round11BishopCutset)
  where

  private
    T = Route.round11MachinTranscendentals inputs
    L = Terms.sourceCanonicalNatLogCandidate

  module Selected = Eta.OriginalRound11DirichletEta inputs
  module Finite = Scale.OriginalRound11 inputs

  originalRound11DyadicScaleFromTwoLaws :
    (s : Analytic.BishopComplex) →
    OriginalDyadicNatLogLaw L →
    OriginalBishopAnalyticExpAddLaw T →
    Scale.OriginalDyadicSourceScale
      (Selected.sourceTerms s)
      (Selected.sourceTerms s (suc zero))
  originalRound11DyadicScaleFromTwoLaws s logLaw expLaw =
    originalEtaDyadicScaleFromLogAndExp T L s logLaw expLaw

  -- All cutoffs, two original Bishop complex coordinates, the same
  -- native Dirichlet series partials, and no P2 eta-factor assumption.
  originalRound11EtaZetaFiniteFromTwoLaws :
    (s : Analytic.BishopComplex) →
    (logLaw : OriginalDyadicNatLogLaw L) →
    (expLaw : OriginalBishopAnalyticExpAddLaw T) →
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
  originalRound11EtaZetaFiniteFromTwoLaws s logLaw expLaw n =
    Finite.actualOriginalRound11EtaFiniteScaleBridge
      s (Selected.sourceTerms s (suc zero))
      (originalRound11DyadicScaleFromTwoLaws s logLaw expLaw) n
