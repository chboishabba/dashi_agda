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

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Product.Base using (proj₁; proj₂)

import Real as R
import RealProperties as RP
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Analysis.BishopRiemannAnalyticSetoidExpReuseExact as ExpBridge
import Relation.Binary.PropositionalEquality as Eq
import Data.Nat.Properties as NatP
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as Analytic
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Analysis.BishopOriginalEtaPairBlockTelescopingExact as Shifted
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopOriginalEtaDyadicSourceLawReductionExact as Dyadic
import DASHI.Analysis.BishopOriginalNativeComplexExpAdditionFromTrigExact as Native
import DASHI.Analysis.BishopOriginalNegativeLogTerminalFromMeshExact as Log
import DASHI.Analysis.BishopOriginalEtaEvenSourceScaleFiniteWeldExact as Scale
import DASHI.Analysis.BishopOriginalEtaZetaEvenCutoffSeriesWeldExact as SeriesWeld
import DASHI.Analysis.BishopOriginalXiPolynomialReflectionSameCarrierExact as Xi
import DASHI.Foundations.BishopSignedFactorialDegreeBinomialExact as Signed
import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11

module OriginalRound11 (inputs : Round11.BishopCutset) where

  private
    T = Route.machinTranscendentals inputs
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


  -- Both trig inputs now come from the original factorial product.
  -- Only the literal dyadic Nat-log identity remains an argument.
  -- Source-written, not pinned kernel accepted.
  originalRound11FiniteEtaZetaFromNativeFactorial :
    (s : Analytic.BishopComplex) →
    Dyadic.OriginalDyadicNatLogLaw L →
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
  originalRound11FiniteEtaZetaFromNativeFactorial s logLaw n =
    Existing.originalRound11EtaZetaFiniteFromTwoLaws
      s logLaw (Native.originalBishopAnalyticExpAddFromFactorial T) n


  -- Both original analytic inputs now have literal source producers.
  -- All finite cutoffs on the SAME Round11 term family; not uniform
  -- continuation, zero exclusion, or kernel-verified discharge.
  originalRound11FiniteEtaZetaFromOriginalSources :
    (s : Analytic.BishopComplex) →
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
  originalRound11FiniteEtaZetaFromOriginalSources s n =
    originalRound11FiniteEtaZetaFromNativeTrigAddition
      s Log.canonicalNatLogDyadic
      (λ x y → proj₂ (Signed.originalSineCosineAdditionFromNativeFactorials inputs x y))
      (λ x y → proj₁ (Signed.originalSineCosineAdditionFromNativeFactorials inputs x y))
      n


  -- Every positive-integer scale, including b=1 and the original b=2.
  -- Same literal Dirichlet terms; the index is b*(j+1)-1.
  originalRound11AllProductScale :
    (s : Analytic.BishopComplex) (i j : Nat) →
    Eta._≈C_
      (Selected.sourceTerms s (j + i * suc j))
      (Analytic._*C_ (Selected.sourceTerms s i)
                     (Selected.sourceTerms s j))
  originalRound11AllProductScale s i j =
    let
      logLaw = Log.canonicalNatLogAllProducts i j
      negReal = R.-_ (Analytic.re s)
      negImag = R.-_ (Analytic.im s)
      realLaw = RP.≃-trans (RP.*-congˡ logLaw)
        (RP.*-distribˡ-+ negReal (L i) (L j))
      imagLaw = RP.≃-trans (RP.*-congˡ logLaw)
        (RP.*-distribˡ-+ negImag (L i) (L j))
      addLaw = Native.originalBishopAnalyticExpAddFromNativeRealExpAndTrig T
        (λ x y → proj₂ (Signed.originalSineCosineAdditionFromNativeFactorials inputs x y))
        (λ x y → proj₁ (Signed.originalSineCosineAdditionFromNativeFactorials inputs x y))
    in
    Eta.≈C-trans
      (ExpBridge.bishopAnalyticExpCongruent T realLaw imagLaw)
      (addLaw (Terms.bishopNegativeSLn L s i)
              (Terms.bishopNegativeSLn L s j))

  -- Retain the signed residual at each base and actual cutoff.
  -- b = suc i; source coefficient b^(-s) is at zero-based i.
  baseScale : Analytic.BishopComplex → Nat → Analytic.BishopComplex
  baseScale s i =
    Analytic._*C_ (Analytic.bishop-complex (NatReal.natReal (suc i)) R.0ℝ)
                  (Selected.sourceTerms s i)

  baseResidual : Analytic.BishopComplex → Nat → Nat → Analytic.BishopComplex
  baseResidual s i n =
    Analytic._+C_ (Dirichlet.dirichletPartial Selected.sourceTerms s (suc i * n))
      (Analytic.negC (Analytic._*C_ (baseScale s i)
        (Dirichlet.dirichletPartial Selected.sourceTerms s n)))

  -- Exact signed diamond algebra, before any limit or division.
  residualDiamondAlgebra :
    (a b c d p q : Analytic.BishopComplex) →
    Eta._≈C_
      (Analytic._+C_ (Analytic._+C_ a (Analytic.negC (Analytic._*C_ p b)))
        (Analytic._*C_ p (Analytic._+C_ b (Analytic.negC (Analytic._*C_ q d)))))
      (Analytic._+C_ (Analytic._+C_ a (Analytic.negC (Analytic._*C_ q c)))
        (Analytic._*C_ q (Analytic._+C_ c (Analytic.negC (Analytic._*C_ p d)))))
  residualDiamondAlgebra
    (Analytic.bishop-complex ar ai) (Analytic.bishop-complex br bi)
    (Analytic.bishop-complex cr ci) (Analytic.bishop-complex dr di)
    (Analytic.bishop-complex pr pi) (Analytic.bishop-complex qr qi) =
    (let open RP.ℝ-Solver in
     solve 12
       (λ ar ai br bi cr ci dr di pr pi qr qi →
         ((ar ⊕ (⊝ ((pr ⊗ br) ⊖ (pi ⊗ bi)))) ⊕ ((pr ⊗ (br ⊕ (⊝ ((qr ⊗ dr) ⊖ (qi ⊗ di))))) ⊖ (pi ⊗ (bi ⊕ (⊝ ((qr ⊗ di) ⊕ (qi ⊗ dr)))))))
         ⊜
         ((ar ⊕ (⊝ ((qr ⊗ cr) ⊖ (qi ⊗ ci)))) ⊕ ((qr ⊗ (cr ⊕ (⊝ ((pr ⊗ dr) ⊖ (pi ⊗ di))))) ⊖ (qi ⊗ (ci ⊕ (⊝ ((pr ⊗ di) ⊕ (pi ⊗ dr))))))))
       RP.≃-refl ar ai br bi cr ci dr di pr pi qr qi)
    ,
    (let open RP.ℝ-Solver in
     solve 12
       (λ ar ai br bi cr ci dr di pr pi qr qi →
         ((ai ⊕ (⊝ ((pr ⊗ bi) ⊕ (pi ⊗ br)))) ⊕ ((pr ⊗ (bi ⊕ (⊝ ((qr ⊗ di) ⊕ (qi ⊗ dr))))) ⊕ (pi ⊗ (br ⊕ (⊝ ((qr ⊗ dr) ⊖ (qi ⊗ di)))))))
         ⊜
         ((ai ⊕ (⊝ ((qr ⊗ ci) ⊕ (qi ⊗ cr)))) ⊕ ((qr ⊗ (ci ⊕ (⊝ ((pr ⊗ di) ⊕ (pi ⊗ dr))))) ⊕ (qi ⊗ (cr ⊕ (⊝ ((pr ⊗ dr) ⊖ (pi ⊗ di))))))))
       RP.≃-refl ar ai br bi cr ci dr di pr pi qr qi)

  sameProductCutoff : (b c n : Nat) → b * (c * n) Eq.≡ c * (b * n)
  sameProductCutoff b c n =
    Eq.trans (Eq.sym (NatP.*-assoc b c n))
      (Eq.trans (Eq.cong (λ m → m * n) (NatP.*-comm b c))
        (NatP.*-assoc c b n))

  -- The two orders of base refinement have exactly equal signed endpoints.
  -- No cancellation of a divisor or promotion to an analytic limit.
  originalRound11BaseResidualDiamond :
    (s : Analytic.BishopComplex) (i j n : Nat) →
    Eta._≈C_
      (Analytic._+C_ (baseResidual s i (suc j * n))
        (Analytic._*C_ (baseScale s i) (baseResidual s j n)))
      (Analytic._+C_ (baseResidual s j (suc i * n))
        (Analytic._*C_ (baseScale s j) (baseResidual s i n)))
  originalRound11BaseResidualDiamond s i j n
    rewrite sameProductCutoff (suc i) (suc j) n =
    residualDiamondAlgebra
      (Dirichlet.dirichletPartial Selected.sourceTerms s (suc j * (suc i * n)))
      (Dirichlet.dirichletPartial Selected.sourceTerms s (suc j * n))
      (Dirichlet.dirichletPartial Selected.sourceTerms s (suc i * n))
      (Dirichlet.dirichletPartial Selected.sourceTerms s n)
      (baseScale s i) (baseScale s j)


  -- Original subsequence at multiples of each positive integer.
  -- Accumulate on the existing prefix owner and transport to SeriesOf.
  baseMultiplePrefix :
    (s : Analytic.BishopComplex) (i n : Nat) → Analytic.BishopComplex
  baseMultiplePrefix s i n =
    Eta.originalBishopPrefix
      (λ j → Selected.sourceTerms s (j + i * suc j)) n

  originalRound11BaseMultiplePrefixScale :
    (s : Analytic.BishopComplex) (i n : Nat) →
    Eta._≈C_ (baseMultiplePrefix s i n)
      (Analytic._*C_ (Selected.sourceTerms s i)
        (Eta.originalBishopPrefix (Selected.sourceTerms s) n))
  originalRound11BaseMultiplePrefixScale s i zero =
    Scale.originalZeroIsScaleTimesZero (Selected.sourceTerms s i)
  originalRound11BaseMultiplePrefixScale s i (suc n) =
    Eta.≈C-trans
      (Scale.complexAddBothCongruent
        (originalRound11BaseMultiplePrefixScale s i n)
        (originalRound11AllProductScale s i n))
      (Scale.originalScaleDistributesOverPair
        (Selected.sourceTerms s i)
        (Eta.originalBishopPrefix (Selected.sourceTerms s) n)
        (Selected.sourceTerms s n))

  originalRound11BaseMultipleNativeScale :
    (s : Analytic.BishopComplex) (i n : Nat) →
    Eta._≈C_ (baseMultiplePrefix s i n)
      (Analytic._*C_ (Selected.sourceTerms s i)
        (Dirichlet.dirichletPartial Selected.sourceTerms s n))
  originalRound11BaseMultipleNativeScale s i n =
    Eta.≈C-trans
      (originalRound11BaseMultiplePrefixScale s i n)
      (Xi.complexMultiplyCongruent (Xi.complexRefl (Selected.sourceTerms s i))
        (SeriesWeld.originalBishopPrefixIsNativeSeries
          (Selected.sourceTerms s) n))
