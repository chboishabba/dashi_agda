module DASHI.Analysis.NonArchimedeanTaoConcentrationSameObjectNoGoExact where

------------------------------------------------------------------------
-- TAO-STYLE STOPPING CONCENTRATION -- SAME-OBJECT NO-GO
--
-- Source attribution
-- ------------------
-- Terence Tao,
-- "Almost all orbits of the Collatz map attain almost bounded values",
-- Forum of Mathematics, Pi 10 (2022), e12.
-- DOI: 10.1017/fmp.2022.8
--
-- Daniel Paulin,
-- "Concentration inequalities for Markov chains by Marton couplings and
-- spectral methods",
-- Electronic Journal of Probability 20 (2015), paper 79.
-- DOI: 10.1214/EJP.v20-4039
--
-- The source document `docs/collatz_markov_mixing_stopping_times.md` claims a
-- Tao-style sub-Gaussian stopping-time theorem by combining a drift calculation
-- with its finite 2-adic spectral gap.  The derivation changes mathematical
-- objects mid-proof:
--
-- Formalized finite Markov chain:
--   A(x) = 3x,   B(x) = 3x - 1       in Z/2^n Z.
--
-- Drift process used in the concentration section:
--   x -> x/2                    on even positive integers,
--   x -> (3x+1)/2               on odd positive integers.
--
-- These are not the same transition kernel.  Moreover `log_2 x` is not a
-- canonical real observable on a residue class in Z/2^n Z, so the displayed
-- centered increments xi_s are not supplied by the formal finite chain.
--
-- Paulin's non-reversible concentration theory also distinguishes the
-- pseudo-spectral gap; an ordinary eigenvalue-radius gap does not by itself
-- discharge the needed concentration hypotheses.
--
-- Therefore the current source does NOT derive the displayed Tao-style
-- concentration theorem.  A future theorem would require a genuine same-object
-- bridge to an integer/Syracuse process plus theorem-bearing concentration
-- hypotheses.  That would be additional mathematics, not a missing compiler
-- around the present finite 2-adic chain.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record TaoConcentrationAudit : Set where
  constructor taoConcentrationAudit
  field
    finiteChainUsesThreeXAndThreeXMinusOne : Bool
    driftCalculationUsesShortcutIntegerCollatz : Bool
    thoseTransitionKernelsAreSameObject : Bool
    logTwoResidueIsCanonicalRealObservable : Bool
    centeredLogIncrementsMartingaleProved : Bool
    ordinaryEigenvalueGapSufficesForPaulinNonreversibleTheory : Bool
    tao2022StatesDisplayedSubGaussianStoppingBound : Bool
    currentSourceDerivesTaoStyleConcentration : Bool
    futureSameObjectBridgeWouldBeNewMathematics : Bool

canonicalTaoConcentrationAudit : TaoConcentrationAudit
canonicalTaoConcentrationAudit =
  taoConcentrationAudit
    true true false false false false false false true

transitionKernelMismatch :
  TaoConcentrationAudit.thoseTransitionKernelsAreSameObject
    canonicalTaoConcentrationAudit
  ≡ false
transitionKernelMismatch = refl

logObservableMismatch :
  TaoConcentrationAudit.logTwoResidueIsCanonicalRealObservable
    canonicalTaoConcentrationAudit
  ≡ false
logObservableMismatch = refl

martingaleReceiptAbsent :
  TaoConcentrationAudit.centeredLogIncrementsMartingaleProved
    canonicalTaoConcentrationAudit
  ≡ false
martingaleReceiptAbsent = refl

paulinShortcutRejected :
  TaoConcentrationAudit.ordinaryEigenvalueGapSufficesForPaulinNonreversibleTheory
    canonicalTaoConcentrationAudit
  ≡ false
paulinShortcutRejected = refl

currentTaoPromotionClosedNegative :
  TaoConcentrationAudit.currentSourceDerivesTaoStyleConcentration
    canonicalTaoConcentrationAudit
  ≡ false
currentTaoPromotionClosedNegative = refl
