module DASHI.Physics.Closure.NSTriadKNPhysicalTriadicMultiplicityLossLedgerRound72Exact where

------------------------------------------------------------------------
-- ROUND72 / PHYSICAL TRIADIC MULTIPLICITY-LOSS LEDGER
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Authors: Ruilin Hu; Phuoc-Tai Nguyen; Quoc-Hung Nguyen; Ping Zhang.
-- Title: "Quantitative bounds for bounded solutions to the Navier-Stokes
-- equations in endpoint critical Besov spaces".
-- arXiv DOI: 10.48550/arXiv.2411.06483.
--
-- ROUND72 RESULT
--
-- 1. FIXED OUTPUT GEOMETRY
--    A resonant physical output fibre has one free Z^3 input: p and k determine
--    q.  Its crude geometric code therefore lives in one cutoff cube, with
--    exact cubic cardinality majorant.  The earlier surface-area O(N^2)
--    heuristic is not assumed.
--
-- 2. CLASSWISE LOW-LEG GEOMETRY
--    In LH and HL, the low leg codes the fixed-output triad and lies in its own
--    dyadic 2^ell cube, whose exact majorant is (3*2^ell)^3.  HH/CC do not gain
--    such a low-leg count for free.
--
-- 3. RAW-COUNT FUNDING FALSIFIER
--    Even optimistic N^2 and the crude N^3 effective-cardinality losses yield
--    shell floors 2^(-2j), 2^(-3j).  Every finite prefix of BOTH families is
--    explicitly fundable below E=2 by the Round70 exact event ledger.  Hence
--    polynomial-in-frequency raw counting alone cannot close C1.
--
-- 4. MULTIPLICITY THRESHOLD
--    Four-way physical branching exactly compensates 2^(-2j); eight-way
--    branching exactly compensates 2^(-3j).  These are arithmetic thresholds,
--    not claims that NS produces such descendants.
--
-- 5. EFFECTIVE COMPLEXITY
--    A same-object factorization a_tau=x_tau*y_tau gives
--
--        mu^2 <= Q*W,
--        Q=sum x_tau^2, W=sum y_tau^2,
--
--    after the Round69 amplification remainder is identified with the Round62
--    structured triadic signed sum.  This strictly generalises the unit-weight
--    cardinality Cauchy theorem.
--
-- 6. NON-CANONICITY FALSIFIER
--    The scalar value a_tau alone does not determine Q or W: reciprocal
--    rescaling preserves a_tau while changing both.  Therefore an improved W
--    MUST come from actual physical velocity/Gram/energy structure, not from a
--    favorable post-hoc choice of factors.
--
-- NEW DECISIVE PRODUCER
--
-- Round71's `CriticalAmplificationForcesControlledSubfibre` is sharpened to:
--
--   CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization
--
-- on the literal localized trajectory, proving simultaneously:
--
--   * remainder = exact triadic structured grouping;
--   * physical factors a_tau=x_tau*y_tau;
--   * Q is a genuine charge paid by the finite physical budget;
--   * W has a strong enough scale bound.
--
-- The other decisive producer becomes:
--
--   PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss.
--
-- It must produce genuinely non-duplicate descendants whose multiplicity and
-- propagated amplitude floors make the resulting Q-floors outrun every finite
-- budget.  Raw O(N^2)/O(N^3) counting by itself is now formally ruled out.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFixedOutputFiberThreeDOFRound72Exact as ThreeDOF
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadicSubfibreComplexityByClassRound72Exact as Classwise
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationFactorizedConcentrationRound72Exact as Amplified
import DASHI.Physics.Closure.NSTriadKNPolynomialFrequencyCardinalityFundingNoGoRound72Exact as RawNoGo
import DASHI.Physics.Closure.NSTriadKNPolynomialComplexityMultiplicityThresholdRound72Exact as Threshold
import DASHI.Physics.Closure.NSTriadKNFactorizationRescalingNoGoRound72Exact as Rescaling

round72FixedOutputThreeDOFConstructed : Bool
round72FixedOutputThreeDOFConstructed = ThreeDOF.round72FixedOutputHasThreeLatticeDOF

round72LHLowLegComplexityConstructed : Bool
round72LHLowLegComplexityConstructed = Classwise.round72LHComplexityUsesLowLegShell

round72HLLowLegComplexityConstructed : Bool
round72HLLowLegComplexityConstructed = Classwise.round72HLComplexityUsesLowLegShell

round72LowLegCubicMajorantConstructed : Bool
round72LowLegCubicMajorantConstructed =
  Classwise.round72LowLegCubicCardinalityMajorantConstructed

round72FactorizedEffectiveComplexityConstructed : Bool
round72FactorizedEffectiveComplexityConstructed =
  Effective.round72FactorizedEffectiveComplexityCauchyConstructed

round72SameObjectOverlayConstructed : Bool
round72SameObjectOverlayConstructed =
  Overlay.round72SameObjectFactorizationOverlayConstructed

round72AmplificationFactorizedConcentrationConstructed : Bool
round72AmplificationFactorizedConcentrationConstructed =
  Amplified.round72AmplificationToFactorizedConcentrationConstructed

round72PolynomialFrequencyRawCountingFundingNoGoConstructed : Bool
round72PolynomialFrequencyRawCountingFundingNoGoConstructed =
  RawNoGo.round72PolynomialFrequencyCountingFundingNoGoConstructed

round72N2FourWayThresholdConstructed : Bool
round72N2FourWayThresholdConstructed =
  Threshold.round72N2ComplexityNeedsFourWayCriticalMultiplicity

round72N3EightWayThresholdConstructed : Bool
round72N3EightWayThresholdConstructed =
  Threshold.round72N3ComplexityNeedsEightWayCriticalMultiplicity

round72FactorizationNonCanonicalFromScalarValue : Bool
round72FactorizationNonCanonicalFromScalarValue =
  Rescaling.round72PhysicalFactorizationAuthorityRequired

-- Genuine remaining physical producers.
round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization : Bool
round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization = false

round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss : Bool
round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss = false

round72CriticalRatioBarrierConstructed : Bool
round72CriticalRatioBarrierConstructed = false

round72ClayPromotion : Bool
round72ClayPromotion = false

round72FixedOutputThreeDOFConstructedIsTrue :
  round72FixedOutputThreeDOFConstructed ≡ true
round72FixedOutputThreeDOFConstructedIsTrue = refl

round72FactorizedEffectiveComplexityConstructedIsTrue :
  round72FactorizedEffectiveComplexityConstructed ≡ true
round72FactorizedEffectiveComplexityConstructedIsTrue = refl

round72PolynomialFrequencyRawCountingFundingNoGoConstructedIsTrue :
  round72PolynomialFrequencyRawCountingFundingNoGoConstructed ≡ true
round72PolynomialFrequencyRawCountingFundingNoGoConstructedIsTrue = refl

round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorizationIsFalse :
  round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization ≡ false
round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorizationIsFalse = refl

round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLossIsFalse :
  round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss ≡ false
round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLossIsFalse = refl

round72ClayPromotionIsFalse : round72ClayPromotion ≡ false
round72ClayPromotionIsFalse = refl
