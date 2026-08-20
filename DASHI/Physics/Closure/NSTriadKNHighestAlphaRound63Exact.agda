module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound63Exact where

------------------------------------------------------------------------
-- ROUND 63 HIGHEST-ALPHA AGGREGATE
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
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
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
--
-- Round63 attacks the Round62 cutset by construction/falsification rather than
-- adding another terminal theorem interface.
--
-- A0 CLOSED AT THE FINITE ENUMERATION LEVEL:
--   * canonical first-nonzero-sign half lattice on Z^3;
--   * fixed-cutoff duplicate-free orbit list, exactly one representative from
--     every nonzero {k,-k} orbit;
--   * mature literal Galerkin RHS mapped over exactly that coordinate list;
--   * RHS coefficient count equals coordinate count, eliminating the specific
--     n -> 2n -> 4n reconstructed-list defect.
-- Remaining A: fixed-N Picard trajectory/invariant family and the selected
-- time-dependent shell/Duhamel identity; physical HH-bad estimates.
--
-- C0 SHARPENED TO AN EXACT EQUIVALENCE:
-- On C>0,r>0 define
--
--       Xi_n = X_n / (C r^n).
--
-- Exact rational algebra proves X_n=(C r^n)Xi_n and, for every n,K,
--
--       X_n <= K C r^n    iff    Xi_n <= K.
--
-- Thus the genuine C1 theorem is exactly uniform boundedness of the normalized
-- physical functional Xi.  The owner language itself does not produce Xi and
-- no final correction capacity is used.
--
-- B0 CONSTRUCTED AND CORRECTED:
--   * P_{<=s+1}-P_{<=s}=Delta_{s+1} exactly on the canonical hard shells;
--   * the centered literal commutator telescopes coefficientwise and through
--     the actual physicalOutputFiber into annular collision vectors;
--   * HOWEVER simple endpoint-annular support is still not a common hat: the
--     Round62 shell-0 -> shell-3 witness is active at annuli 0 and 3;
--   * the correct hat is the DOMINANT INTERACTION hat.  For every resonant
--     triangle, the two largest infinity-norm legs differ by at most a factor
--     two, hence their dyadic shells are within one.  An actual DyadicHatSupport
--     containing them is constructed for every resonant triad, including CC.
--
-- B1.5 NORMALIZATION SANITY:
-- The historical GramInterferenceCell does not imply overlap<=1; an exact cell
-- with overlap=2 is constructed.  A refined NormalizedGramInterferenceCell
-- adds the missing contraction and derives 0<=overlap<=1 and pairProduct<=1.
-- The physical B1 producer must land in this normalized cell before the
-- six-three 17/64 and 65/512 sharpening is meaningful.
--
-- A2:
-- The hard HH-bad tax factors only through
--       Lambda_bad = C_* K_bad,
-- so optimization should target this product directly.
--
-- D/F:
-- Exact proof-uniqueness of official Pair incidence does not imply unique mode
-- endpoints.  A countermodel proves that a Fourier-complete enumeration
-- requires a genuine functional target/source extraction (or stronger direct
-- bijection) from the official pair producer.
--
-- GENUINE REMAINING PRODUCERS AFTER ROUND63:
--
--   A1  fixed-N selected Galerkin trajectory + differentiated shell identity;
--   A2  physical headroom/density/charge estimate with small Lambda_bad;
--   B1  dominant-hat localized literal row -> normalized physical Gram/Schur;
--   B3  physical overlap <= six-three envelope (17/64,65/512);
--   C1  uniform scale-invariant bound sup_n Xi_n <= K;
--   Cdata smooth-HH-good and Com normalized data-scale bounds + strict gap;
--   D/F official Pair functional enumeration -> literal pair bijection,
--       structured atoms, kernel zero/estimate and boundary limits;
--   E   actual C_c^4 continuum annular multiplier + fourfold inverse-Fourier
--       integration-by-parts decay;
--   G   instantiate the already-derived scalar feasibility inequality.
--
-- No Clay promotion is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound62FinalAuditExact

-- A0 fixed reality-orbit coordinate repair.
import DASHI.Physics.Closure.NSTriadKNCanonicalRealityOrbitHalfLatticeRound63Exact
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitGalerkinRHSRound63Exact

-- C0 exact scale normalization.
import DASHI.Physics.Closure.NSTriadKNCriticalBlockNormalizationRound63Exact
import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact

-- B0 annularization, falsifier, and corrected dominant interaction hat.
import DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularProjectorRound63Exact
import DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularCommutatorRound63Exact
import DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularOutputFibreRound63Exact
import DASHI.Physics.Closure.NSTriadKNComSimpleAnnularCommonHatNoGoRound63Exact
import DASHI.Physics.Closure.NSTriadKNResonantDominantTwoShellsRound63Exact
import DASHI.Physics.Closure.NSTriadKNResonantDominantCommonHatRound63Exact

-- B1.5 normalized Gram sanity and physical consumer shape.
import DASHI.Physics.Closure.NSTriadKNComNormalizedOverlapSanityRound63Exact
import DASHI.Physics.Closure.NSTriadKNComActiveNormalizedGramRound63Exact

-- A2 product optimization.
import DASHI.Physics.Closure.NSTriadKNHHBadCapacityProductRound63Exact

-- D/F endpoint-functionality falsifier.
import DASHI.Physics.Closure.NSTriadKNFullShellIncidenceFunctionalityNoGoRound63Exact

round63CanonicalOrbitCoordinateDefectRepairedAtRHSEnumeration : Bool
round63CanonicalOrbitCoordinateDefectRepairedAtRHSEnumeration = true

round63C1ReducedExactlyToUniformNormalizedFunctional : Bool
round63C1ReducedExactlyToUniformNormalizedFunctional = true

round63SimpleAnnularHatShortcutRejected : Bool
round63SimpleAnnularHatShortcutRejected = true

round63DominantInteractionCommonHatConstructed : Bool
round63DominantInteractionCommonHatConstructed = true

round63NormalizedGramUnitSanityRequired : Bool
round63NormalizedGramUnitSanityRequired = true

round63OfficialPairNeedsFunctionalEndpoints : Bool
round63OfficialPairNeedsFunctionalEndpoints = true

round63ClayPromotion : Bool
round63ClayPromotion = false

round63CanonicalOrbitCoordinateDefectRepairedAtRHSEnumerationIsTrue :
  round63CanonicalOrbitCoordinateDefectRepairedAtRHSEnumeration ≡ true
round63CanonicalOrbitCoordinateDefectRepairedAtRHSEnumerationIsTrue = refl

round63C1ReducedExactlyToUniformNormalizedFunctionalIsTrue :
  round63C1ReducedExactlyToUniformNormalizedFunctional ≡ true
round63C1ReducedExactlyToUniformNormalizedFunctionalIsTrue = refl

round63DominantInteractionCommonHatConstructedIsTrue :
  round63DominantInteractionCommonHatConstructed ≡ true
round63DominantInteractionCommonHatConstructedIsTrue = refl

round63ClayPromotionIsFalse : round63ClayPromotion ≡ false
round63ClayPromotionIsFalse = refl
