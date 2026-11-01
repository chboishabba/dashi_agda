module DASHI.Physics.Closure.NSTriadKNOrthogonalProfileMixedDefectRound239Exact where

------------------------------------------------------------------------
-- ROUND239 / ORTHOGONAL PROFILE MIXED-DEFECT DECOUPLING
--
-- Published source:
-- Isabelle Gallagher, "Profile decomposition for solutions of the
-- Navier-Stokes equations", Bull. Soc. Math. France 129 (2001), 285--316,
-- DOI 10.24033/bsmf.2398.
--
-- In the proof of Proposition 3.3 Gallagher proves, for distinct orthogonal
-- nonlinear profiles v_n^j and v_n^k,
--
--   || v_n^j v_n^k ||_{L^4_t L^2_x} -> 0.
--
-- On every finite interval [0,T], Holder in time gives convergence in
-- L^2_t L^2_x as well.  The normalized-curl/helicity involution
-- H = |D|^{-1} curl is an order-zero Fourier multiplier and commutes with the
-- translation/scaling operations defining the profiles.  Consequently the
-- same published orthogonality mechanism applies with H v_n^j in either slot:
--
--   || (H v_n^j) x v_n^k ||_{L^2([0,T];L^2)} -> 0,  j != k.
--
-- This file records the source-level reduction only.  The repository does not
-- currently formalise Sobolev spaces, time integration, Gallagher profiles or
-- multiplier boundedness as Agda analytic objects, so no fake finite-algebra
-- proof is installed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

round239GallagherDistinctProfileProductL4L2Published : Bool
round239GallagherDistinctProfileProductL4L2Published = true

round239FiniteTimeL4ToL2ReductionStandard : Bool
round239FiniteTimeL4ToL2ReductionStandard = true

round239NormalizedCurlIsOrderZeroProfileEquivariant : Bool
round239NormalizedCurlIsOrderZeroProfileEquivariant = true

round239OrthogonalMixedHelicityCrossProfileDecouplingPublishedReduction : Bool
round239OrthogonalMixedHelicityCrossProfileDecouplingPublishedReduction = true

round239AgdaAnalyticSourceInstanceInstalled : Bool
round239AgdaAnalyticSourceInstanceInstalled = false

round239ProfileExtractionFromDefectFailureClosed : Bool
round239ProfileExtractionFromDefectFailureClosed = false

round239SingleCriticalProfileRigidityClosed : Bool
round239SingleCriticalProfileRigidityClosed = false

round239PackageAClosed : Bool
round239PackageAClosed = false

round239ClayPromotion : Bool
round239ClayPromotion = false

round239GallagherDistinctProfileProductL4L2PublishedIsTrue :
  round239GallagherDistinctProfileProductL4L2Published ≡ true
round239GallagherDistinctProfileProductL4L2PublishedIsTrue = refl

round239OrthogonalMixedHelicityCrossProfileDecouplingPublishedReductionIsTrue :
  round239OrthogonalMixedHelicityCrossProfileDecouplingPublishedReduction ≡ true
round239OrthogonalMixedHelicityCrossProfileDecouplingPublishedReductionIsTrue = refl

round239AgdaAnalyticSourceInstanceInstalledIsFalse :
  round239AgdaAnalyticSourceInstanceInstalled ≡ false
round239AgdaAnalyticSourceInstanceInstalledIsFalse = refl

round239PackageAClosedIsFalse : round239PackageAClosed ≡ false
round239PackageAClosedIsFalse = refl
