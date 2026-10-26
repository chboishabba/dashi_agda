module DASHI.Physics.Closure.NSTriadKNPermanaAlignmentRateAudit where

------------------------------------------------------------------------
-- 2026-10-25 PERMANA / IBRAHIM SAME-SOURCE PHYSICAL NEGATIVE CONTROL
--
-- Source: Permana, Lathief, Ibrahim, Zenodo 19632058 v3 abstract
-- (17 April 2026) advertises high-vorticity directional curvature
-- |grad xi| <= C_nu |omega|^(1/2). A separate 6 May 2026 v4 record,
-- Zenodo 20049273, changes the claimed conclusion to CONDITIONAL
-- small-data regularity. Versions are same-author family, not two
-- independent confirmations. See exact executable regression
-- tests/test_ns_permana_ibrahim_direction_rigidity_heat_shear.py.
--
-- In fact choose for each n>0 the smooth periodic, zero-mean,
-- divergence-free and UNFORCED heat shear
--
-- u_n(t,x) = (A/n)exp(-nu n²t) (0,sin(nx),cos(nx)).
--
-- Its nonlinearity (u.nabla)u is identically zero. With
-- omega_n=curl u_n,
--   omega_n(t,x)=A exp(-nu n²t)(0,sin(nx),cos(nx)),
--   |omega_n(t,x)|=A exp(-nu n²t) for EVERY x,
--   xi_n=(0,sin(nx),cos(nx)), |grad xi_n|=n for EVERY x.
-- At t_n=1/(nu n²)>0, |omega_n|=A/e independent of n,
-- while |grad xi_n|=n→infinity. Choose A>e*Omega for any fixed
-- high-vorticity threshold Omega. The entire physical domain is
-- in the high-vorticity region. Its kinetic mass is A²/n², its
-- enstrophy is A² (normalized torus averages) at time zero.
--
-- Thus the claimed curvature estimate CANNOT be universal with
-- C_nu depending only on viscosity, and cannot be derived solely
-- from the PDE/viscous smoothing with no further data-dependent
-- geometry/regularity premise. This does not refute the manuscript
-- if C_nu secretly depends on T3, high Sobolev data or other
-- hypotheses, nor classical conditional Constantin--Fefferman
-- or Beirão da Veiga--Berselli regularity results.
--
-- On the SAME field, the physical strain annihilates the unit
-- direction: S[u_n] xi_n = 0. The unit phase solves the harmonic-map
-- stationary identity Delta xi_n + |grad xi_n|² xi_n = 0 because
-- Delta xi_n=-n² xi_n and |grad xi_n|²=n². Spatial vorticity
-- magnitude is constant, so the cross-diffusion 2nu grad log|omega|
-- ·grad xi also vanishes. Thus the physical vorticity-direction
-- evolution highlighted in Grujic, arXiv:2609.05720, permits arbitrarily
-- fine *persistent phase oscillations* despite strictly positive
-- viscous damping of |omega|. Conditional logarithmic BMO, relative
-- alignment or strain-geometry criteria are not thereby falsified.
--
-- SOURCE-DIRECT status (verified against the author-uploaded May-06
-- manuscript transcription, ResearchGate text, section 2.1/2.2/3.2):
-- v4 Equation (3) explicitly sets T3=∫|curl(omega×u)|², so it is
-- merely NONNEGATIVE, not strictly positive-definite on nonzero flow.
-- Definition 2.1 *assumes* the nonlinear T3 terms are a divergence
-- (Topological Invariant Conservation Hypothesis, TICH). Remark 2.3
-- calls that cancellation an OPEN CONJECTURE: it is not a theorem
-- derived from the periodic divergence theorem alone.
-- Definition 3.1 introduces separate Turbulence Alignment Hypothesis
-- (TAH); Definition 3.2 assumes an A2 Muckenhoupt weight/DGMICH;
-- Definition 3.3 *postulates* curvature coefficient
-- C_nu <= C T3^(1/2) E^(-1/2), rather than deriving it from NS.
-- For the explicit Beltrami family above, T3=0 even with
-- |omega|=A/e and |grad xi|=n; thus that T3-to-curvature
-- postulate cannot be universal if C_nu represents curvature.
-- Alignment inequality |<xi,S xi>|<=Cnu T3 E^(1/5)|omega|^(.9)
-- is NOT contradicted by this example, since <xi,S xi>=0 as well.
-- These are source HYPOTHESES and an exact SAME-EQUATION negative
-- control, not a proof that all conditional conclusions are false.
-- Related v3 author metadata Zenodo says "Hanif A., Lathif";
-- v4 says "Hanif A., Lathief". Preserve version spelling rather
-- than mechanically normalizing two primary-source records.
--
-- The present Agda file retains the pre-existing T3 finite-carrier
-- checks. The dynamic field algebra here is SOURCE-WRITTEN COMMENT
-- with an exact locally executed SymPy regression (4 passed);
-- it is NOT a new Agda kernel theorem. Never mark v3/v4 global
-- regularity proved or promote citations into independent proof.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Bryan P. Permana; Sage A. Ibrahim; Hanif A. Lathief.
-- Title: "Quantitative Resolution of Global Regularity for 3D
-- Incompressible Navier-Stokes Equations: Explicit Geometric Depletion and
-- Non-Local Alignment Rates".
-- Venue/year: SSRN manuscript dated 11 April 2026; posted 30 April 2026.
-- DOI: 10.2139/ssrn.6557718.
-- Uses: candidate claims |<xi,S xi>| <= C_nu T3 E^(1/5)|omega|^(9/10)
-- and exponential viscous damping of a proposed third topological invariant.
-- Relationship: unrefereed candidate only.  No regularity theorem is imported.
--
-- Authors: Bryan P. Permana; Sage A. Ibrahim; Hanif A. Lathief.
-- Title: "Quantitative Regularity of the 3D Incompressible Navier-Stokes
-- Equations on the Periodic Torus: Geometric Depletion, Fractal Bounds, and
-- Topological Damping".
-- Venue/year: Zenodo version 3, 17 April 2026.
-- DOI: 10.5281/zenodo.19632058.
-- Relationship: audited separately from the SSRN version because its domain,
-- title, invariant formula, and claimed proof route materially differ.
--
-- Authors: DASHI repository contributors.
-- Title: "Exact fail-closed audit of the Permana alignment-rate route".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original exact audit.
-- Relationship: gives an explicit trace-free compressive-strain counterexample
-- to the asserted damping inference and evaluates the proposed
-- T3 = ||curl(omega cross u)||_2^2 on two finite Galerkin states, where its
-- Euler derivative is exactly nonzero.  The manuscript's global theorem is
-- therefore not consumed.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNFourierSelfModeVortexStretchingNoGoRound78Exact as SelfMode
open import Data.Nat.Base using (_<_; z≤n; s≤s)
import Data.Integer.Base as Int
open import Data.Integer.Base using (+_)

------------------------------------------------------------------------
-- ACTUAL REUSE OF EXISTING PHYSICAL CROSS-PRODUCT CARRIER.
--
-- Classical Beltrami property curl u = λ u gives pointwise Lamb
-- vector ω×u=0. Exact polynomial content is transported here through
-- existing RationalLeray Vector3 and FourierBiotSavart cross (the same
-- owner used in the Round78 self-stretching no-go).
-- This is the algebraic core of the real smooth heat-shear witness.
-- The trigonometric function/evolution and L² integral are verified
-- separately in tests; no fictitious Agda time-evolution kernel proof
-- or global Navier--Stokes regularity theorem is claimed.
------------------------------------------------------------------------

beltramiLambVectorZero :
  (lambda : ℚ) (velocity : V.Vector3) →
  BS.cross (V.scale lambda velocity) velocity
    ≡ V.v3 0ℚ 0ℚ 0ℚ
beltramiLambVectorZero lambda (V.v3 ux uy uz) =
  V.vectorExt
    (solve (lambda ∷ ux ∷ uy ∷ uz ∷ []))
    (solve (lambda ∷ ux ∷ uy ∷ uz ∷ []))
    (solve (lambda ∷ ux ∷ uy ∷ uz ∷ []))

-- Do not promote any T3-based coercivity from this identity: on
-- Beltrami velocity fields ω×u=0 and its curl vanishes, while
-- directional curvature, enstrophy, and helicity may be nonzero.
-- The particular oscillatory heat-shear family has |grad ξ|=n
-- at all spatial points even though proposed T3≡0.
-- This does not falsify separate T3-dependent alignment estimates
-- whose LEFT side also vanishes on the given field.

data ManuscriptVersion : Set where
  ssrnApril11 : ManuscriptVersion
  zenodoApril17 : ManuscriptVersion

data ClaimStatus : Set where
  represented : ClaimStatus
  unverified : ClaimStatus
  falsifiedOnFiniteCarrier : ClaimStatus

record ExactRational : Set where
  constructor ratio
  field
    numerator : Int.ℤ
    denominator : Nat

open ExactRational public

strainEigenvalueOne strainEigenvalueTwo strainEigenvalueThree : Int.ℤ
strainEigenvalueOne = + 1
strainEigenvalueTwo = + 1
strainEigenvalueThree = Int.-_ (+ 2)

traceFreeDiagonalSum : Int.ℤ
traceFreeDiagonalSum =
  Int._+_
    (Int._+_ strainEigenvalueOne strainEigenvalueTwo)
    strainEigenvalueThree

traceFreeDiagonalSumIsZero : traceFreeDiagonalSum ≡ + 0
traceFreeDiagonalSumIsZero = refl

compressiveAlignmentScalar : Int.ℤ
compressiveAlignmentScalar = strainEigenvalueThree

compressiveAlignmentScalarIsNegativeTwo :
  compressiveAlignmentScalar ≡ Int.-_ (+ 2)
compressiveAlignmentScalarIsNegativeTwo = refl

traceFreeDoesNotForcePositiveAlignment : Bool
traceFreeDoesNotForcePositiveAlignment = true

traceFreeDoesNotForcePositiveAlignmentIsTrue :
  traceFreeDoesNotForcePositiveAlignment ≡ true
traceFreeDoesNotForcePositiveAlignmentIsTrue = refl

witnessT3 witnessT3EulerDerivative optimizedSupportT3
  optimizedSupportT3EulerDerivative : ExactRational
witnessT3 = ratio (+ 867456) 1
witnessT3EulerDerivative = ratio (+ 34108128) 5
optimizedSupportT3 = ratio (+ 12172469428) 1
optimizedSupportT3EulerDerivative =
  ratio (Int.-_ (+ 12347695354951776)) 11305

witnessT3EulerDerivativeNonzero : 0 < 34108128
witnessT3EulerDerivativeNonzero = s≤s z≤n

optimizedSupportT3EulerDerivativeNonzero : 0 < 12347695354951776
optimizedSupportT3EulerDerivativeNonzero = s≤s z≤n

record PermanaAlignmentClaimSurface
    {x t s v : Level} : Set (lsuc (x ⊔ t ⊔ s ⊔ v)) where
  field
    Point : Set x
    Time : Set t
    Scalar : Set s
    Vector : Set v

    vorticityMagnitude : Point → Time → Scalar
    vorticityDirection : Point → Time → Vector
    strainActs : Point → Time → Vector → Vector
    directionStrainPairing : Point → Time → Scalar
    enstrophy : Time → Scalar
    proposedT3 : Time → Scalar
    oneFifth nineTenths : Scalar
    power : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    claimedAlignmentRate :
      ∀ point time →
      _≤_ (directionStrainPairing point time)
           (multiply
             (proposedT3 time)
             (multiply
               (power (enstrophy time) oneFifth)
               (power (vorticityMagnitude point time) nineTenths)))

open PermanaAlignmentClaimSurface public

record PermanaUnclosedCutset
    {s : Level} : Set (lsuc s) where
  field
    Obligation : Set s

    movingHighVorticityDomainBoundaryTerms : Obligation
    deterministicMoserDampingSign : Obligation
    directionCurvatureEstimateWithoutCircularRegularity : Obligation
    proposedT3WellDefinedAndCoordinateIndependent : Obligation
    proposedT3ExactEvolutionIdentity : Obligation
    nonlinearT3TermsArePureDivergences : Obligation
    spectralGapAppliedToCorrectMeanZeroCarrier : Obligation
    cknParabolicToSpatialHighVorticityTransfer : Obligation
    bonyCommutatorClosesWithoutLInfinityAssumption : Obligation
    noncircularH2AndBKMBootstrap : Obligation
    ssrnAndZenodoVersionCompatibility : Obligation

open PermanaUnclosedCutset public

ssrnClaimStatus : ClaimStatus
ssrnClaimStatus = unverified

zenodoT3EulerInvarianceStatus : ClaimStatus
zenodoT3EulerInvarianceStatus = falsifiedOnFiniteCarrier

permanav3GlobalRegularityImported : Bool
permanav3GlobalRegularityImported = false

permanav3GlobalRegularityImportedIsFalse :
  permanav3GlobalRegularityImported ≡ false
permanav3GlobalRegularityImportedIsFalse = refl

proposedT3EulerInvariantOnRepresentedStates : Bool
proposedT3EulerInvariantOnRepresentedStates = false

proposedT3EulerInvariantOnRepresentedStatesIsFalse :
  proposedT3EulerInvariantOnRepresentedStates ≡ false
proposedT3EulerInvariantOnRepresentedStatesIsFalse = refl
