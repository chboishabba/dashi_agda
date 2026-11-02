module DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact where

------------------------------------------------------------------------
-- ALL FINITE PERIODIC 4D SIZES: ORIGINAL SU(N) WILSON/GIBBS GAUGE THEOREM
--
-- R443/R445 max-cut: the earlier n=3 fixed side-four matrix-SUN action
-- does not describe a changing-cutoff family. The ORIGINAL native Balaban
-- PeriodicBondField n, finite enumeration, six positive planes, native
-- oriented-link gauge cancellation and SU(N) trace class function already
-- work FOR EVERY n. This module instantiates them at every n, with a
-- literal exact finite sum over all periodic sites and all six planes.
--
-- This is NOT a continuum measure: at each n the continuous product-Haar
-- functional, physical beta(a), moments, cutoff compatibility and UV/IR
-- convergence still require real mathematical producers.
--
-- Sources: Wilson (1974), DOI 10.1103/PhysRevD.10.2445;
-- Balaban (1985), CMP 98 DOI 10.1007/BF01211042, CMP 99
-- DOI 10.1007/BF01466594; originals own the group/geometry.
-- DASHI contributes the exact real matrix-link n-parametric wiring.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; -ℝ_; _<ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

SUNPeriodicLinks :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
    Nat → Set
SUNPeriodicLinks theory n =
  Bond.PeriodicBondField n (SUN.SUNMatrixElement theory)

SUNPeriodicGauge :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
    Nat → Set
SUNPeriodicGauge theory n =
  Bond.PeriodicSiteGauge n (SUN.SUNMatrixElement theory)

periodicSUNRealization :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (n : Nat)
    (links : SUNPeriodicLinks theory n)
    (gamma : SUNPeriodicGauge theory n) →
  Bond.PeriodicBondGaugeRealization n
    (SUN.SUNMatrixElement theory) (Native.sunExactSignedLinkGroup theory)
periodicSUNRealization theory n links gamma =
  Covariance.literalPeriodicBondGaugeRealization
    (Native.sunExactSignedLinkGroup theory)
    (Geometry.periodicStepInverseLaws n)
    links gamma

periodicSUNGaugeTransform :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (n : Nat) →
  SUNPeriodicLinks theory n →
  SUNPeriodicGauge theory n →
  SUNPeriodicLinks theory n
periodicSUNGaugeTransform theory n links gamma =
  Bond.transformedBond (periodicSUNRealization theory n links gamma)

periodicSUNPositivePlaquette :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (n : Nat)
    (links : SUNPeriodicLinks theory n) →
  Plaquette.PeriodicPlaquette n → SUN.SUNMatrixElement theory
periodicSUNPositivePlaquette theory n links p =
  Bond.plaquetteHolonomyFromBonds
    (periodicSUNRealization theory n links (λ _ → SUN.sunIdentity theory))
    p

periodicSUNPositivePlaquetteGaugeTrace :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = Scalar} theory)
    (n : Nat)
    (links : SUNPeriodicLinks theory n)
    (gamma : SUNPeriodicGauge theory n)
    (p : Plaquette.PeriodicPlaquette n) →
  Trace.matrixWilsonValue traceData
    (periodicSUNPositivePlaquette theory n
      (periodicSUNGaugeTransform theory n links gamma) p)
  ≡ Trace.matrixWilsonValue traceData
      (periodicSUNPositivePlaquette theory n links p)
periodicSUNPositivePlaquetteGaugeTrace
    theory traceData n links gamma p =
  trans
    (cong (Trace.matrixWilsonValue traceData)
      (Bond.plaquetteGaugeCancellation
        (Geometry.periodicPlaquetteClosure n)
        (periodicSUNRealization theory n links gamma) p))
    (Trace.sunTraceConjugationInvariant traceData
      (gamma (Torus.first p))
      (periodicSUNPositivePlaquette theory n links p))

-- Original canonical all-site enumeration; changing n changes the
-- ACTUAL physical lattice and #links, not just beta at side four.
periodicSUNSites :
  (n : Nat) → Torus.FiniteEnumeration
    (Torus.periodicTorus4Definition (suc n))
periodicSUNSites n = Torus.periodicTorus4Finite (suc n)

periodicSUNSixDeficit :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (n : Nat) →
  SUNPeriodicLinks theory n → ℝ
periodicSUNSixDeficit theory traceData n links =
  Sums.realSum
    (Torus.elements (Torus.periodicTorus4Finite (suc n)))
    (λ site →
      Sums.realSum (Plaquette.ownedPeriodicPlaquettes site)
        (λ p → 1ℝ -ℝ
          Trace.matrixWilsonValue traceData
            (periodicSUNPositivePlaquette theory n links p)))

periodicSUNSixDeficitGaugeInvariant :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (n : Nat)
    (links : SUNPeriodicLinks theory n)
    (gamma : SUNPeriodicGauge theory n) →
  periodicSUNSixDeficit theory traceData n
    (periodicSUNGaugeTransform theory n links gamma)
  ≡ periodicSUNSixDeficit theory traceData n links
periodicSUNSixDeficitGaugeInvariant theory traceData n links gamma =
  Sums.realSumCong
    (Torus.elements (Torus.periodicTorus4Finite (suc n)))
    (λ site →
      Sums.realSumCong (Plaquette.ownedPeriodicPlaquettes site)
        (λ p → cong (1ℝ -ℝ_)
          (periodicSUNPositivePlaquetteGaugeTrace
            theory traceData n links gamma p)))

periodicSUNWilsonAction :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (n : Nat) (beta : ℝ) →
  SUNPeriodicLinks theory n → ℝ
periodicSUNWilsonAction theory traceData n beta links =
  beta *ℝ periodicSUNSixDeficit theory traceData n links

periodicSUNWilsonActionGaugeInvariant :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (n : Nat) (beta : ℝ)
    (links : SUNPeriodicLinks theory n)
    (gamma : SUNPeriodicGauge theory n) →
  periodicSUNWilsonAction theory traceData n beta
    (periodicSUNGaugeTransform theory n links gamma)
  ≡ periodicSUNWilsonAction theory traceData n beta links
periodicSUNWilsonActionGaugeInvariant theory traceData n beta links gamma =
  cong (beta *ℝ_)
    (periodicSUNSixDeficitGaugeInvariant theory traceData n links gamma)

periodicSUNGibbsDensity :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (n : Nat) (beta : ℝ) →
  SUNPeriodicLinks theory n → ℝ
periodicSUNGibbsDensity theory traceData exponential n beta links =
  Exp.expReal exponential
    (-ℝ periodicSUNWilsonAction theory traceData n beta links)

periodicSUNGibbsDensityGaugeInvariant :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (n : Nat) (beta : ℝ)
    (links : SUNPeriodicLinks theory n)
    (gamma : SUNPeriodicGauge theory n) →
  periodicSUNGibbsDensity theory traceData exponential n beta
    (periodicSUNGaugeTransform theory n links gamma)
  ≡ periodicSUNGibbsDensity theory traceData exponential n beta links
periodicSUNGibbsDensityGaugeInvariant
    theory traceData exponential n beta links gamma =
  cong (λ action → Exp.expReal exponential (-ℝ action))
    (periodicSUNWilsonActionGaugeInvariant
      theory traceData n beta links gamma)

-- Selected physical n-dependent finite measure constructor. The Haar
-- integral remains an explicit *per-n physical input*, not counting
-- rational points or assuming arbitrary selected measures are Haar.
periodicSUNFiniteGibbsMeasure :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (n : Nat) (beta : ℝ)
    (productHaar : (SUNPeriodicLinks theory n → ℝ) → ℝ)
    (divide : ℝ → ℝ → ℝ) →
  Physical.PhysicalFiniteYMMeasure (SUNPeriodicLinks theory n) ℝ
periodicSUNFiniteGibbsMeasure theory traceData exponential n beta productHaar divide =
  record
    { Physical.density =
        periodicSUNGibbsDensity theory traceData exponential n beta
    ; Physical.haarIntegral = productHaar
    ; Physical.multiply = _*ℝ_
    ; Physical.divide = divide
    ; Physical.partitionFunction =
        productHaar (periodicSUNGibbsDensity theory traceData exponential n beta)
    }


------------------------------------------------------------------------
-- Fixed n=3 is the ACTUAL old side-four native signed plaquette object.
-- This is a local same-holonomy equation; global-sum reassociation and
-- physical UV compatibility must not be inferred from it without proof.
------------------------------------------------------------------------

sideFourPlaquetteSameNativeHolonomy :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (links : Native.SUNSideFourLinks N theory)
    (p : Plaquette.PeriodicPlaquette Weld.three) →
  periodicSUNPositivePlaquette theory Weld.three links p
  ≡ Native.sunPositivePlaquetteHolonomy theory links p
sideFourPlaquetteSameNativeHolonomy theory links p = refl

sideFourPlaquetteSameNativeWilsonTrace :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = Scalar} theory)
    (links : Native.SUNSideFourLinks N theory)
    (p : Plaquette.PeriodicPlaquette Weld.three) →
  Trace.matrixWilsonValue traceData
    (periodicSUNPositivePlaquette theory Weld.three links p)
  ≡ Trace.matrixWilsonValue traceData
    (Native.sunPositivePlaquetteHolonomy theory links p)
sideFourPlaquetteSameNativeWilsonTrace theory traceData links p =
  cong (Trace.matrixWilsonValue traceData)
    (sideFourPlaquetteSameNativeHolonomy theory links p)
