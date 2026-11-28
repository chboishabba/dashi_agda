module DASHI.Physics.YangMills.YMClaySUNPeriodicWilsonDensityCoreExact where

------------------------------------------------------------------------
-- Sources: K. Wilson, Phys. Rev. D 10 (1974) 2445-2459,
-- DOI 10.1103/PhysRevD.10.2445; T. Balaban, CMP 98 (1985) 75-102,
-- DOI 10.1007/BF01211042, and CMP 99 (1985) 75-102,
-- DOI 10.1007/BF01466594.
--
-- DASHI contribution: a lightweight same-source periodic Wilson density
-- core for finite lattices.  Gauge-invariance proofs remain in the full
-- YMClaySUNVariablePeriodicGibbsGaugeExact module; consumers that only need
-- the literal density use this core to avoid importing that heavier proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; -ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.CompactLieGroupDerived as Derived
import DASHI.Physics.YangMills.CompactLieInnerC3Exact as Inner
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceCoreExact as Trace
import DASHI.Physics.YangMills.YMClayStrictPositiveRealExponentialCoreExact as Exp

realSumLight : ∀ {A : Set} → List A → (A → ℝ) → ℝ
realSumLight [] f = 0ℝ
realSumLight (value ∷ values) f = f value +ℝ realSumLight values f

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

periodicSUNLinkGroup :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  Bond.ExactLinkGroup (SUN.SUNMatrixElement theory)
periodicSUNLinkGroup theory =
  let group : Core.Group (SUN.SUNMatrixElement theory)
      group = SUN.sunMatrixGroup theory
  in record
    { identity = Core.identity group
    ; multiply = Core.multiply group
    ; inverse = Core.inverse group
    ; multiplyAssociative = Core.multiplyAssociative group
    ; identityLeft = Core.identityLeft group
    ; identityRight = Core.identityRight group
    ; inverseLeft = Core.inverseLeft group
    ; inverseRight = Core.inverseRight group
    ; inverseProduct = λ x y → sym (Inner.inverseProduct group x y)
    ; inverseInverse = Derived.inverseInvolutive group
    }

periodicSUNRealization :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (n : Nat)
    (links : SUNPeriodicLinks theory n)
    (gamma : SUNPeriodicGauge theory n) →
  Bond.PeriodicBondGaugeRealization n
    (SUN.SUNMatrixElement theory) (periodicSUNLinkGroup theory)
periodicSUNRealization theory n links gamma =
  Covariance.literalPeriodicBondGaugeRealization
    (periodicSUNLinkGroup theory)
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
  realSumLight
    (Torus.elements (Torus.periodicTorus4Finite (suc n)))
    (λ site →
      realSumLight (Plaquette.ownedPeriodicPlaquettes site)
        (λ p → 1ℝ -ℝ
          Trace.matrixWilsonValue traceData
            (periodicSUNPositivePlaquette theory n links p)))

periodicSUNWilsonAction :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (n : Nat) (beta : ℝ) →
  SUNPeriodicLinks theory n → ℝ
periodicSUNWilsonAction theory traceData n beta links =
  beta *ℝ periodicSUNSixDeficit theory traceData n links

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
