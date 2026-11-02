{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNVariablePeriodicBondPointwiseExact where

------------------------------------------------------------------------
-- R445 FINITE CUT-OFF FAMILY: ALL n, SAME LITERAL PERIODIC BOND FIELD.
--
-- The existing YMClaySUNVariablePeriodicGibbsGaugeExact already owns
-- the complete SU(N) finite Wilson/Gibbs sources at every side (n+1).
-- Reuse them, rather than construct new cutoff actions.
--
-- A periodic bond carrier is an indexed FUNCTION, not a Vec.
-- This module proves that its original Wilson plaquette, 6-plane deficit,
-- beta-weighted action and Gibbs density are extensional under POINTWISE
-- bond equality for EVERY cutoff n. No global function-extensionality
-- axiom, independent field carrier or analytic/continuum premise.
--
-- This pays an algebraic prerequisite for a future setoid/finite-codec
-- marginal route; it does NOT prove cutoff/refinement consistency,
-- tightness, moments or the R445 physical continuum limit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 1ℝ; _-ℝ_; _*ℝ_; -ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Signed
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

VariableBondPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (n : Nat) →
  Variable.SUNPeriodicLinks theory n →
  Variable.SUNPeriodicLinks theory n → Set
VariableBondPointwise theory n left right =
  ∀ bond → left bond ≡ right bond

variableOrientedLinkPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (n : Nat)
    (left right : Variable.SUNPeriodicLinks theory n) →
    VariableBondPointwise theory n left right →
    (site : Periodic.PeriodicBlock n)
    (direction : Signed.SignedAxis4) →
  Bond.orientedLinkBase
    (Native.sunExactSignedLinkGroup theory) left site direction
  ≡ Bond.orientedLinkBase
      (Native.sunExactSignedLinkGroup theory) right site direction
variableOrientedLinkPointwise theory n left right same site
    (Torus.pair axis true) =
  same (Torus.pair site axis)
variableOrientedLinkPointwise theory n left right same site
    (Torus.pair axis false) =
  cong (SUN.sunInverse theory)
    (same (Torus.pair (Bond.negativeStep site axis) axis))

variableSignedPathPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (n : Nat)
    (left right : Variable.SUNPeriodicLinks theory n) →
    VariableBondPointwise theory n left right →
    (site : Periodic.PeriodicBlock n)
    (directions : List Signed.SignedAxis4) →
  Bond.pathHolonomy
    (Variable.periodicSUNRealization theory n left
      (λ _ → SUN.sunIdentity theory)) site directions
  ≡ Bond.pathHolonomy
      (Variable.periodicSUNRealization theory n right
        (λ _ → SUN.sunIdentity theory)) site directions
variableSignedPathPointwise theory n left right same site [] = refl
variableSignedPathPointwise theory n left right same site
    (direction ∷ directions) =
  cong₂ (SUN.sunMultiply theory)
    (variableOrientedLinkPointwise theory n left right same site direction)
    (variableSignedPathPointwise theory n left right same
      (Bond.walkStep site direction) directions)

variablePositivePlaquettePointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (n : Nat)
    (left right : Variable.SUNPeriodicLinks theory n) →
    VariableBondPointwise theory n left right →
    (plaquette : Plaquette.PeriodicPlaquette n) →
  Variable.periodicSUNPositivePlaquette theory n left plaquette
  ≡ Variable.periodicSUNPositivePlaquette theory n right plaquette
variablePositivePlaquettePointwise theory n left right same plaquette =
  variableSignedPathPointwise theory n left right same
    (Torus.first plaquette)
    (Bond.plaquetteBoundaryDirections (Torus.second plaquette))

variableSixWilsonDeficitPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (n : Nat)
    (left right : Variable.SUNPeriodicLinks theory n) →
    VariableBondPointwise theory n left right →
  Variable.periodicSUNSixDeficit theory traceData n left
  ≡ Variable.periodicSUNSixDeficit theory traceData n right
variableSixWilsonDeficitPointwise theory traceData n left right same =
  Sums.realSumCong
    (Torus.elements (Torus.periodicTorus4Finite (suc n)))
    (λ site →
      Sums.realSumCong (Plaquette.ownedPeriodicPlaquettes site)
        (λ plaquette →
          cong (1ℝ -ℝ_)
            (cong (Trace.matrixWilsonValue traceData)
              (variablePositivePlaquettePointwise
                theory n left right same plaquette))))

variableWilsonActionPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (n : Nat) (beta : ℝ)
    (left right : Variable.SUNPeriodicLinks theory n) →
    VariableBondPointwise theory n left right →
  Variable.periodicSUNWilsonAction theory traceData n beta left
  ≡ Variable.periodicSUNWilsonAction theory traceData n beta right
variableWilsonActionPointwise theory traceData n beta left right same =
  cong (beta *ℝ_)
    (variableSixWilsonDeficitPointwise
      theory traceData n left right same)

variableGibbsDensityPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (n : Nat) (beta : ℝ)
    (left right : Variable.SUNPeriodicLinks theory n) →
    VariableBondPointwise theory n left right →
  Variable.periodicSUNGibbsDensity
    theory traceData exponential n beta left
  ≡ Variable.periodicSUNGibbsDensity
      theory traceData exponential n beta right
variableGibbsDensityPointwise
    theory traceData exponential n beta left right same =
  cong (λ action → Exp.expReal exponential (-ℝ action))
    (variableWilsonActionPointwise
      theory traceData n beta left right same)
