module DASHI.Physics.Closure.NSTriadKNTaoDyadicFineStructureCalibrationRound88Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Finite time blowup for an averaged three-dimensional Navier-Stokes
-- equation".
-- Journal: Journal of the American Mathematical Society 29 (2016), 601--674.
-- DOI: 10.1090/jams/838.
-- arXiv DOI: 10.48550/arXiv.1402.0290.
--
-- Authors: Nets Hawk Katz; Natasa Pavlovic.
-- Title: "Finite time blow-up for a dyadic model of the Euler equations".
-- Journal: Transactions of the American Mathematical Society 357 (2005),
-- 695--708.
-- DOI: 10.1090/S0002-9947-04-03532-9.
--
-- Author: Alexey Cheskidov.
-- Title: "Blow-up in finite time for the dyadic model of the Navier-Stokes
-- equations".
-- Journal: Transactions of the American Mathematical Society 360 (2008),
-- 5101--5120.
-- DOI: 10.1090/S0002-9947-08-04494-2.
-- arXiv DOI: 10.48550/arXiv.math/0601074.
--
-- SOURCE BOUNDARY
-- Tao proves that energy cancellation plus harmonic-analysis-level averaged
-- structure is not enough to force 3-D NS regularity.  Katz--Pavlovic and
-- Cheskidov provide a rigorous dyadic-model calibration in which shell transfer
-- and hyperdissipation compete at exact scale exponents.  Those published
-- theorems are context, NOT imported proof authority for the literal NS
-- carrier below.  In particular this file does not claim an equivalence or
-- morphism between DASHI's physical triads and a dyadic model.
--
-- ROUND88 CONTRIBUTION
-- The exact scale comparison needed by the new Round87 viscous-margin route is
-- elementary but decisive.  On lambda_q=2^q,
--
--     degree-one transfer scale  L_q = lambda_q,
--     Laplacian margin scale     V_q = lambda_q^2.
--
-- Hence
--
--     L_(q+1) = 2 L_q,
--     V_(q+1) = 4 V_q,
--
-- and after dividing by the viscous scale the degree-one residual carries
-- exactly one inverse shell factor:
--
--     L_q / V_q = lambda_q^-1.
--
-- This is the source-independent algebraic content of the dyadic sanity check:
-- standard Laplacian damping has one full shell power of headroom over a
-- degree-one cascade coefficient.  The physical theorem must still show that
-- the signed residual actually has at most this degree-one shell growth.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
import Data.Integer.Base as Int
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Dyadic

four : ℚ
four = Int.+ 4 / 1

degreeOneTransferScale : Nat → ℚ
degreeOneTransferScale = Dyadic.dyadicScale

laplacianMarginScale : Nat → ℚ
laplacianMarginScale shell =
  Dyadic.dyadicScale shell * Dyadic.dyadicScale shell

normalizedDegreeOneResidualScale : Nat → ℚ
normalizedDegreeOneResidualScale shell =
  degreeOneTransferScale shell
    * Dyadic.inverseDyadicScale shell
    * Dyadic.inverseDyadicScale shell

degreeOneTransferDoubles : ∀ shell →
  degreeOneTransferScale (suc shell)
  ≡ Dyadic.two * degreeOneTransferScale shell
degreeOneTransferDoubles shell = refl

laplacianMarginQuadruples : ∀ shell →
  laplacianMarginScale (suc shell)
  ≡ four * laplacianMarginScale shell
laplacianMarginQuadruples shell =
  Ring.solve-∀ (Dyadic.dyadicScale shell)

normalizedDegreeOneResidualIsInverseShell : ∀ shell →
  normalizedDegreeOneResidualScale shell
  ≡ Dyadic.inverseDyadicScale shell
normalizedDegreeOneResidualIsInverseShell shell =
  let
    lambda = Dyadic.dyadicScale shell
    mu = Dyadic.inverseDyadicScale shell
    reciprocal : mu * lambda ≡ 1ℚ
    reciprocal = Dyadic.inverseDyadicReciprocal shell

    rearranged :
      lambda * mu * mu ≡ (mu * lambda) * mu
    rearranged = Ring.solve-∀ lambda mu
  in
  trans rearranged
    (trans
      (cong (_* mu) reciprocal)
      (Ring.solve-∀ mu))

normalizedDegreeOneResidualHalves : ∀ shell →
  normalizedDegreeOneResidualScale (suc shell)
  ≡ Dyadic.half * normalizedDegreeOneResidualScale shell
normalizedDegreeOneResidualHalves shell =
  trans
    (normalizedDegreeOneResidualIsInverseShell (suc shell))
    (trans
      (Dyadic.successorInverseDyadicScale shell)
      (cong (Dyadic.half *_)
        (sym (normalizedDegreeOneResidualIsInverseShell shell))))
  where
  open import Relation.Binary.PropositionalEquality using (sym)

record DegreeOneResidualEnvelope : Set where
  constructor degree-one-residual-envelope
  field
    coefficient : ℚ
    shell : Nat

open DegreeOneResidualEnvelope public

unnormalizedResidualEnvelope : DegreeOneResidualEnvelope → ℚ
unnormalizedResidualEnvelope envelope =
  coefficient envelope * degreeOneTransferScale (shell envelope)

viscouslyNormalizedResidualEnvelope : DegreeOneResidualEnvelope → ℚ
viscouslyNormalizedResidualEnvelope envelope =
  coefficient envelope * normalizedDegreeOneResidualScale (shell envelope)

normalizedEnvelopeHasExactInverseShellPayment : ∀ envelope →
  viscouslyNormalizedResidualEnvelope envelope
  ≡ coefficient envelope * Dyadic.inverseDyadicScale (shell envelope)
normalizedEnvelopeHasExactInverseShellPayment envelope =
  cong (coefficient envelope *_)
    (normalizedDegreeOneResidualIsInverseShell (shell envelope))

round88StandardLaplacianBeatsDegreeOneShellGrowthByOnePower : Bool
round88StandardLaplacianBeatsDegreeOneShellGrowthByOnePower = true

round88DyadicModelTheoremImportedAsLiteralNSProof : Bool
round88DyadicModelTheoremImportedAsLiteralNSProof = false

round88TaoEnergyIdentityAlonePromotedToRegularity : Bool
round88TaoEnergyIdentityAlonePromotedToRegularity = false

round88StandardLaplacianBeatsDegreeOneShellGrowthByOnePowerIsTrue :
  round88StandardLaplacianBeatsDegreeOneShellGrowthByOnePower ≡ true
round88StandardLaplacianBeatsDegreeOneShellGrowthByOnePowerIsTrue = refl

round88DyadicModelTheoremImportedAsLiteralNSProofIsFalse :
  round88DyadicModelTheoremImportedAsLiteralNSProof ≡ false
round88DyadicModelTheoremImportedAsLiteralNSProofIsFalse = refl
