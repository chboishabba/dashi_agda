module DASHI.Physics.Closure.NSTriadKNComSquaredEndpointRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Issai Schur.
-- Classical row/column operator test; no DOI assigned to the historical
-- theorem used here.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 53 resolves the square-root ambiguity left by the coexistence of the
-- Gram/Cotlar and bandwidth-one Schur lanes.  The constants
--
--   17/64, 65/512, 65/512
--
-- sum to 133/256 as a ROW-MASS / SQUARED-NORM coefficient.  The actual Round-49
-- consumer already asks for
--
--   inputNorm^2 <= physicalRowMass * integralCritical.
--
-- Hence, once the literal bandwidth-one Schur theorem is supplied, the exact
-- endpoint is
--
--   inputNorm^2 <= (133/256) integralCritical.
--
-- No square root is required in the subsequent mixed Young estimate.  What is
-- invalid is only re-reading an abstract Gram pairProduct as an UNSQUARED
-- shell-block norm with the same numerical constant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active
import DASHI.Physics.Closure.NSTriadKNComThreeChannelRowMassRound48Exact as Row
import DASHI.Physics.Closure.NSTriadKNComBandwidthOnePreYoungRound49Exact as PreYoung

physicalComSquaredEndpointAt133Over256 :
  ∀ {environment skeleton identification bounds shell} →
  (physical : PreYoung.PhysicalBandwidthOneComEndpoint
    environment skeleton identification bounds shell) →
  L2.square (PreYoung.inputNorm physical)
  ≤ Row.threeChannelTarget * Owner.integralCritical environment
physicalComSquaredEndpointAt133Over256
    {environment} {skeleton} {bounds = bounds} {shell} physical =
  let
    rowBelow :
      Row.physicalThreeChannelRowMass skeleton shell ≤ Row.threeChannelTarget
    rowBelow = Row.physicalThreeChannelRowMassBelowTarget bounds shell

    criticalNN = PreYoung.criticalNonnegative physical

    scaled :
      Row.physicalThreeChannelRowMass skeleton shell
        * Owner.integralCritical environment
      ≤ Row.threeChannelTarget * Owner.integralCritical environment
    scaled =
      let instance criticalNNI = nonNegative criticalNN
      in ℚP.*-monoʳ-≤-nonNeg
        (Owner.integralCritical environment)
        rowBelow
  in
  ℚP.≤-trans
    (PreYoung.physicalBandwidthOneSchur physical)
    scaled

com133Over256LivesAtSquaredEndpoint : Bool
com133Over256LivesAtSquaredEndpoint = true

physicalBandwidthOneSchurStillRequired : Bool
physicalBandwidthOneSchurStillRequired = true

com133Over256LivesAtSquaredEndpointIsTrue :
  com133Over256LivesAtSquaredEndpoint ≡ true
com133Over256LivesAtSquaredEndpointIsTrue = refl
