module DASHI.Physics.Closure.NSTriadKNComBandwidthOnePreYoungRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Issai Schur.
-- Classical row/column test for integral and matrix operators; no DOI is
-- assigned to the historical theorem used here.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Once common-hat support makes the physical shell graph bandwidth one, the
-- owner route no longer needs generic Cotlar summability. Round 48 proves
--
--   17/64 + 2(65/512) = 133/256 < 1,
--
-- leaving the exact row complement 123/256.  The only load-bearing
-- Hilbert-space theorem retained here is that the literal odd P/Q action has
-- squared output bounded by its physical bandwidth-one row mass times the
-- critical energy. The existing mixed Young endpoint then makes Com soft.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _-_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active
import DASHI.Physics.Closure.NSTriadKNComThreeChannelRowMassRound48Exact as Row
import DASHI.Physics.Closure.NSTriadKNComRowMassYoungSoftRound48Exact as SoftRow
import DASHI.Physics.Closure.NSTriadKNHHGoodYoungSoftTaxRound45Exact as Soft

rowComplement : ℚ
rowComplement = Int.+ 123 / 256

rowComplementExact : 1ℚ - Row.threeChannelTarget ≡ rowComplement
rowComplementExact = solve []

record PhysicalBandwidthOneComEndpoint
    (environment : Owner.TaxEnvironment)
    (skeleton : Active.PhysicalOddPQSupportSkeleton)
    (identification : Active.PhysicalOddPQHatIdentification skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    (shell : Nat) : Set where
  field
    production oddOutputNorm inputNorm dataRemainder : ℚ

    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment
    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment

    physicalComPairingEndpoint :
      production ≤ oddOutputNorm * inputNorm + dataRemainder

    physicalOddOutputSquareBelowDissipation :
      L2.square oddOutputNorm ≤ Owner.dissipation environment

    physicalBandwidthOneSchur :
      L2.square inputNorm
      ≤ Row.physicalThreeChannelRowMass skeleton shell
        * Owner.integralCritical environment

open PhysicalBandwidthOneComEndpoint public

asRound48RowMixedEndpoint :
  ∀ {environment skeleton identification bounds shell} →
  PhysicalBandwidthOneComEndpoint
    environment skeleton identification bounds shell →
  SoftRow.PhysicalComRowMixedEndpoint
    environment skeleton identification bounds shell
asRound48RowMixedEndpoint physical = record
  { production = production physical
  ; leftFactor = oddOutputNorm physical
  ; rightFactor = inputNorm physical
  ; dataRemainder = dataRemainder physical
  ; dissipationNonnegative = dissipationNonnegative physical
  ; criticalNonnegative = criticalNonnegative physical
  ; productionBelowMixed = physicalComPairingEndpoint physical
  ; leftSquareBelowDissipation = physicalOddOutputSquareBelowDissipation physical
  ; rightSquareBelowPhysicalRowMassCritical = physicalBandwidthOneSchur physical
  }

physicalComYoungSoftFromBandwidthOneSchur :
  ∀ {environment skeleton identification bounds shell} →
  PhysicalBandwidthOneComEndpoint
    environment skeleton identification bounds shell →
  Soft.YoungSoftOwnerFamily environment Tax.Com
physicalComYoungSoftFromBandwidthOneSchur physical =
  SoftRow.physicalComYoungSoftFromThreeChannelRow
    (asRound48RowMixedEndpoint physical)

bandwidthOneRowTarget : ℚ
bandwidthOneRowTarget = Row.threeChannelTarget

bandwidthOneRowTargetExact :
  bandwidthOneRowTarget ≡ Row.threeChannelTarget
bandwidthOneRowTargetExact = refl

bandwidthOneComReductionClosed : Bool
bandwidthOneComReductionClosed = true

physicalBandwidthOneSchurConstructed : Bool
physicalBandwidthOneSchurConstructed = false

bandwidthOneComReductionClosedIsTrue : bandwidthOneComReductionClosed ≡ true
bandwidthOneComReductionClosedIsTrue = refl

physicalBandwidthOneSchurConstructedIsFalse : physicalBandwidthOneSchurConstructed ≡ false
physicalBandwidthOneSchurConstructedIsFalse = refl
