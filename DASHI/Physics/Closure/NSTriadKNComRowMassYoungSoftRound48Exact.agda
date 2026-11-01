module DASHI.Physics.Closure.NSTriadKNComRowMassYoungSoftRound48Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Once the physical common-hat and same/adjacent estimates are available,
-- Round 48 proves the active Com row mass is at most 133/256.  This module
-- identifies the weakest remaining pre-Young endpoint that would classify Com
-- as soft:
--
--   P_Com <= x y + A,
--   x^2 <= D,
--   y^2 <= rowMass_q X.
--
-- Since rowMass_q <= 133/256, the existing Round-47 Young theorem applies with
-- an explicit cutoff-uniform critical coefficient 133/256.  The coefficient
-- is not a viscosity floor: epsilon remains freely selectable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active
import DASHI.Physics.Closure.NSTriadKNComThreeChannelRowMassRound48Exact as Row
import DASHI.Physics.Closure.NSTriadKNMixedCriticalYoungSoftRound47Exact as Mixed
import DASHI.Physics.Closure.NSTriadKNHHGoodYoungSoftTaxRound45Exact as Soft

threeChannelTargetNonnegative : 0ℚ ≤ Row.threeChannelTarget
threeChannelTargetNonnegative =
  toWitness {a? = 0ℚ ≤? Row.threeChannelTarget} _

record PhysicalComRowMixedEndpoint
    (environment : Owner.TaxEnvironment)
    (skeleton : Active.PhysicalOddPQSupportSkeleton)
    (identification : Active.PhysicalOddPQHatIdentification skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    (shell : Nat) : Set where
  field
    production leftFactor rightFactor dataRemainder : ℚ

    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment
    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment

    productionBelowMixed :
      production ≤ leftFactor * rightFactor + dataRemainder

    leftSquareBelowDissipation :
      L2.square leftFactor ≤ Owner.dissipation environment

    rightSquareBelowPhysicalRowMassCritical :
      L2.square rightFactor
      ≤ Row.physicalThreeChannelRowMass skeleton shell
        * Owner.integralCritical environment

open PhysicalComRowMixedEndpoint public

rightSquareBelowThreeChannelTargetCritical :
  ∀ {environment skeleton identification bounds shell}
    (physical : PhysicalComRowMixedEndpoint
      environment skeleton identification bounds shell) →
  L2.square (rightFactor physical)
  ≤ Row.threeChannelTarget * Owner.integralCritical environment
rightSquareBelowThreeChannelTargetCritical
    {environment} {skeleton} {bounds = bounds} {shell} physical =
  let
    rowBelow :
      Row.physicalThreeChannelRowMass skeleton shell
      ≤ Row.threeChannelTarget
    rowBelow = Row.physicalThreeChannelRowMassBelowTarget bounds shell

    scaled :
      Row.physicalThreeChannelRowMass skeleton shell
        * Owner.integralCritical environment
      ≤ Row.threeChannelTarget * Owner.integralCritical environment
    scaled =
      let instance criticalNNI = nonNegative (criticalNonnegative physical)
      in ℚP.*-monoʳ-≤-nonNeg
        (Owner.integralCritical environment) rowBelow
  in
  ℚP.≤-trans
    (rightSquareBelowPhysicalRowMassCritical physical)
    scaled

asMixedCriticalPreAbsorption :
  ∀ {environment skeleton identification bounds shell} →
  PhysicalComRowMixedEndpoint
    environment skeleton identification bounds shell →
  Mixed.MixedCriticalPreAbsorption environment Tax.Com
asMixedCriticalPreAbsorption physical = record
  { production = production physical
  ; leftFactor = leftFactor physical
  ; rightFactor = rightFactor physical
  ; dataRemainder = dataRemainder physical
  ; baseCriticalCoefficient = Row.threeChannelTarget
  ; dissipationNonnegative = dissipationNonnegative physical
  ; criticalNonnegative = criticalNonnegative physical
  ; baseCriticalCoefficientNonnegative = threeChannelTargetNonnegative
  ; productionBelowMixed = productionBelowMixed physical
  ; leftSquareBelowDissipation = leftSquareBelowDissipation physical
  ; rightSquareBelowCritical =
      rightSquareBelowThreeChannelTargetCritical physical
  }

physicalComYoungSoftFromThreeChannelRow :
  ∀ {environment skeleton identification bounds shell} →
  PhysicalComRowMixedEndpoint
    environment skeleton identification bounds shell →
  Soft.YoungSoftOwnerFamily environment Tax.Com
physicalComYoungSoftFromThreeChannelRow physical =
  Mixed.comYoungSoftFromMixedEndpoint
    (asMixedCriticalPreAbsorption physical)

comThreeChannelMixedEndpointImpliesYoungSoft : Bool
comThreeChannelMixedEndpointImpliesYoungSoft = true

physicalComRowMixedEndpointConstructed : Bool
physicalComRowMixedEndpointConstructed = false

comThreeChannelMixedEndpointImpliesYoungSoftIsTrue :
  comThreeChannelMixedEndpointImpliesYoungSoft ≡ true
comThreeChannelMixedEndpointImpliesYoungSoftIsTrue = refl

physicalComRowMixedEndpointConstructedIsFalse :
  physicalComRowMixedEndpointConstructed ≡ false
physicalComRowMixedEndpointConstructedIsFalse = refl
