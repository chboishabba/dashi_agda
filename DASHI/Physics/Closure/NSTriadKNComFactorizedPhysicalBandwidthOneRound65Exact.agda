module DASHI.Physics.Closure.NSTriadKNComFactorizedPhysicalBandwidthOneRound65Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- DOI: no DOI assigned to the cited historical conference article.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 65 / B DOWNSTREAM CLOSURE
--
-- Once an active physical pair is realized as a same-carrier factorized Gram
-- cell whose INTERNAL overlap obeys the six-three gap, no further analytic
-- theorem is needed to obtain the historical same/adjacent constants and the
-- bandwidth-one 133/256 bound.
--
-- This module performs that complete same-carrier composition.  It converts a
-- physical factorized source into the existing ordered physical majorant source
-- and reuses the already-proved 17/64 + 65/512 + 65/512 = 133/256 arithmetic.
--
-- Thus the remaining B producer is now sharply upstream:
--   literal dominant-hat annular row
--     -> active PhysicalSixThreeGramCell.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Ordered
import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as Targets
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact as Aggregate
import DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalMajorantRound62Exact as Majorant
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree
import DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalGramFactorizationRound65Exact as Gram

sameGapExact : SixThree.twoBranchSquaredGap zero ≡ Targets.sameShellTarget
sameGapExact = solve []

adjacentGapExact :
  SixThree.twoBranchSquaredGap (suc zero) ≡ Targets.adjacentShellTarget
adjacentGapExact = solve []

record FactorizedPhysicalOddPQSource
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (O : Ordered.OrderedRealExtension (LP.realField model))
    (M : Gram.NonnegativeMultiplicativeOrder O)
    (R : Majorant.OrderedRationalEmbedding O) : Set (lsuc r) where
  field
    support : Hat.PhysicalOddPQCommonHatIdentification
    shellDistance : Nat → Nat → Nat
    physicalPairProduct : Nat → Nat → C3.Carrier (LP.realField model)

    pairProductNonnegative : ∀ q s →
      Ordered._≤_ O (C3.zero (LP.realField model))
        (physicalPairProduct q s)

    inactivePairProductZero : ∀ q s →
      Hat.supportActive support q s ≡ false →
      physicalPairProduct q s ≡ C3.zero (LP.realField model)

    activeFactorizedCell : ∀ q s →
      Hat.supportActive support q s ≡ true →
      Gram.PhysicalSixThreeGramCell O M R (shellDistance q s)

    activePairProductExact : ∀ q s →
      (active : Hat.supportActive support q s ≡ true) →
      physicalPairProduct q s
      ≡ Gram.pairProduct
          (Gram.factorized (activeFactorizedCell q s active))

    sameShellDistance : ∀ q → shellDistance q q ≡ zero
    forwardAdjacentDistance : ∀ q →
      shellDistance q (suc q) ≡ suc zero
    reverseAdjacentDistance : ∀ q →
      shellDistance (suc q) q ≡ suc zero

open FactorizedPhysicalOddPQSource public

activePairBelowEmbeddedGap :
  ∀ {r model O M R}
    (source : FactorizedPhysicalOddPQSource {r} model O M R)
    q s
    (active : Hat.supportActive (support source) q s ≡ true) →
  Ordered._≤_ O
    (physicalPairProduct source q s)
    (Majorant.embed R (SixThree.twoBranchSquaredGap (shellDistance source q s)))
activePairBelowEmbeddedGap {O = O} source q s active =
  subst
    (λ left → Ordered._≤_ O left
      (Majorant.embed _
        (SixThree.twoBranchSquaredGap (shellDistance source q s))))
    (sym (activePairProductExact source q s active))
    (Gram.physicalPairProductBelowSixThree
      (activeFactorizedCell source q s active))

sameActiveBound :
  ∀ {r model O M R}
    (source : FactorizedPhysicalOddPQSource {r} model O M R)
    q →
  Hat.supportActive (support source) q q ≡ true →
  Ordered._≤_ O
    (physicalPairProduct source q q)
    (Majorant.embed R Targets.sameShellTarget)
sameActiveBound source q active
  rewrite sameShellDistance source q
        | sameGapExact =
  activePairBelowEmbeddedGap source q q active

forwardActiveBound :
  ∀ {r model O M R}
    (source : FactorizedPhysicalOddPQSource {r} model O M R)
    q →
  Hat.supportActive (support source) q (suc q) ≡ true →
  Ordered._≤_ O
    (physicalPairProduct source q (suc q))
    (Majorant.embed R Targets.adjacentShellTarget)
forwardActiveBound source q active
  rewrite forwardAdjacentDistance source q
        | adjacentGapExact =
  activePairBelowEmbeddedGap source q (suc q) active

reverseActiveBound :
  ∀ {r model O M R}
    (source : FactorizedPhysicalOddPQSource {r} model O M R)
    q →
  Hat.supportActive (support source) (suc q) q ≡ true →
  Ordered._≤_ O
    (physicalPairProduct source (suc q) q)
    (Majorant.embed R Targets.adjacentShellTarget)
reverseActiveBound source q active
  rewrite reverseAdjacentDistance source q
        | adjacentGapExact =
  activePairBelowEmbeddedGap source (suc q) q active

factorizedSourceToOrderedPhysicalMajorant :
  ∀ {r model O M R} →
  FactorizedPhysicalOddPQSource {r} model O M R →
  Majorant.OrderedPhysicalNormalizedOddPQSource model O R
factorizedSourceToOrderedPhysicalMajorant source = record
  { Majorant.OrderedPhysicalNormalizedOddPQSource.support = support source
  ; Majorant.OrderedPhysicalNormalizedOddPQSource.normalizedPhysicalEnergy =
      physicalPairProduct source
  ; Majorant.OrderedPhysicalNormalizedOddPQSource.energyNonnegative =
      pairProductNonnegative source
  ; Majorant.OrderedPhysicalNormalizedOddPQSource.inactiveEnergyZero =
      inactivePairProductZero source
  ; Majorant.OrderedPhysicalNormalizedOddPQSource.sameShellActiveBound =
      sameActiveBound source
  ; Majorant.OrderedPhysicalNormalizedOddPQSource.forwardAdjacentActiveBound =
      forwardActiveBound source
  ; Majorant.OrderedPhysicalNormalizedOddPQSource.reverseAdjacentActiveBound =
      reverseActiveBound source
  }

factorizedBandwidthOneBelow133Over256 :
  ∀ {r model O M R}
    (source : FactorizedPhysicalOddPQSource {r} model O M R)
    q →
  Ordered._≤_ O
    (Majorant.bandwidthOnePhysicalEnergy
      (factorizedSourceToOrderedPhysicalMajorant source) q)
    (Majorant.embed R Aggregate.bandwidthOneTarget)
factorizedBandwidthOneBelow133Over256 source q =
  Majorant.bandwidthOnePhysicalEnergyBelow133Over256
    (factorizedSourceToOrderedPhysicalMajorant source) q

round65FactorizedSixThreeClosesPhysicalBandwidthOne : Bool
round65FactorizedSixThreeClosesPhysicalBandwidthOne = true

round65FactorizedSixThreeClosesPhysicalBandwidthOneIsTrue :
  round65FactorizedSixThreeClosesPhysicalBandwidthOne ≡ true
round65FactorizedSixThreeClosesPhysicalBandwidthOneIsTrue = refl
