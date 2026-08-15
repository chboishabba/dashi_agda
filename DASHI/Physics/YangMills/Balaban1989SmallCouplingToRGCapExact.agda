module DASHI.Physics.YangMills.Balaban1989SmallCouplingToRGCapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- SOURCE STATUS
--
-- The complete-density theorem is conditional on the effective couplings
-- staying in a sufficiently small interval.  That hypothesis is enough for the
-- one-step coupling-cap field of Gate 4; one must not strengthen this transport
-- into a claim that CMP109/CMP122 prove the missing positive beta calculation.
--
-- DASHI CONTRIBUTION
--
-- If the source coupling at every scale is <= gamma, and the repository RG
-- coupling coordinate is literally that source coupling with a cap >= gamma,
-- then coupling-domain preservation is immediate.  This isolates the actual
-- hard issue correctly: constructing the required small-coupling history, not
-- reproving cap preservation after the history is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

record SourceSmallCouplingRGDictionary
    (parameters : RG.YM4RGRegionParameters)
    (stateAt : Nat → RG.YM4RGState) : Set where
  field
    sourceCoupling : Nat → ℚ
    gamma : ℚ

    sourceCouplingSmall : ∀ scale → sourceCoupling scale ≤ gamma
    gammaInsideRepositoryCap : gamma ≤ RG.couplingCap parameters

    repositoryCouplingMeaning : ∀ scale →
      RG.runningCoupling (stateAt scale) ≡ sourceCoupling scale

open SourceSmallCouplingRGDictionary public

sourceSmallCouplingGivesRepositoryCap :
  ∀ {parameters stateAt}
    (dictionary : SourceSmallCouplingRGDictionary parameters stateAt)
    scale →
  RG.runningCoupling (stateAt scale) ≤ RG.couplingCap parameters
sourceSmallCouplingGivesRepositoryCap dictionary scale
  rewrite repositoryCouplingMeaning dictionary scale =
  ℚP.≤-trans
    (sourceCouplingSmall dictionary scale)
    (gammaInsideRepositoryCap dictionary)

sourceSmallCouplingGivesNextRepositoryCap :
  ∀ {parameters stateAt}
    (dictionary : SourceSmallCouplingRGDictionary parameters stateAt)
    scale →
  RG.runningCoupling (stateAt (Agda.Builtin.Nat.suc scale))
  ≤ RG.couplingCap parameters
sourceSmallCouplingGivesNextRepositoryCap dictionary scale =
  sourceSmallCouplingGivesRepositoryCap dictionary
    (Agda.Builtin.Nat.suc scale)

balabanSmallCouplingHypothesisAuthorityLevel : ProofLevel
balabanSmallCouplingHypothesisAuthorityLevel = standardImported

balabanSmallCouplingToRGCapTransportLevel : ProofLevel
balabanSmallCouplingToRGCapTransportLevel = machineChecked

-- Genuine remaining coupling theorem: produce the all-scale source coupling
-- history in the required interval.  CMP109 explicitly defers the perturbative
-- analysis intended to establish the stronger running-coupling theorem.
balabanPhysicalSmallCouplingHistoryLevel : ProofLevel
balabanPhysicalSmallCouplingHistoryLevel = conditional
