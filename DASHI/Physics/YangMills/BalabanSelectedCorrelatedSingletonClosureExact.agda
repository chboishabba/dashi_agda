module DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Assemble the corrected selected-variation sign with the pair-indexed Green
-- owner ledger.  After exact cancellation and before positive majorisation,
-- the canonical residual
--
--   RawLocalization - <Lg,K+Lw>
--
-- is bounded by 55/18874368 times the plaquette cross charge.  Stationarity
-- then gives the literal singleton curvature lower bound with the correct
-- reflected sign.  This is the terminal algebraic reducer for Gate I; the
-- selected-background atom estimates remain explicit producer data.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; -_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedGreenAtomOwnershipExact as Ownership

record CorrelatedSingletonClosureData : Set₁ where
  field
    family : Ownership.CorrelatedGreenAtomFamily
    charge : ℚ
    singleton rawLocalization multiplierPairing : ℚ

    chargeNonnegative : 0ℚ ≤ charge

    exactCancellation :
      Ownership.ExactCorrelatedCancellation family

    ownerBudgets :
      Ownership.CorrelatedOwnerBudgets family charge
        Selector.remainingSingletonCoefficient

    residualRepresentationExact :
      Sign.canonicalProjectedSpillover
        rawLocalization multiplierPairing
      ≡ Ownership.correlatedResidualTotal family

    selectedStationarity :
      singleton
        + Sign.canonicalProjectedSpillover
            rawLocalization multiplierPairing
      ≡ 0ℚ

open CorrelatedSingletonClosureData public

correlatedResidualUpper :
  ∀ data →
  Sign.canonicalProjectedSpillover
    (rawLocalization data) (multiplierPairing data)
  ≤ Selector.remainingSingletonCoefficient * charge data
correlatedResidualUpper data =
  let
    survivingUpper =
      Ownership.survivingCorrelatedOwnersCloseBudget
        (chargeNonnegative data) (ownerBudgets data)

    totalUpper :
      Ownership.correlatedResidualTotal (family data)
      ≤ Selector.remainingSingletonCoefficient * charge data
    totalUpper =
      subst
        (λ lower → lower
          ≤ Selector.remainingSingletonCoefficient * charge data)
        (sym
          (Ownership.exactCorrelatedCancellationRemovedBeforeMajorisation
            (exactCancellation data)))
        survivingUpper
  in
  subst
    (λ lower → lower
      ≤ Selector.remainingSingletonCoefficient * charge data)
    (sym (residualRepresentationExact data))
    totalUpper

selectedCorrelatedSingletonLower :
  ∀ data →
  - (Selector.remainingSingletonCoefficient * charge data)
  ≤ singleton data
selectedCorrelatedSingletonLower data =
  Sign.singletonBudgetTargetExact
    (singleton data)
    (rawLocalization data)
    (multiplierPairing data)
    Selector.remainingSingletonCoefficient
    (charge data)
    (selectedStationarity data)
    (correlatedResidualUpper data)

record CorrelatedSingletonPhysicalAuthority : Set₁ where
  field
    closureData : CorrelatedSingletonClosureData
    rawLocalizationComesFromLiteralWilsonExpansion : Set
    multiplierPairingComesFromSelectedKKTGreen : Set
    pairOwnersCarryD4OrientationAndCollarDisplacement : Set

open CorrelatedSingletonPhysicalAuthority public

correlatedSingletonClosureLevel : ProofLevel
correlatedSingletonClosureLevel = machineChecked

selectedCorrelatedSingletonPhysicalAuthorityProducerLevel : ProofLevel
selectedCorrelatedSingletonPhysicalAuthorityProducerLevel = conditional
