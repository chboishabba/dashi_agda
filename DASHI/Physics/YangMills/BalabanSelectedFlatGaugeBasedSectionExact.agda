module DASHI.Physics.YangMills.BalabanSelectedFlatGaugeBasedSectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Construct a literal based section of the *flat* three-component constant
-- gauge-multiplier quotient.  For each su(2) component subtract its value at
-- one distinguished periodic site.  This gives a canonical representative
-- with zero value at the base site, proves the section is idempotent and
-- unique inside each constant-shift class, and proves the actual selected
-- identity-background gauge transpose is unchanged by this replacement.
--
-- This is deliberately a flat-anchor theorem.  It does not assume that the
-- same three constant directions remain redundant at a noncentral background;
-- the Round-42 holonomy guard proves that such a background-independent
-- trivialization is false.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath4PhysicalFibreMatchExact as Indices
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint

GaugeMultiplier : Set
GaugeMultiplier = FlatAdjoint.GaugeMultiplier

baseSite : Periodic.Site4
baseSite =
  pair (pair Indices.index0 Indices.index0)
    (pair Indices.index0 Indices.index0)

componentBaseValue :
  GaugeMultiplier → Coordinates.LieCoordinate3 → ℚ
componentBaseValue multiplier coordinate =
  multiplier (pair coordinate baseSite)

basedRepresentative : GaugeMultiplier → GaugeMultiplier
basedRepresentative multiplier (pair coordinate site) =
  multiplier (pair coordinate site) - componentBaseValue multiplier coordinate

BasedGaugeMultiplier : GaugeMultiplier → Set
BasedGaugeMultiplier multiplier =
  ∀ coordinate → multiplier (pair coordinate baseSite) ≡ 0ℚ

basedRepresentativeAtBase : ∀ multiplier coordinate →
  basedRepresentative multiplier (pair coordinate baseSite) ≡ 0ℚ
basedRepresentativeAtBase multiplier coordinate = ℚRing.solve-∀

basedRepresentativeIsBased : ∀ multiplier →
  BasedGaugeMultiplier (basedRepresentative multiplier)
basedRepresentativeIsBased multiplier = basedRepresentativeAtBase multiplier

record FlatConstantGaugeEquivalent
    (left right : GaugeMultiplier) : Set where
  constructor flatConstantGaugeEquivalent
  field
    constantShift : Coordinates.LieCoordinate3 → ℚ
    pointwiseShift : ∀ coordinate site →
      right (pair coordinate site)
      ≡ left (pair coordinate site) + constantShift coordinate

open FlatConstantGaugeEquivalent public

flatConstantGaugeEquivalentRefl : ∀ multiplier →
  FlatConstantGaugeEquivalent multiplier multiplier
flatConstantGaugeEquivalentRefl multiplier =
  flatConstantGaugeEquivalent
    (λ _ → 0ℚ)
    (λ coordinate site → sym (ℚRing.solve-∀))

flatConstantGaugeEquivalentSym : ∀ {left right} →
  FlatConstantGaugeEquivalent left right →
  FlatConstantGaugeEquivalent right left
flatConstantGaugeEquivalentSym {left} {right} equivalent =
  flatConstantGaugeEquivalent
    (λ coordinate → - constantShift equivalent coordinate)
    (λ coordinate site →
      let shifted = pointwiseShift equivalent coordinate site
      in trans
        (sym
          (cong
            (λ value → value - constantShift equivalent coordinate)
            shifted))
        (ℚRing.solve-∀
          (left (pair coordinate site))
          (constantShift equivalent coordinate)))

flatConstantGaugeEquivalentTrans : ∀ {first middle last} →
  FlatConstantGaugeEquivalent first middle →
  FlatConstantGaugeEquivalent middle last →
  FlatConstantGaugeEquivalent first last
flatConstantGaugeEquivalentTrans firstMiddle middleLast =
  flatConstantGaugeEquivalent
    (λ coordinate →
      constantShift firstMiddle coordinate
      + constantShift middleLast coordinate)
    (λ coordinate site →
      trans
        (pointwiseShift middleLast coordinate site)
        (trans
          (cong
            (_+ constantShift middleLast coordinate)
            (pointwiseShift firstMiddle coordinate site))
          (ℚRing.solve-∀
            (FlatConstantGaugeEquivalent.constantShift firstMiddle coordinate)
            (FlatConstantGaugeEquivalent.constantShift middleLast coordinate)
            _)))

originalEquivalentToBased : ∀ multiplier →
  FlatConstantGaugeEquivalent multiplier (basedRepresentative multiplier)
originalEquivalentToBased multiplier =
  flatConstantGaugeEquivalent
    (λ coordinate → - componentBaseValue multiplier coordinate)
    (λ coordinate site →
      ℚRing.solve-∀
        (multiplier (pair coordinate site))
        (componentBaseValue multiplier coordinate))

basedRepresentativeIdempotentPointwise : ∀ multiplier coordinate site →
  basedRepresentative (basedRepresentative multiplier) (pair coordinate site)
  ≡ basedRepresentative multiplier (pair coordinate site)
basedRepresentativeIdempotentPointwise multiplier coordinate site =
  let
    baseZero = basedRepresentativeAtBase multiplier coordinate
  in
  trans
    (cong
      (λ base →
        basedRepresentative multiplier (pair coordinate site) - base)
      baseZero)
    (ℚRing.solve-∀
      (basedRepresentative multiplier (pair coordinate site)))

basedRepresentativeUniqueInClass :
  ∀ original candidate →
  BasedGaugeMultiplier candidate →
  FlatConstantGaugeEquivalent original candidate →
  ∀ coordinate site →
  candidate (pair coordinate site)
  ≡ basedRepresentative original (pair coordinate site)
basedRepresentativeUniqueInClass
    original candidate candidateBased equivalent coordinate site =
  let
    shift = constantShift equivalent coordinate
    originalBase = componentBaseValue original coordinate

    atBase :
      candidate (pair coordinate baseSite)
      ≡ originalBase + shift
    atBase = pointwiseShift equivalent coordinate baseSite

    candidateZero : candidate (pair coordinate baseSite) ≡ 0ℚ
    candidateZero = candidateBased coordinate

    shiftExact : shift ≡ - originalBase
    shiftExact =
      let
        sumZero : originalBase + shift ≡ 0ℚ
        sumZero = trans (sym atBase) candidateZero
      in
      trans
        (sym (ℚRing.solve-∀ originalBase shift))
        (cong (λ total → total - originalBase) sumZero)
  in
  trans
    (pointwiseShift equivalent coordinate site)
    (trans
      (cong
        (original (pair coordinate site) +_)
        shiftExact)
      (ℚRing.solve-∀
        (original (pair coordinate site)) originalBase))

basedRepresentativeForwardDifferenceExact :
  ∀ multiplier coordinate axis site →
  Periodic.forwardDifference axis
    (FlatAdjoint.multiplierField (basedRepresentative multiplier) coordinate)
    site
  ≡ Periodic.forwardDifference axis
    (FlatAdjoint.multiplierField multiplier coordinate) site
basedRepresentativeForwardDifferenceExact multiplier coordinate axis site =
  ℚRing.solve-∀
    (multiplier
      (pair coordinate (Periodic.shiftForward axis site)))
    (multiplier (pair coordinate site))
    (componentBaseValue multiplier coordinate)

flatNegativeGradientStateBasedInvariant :
  ∀ multiplier selected →
  FlatAdjoint.flatNegativeGradientState (basedRepresentative multiplier) selected
  ≡ FlatAdjoint.flatNegativeGradientState multiplier selected
flatNegativeGradientStateBasedInvariant multiplier
    (pair coordinate (pair axis site)) =
  cong -_
    (basedRepresentativeForwardDifferenceExact
      multiplier coordinate axis site)

actualFlatGaugeAdjointBasedInvariant :
  ∀ multiplier selected →
  FlatAdjoint.actualFlatGaugeAdjoint (basedRepresentative multiplier) selected
  ≡ FlatAdjoint.actualFlatGaugeAdjoint multiplier selected
actualFlatGaugeAdjointBasedInvariant multiplier selected =
  trans
    (FlatAdjoint.actualFlatGaugeAdjointPointwiseExact
      (basedRepresentative multiplier) selected)
    (trans
      (flatNegativeGradientStateBasedInvariant multiplier selected)
      (sym
        (FlatAdjoint.actualFlatGaugeAdjointPointwiseExact
          multiplier selected)))

selectedFlatGaugeBasedSectionLevel : ProofLevel
selectedFlatGaugeBasedSectionLevel = machineChecked

selectedFlatGaugeBasedRepresentativeUniquenessLevel : ProofLevel
selectedFlatGaugeBasedRepresentativeUniquenessLevel = machineChecked

selectedFlatGaugeAdjointBasedInvarianceLevel : ProofLevel
selectedFlatGaugeAdjointBasedInvarianceLevel = machineChecked
