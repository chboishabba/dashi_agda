module DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointMatrixExact where

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
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- Build the flat gauge-divergence matrix directly on the source-faithful
-- L=13 carriers:
--
--   rows    = {x,y,z} x sites(13^4),
--   columns = {x,y,z} x axes(4) x sites(13^4).
--
-- Hence the state carrier has exactly 3*4*13^4=342732 coordinates.  The
-- matrix is literal incidence: a row receives +1 from the current endpoint
-- and -1 from the forward endpoint.  Exact finite Kronecker selection proves
-- its transpose is the negative periodic forward gradient, component by
-- component, and therefore its squared norm is exactly the periodic gradient
-- energy.  No side-four matrix or cardinality transfer is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalSU2RationalMatrixCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13

------------------------------------------------------------------------
-- Periodic successor on an arbitrary finite cyclic index and its L=13 site
-- action.  This is the same literal positive step convention used by the
-- repository's periodic side-four lane, generalized without changing carrier.
------------------------------------------------------------------------

cyclicNext : ∀ {n} → CyclicIndex (suc n) → CyclicIndex (suc n)
cyclicNext {zero} zeroᵢ = zeroᵢ
cyclicNext {suc n} zeroᵢ = sucᵢ zeroᵢ
cyclicNext {suc n} (sucᵢ index) with cyclicNext {n} index
... | zeroᵢ = zeroᵢ
... | sucᵢ next = sucᵢ (sucᵢ next)

shiftForward13 :
  Axis4 → PhysicalBlockL Side13.side13 → PhysicalBlockL Side13.side13
shiftForward13 zeroᵢ (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (cyclicNext x0) x1) (pair x2 x3)
shiftForward13 (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (cyclicNext x1)) (pair x2 x3)
shiftForward13 (sucᵢ (sucᵢ zeroᵢ))
    (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (cyclicNext x2) x3)
shiftForward13 (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (cyclicNext x3))

------------------------------------------------------------------------
-- Exact L=13 row enumeration.
------------------------------------------------------------------------

GaugeRow13 : Set
GaugeRow13 = Product Physical.LieCoordinate3 (PhysicalBlockL Side13.side13)

GaugeMultiplier13 : Set
GaugeMultiplier13 = GaugeRow13 → ℚ

State13 : Set
State13 = Physical.PhysicalSU2Coordinate Side13.side13

StateVector13 : Set
StateVector13 = State13 → ℚ

gaugeRowFinite13 : FiniteEnumeration GaugeRow13
gaugeRowFinite13 =
  productFinite Coordinates.lieCoordinateFinite
    (periodicTorus4Finite Side13.side13)

gaugeRows13 : List GaugeRow13
gaugeRows13 = elements gaugeRowFinite13

gaugeRowDecidableEquality13 : DecidableEquality GaugeRow13
gaugeRowDecidableEquality13 =
  productDecidableEquality
    Coordinates.lieCoordinateDecidableEquality
    (periodicTorus4DecidableEquality Side13.side13)

gaugeRows13DuplicateFree : DuplicateFree gaugeRows13
gaugeRows13DuplicateFree =
  cartesianDuplicateFree
    Coordinates.lieCoordinatesDuplicateFree
    (Coordinates.siteElementsDuplicateFree Side13.side13)

gaugeRowDelta13 : GaugeRow13 → GaugeRow13 → ℚ
gaugeRowDelta13 = Coordinates.kroneckerDelta gaugeRowDecidableEquality13

gaugeRowSelectorExact : ∀ target multiplier →
  sumRational gaugeRows13
    (λ row → gaugeRowDelta13 target row * multiplier row)
  ≡ multiplier target
gaugeRowSelectorExact target multiplier =
  Coordinates.deltaSumIdentity
    gaugeRowDecidableEquality13
    gaugeRows13DuplicateFree
    target
    (complete gaugeRowFinite13 target)
    multiplier

------------------------------------------------------------------------
-- Literal incidence matrix and transpose action.
------------------------------------------------------------------------

flatGaugeConstraintMatrix13 : GaugeRow13 → State13 → ℚ
flatGaugeConstraintMatrix13 row
    (pair coordinate (pair axis site)) =
  gaugeRowDelta13 (pair coordinate site) row
  - gaugeRowDelta13 (pair coordinate (shiftForward13 axis site)) row

flatGaugeAdjoint13 : GaugeMultiplier13 → StateVector13
flatGaugeAdjoint13 multiplier column =
  sumRational gaugeRows13
    (λ row → flatGaugeConstraintMatrix13 row column * multiplier row)

multiplierField13 :
  GaugeMultiplier13 → Physical.LieCoordinate3 →
  PhysicalBlockL Side13.side13 → ℚ
multiplierField13 multiplier coordinate site =
  multiplier (pair coordinate site)

forwardDifference13 :
  Axis4 → (PhysicalBlockL Side13.side13 → ℚ) →
  PhysicalBlockL Side13.side13 → ℚ
forwardDifference13 axis field site =
  field (shiftForward13 axis site) - field site

flatGaugeAdjointPointwiseExact :
  ∀ multiplier coordinate axis site →
  flatGaugeAdjoint13 multiplier (pair coordinate (pair axis site))
  ≡ - forwardDifference13 axis (multiplierField13 multiplier coordinate) site
flatGaugeAdjointPointwiseExact multiplier coordinate axis site =
  let
    current = pair coordinate site
    forward = pair coordinate (shiftForward13 axis site)

    splitProducts :
      sumRational gaugeRows13
        (λ row →
          (gaugeRowDelta13 current row - gaugeRowDelta13 forward row)
          * multiplier row)
      ≡ sumRational gaugeRows13
          (λ row → gaugeRowDelta13 current row * multiplier row
            - gaugeRowDelta13 forward row * multiplier row)
    splitProducts =
      sumRationalCong gaugeRows13 _ _
        (λ row → ℚRing.solve-∀
          (gaugeRowDelta13 current row)
          (gaugeRowDelta13 forward row)
          (multiplier row))

    splitSum :
      sumRational gaugeRows13
          (λ row → gaugeRowDelta13 current row * multiplier row
            - gaugeRowDelta13 forward row * multiplier row)
      ≡ sumRational gaugeRows13
          (λ row → gaugeRowDelta13 current row * multiplier row)
        - sumRational gaugeRows13
          (λ row → gaugeRowDelta13 forward row * multiplier row)
    splitSum =
      sumRationalSubtract gaugeRows13
        (λ row → gaugeRowDelta13 current row * multiplier row)
        (λ row → gaugeRowDelta13 forward row * multiplier row)
  in
  trans splitProducts
    (trans splitSum
      (trans
        (cong₂ _-_
          (gaugeRowSelectorExact current multiplier)
          (gaugeRowSelectorExact forward multiplier))
        (ℚRing.solve-∀
          (multiplier current) (multiplier forward))))

------------------------------------------------------------------------
-- Exact transpose norm = periodic L=13 gradient energy.
------------------------------------------------------------------------

periodicComponentGradientEnergy13 :
  GaugeMultiplier13 → Physical.LieCoordinate3 → ℚ
periodicComponentGradientEnergy13 multiplier coordinate =
  sumRational (Physical.physicalBondCells Side13.side13)
    (λ { (pair axis site) →
      sq (forwardDifference13 axis
        (multiplierField13 multiplier coordinate) site) })

periodicGaugeGradientEnergy13 : GaugeMultiplier13 → ℚ
periodicGaugeGradientEnergy13 multiplier =
  sumRational Physical.lieCoordinates3
    (periodicComponentGradientEnergy13 multiplier)

flatGaugeAdjointNormSq13 : GaugeMultiplier13 → ℚ
flatGaugeAdjointNormSq13 multiplier =
  Physical.physicalSU2CoordinateNormSq (flatGaugeAdjoint13 multiplier)

componentAdjointNormExact13 : ∀ multiplier coordinate →
  sumRational (Physical.physicalBondCells Side13.side13)
    (λ cell → sq (flatGaugeAdjoint13 multiplier (pair coordinate cell)))
  ≡ periodicComponentGradientEnergy13 multiplier coordinate
componentAdjointNormExact13 multiplier coordinate =
  sumRationalCong (Physical.physicalBondCells Side13.side13) _ _
    (λ { (pair axis site) →
      trans
        (cong sq
          (flatGaugeAdjointPointwiseExact multiplier coordinate axis site))
        (ℚRing.solve-∀
          (forwardDifference13 axis
            (multiplierField13 multiplier coordinate) site)) })

flatGaugeAdjointNormExact13 : ∀ multiplier →
  flatGaugeAdjointNormSq13 multiplier
  ≡ periodicGaugeGradientEnergy13 multiplier
flatGaugeAdjointNormExact13 multiplier =
  trans
    (sumCartesian
      Physical.lieCoordinates3
      (Physical.physicalBondCells Side13.side13)
      (λ coordinate → sq (flatGaugeAdjoint13 multiplier coordinate)))
    (sumRationalCong Physical.lieCoordinates3 _ _
      (componentAdjointNormExact13 multiplier))

flatGaugeL13LiteralMatrixLevel : ProofLevel
flatGaugeL13LiteralMatrixLevel = machineChecked

flatGaugeL13AdjointGradientIdentificationLevel : ProofLevel
flatGaugeL13AdjointGradientIdentificationLevel = machineChecked

flatGaugeL13SameCarrierNormLevel : ProofLevel
flatGaugeL13SameCarrierNormLevel = machineChecked
