module DASHI.Physics.YangMills.BalabanSelectedGaugeReducedLinearClosureExact where

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
-- Record the proof-relevant linear closure of the literal componentwise
-- mean-zero gauge quotient.  This is needed by the Schur reconstruction:
-- reduced sources, projected residuals and their differences must remain in
-- the SAME `FlatGaugeReducedMultiplier` carrier, not only be pointwise equal
-- to some centered representative.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedGaugeCenteringLinearityExact as Linear

GaugeMultiplier = FlatFloor.GaugeMultiplier

meanZeroRespectsPointwise :
  ∀ {left right : GaugeMultiplier} →
  (∀ row → left row ≡ right row) →
  FlatFloor.FlatGaugeReducedMultiplier right →
  FlatFloor.FlatGaugeReducedMultiplier left
meanZeroRespectsPointwise {left} {right} pointwise reduced = record
  { FlatFloor.FlatGaugeReducedMultiplier.coordinateXMeanZero =
      transport Coordinates.coordinateX
        (FlatFloor.coordinateXMeanZero reduced)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateYMeanZero =
      transport Coordinates.coordinateY
        (FlatFloor.coordinateYMeanZero reduced)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateZMeanZero =
      transport Coordinates.coordinateZ
        (FlatFloor.coordinateZMeanZero reduced)
  }
  where
  transport : ∀ coordinate →
    (∀ site →
      GlobalAverage.average0123
        (FlatFloor.gaugeMultiplierField right coordinate) site ≡ 0ℚ) →
    ∀ site →
      GlobalAverage.average0123
        (FlatFloor.gaugeMultiplierField left coordinate) site ≡ 0ℚ
  transport coordinate rightZero site =
    trans
      (GlobalAverage.average0123EqualsGlobalMean
        (FlatFloor.gaugeMultiplierField left coordinate) site)
      (trans
        (cong (GlobalAverage.oneTwoFiftySix *_)
          (Periodic.sumSitesCong
            (FlatFloor.gaugeMultiplierField left coordinate)
            (FlatFloor.gaugeMultiplierField right coordinate)
            (λ current → pointwise (Torus.pair coordinate current))))
        (trans
          (sym
            (GlobalAverage.average0123EqualsGlobalMean
              (FlatFloor.gaugeMultiplierField right coordinate) site))
          (rightZero site)))

reducedAdd :
  ∀ left right →
  FlatFloor.FlatGaugeReducedMultiplier left →
  FlatFloor.FlatGaugeReducedMultiplier right →
  FlatFloor.FlatGaugeReducedMultiplier (Linear.addMultiplier left right)
reducedAdd left right leftReduced rightReduced = record
  { FlatFloor.FlatGaugeReducedMultiplier.coordinateXMeanZero =
      close Coordinates.coordinateX
        (FlatFloor.coordinateXMeanZero leftReduced)
        (FlatFloor.coordinateXMeanZero rightReduced)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateYMeanZero =
      close Coordinates.coordinateY
        (FlatFloor.coordinateYMeanZero leftReduced)
        (FlatFloor.coordinateYMeanZero rightReduced)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateZMeanZero =
      close Coordinates.coordinateZ
        (FlatFloor.coordinateZMeanZero leftReduced)
        (FlatFloor.coordinateZMeanZero rightReduced)
  }
  where
  close : ∀ coordinate →
    (∀ site → GlobalAverage.average0123
      (FlatFloor.gaugeMultiplierField left coordinate) site ≡ 0ℚ) →
    (∀ site → GlobalAverage.average0123
      (FlatFloor.gaugeMultiplierField right coordinate) site ≡ 0ℚ) →
    ∀ site → GlobalAverage.average0123
      (FlatFloor.gaugeMultiplierField (Linear.addMultiplier left right) coordinate)
      site ≡ 0ℚ
  close coordinate leftZero rightZero site =
    trans
      (GlobalAverage.average0123EqualsGlobalMean _ site)
      (trans
        (cong (GlobalAverage.oneTwoFiftySix *_)
          (Periodic.sumSitesAdd
            (FlatFloor.gaugeMultiplierField left coordinate)
            (FlatFloor.gaugeMultiplierField right coordinate)))
        (trans
          (ℚRing.solve-∀
            (Periodic.sumSites (FlatFloor.gaugeMultiplierField left coordinate))
            (Periodic.sumSites (FlatFloor.gaugeMultiplierField right coordinate)))
          (trans
            (cong₂ _+_
              (sym (GlobalAverage.average0123EqualsGlobalMean
                (FlatFloor.gaugeMultiplierField left coordinate) site))
              (sym (GlobalAverage.average0123EqualsGlobalMean
                (FlatFloor.gaugeMultiplierField right coordinate) site)))
            (trans
              (cong₂ _+_ (leftZero site) (rightZero site))
              (ℚRing.solve [])))))

reducedSubtract :
  ∀ left right →
  FlatFloor.FlatGaugeReducedMultiplier left →
  FlatFloor.FlatGaugeReducedMultiplier right →
  FlatFloor.FlatGaugeReducedMultiplier (Linear.subtractMultiplier left right)
reducedSubtract left right leftReduced rightReduced = record
  { FlatFloor.FlatGaugeReducedMultiplier.coordinateXMeanZero =
      close Coordinates.coordinateX
        (FlatFloor.coordinateXMeanZero leftReduced)
        (FlatFloor.coordinateXMeanZero rightReduced)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateYMeanZero =
      close Coordinates.coordinateY
        (FlatFloor.coordinateYMeanZero leftReduced)
        (FlatFloor.coordinateYMeanZero rightReduced)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateZMeanZero =
      close Coordinates.coordinateZ
        (FlatFloor.coordinateZMeanZero leftReduced)
        (FlatFloor.coordinateZMeanZero rightReduced)
  }
  where
  close : ∀ coordinate →
    (∀ site → GlobalAverage.average0123
      (FlatFloor.gaugeMultiplierField left coordinate) site ≡ 0ℚ) →
    (∀ site → GlobalAverage.average0123
      (FlatFloor.gaugeMultiplierField right coordinate) site ≡ 0ℚ) →
    ∀ site → GlobalAverage.average0123
      (FlatFloor.gaugeMultiplierField
        (Linear.subtractMultiplier left right) coordinate) site ≡ 0ℚ
  close coordinate leftZero rightZero site =
    trans
      (GlobalAverage.average0123EqualsGlobalMean _ site)
      (trans
        (cong (GlobalAverage.oneTwoFiftySix *_)
          (Periodic.sumSitesSubtract
            (FlatFloor.gaugeMultiplierField left coordinate)
            (FlatFloor.gaugeMultiplierField right coordinate)))
        (trans
          (ℚRing.solve-∀
            (Periodic.sumSites (FlatFloor.gaugeMultiplierField left coordinate))
            (Periodic.sumSites (FlatFloor.gaugeMultiplierField right coordinate)))
          (trans
            (cong₂ _-_
              (sym (GlobalAverage.average0123EqualsGlobalMean
                (FlatFloor.gaugeMultiplierField left coordinate) site))
              (sym (GlobalAverage.average0123EqualsGlobalMean
                (FlatFloor.gaugeMultiplierField right coordinate) site)))
            (trans
              (cong₂ _-_ (leftZero site) (rightZero site))
              (ℚRing.solve [])))))

reducedScale :
  ∀ coefficient multiplier →
  FlatFloor.FlatGaugeReducedMultiplier multiplier →
  FlatFloor.FlatGaugeReducedMultiplier (Linear.scaleMultiplier coefficient multiplier)
reducedScale coefficient multiplier reduced = record
  { FlatFloor.FlatGaugeReducedMultiplier.coordinateXMeanZero =
      close Coordinates.coordinateX (FlatFloor.coordinateXMeanZero reduced)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateYMeanZero =
      close Coordinates.coordinateY (FlatFloor.coordinateYMeanZero reduced)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateZMeanZero =
      close Coordinates.coordinateZ (FlatFloor.coordinateZMeanZero reduced)
  }
  where
  close : ∀ coordinate →
    (∀ site → GlobalAverage.average0123
      (FlatFloor.gaugeMultiplierField multiplier coordinate) site ≡ 0ℚ) →
    ∀ site → GlobalAverage.average0123
      (FlatFloor.gaugeMultiplierField
        (Linear.scaleMultiplier coefficient multiplier) coordinate) site ≡ 0ℚ
  close coordinate zero site =
    trans
      (GlobalAverage.average0123EqualsGlobalMean _ site)
      (trans
        (cong (GlobalAverage.oneTwoFiftySix *_)
          (Periodic.sumSitesScale coefficient
            (FlatFloor.gaugeMultiplierField multiplier coordinate)))
        (trans
          (ℚRing.solve-∀ coefficient
            (Periodic.sumSites (FlatFloor.gaugeMultiplierField multiplier coordinate)))
          (trans
            (cong (coefficient *_)
              (sym (GlobalAverage.average0123EqualsGlobalMean
                (FlatFloor.gaugeMultiplierField multiplier coordinate) site)))
            (trans (cong (coefficient *_) (zero site)) (ℚRing.solve [])))))

selectedGaugeReducedLinearClosureLevel : ProofLevel
selectedGaugeReducedLinearClosureLevel = machineChecked
