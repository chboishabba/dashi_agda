module DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hermann Weyl,
-- "The Classical Groups: Their Invariants and Representations",
-- Princeton University Press, 1939/1946. No DOI assigned.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Turn the geometric orbit counts into the exact finite arithmetic consumed by
-- the one-loop interval certificate.  If a certified lower contribution is
-- constant on the full B4 geometric classes, the 240-term sum is exactly
--
--     64 L1 + 96 L2 + 64 L3 + 16 L4.
--
-- If only the fixed-external-axis stabilizer is available, the safe seven-term
-- formula is
--
--     48 L01 + 48 L02 + 16 L03
--   + 16 L10 + 48 L11 + 48 L12 + 16 L13.
--
-- Thus the implementation does not force the stronger 240->4 reduction when
-- a fixed external momentum only justifies 240->7.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit

sixtyFour ninetySix sixteen fortyEight : ℚ
sixtyFour = + 64 / 1
ninetySix = + 96 / 1
sixteen = + 16 / 1
fortyEight = + 48 / 1

record FourOrbitValues : Set where
  constructor fourOrbitValues
  field
    rank1Value rank2Value rank3Value rank4Value : ℚ
open FourOrbitValues public

fourOrbitValueAt : FourOrbitValues → Grid.GridCell4 → ℚ
fourOrbitValueAt values cell with Orbit.geometricOrbit cell
... | Orbit.infrared = 0ℚ
... | Orbit.rank1 = rank1Value values
... | Orbit.rank2 = rank2Value values
... | Orbit.rank3 = rank3Value values
... | Orbit.rank4 = rank4Value values

fourOrbitWeightedSum : FourOrbitValues → ℚ
fourOrbitWeightedSum values =
  sixtyFour * rank1Value values
  + ninetySix * rank2Value values
  + sixtyFour * rank3Value values
  + sixteen * rank4Value values

fourOrbitRegularSumExact : ∀ values →
  Sums.sumRational Grid.regularGridCells (fourOrbitValueAt values)
  ≡ fourOrbitWeightedSum values
fourOrbitRegularSumExact (fourOrbitValues l1 l2 l3 l4) =
  ℚRing.solve-∀ l1 l2 l3 l4

record SevenOrbitValues : Set where
  constructor sevenOrbitValues
  field
    a0t1Value a0t2Value a0t3Value
      a1t0Value a1t1Value a1t2Value a1t3Value : ℚ
open SevenOrbitValues public

sevenOrbitValueAt : SevenOrbitValues → Grid.GridCell4 → ℚ
sevenOrbitValueAt values cell with Orbit.axis0Orbit cell
... | Orbit.a0t0 = 0ℚ
... | Orbit.a0t1 = a0t1Value values
... | Orbit.a0t2 = a0t2Value values
... | Orbit.a0t3 = a0t3Value values
... | Orbit.a1t0 = a1t0Value values
... | Orbit.a1t1 = a1t1Value values
... | Orbit.a1t2 = a1t2Value values
... | Orbit.a1t3 = a1t3Value values

sevenOrbitWeightedSum : SevenOrbitValues → ℚ
sevenOrbitWeightedSum values =
  fortyEight * a0t1Value values
  + fortyEight * a0t2Value values
  + sixteen * a0t3Value values
  + sixteen * a1t0Value values
  + fortyEight * a1t1Value values
  + fortyEight * a1t2Value values
  + sixteen * a1t3Value values

sevenOrbitRegularSumExact : ∀ values →
  Sums.sumRational Grid.regularGridCells (sevenOrbitValueAt values)
  ≡ sevenOrbitWeightedSum values
sevenOrbitRegularSumExact
  (sevenOrbitValues l01 l02 l03 l10 l11 l12 l13) =
  ℚRing.solve-∀ l01 l02 l03 l10 l11 l12 l13

record FourOrbitIntervalCertificate : Set where
  field
    lowerContribution : FourOrbitValues
    quadratureLoss : ℚ
    positiveMargin : ℚ
    marginExact :
      positiveMargin ≡ fourOrbitWeightedSum lowerContribution + (0ℚ - quadratureLoss)
open FourOrbitIntervalCertificate public

record SevenOrbitIntervalCertificate : Set where
  field
    lowerContribution : SevenOrbitValues
    quadratureLoss : ℚ
    positiveMargin : ℚ
    marginExact :
      positiveMargin ≡ sevenOrbitWeightedSum lowerContribution + (0ℚ - quadratureLoss)
open SevenOrbitIntervalCertificate public

fourOrbitFiniteSumReductionLevel : ProofLevel
fourOrbitFiniteSumReductionLevel = machineChecked

sevenOrbitFiniteSumReductionLevel : ProofLevel
sevenOrbitFiniteSumReductionLevel = machineChecked

-- Physical source leaves: prove that the literal box lower contributions and
-- quadrature losses can be represented by one of these orbit data structures.
-- Once that is done the 240-cell summation itself is no longer a proof burden.
literalFourOrbitBoxCertificateLevel : ProofLevel
literalFourOrbitBoxCertificateLevel = conditional

literalFixedAxisSevenOrbitBoxCertificateLevel : ProofLevel
literalFixedAxisSevenOrbitBoxCertificateLevel = conditional
