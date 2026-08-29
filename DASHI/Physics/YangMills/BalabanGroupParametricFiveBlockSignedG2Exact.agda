module DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact where

------------------------------------------------------------------------
-- ROUND69: GROUP-PARAMETRIC FIVE-BLOCK SIGNED G2 ABSORPTION
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Anthony W. Knapp,
-- "Lie Groups Beyond an Introduction", second edition, Birkhauser, 2002.
-- DOI: 10.1007/978-1-4757-2453-0.
--
-- DASHI CONTRIBUTION
--
-- The older five-block compiler was accidentally tied to the executable SU(2)
-- quaternion/KKT carrier even though its FINAL signed absorption argument uses
-- only five rational scalar estimates:
--
--   R_i <= r_i Q      (i=1..4),
--   g Q <= G_11,
--   r1+r2+r3+r4-g <= 55/18874368,
--   Q >= 0.
--
-- Extract that mathematics over an arbitrary compact-simple group equipped
-- with the repository's QuantitativeCompactLiePackage.  Group-specific work is
-- now exactly the source map that constructs these five scalars from the
-- group's literal selected-background variation/KKT/Green data.  The signed
-- absorption proof itself is no longer SU(2)-specific.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Compact
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record GroupParametricFiveBlockG2Data
    (LieElement GroupElement : Set)
    (G : Compact.CompactSimpleLieGroup) : Set₁ where
  field
    quantitativeLiePackage :
      Compact.QuantitativeCompactLiePackage ℚ LieElement GroupElement G

    Configuration : Set
    InCertifiedRegion : Configuration → Set

    charge raw1 raw2 raw3 raw4 green11 : Configuration → ℚ
    chargeNonnegative : ∀ configuration →
      InCertifiedRegion configuration → 0ℚ ≤ charge configuration

    raw1Ratio raw2Ratio raw3Ratio raw4Ratio green11LowerRatio : ℚ

    raw1RelativeSound : ∀ configuration → InCertifiedRegion configuration →
      raw1 configuration ≤ raw1Ratio * charge configuration
    raw2RelativeSound : ∀ configuration → InCertifiedRegion configuration →
      raw2 configuration ≤ raw2Ratio * charge configuration
    raw3RelativeSound : ∀ configuration → InCertifiedRegion configuration →
      raw3 configuration ≤ raw3Ratio * charge configuration
    raw4RelativeSound : ∀ configuration → InCertifiedRegion configuration →
      raw4 configuration ≤ raw4Ratio * charge configuration

    green11RelativeLowerSound : ∀ configuration → InCertifiedRegion configuration →
      green11LowerRatio * charge configuration ≤ green11 configuration

    fiveBlockCoefficientFits :
      raw1Ratio + raw2Ratio + raw3Ratio + raw4Ratio - green11LowerRatio
      ≤ Selector.remainingSingletonCoefficient

open GroupParametricFiveBlockG2Data public

signedResidual :
  ∀ {LieElement GroupElement G} →
  GroupParametricFiveBlockG2Data LieElement GroupElement G →
  Configuration → ℚ
signedResidual dataSet configuration =
  raw1 dataSet configuration + raw2 dataSet configuration
  + raw3 dataSet configuration + raw4 dataSet configuration
  - green11 dataSet configuration

fiveBlockRatio :
  ∀ {LieElement GroupElement G} →
  GroupParametricFiveBlockG2Data LieElement GroupElement G → ℚ
fiveBlockRatio dataSet =
  raw1Ratio dataSet + raw2Ratio dataSet
  + raw3Ratio dataSet + raw4Ratio dataSet
  - green11LowerRatio dataSet

signedResidualBelowFiveBlockRatio :
  ∀ {LieElement GroupElement G}
    (dataSet : GroupParametricFiveBlockG2Data LieElement GroupElement G)
    configuration → InCertifiedRegion dataSet configuration →
  signedResidual dataSet configuration
  ≤ fiveBlockRatio dataSet * charge dataSet configuration
signedResidualBelowFiveBlockRatio dataSet configuration inRegion =
  let
    q = charge dataSet configuration
    r1 = raw1RelativeSound dataSet configuration inRegion
    r2 = raw2RelativeSound dataSet configuration inRegion
    r3 = raw3RelativeSound dataSet configuration inRegion
    r4 = raw4RelativeSound dataSet configuration inRegion
    g = green11RelativeLowerSound dataSet configuration inRegion

    summed = ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤ r1 r2)
          r3)
        r4)
      (ℚP.neg-mono-≤ g)
  in
  subst
    (λ left → left ≤ fiveBlockRatio dataSet * q)
    (ℚRing.solve-∀
      (raw1 dataSet configuration)
      (raw2 dataSet configuration)
      (raw3 dataSet configuration)
      (raw4 dataSet configuration)
      (green11 dataSet configuration))
    (subst
      (λ right →
        raw1 dataSet configuration + raw2 dataSet configuration
        + raw3 dataSet configuration + raw4 dataSet configuration
        + (- green11 dataSet configuration) ≤ right)
      (ℚRing.solve-∀
        (raw1Ratio dataSet) (raw2Ratio dataSet)
        (raw3Ratio dataSet) (raw4Ratio dataSet)
        (green11LowerRatio dataSet) q)
      summed)

fiveBlockRatioBelowRemainingCoefficient :
  ∀ {LieElement GroupElement G}
    (dataSet : GroupParametricFiveBlockG2Data LieElement GroupElement G) →
  fiveBlockRatio dataSet ≤ Selector.remainingSingletonCoefficient
fiveBlockRatioBelowRemainingCoefficient dataSet =
  fiveBlockCoefficientFits dataSet

groupParametricSignedG2Absorbed :
  ∀ {LieElement GroupElement G}
    (dataSet : GroupParametricFiveBlockG2Data LieElement GroupElement G)
    configuration → InCertifiedRegion dataSet configuration →
  signedResidual dataSet configuration
  ≤ Selector.remainingSingletonCoefficient * charge dataSet configuration
groupParametricSignedG2Absorbed dataSet configuration inRegion =
  let
    q = charge dataSet configuration
    first = signedResidualBelowFiveBlockRatio dataSet configuration inRegion
    scaled = Norm.scaleNonnegative q
      (chargeNonnegative dataSet configuration inRegion)
      (fiveBlockRatioBelowRemainingCoefficient dataSet)
    second :
      fiveBlockRatio dataSet * q
      ≤ Selector.remainingSingletonCoefficient * q
    second =
      subst
        (λ left → left ≤ Selector.remainingSingletonCoefficient * q)
        (ℚRing.solve-∀ q (fiveBlockRatio dataSet))
        (subst
          (λ right → q * fiveBlockRatio dataSet ≤ right)
          (ℚRing.solve-∀ q Selector.remainingSingletonCoefficient)
          scaled)
  in
  ℚP.≤-trans first second

groupParametricFiveBlockSignedG2CompilerLevel : ProofLevel
groupParametricFiveBlockSignedG2CompilerLevel = machineChecked

-- Remaining L1 physical theorem, now correctly group-parametric:
-- for arbitrary G and QuantitativeCompactLiePackage G, construct the literal
-- selected-background/KKT/Mobius/Green source map whose five scalar projections
-- satisfy the fields above.  No SU(2)-to-all-groups promotion is permitted.
physicalGroupParametricFiveBlockSourceMapLevel : ProofLevel
physicalGroupParametricFiveBlockSourceMapLevel = conditional
