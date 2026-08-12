module DASHI.Physics.YangMills.BalabanPath13ZeroMeanFibrePoincareExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Convert the division-free centered Path13 certificate into the ordinary
-- zero-mean fibre inequality needed by the four-axis martingale proof.  When a
-- physical length-13 fibre has sum zero, scaled centering is exactly 13 times
-- the field, so both norm and open-edge energy acquire the common factor 169.
-- We prove the two exact rescaling identities and cancel the strictly positive
-- rational factor, obtaining
--
--       (1/18) ||f||_fibre^2 <= E_fibre(f).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_; _/_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as Generated
import DASHI.Physics.YangMills.BalabanPath13PhysicalFibreMatchExact as Physical13

side13 : Agda.Builtin.Nat.Nat
side13 = 13

oneHundredSixtyNine : ℚ
oneHundredSixtyNine = + 169 / 1

scale13SquareExact : sq (natAsRational side13) ≡ oneHundredSixtyNine
scale13SquareExact = ℚRing.solve []

instance
  oneHundredSixtyNinePositive : Positive oneHundredSixtyNine
  oneHundredSixtyNinePositive = ℚP.normalize-pos 169 1

zeroMeanScaledNormExact :
  ∀ field axis transverse →
  physicalFibreSum field axis transverse ≡ 0ℚ →
  scaledCenteredFibreNormSq field axis transverse
  ≡ oneHundredSixtyNine * physicalFibreNormSq field axis transverse
zeroMeanScaledNormExact field axis transverse meanZero =
  trans
    (scaledCenteredFibreNormExact field axis transverse)
    (trans
      (cong
        (λ total →
          sq (natAsRational side13) * physicalFibreNormSq field axis transverse
          - natAsRational side13 * sq total)
        meanZero)
      (trans
        (cong
          (λ coefficient →
            coefficient * physicalFibreNormSq field axis transverse
            - natAsRational side13 * sq 0ℚ)
          scale13SquareExact)
        (ℚRing.solve-∀
          (physicalFibreNormSq field axis transverse))))

scaledEnergy169Exact :
  ∀ field axis transverse →
  scaledCenteredFibreEdgeEnergy field axis transverse
  ≡ oneHundredSixtyNine * physicalFibreEdgeEnergy field axis transverse
scaledEnergy169Exact field axis transverse =
  trans
    (scaledCenteredFibreEnergyExact field axis transverse)
    (cong
      (λ coefficient → coefficient * physicalFibreEdgeEnergy field axis transverse)
      scale13SquareExact)

zeroMeanPhysicalFibrePoincare13 :
  ∀ field axis transverse →
  physicalFibreSum field axis transverse ≡ 0ℚ →
  Generated.oneEighteenth * physicalFibreNormSq field axis transverse
  ≤ physicalFibreEdgeEnergy field axis transverse
zeroMeanPhysicalFibrePoincare13 field axis transverse meanZero =
  let
    scaled = Physical13.physicalSide13FibrePoincare field axis transverse

    scaledRewritten :
      oneHundredSixtyNine
        * (Generated.oneEighteenth * physicalFibreNormSq field axis transverse)
      ≤ oneHundredSixtyNine * physicalFibreEdgeEnergy field axis transverse
    scaledRewritten =
      subst
        (λ left →
          left ≤ oneHundredSixtyNine * physicalFibreEdgeEnergy field axis transverse)
        (ℚRing.solve-∀
          Generated.oneEighteenth
          (physicalFibreNormSq field axis transverse)
          oneHundredSixtyNine)
        (subst
          (λ normValue →
            Generated.oneEighteenth * normValue
            ≤ oneHundredSixtyNine * physicalFibreEdgeEnergy field axis transverse)
          (sym (zeroMeanScaledNormExact field axis transverse meanZero))
          (subst
            (λ energyValue →
              Generated.oneEighteenth
                * scaledCenteredFibreNormSq field axis transverse
              ≤ energyValue)
            (sym (scaledEnergy169Exact field axis transverse))
            scaled))
  in
  ℚP.*-cancelˡ-≤-pos oneHundredSixtyNine scaledRewritten

path13ZeroMeanFibrePoincareLevel : ProofLevel
path13ZeroMeanFibrePoincareLevel = machineChecked
