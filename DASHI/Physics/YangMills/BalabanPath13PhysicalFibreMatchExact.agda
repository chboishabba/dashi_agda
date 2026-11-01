module DASHI.Physics.YangMills.BalabanPath13PhysicalFibreMatchExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; -_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as Generated

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson, "Matrix Analysis", 2nd ed., 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Consume the exact Path13 LDL certificate on the repository's literal
-- length-13 physical axis fibres.  Division-free centering supplies the
-- mean-zero relation; the thirteenth coordinate is therefore exactly the
-- generated dependent coordinate.  Literal list reductions identify the
-- physical fibre norm and open-edge energy with the generated certificate,
-- yielding
--
--       (1/18) ||f-centre(f)||^2 <= E_axis(f)
--
-- on every source-admissible L=13 axis fibre.
------------------------------------------------------------------------

thirteenSide : Nat
thirteenSide = 13

index0 : CyclicIndex thirteenSide
index0 = zeroᵢ
index1 : CyclicIndex thirteenSide
index1 = sucᵢ (zeroᵢ)
index2 : CyclicIndex thirteenSide
index2 = sucᵢ (sucᵢ (zeroᵢ))
index3 : CyclicIndex thirteenSide
index3 = sucᵢ (sucᵢ (sucᵢ (zeroᵢ)))
index4 : CyclicIndex thirteenSide
index4 = sucᵢ (sucᵢ (sucᵢ (sucᵢ (zeroᵢ))))
index5 : CyclicIndex thirteenSide
index5 = sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (zeroᵢ)))))
index6 : CyclicIndex thirteenSide
index6 = sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (zeroᵢ))))))
index7 : CyclicIndex thirteenSide
index7 = sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (zeroᵢ)))))))
index8 : CyclicIndex thirteenSide
index8 = sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (zeroᵢ))))))))
index9 : CyclicIndex thirteenSide
index9 = sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (zeroᵢ)))))))))
index10 : CyclicIndex thirteenSide
index10 = sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (zeroᵢ))))))))))
index11 : CyclicIndex thirteenSide
index11 = sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (zeroᵢ)))))))))))
index12 : CyclicIndex thirteenSide
index12 = sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ (zeroᵢ))))))))))))

physicalFibre13Coordinate :
  SiteField thirteenSide → Axis4 → Triple (CyclicIndex thirteenSide) →
  CyclicIndex thirteenSide → ℚ
physicalFibre13Coordinate field axis transverse =
  scaledCenteredFibreValue field axis transverse

path13CoordinatesFromPhysicalFibre :
  SiteField thirteenSide → Axis4 → Triple (CyclicIndex thirteenSide) →
  Generated.Path13Coordinates
path13CoordinatesFromPhysicalFibre field axis transverse =
  Generated.path13Coordinates
    (physicalFibre13Coordinate field axis transverse index0)
    (physicalFibre13Coordinate field axis transverse index1)
    (physicalFibre13Coordinate field axis transverse index2)
    (physicalFibre13Coordinate field axis transverse index3)
    (physicalFibre13Coordinate field axis transverse index4)
    (physicalFibre13Coordinate field axis transverse index5)
    (physicalFibre13Coordinate field axis transverse index6)
    (physicalFibre13Coordinate field axis transverse index7)
    (physicalFibre13Coordinate field axis transverse index8)
    (physicalFibre13Coordinate field axis transverse index9)
    (physicalFibre13Coordinate field axis transverse index10)
    (physicalFibre13Coordinate field axis transverse index11)

isolateThirteenthFromZero : ∀ a b c d e f g h i j k l m →
  a + (b + (c + (d + (e + (f + (g + (h + (i + (j + (k + (l + (m + (0ℚ))))))))))))) ≡ 0ℚ →
  m ≡ - (a + (b + (c + (d + (e + (f + (g + (h + (i + (j + (k + (l + (0ℚ)))))))))))))
isolateThirteenthFromZero a b c d e f g h i j k l m total =
  let
    isolate :
      m ≡ (a + (b + (c + (d + (e + (f + (g + (h + (i + (j + (k + (l + (m + (0ℚ)))))))))))))) - (a + (b + (c + (d + (e + (f + (g + (h + (i + (j + (k + (l + (0ℚ)))))))))))))
    isolate = ℚRing.solve-∀

    zeroReduction :
      0ℚ - (a + (b + (c + (d + (e + (f + (g + (h + (i + (j + (k + (l + (0ℚ)))))))))))))
      ≡ - (a + (b + (c + (d + (e + (f + (g + (h + (i + (j + (k + (l + (0ℚ)))))))))))))
    zeroReduction = ℚRing.solve-∀
  in
  trans isolate
    (trans
      (cong
        (λ value → value - (a + (b + (c + (d + (e + (f + (g + (h + (i + (j + (k + (l + (0ℚ))))))))))))))
        total)
      zeroReduction)

physicalThirteenthCoordinateIsGeneratedLast :
  ∀ field axis transverse →
  physicalFibre13Coordinate field axis transverse index12
  ≡ Generated.lastCoordinate
      (path13CoordinatesFromPhysicalFibre field axis transverse)
physicalThirteenthCoordinateIsGeneratedLast field axis transverse =
  isolateThirteenthFromZero
    (physicalFibre13Coordinate field axis transverse index0)
    (physicalFibre13Coordinate field axis transverse index1)
    (physicalFibre13Coordinate field axis transverse index2)
    (physicalFibre13Coordinate field axis transverse index3)
    (physicalFibre13Coordinate field axis transverse index4)
    (physicalFibre13Coordinate field axis transverse index5)
    (physicalFibre13Coordinate field axis transverse index6)
    (physicalFibre13Coordinate field axis transverse index7)
    (physicalFibre13Coordinate field axis transverse index8)
    (physicalFibre13Coordinate field axis transverse index9)
    (physicalFibre13Coordinate field axis transverse index10)
    (physicalFibre13Coordinate field axis transverse index11)
    (physicalFibre13Coordinate field axis transverse index12)
    (scaledCenteredFibreSumZero field axis transverse)

physicalFibre13NormExpansion :
  ∀ field axis transverse →
  scaledCenteredFibreNormSq field axis transverse
  ≡ sq (physicalFibre13Coordinate field axis transverse index0) + (sq (physicalFibre13Coordinate field axis transverse index1) + (sq (physicalFibre13Coordinate field axis transverse index2) + (sq (physicalFibre13Coordinate field axis transverse index3) + (sq (physicalFibre13Coordinate field axis transverse index4) + (sq (physicalFibre13Coordinate field axis transverse index5) + (sq (physicalFibre13Coordinate field axis transverse index6) + (sq (physicalFibre13Coordinate field axis transverse index7) + (sq (physicalFibre13Coordinate field axis transverse index8) + (sq (physicalFibre13Coordinate field axis transverse index9) + (sq (physicalFibre13Coordinate field axis transverse index10) + (sq (physicalFibre13Coordinate field axis transverse index11) + (sq (physicalFibre13Coordinate field axis transverse index12) + (0ℚ)))))))))))))
physicalFibre13NormExpansion field axis transverse = refl

physicalFibre13EnergyExpansion :
  ∀ field axis transverse →
  scaledCenteredFibreEdgeEnergy field axis transverse
  ≡ sqDiff (physicalFibre13Coordinate field axis transverse index1)
        (physicalFibre13Coordinate field axis transverse index0) + (sqDiff (physicalFibre13Coordinate field axis transverse index2)
        (physicalFibre13Coordinate field axis transverse index1) + (sqDiff (physicalFibre13Coordinate field axis transverse index3)
        (physicalFibre13Coordinate field axis transverse index2) + (sqDiff (physicalFibre13Coordinate field axis transverse index4)
        (physicalFibre13Coordinate field axis transverse index3) + (sqDiff (physicalFibre13Coordinate field axis transverse index5)
        (physicalFibre13Coordinate field axis transverse index4) + (sqDiff (physicalFibre13Coordinate field axis transverse index6)
        (physicalFibre13Coordinate field axis transverse index5) + (sqDiff (physicalFibre13Coordinate field axis transverse index7)
        (physicalFibre13Coordinate field axis transverse index6) + (sqDiff (physicalFibre13Coordinate field axis transverse index8)
        (physicalFibre13Coordinate field axis transverse index7) + (sqDiff (physicalFibre13Coordinate field axis transverse index9)
        (physicalFibre13Coordinate field axis transverse index8) + (sqDiff (physicalFibre13Coordinate field axis transverse index10)
        (physicalFibre13Coordinate field axis transverse index9) + (sqDiff (physicalFibre13Coordinate field axis transverse index11)
        (physicalFibre13Coordinate field axis transverse index10) + (sqDiff (physicalFibre13Coordinate field axis transverse index12)
        (physicalFibre13Coordinate field axis transverse index11) + (0ℚ))))))))))))
physicalFibre13EnergyExpansion field axis transverse = refl

physicalFibre13NormMatchesGenerated :
  ∀ field axis transverse →
  scaledCenteredFibreNormSq field axis transverse
  ≡ Generated.path13NormSq
      (path13CoordinatesFromPhysicalFibre field axis transverse)
physicalFibre13NormMatchesGenerated field axis transverse =
  trans
    (physicalFibre13NormExpansion field axis transverse)
    (subst
      (λ thirteenth →
        sq (physicalFibre13Coordinate field axis transverse index0) + (sq (physicalFibre13Coordinate field axis transverse index1) + (sq (physicalFibre13Coordinate field axis transverse index2) + (sq (physicalFibre13Coordinate field axis transverse index3) + (sq (physicalFibre13Coordinate field axis transverse index4) + (sq (physicalFibre13Coordinate field axis transverse index5) + (sq (physicalFibre13Coordinate field axis transverse index6) + (sq (physicalFibre13Coordinate field axis transverse index7) + (sq (physicalFibre13Coordinate field axis transverse index8) + (sq (physicalFibre13Coordinate field axis transverse index9) + (sq (physicalFibre13Coordinate field axis transverse index10) + (sq (physicalFibre13Coordinate field axis transverse index11) + (sq thirteenth + (0ℚ)))))))))))))
        ≡ Generated.path13NormSq
            (path13CoordinatesFromPhysicalFibre field axis transverse))
      (physicalThirteenthCoordinateIsGeneratedLast field axis transverse)
      (ℚRing.solve-∀))

physicalFibre13EnergyMatchesGenerated :
  ∀ field axis transverse →
  scaledCenteredFibreEdgeEnergy field axis transverse
  ≡ Generated.path13Energy
      (path13CoordinatesFromPhysicalFibre field axis transverse)
physicalFibre13EnergyMatchesGenerated field axis transverse =
  trans
    (physicalFibre13EnergyExpansion field axis transverse)
    (subst
      (λ thirteenth →
        sqDiff (physicalFibre13Coordinate field axis transverse index1) (physicalFibre13Coordinate field axis transverse index0) + (sqDiff (physicalFibre13Coordinate field axis transverse index2) (physicalFibre13Coordinate field axis transverse index1) + (sqDiff (physicalFibre13Coordinate field axis transverse index3) (physicalFibre13Coordinate field axis transverse index2) + (sqDiff (physicalFibre13Coordinate field axis transverse index4) (physicalFibre13Coordinate field axis transverse index3) + (sqDiff (physicalFibre13Coordinate field axis transverse index5) (physicalFibre13Coordinate field axis transverse index4) + (sqDiff (physicalFibre13Coordinate field axis transverse index6) (physicalFibre13Coordinate field axis transverse index5) + (sqDiff (physicalFibre13Coordinate field axis transverse index7) (physicalFibre13Coordinate field axis transverse index6) + (sqDiff (physicalFibre13Coordinate field axis transverse index8) (physicalFibre13Coordinate field axis transverse index7) + (sqDiff (physicalFibre13Coordinate field axis transverse index9) (physicalFibre13Coordinate field axis transverse index8) + (sqDiff (physicalFibre13Coordinate field axis transverse index10) (physicalFibre13Coordinate field axis transverse index9) + (sqDiff (physicalFibre13Coordinate field axis transverse index11) (physicalFibre13Coordinate field axis transverse index10) + (sqDiff thirteenth (physicalFibre13Coordinate field axis transverse index11) + (0ℚ))))))))))))
        ≡ Generated.path13Energy
            (path13CoordinatesFromPhysicalFibre field axis transverse))
      (physicalThirteenthCoordinateIsGeneratedLast field axis transverse)
      (ℚRing.solve-∀))

physicalSide13FibrePoincare :
  ∀ field axis transverse →
  Generated.oneEighteenth * scaledCenteredFibreNormSq field axis transverse
  ≤ scaledCenteredFibreEdgeEnergy field axis transverse
physicalSide13FibrePoincare field axis transverse =
  subst
    (λ energyValue →
      Generated.oneEighteenth
        * scaledCenteredFibreNormSq field axis transverse
      ≤ energyValue)
    (sym (physicalFibre13EnergyMatchesGenerated field axis transverse))
    (subst
      (λ normValue →
        Generated.oneEighteenth * normValue
        ≤ Generated.path13Energy
            (path13CoordinatesFromPhysicalFibre field axis transverse))
      (sym (physicalFibre13NormMatchesGenerated field axis transverse))
      (Generated.path13Poincare
        (path13CoordinatesFromPhysicalFibre field axis transverse)))

path13PhysicalFibreCoordinateMatchLevel : ProofLevel
path13PhysicalFibreCoordinateMatchLevel = machineChecked

path13PhysicalFibreEnergyMatchLevel : ProofLevel
path13PhysicalFibreEnergyMatchLevel = machineChecked

path13PhysicalFibrePoincareLevel : ProofLevel
path13PhysicalFibrePoincareLevel = machineChecked