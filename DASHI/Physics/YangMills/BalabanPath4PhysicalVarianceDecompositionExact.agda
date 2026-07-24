module DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanFourAxisMartingaleExact using
  (fourSquareSum; pairCrossSum; twoℚ; fourSquareExpansionRaw)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact

------------------------------------------------------------------------
-- Global Pythagoras identity for the four physical coordinate martingales.
------------------------------------------------------------------------

addField : SiteField side4 → SiteField side4 → SiteField side4
addField left right site = left site + right site

fourMartingaleSumField : SiteField side4 → SiteField side4
fourMartingaleSumField field site =
  martingaleField0 field site
  + (martingaleField1 field site
  + (martingaleField2 field site + martingaleField3 field site))

globalNormSq : SiteField side4 → ℚ
globalNormSq field = globalBlockInner field field

GlobalMeanZero4 : SiteField side4 → Set
GlobalMeanZero4 field = ∀ site → average0123 field site ≡ 0ℚ

fourMartingaleReconstructsPointwise :
  ∀ field → GlobalMeanZero4 field →
  FieldEqual (fourMartingaleSumField field) field
fourMartingaleReconstructsPointwise field meanZero site =
  fourAxisPhysicalMartingaleDecomposition field site (meanZero site)

globalNormRespectsPointwise :
  ∀ {left right} → FieldEqual left right →
  globalNormSq left ≡ globalNormSq right
globalNormRespectsPointwise {left} {right} equality =
  sumRationalCong
    (physicalBlockSites side4)
    (λ site → left site * left site)
    (λ site → right site * right site)
    (λ site → cong₂ _*_ (equality site) (equality site))

sumFourSquaresExact : ∀ field →
  sumRational (physicalBlockSites side4) (λ site →
    fourSquareSum
      (martingaleField0 field site)
      (martingaleField1 field site)
      (martingaleField2 field site)
      (martingaleField3 field site))
  ≡ globalNormSq (martingaleField0 field)
    + (globalNormSq (martingaleField1 field)
    + (globalNormSq (martingaleField2 field)
    + globalNormSq (martingaleField3 field)))
sumFourSquaresExact field =
  trans
    (sumRationalAdd
      (physicalBlockSites side4)
      (λ site → sq (martingaleField0 field site))
      (λ site →
        sq (martingaleField1 field site)
        + (sq (martingaleField2 field site)
        + sq (martingaleField3 field site))))
    (cong₂ _+_
      refl
      (trans
        (sumRationalAdd
          (physicalBlockSites side4)
          (λ site → sq (martingaleField1 field site))
          (λ site →
            sq (martingaleField2 field site)
            + sq (martingaleField3 field site)))
        (cong₂ _+_
          refl
          (sumRationalAdd
            (physicalBlockSites side4)
            (λ site → sq (martingaleField2 field site))
            (λ site → sq (martingaleField3 field site))))))

sumPairCrossExact : ∀ field →
  sumRational (physicalBlockSites side4) (λ site →
    pairCrossSum
      (martingaleField0 field site)
      (martingaleField1 field site)
      (martingaleField2 field site)
      (martingaleField3 field site))
  ≡ globalBlockInner (martingaleField0 field) (martingaleField1 field)
    + (globalBlockInner (martingaleField0 field) (martingaleField2 field)
    + (globalBlockInner (martingaleField0 field) (martingaleField3 field)
    + (globalBlockInner (martingaleField1 field) (martingaleField2 field)
    + (globalBlockInner (martingaleField1 field) (martingaleField3 field)
    + globalBlockInner (martingaleField2 field) (martingaleField3 field)))))
sumPairCrossExact field =
  trans
    (sumRationalAdd
      (physicalBlockSites side4)
      (λ site → martingaleField0 field site * martingaleField1 field site)
      (λ site →
        martingaleField0 field site * martingaleField2 field site
        + (martingaleField0 field site * martingaleField3 field site
        + (martingaleField1 field site * martingaleField2 field site
        + (martingaleField1 field site * martingaleField3 field site
        + martingaleField2 field site * martingaleField3 field site)))))
    (cong₂ _+_
      refl
      (trans
        (sumRationalAdd
          (physicalBlockSites side4)
          (λ site → martingaleField0 field site * martingaleField2 field site)
          (λ site →
            martingaleField0 field site * martingaleField3 field site
            + (martingaleField1 field site * martingaleField2 field site
            + (martingaleField1 field site * martingaleField3 field site
            + martingaleField2 field site * martingaleField3 field site))))
        (cong₂ _+_
          refl
          (trans
            (sumRationalAdd
              (physicalBlockSites side4)
              (λ site → martingaleField0 field site * martingaleField3 field site)
              (λ site →
                martingaleField1 field site * martingaleField2 field site
                + (martingaleField1 field site * martingaleField3 field site
                + martingaleField2 field site * martingaleField3 field site)))
            (cong₂ _+_
              refl
              (trans
                (sumRationalAdd
                  (physicalBlockSites side4)
                  (λ site →
                    martingaleField1 field site * martingaleField2 field site)
                  (λ site →
                    martingaleField1 field site * martingaleField3 field site
                    + martingaleField2 field site * martingaleField3 field site))
                (cong₂ _+_
                  refl
                  (sumRationalAdd
                    (physicalBlockSites side4)
                    (λ site →
                      martingaleField1 field site * martingaleField3 field site)
                    (λ site →
                      martingaleField2 field site * martingaleField3 field site))))))))

globalFourMartingaleSquareExpansion : ∀ field →
  globalNormSq (fourMartingaleSumField field)
  ≡
  globalNormSq (martingaleField0 field)
  + (globalNormSq (martingaleField1 field)
  + (globalNormSq (martingaleField2 field)
  + globalNormSq (martingaleField3 field)))
  + twoℚ *
    (globalBlockInner (martingaleField0 field) (martingaleField1 field)
    + (globalBlockInner (martingaleField0 field) (martingaleField2 field)
    + (globalBlockInner (martingaleField0 field) (martingaleField3 field)
    + (globalBlockInner (martingaleField1 field) (martingaleField2 field)
    + (globalBlockInner (martingaleField1 field) (martingaleField3 field)
    + globalBlockInner (martingaleField2 field) (martingaleField3 field)))))
globalFourMartingaleSquareExpansion field =
  trans
    (sumRationalCong
      (physicalBlockSites side4)
      (λ site →
        sq
          (martingaleField0 field site
          + (martingaleField1 field site
          + (martingaleField2 field site + martingaleField3 field site))))
      (λ site →
        fourSquareSum
          (martingaleField0 field site)
          (martingaleField1 field site)
          (martingaleField2 field site)
          (martingaleField3 field site)
        + twoℚ * pairCrossSum
          (martingaleField0 field site)
          (martingaleField1 field site)
          (martingaleField2 field site)
          (martingaleField3 field site))
      (λ site →
        fourSquareExpansionRaw
          (martingaleField0 field site)
          (martingaleField1 field site)
          (martingaleField2 field site)
          (martingaleField3 field site)))
    (trans
      (sumRationalAdd
        (physicalBlockSites side4)
        (λ site →
          fourSquareSum
            (martingaleField0 field site)
            (martingaleField1 field site)
            (martingaleField2 field site)
            (martingaleField3 field site))
        (λ site →
          twoℚ * pairCrossSum
            (martingaleField0 field site)
            (martingaleField1 field site)
            (martingaleField2 field site)
            (martingaleField3 field site)))
      (trans
        (cong₂ _+_
          (sumFourSquaresExact field)
          (sumRationalScale
            twoℚ
            (physicalBlockSites side4)
            (λ site →
              pairCrossSum
                (martingaleField0 field site)
                (martingaleField1 field site)
                (martingaleField2 field site)
                (martingaleField3 field site))))
        (cong
          (λ crossTotal →
            globalNormSq (martingaleField0 field)
            + (globalNormSq (martingaleField1 field)
            + (globalNormSq (martingaleField2 field)
            + globalNormSq (martingaleField3 field)))
            + twoℚ * crossTotal)
          (sumPairCrossExact field))))

physicalMartingaleVarianceDecomposition :
  ∀ field → GlobalMeanZero4 field →
  globalNormSq field
  ≡ globalNormSq (martingaleField0 field)
    + (globalNormSq (martingaleField1 field)
    + (globalNormSq (martingaleField2 field)
    + globalNormSq (martingaleField3 field)))
physicalMartingaleVarianceDecomposition field meanZero =
  trans
    (sym
      (globalNormRespectsPointwise
        (fourMartingaleReconstructsPointwise field meanZero)))
    (trans
      (globalFourMartingaleSquareExpansion field)
      (rewriteAllCrossTerms field))
  where
  rewriteAllCrossTerms : ∀ current →
    globalNormSq (martingaleField0 current)
    + (globalNormSq (martingaleField1 current)
    + (globalNormSq (martingaleField2 current)
    + globalNormSq (martingaleField3 current)))
    + twoℚ *
      (globalBlockInner (martingaleField0 current) (martingaleField1 current)
      + (globalBlockInner (martingaleField0 current) (martingaleField2 current)
      + (globalBlockInner (martingaleField0 current) (martingaleField3 current)
      + (globalBlockInner (martingaleField1 current) (martingaleField2 current)
      + (globalBlockInner (martingaleField1 current) (martingaleField3 current)
      + globalBlockInner (martingaleField2 current) (martingaleField3 current)))))
    ≡ globalNormSq (martingaleField0 current)
      + (globalNormSq (martingaleField1 current)
      + (globalNormSq (martingaleField2 current)
      + globalNormSq (martingaleField3 current)))
  rewriteAllCrossTerms current
    rewrite martingale01Zero current
          | martingale02Zero current
          | martingale03Zero current
          | martingale12Zero current
          | martingale13Zero current
          | martingale23Zero current =
    ℚRing.solve-∀
      (globalNormSq (martingaleField0 current))
      (globalNormSq (martingaleField1 current))
      (globalNormSq (martingaleField2 current))
      (globalNormSq (martingaleField3 current))

path4PhysicalVarianceDecompositionLevel : ProofLevel
path4PhysicalVarianceDecompositionLevel = machineChecked
