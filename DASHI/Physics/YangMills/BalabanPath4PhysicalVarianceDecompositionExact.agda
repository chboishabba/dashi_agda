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
fourMartingaleSumField siteF site =
  martingaleField0 siteF site
  + (martingaleField1 siteF site
  + (martingaleField2 siteF site + martingaleField3 siteF site))

globalNormSq : SiteField side4 → ℚ
globalNormSq blockField = globalBlockInner blockField blockField

GlobalMeanZero4 : SiteField side4 → Set
GlobalMeanZero4 siteF = ∀ site → average0123 siteF site ≡ 0ℚ

fourMartingaleReconstructsPointwise :
  ∀ siteF → GlobalMeanZero4 siteF →
  FieldEqual (fourMartingaleSumField siteF) siteF
fourMartingaleReconstructsPointwise siteF meanZero site =
  fourAxisPhysicalMartingaleDecomposition siteF site (meanZero site)

globalNormRespectsPointwise :
  ∀ {left right} → FieldEqual left right →
  globalNormSq left ≡ globalNormSq right
globalNormRespectsPointwise {left} {right} equality =
  sumRationalCong
    (physicalBlockSites side4)
    (λ site → left site * left site)
    (λ site → right site * right site)
    (λ site → cong₂ _*_ (equality site) (equality site))

sumFourSquaresExact : ∀ blockField →
  sumRational (physicalBlockSites side4) (λ site →
    fourSquareSum
      (martingaleField0 blockField site)
      (martingaleField1 blockField site)
      (martingaleField2 blockField site)
      (martingaleField3 blockField site))
  ≡ globalNormSq (martingaleField0 blockField)
    + (globalNormSq (martingaleField1 blockField)
    + (globalNormSq (martingaleField2 blockField)
    + globalNormSq (martingaleField3 blockField)))
sumFourSquaresExact blockField =
  trans
    (sumRationalAdd
      (physicalBlockSites side4)
      (λ site → sq (martingaleField0 blockField site))
      (λ site →
        sq (martingaleField1 blockField site)
        + (sq (martingaleField2 blockField site)
        + sq (martingaleField3 blockField site))))
    (cong₂ _+_
      refl
      (trans
        (sumRationalAdd
          (physicalBlockSites side4)
          (λ site → sq (martingaleField1 blockField site))
          (λ site →
            sq (martingaleField2 blockField site)
            + sq (martingaleField3 blockField site)))
        (cong₂ _+_
          refl
          (sumRationalAdd
            (physicalBlockSites side4)
            (λ site → sq (martingaleField2 blockField site))
            (λ site → sq (martingaleField3 blockField site))))))

sumPairCrossExact : ∀ blockField →
  sumRational (physicalBlockSites side4) (λ site →
    pairCrossSum
      (martingaleField0 blockField site)
      (martingaleField1 blockField site)
      (martingaleField2 blockField site)
      (martingaleField3 blockField site))
  ≡ globalBlockInner (martingaleField0 blockField) (martingaleField1 blockField)
    + (globalBlockInner (martingaleField0 blockField) (martingaleField2 blockField)
    + (globalBlockInner (martingaleField0 blockField) (martingaleField3 blockField)
    + (globalBlockInner (martingaleField1 blockField) (martingaleField2 blockField)
    + (globalBlockInner (martingaleField1 blockField) (martingaleField3 blockField)
    + globalBlockInner (martingaleField2 blockField) (martingaleField3 blockField)))))
sumPairCrossExact blockField =
  trans
    (sumRationalAdd
      (physicalBlockSites side4)
      (λ site → martingaleField0 blockField site * martingaleField1 blockField site)
      (λ site →
        martingaleField0 blockField site * martingaleField2 blockField site
        + (martingaleField0 blockField site * martingaleField3 blockField site
        + (martingaleField1 blockField site * martingaleField2 blockField site
        + (martingaleField1 blockField site * martingaleField3 blockField site
        + martingaleField2 blockField site * martingaleField3 blockField site)))))
    (cong₂ _+_
      refl
      (trans
        (sumRationalAdd
          (physicalBlockSites side4)
          (λ site → martingaleField0 blockField site * martingaleField2 blockField site)
          (λ site →
            martingaleField0 blockField site * martingaleField3 blockField site
            + (martingaleField1 blockField site * martingaleField2 blockField site
            + (martingaleField1 blockField site * martingaleField3 blockField site
            + martingaleField2 blockField site * martingaleField3 blockField site))))
        (cong₂ _+_
          refl
          (trans
            (sumRationalAdd
              (physicalBlockSites side4)
              (λ site → martingaleField0 blockField site * martingaleField3 blockField site)
              (λ site →
                martingaleField1 blockField site * martingaleField2 blockField site
                + (martingaleField1 blockField site * martingaleField3 blockField site
                + martingaleField2 blockField site * martingaleField3 blockField site)))
            (cong₂ _+_
              refl
              (trans
                (sumRationalAdd
                  (physicalBlockSites side4)
                  (λ site →
                    martingaleField1 blockField site * martingaleField2 blockField site)
                  (λ site →
                    martingaleField1 blockField site * martingaleField3 blockField site
                    + martingaleField2 blockField site * martingaleField3 blockField site))
                (cong₂ _+_
                  refl
                  (sumRationalAdd
                    (physicalBlockSites side4)
                    (λ site →
                      martingaleField1 blockField site * martingaleField3 blockField site)
                    (λ site →
                      martingaleField2 blockField site * martingaleField3 blockField site)))))))))

globalFourMartingaleSquareExpansion : ∀ blockField →
  globalNormSq (fourMartingaleSumField blockField)
  ≡
  globalNormSq (martingaleField0 blockField)
  + (globalNormSq (martingaleField1 blockField)
  + (globalNormSq (martingaleField2 blockField)
  + globalNormSq (martingaleField3 blockField)))
  + twoℚ *
    (globalBlockInner (martingaleField0 blockField) (martingaleField1 blockField)
    + (globalBlockInner (martingaleField0 blockField) (martingaleField2 blockField)
    + (globalBlockInner (martingaleField0 blockField) (martingaleField3 blockField)
    + (globalBlockInner (martingaleField1 blockField) (martingaleField2 blockField)
    + (globalBlockInner (martingaleField1 blockField) (martingaleField3 blockField)
    + globalBlockInner (martingaleField2 blockField) (martingaleField3 blockField))))))
globalFourMartingaleSquareExpansion blockField =
  trans
    (sumRationalCong
      (physicalBlockSites side4)
      (λ site →
        sq
          (martingaleField0 blockField site
          + (martingaleField1 blockField site
          + (martingaleField2 blockField site + martingaleField3 blockField site))))
      (λ site →
        fourSquareSum
          (martingaleField0 blockField site)
          (martingaleField1 blockField site)
          (martingaleField2 blockField site)
          (martingaleField3 blockField site)
        + twoℚ * pairCrossSum
          (martingaleField0 blockField site)
          (martingaleField1 blockField site)
          (martingaleField2 blockField site)
          (martingaleField3 blockField site))
      (λ site →
        fourSquareExpansionRaw
          (martingaleField0 blockField site)
          (martingaleField1 blockField site)
          (martingaleField2 blockField site)
          (martingaleField3 blockField site)))
    (trans
      (sumRationalAdd
        (physicalBlockSites side4)
        (λ site →
          fourSquareSum
            (martingaleField0 blockField site)
            (martingaleField1 blockField site)
            (martingaleField2 blockField site)
            (martingaleField3 blockField site))
        (λ site →
          twoℚ * pairCrossSum
            (martingaleField0 blockField site)
            (martingaleField1 blockField site)
            (martingaleField2 blockField site)
            (martingaleField3 blockField site)))
      (trans
        (cong₂ _+_
          (sumFourSquaresExact blockField)
          (sumRationalScale
            twoℚ
            (physicalBlockSites side4)
            (λ site →
              pairCrossSum
                (martingaleField0 blockField site)
                (martingaleField1 blockField site)
                (martingaleField2 blockField site)
                (martingaleField3 blockField site))))
        (cong
          (λ crossTotal →
            globalNormSq (martingaleField0 blockField)
            + (globalNormSq (martingaleField1 blockField)
            + (globalNormSq (martingaleField2 blockField)
            + globalNormSq (martingaleField3 blockField)))
            + twoℚ * crossTotal)
          (sumPairCrossExact blockField))))

physicalMartingaleVarianceDecomposition :
  ∀ blockField → GlobalMeanZero4 blockField →
  globalNormSq blockField
  ≡ globalNormSq (martingaleField0 blockField)
    + (globalNormSq (martingaleField1 blockField)
    + (globalNormSq (martingaleField2 blockField)
    + globalNormSq (martingaleField3 blockField)))
physicalMartingaleVarianceDecomposition blockField meanZero =
  trans
    (sym
      (globalNormRespectsPointwise
        (fourMartingaleReconstructsPointwise blockField meanZero)))
    (trans
      (globalFourMartingaleSquareExpansion blockField)
      (rewriteAllCrossTerms blockField))
  where
  rewriteAllCrossTerms : ∀ current →
    (globalNormSq (martingaleField0 current)
    + (globalNormSq (martingaleField1 current)
    + (globalNormSq (martingaleField2 current)
    + globalNormSq (martingaleField3 current)))
    + twoℚ *
      (globalBlockInner (martingaleField0 current) (martingaleField1 current)
      + (globalBlockInner (martingaleField0 current) (martingaleField2 current)
      + (globalBlockInner (martingaleField0 current) (martingaleField3 current)
      + (globalBlockInner (martingaleField1 current) (martingaleField2 current)
      + (globalBlockInner (martingaleField1 current) (martingaleField3 current)
      + globalBlockInner (martingaleField2 current) (martingaleField3 current))))))
    ≡
    (globalNormSq (martingaleField0 current)
    + (globalNormSq (martingaleField1 current)
    + (globalNormSq (martingaleField2 current)
    + globalNormSq (martingaleField3 current)))))
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
