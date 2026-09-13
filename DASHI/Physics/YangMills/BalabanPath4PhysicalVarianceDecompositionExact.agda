module DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Core.AtomicGlobalFibreLiftExact as FibreLift
import DASHI.Physics.YangMills.BalabanOpaqueGlobalAlgebraExact as OpaqueAlgebra

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
--
-- OOM discipline:
--   * atomic polynomial identities are proved before the physical fibre lift;
--   * fibre observers own pointwise-equality preservation receipts;
--   * global scalar coordinates remain opaque after observation;
--   * no RingSolver invocation in this module may see physical constructors.
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

normTotal : SiteField side4 → ℚ
normTotal current =
  globalNormSq (martingaleField0 current)
  + (globalNormSq (martingaleField1 current)
  + (globalNormSq (martingaleField2 current)
  + globalNormSq (martingaleField3 current)))

crossTotal : SiteField side4 → ℚ
crossTotal current =
  globalBlockInner (martingaleField0 current) (martingaleField1 current)
  + (globalBlockInner (martingaleField0 current) (martingaleField2 current)
  + (globalBlockInner (martingaleField0 current) (martingaleField3 current)
  + (globalBlockInner (martingaleField1 current) (martingaleField2 current)
  + (globalBlockInner (martingaleField1 current) (martingaleField3 current)
  + globalBlockInner (martingaleField2 current) (martingaleField3 current)))))

GlobalMeanZero4 : SiteField side4 → Set
GlobalMeanZero4 siteF = ∀ site → average0123 siteF site ≡ 0ℚ

fourMartingaleReconstructsPointwise :
  ∀ siteF → GlobalMeanZero4 siteF →
  FieldEqual (fourMartingaleSumField siteF) siteF
fourMartingaleReconstructsPointwise siteF meanZero site =
  fourAxisPhysicalMartingaleDecomposition siteF site (meanZero site)

------------------------------------------------------------------------
-- globalNormSq is literally an observer on the site fibre.  This is the only
-- place where its concrete 256-site sum is used to prove equality preservation.
-- Downstream users consume the generic fibre-lift receipt instead.
------------------------------------------------------------------------

globalNormPreservesPointwise :
  ∀ {left right : SiteField side4} →
  (∀ site → left site ≡ right site) →
  globalNormSq left ≡ globalNormSq right
globalNormPreservesPointwise {left} {right} equality =
  sumRationalCong
    (physicalBlockSites side4)
    (λ site → left site * left site)
    (λ site → right site * right site)
    (λ site → cong₂ _*_ (equality site) (equality site))

globalNormObserverLift : FibreLift.FibreObserverLift globalNormSq
globalNormObserverLift =
  FibreLift.fibre-observer-lift globalNormPreservesPointwise

globalNormRespectsPointwise :
  ∀ {left right} → FieldEqual left right →
  globalNormSq left ≡ globalNormSq right
globalNormRespectsPointwise equality =
  FibreLift.atomicFamilyToGlobal globalNormObserverLift equality

sumFourSquaresExact : ∀ blockField →
  sumRational (physicalBlockSites side4) (λ site →
    fourSquareSum
      (martingaleField0 blockField site)
      (martingaleField1 blockField site)
      (martingaleField2 blockField site)
      (martingaleField3 blockField site))
  ≡ normTotal blockField
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
  ≡ crossTotal blockField
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
  ≡ normTotal blockField + twoℚ * crossTotal blockField
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
        (FibreLift.mapEquality
          (λ cross → normTotal blockField + twoℚ * cross)
          (sumPairCrossExact blockField))))

------------------------------------------------------------------------
-- The six global orthogonality theorems are consumed as opaque scalar fibre
-- observations.  The scalar six-zero algebra was proved once in a module that
-- imports no physical carrier; no solver is invoked here.
------------------------------------------------------------------------

crossTotalZero : ∀ current → crossTotal current ≡ 0ℚ
crossTotalZero current =
  OpaqueAlgebra.sixTermSumZero
    (martingale01Zero current)
    (martingale02Zero current)
    (martingale03Zero current)
    (martingale12Zero current)
    (martingale13Zero current)
    (martingale23Zero current)

rewriteAllCrossTerms : ∀ current →
  normTotal current + twoℚ * crossTotal current
  ≡ normTotal current
rewriteAllCrossTerms current =
  trans
    (FibreLift.mapEquality
      (λ cross → normTotal current + twoℚ * cross)
      (crossTotalZero current))
    (OpaqueAlgebra.dropScaledZero (normTotal current) twoℚ)

physicalMartingaleVarianceDecomposition :
  ∀ blockField → GlobalMeanZero4 blockField →
  globalNormSq blockField ≡ normTotal blockField
physicalMartingaleVarianceDecomposition blockField meanZero =
  trans
    (sym
      (globalNormRespectsPointwise
        (fourMartingaleReconstructsPointwise blockField meanZero)))
    (trans
      (globalFourMartingaleSquareExpansion blockField)
      (rewriteAllCrossTerms blockField))

path4PhysicalVarianceDecompositionLevel : ProofLevel
path4PhysicalVarianceDecompositionLevel = machineChecked
