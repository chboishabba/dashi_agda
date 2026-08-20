module DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact where

------------------------------------------------------------------------
-- ROUND83: ONE MARK-KIND-UNIFORM ANALYTIC NORM -> THREE CLAY CONSUMERS
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99(3) (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116(1) (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- Stefan Hollands,
-- "The Operator Product Expansion for Perturbative Quantum Field Theory in
-- Curved Spacetime", Communications in Mathematical Physics 273 (2007), 1--36.
-- DOI: 10.1007/s00220-007-0230-6.
--
-- Bruno Nachtergaele, Anna Vershynina and Valentin A. Zagrebnov,
-- "Lieb-Robinson Bounds and Existence of the Thermodynamic Limit for a Class
-- of Irreversible Quantum Dynamics", Contemporary Mathematics 552 (2011),
-- 161--175. DOI: 10.1090/conm/552/10916.
--
-- DASHI CONTRIBUTION / IMPORTANT GRADE CORRECTION
--
-- The same differentiated source-native analytic NORM is consumed with three
-- different marks:
--
--   betaMark       : separation in preceding RG history / scale,
--   hessianMark    : physical-spatial influence separation,
--   compositeMark  : RG/OPE truncation depth.
--
-- THESE DEPTHS ARE NOT IDENTIFIED.  Earlier drafts used one untyped `depth` and
-- could be read as equating RG scale distance with physical spatial distance.
-- Round83 corrects that: the source theorem is uniform over `MarkedResponseKind`,
-- but each mark has its own shell and constant.  What is shared is the analytic
-- producer/proof method, not the physical metric.
--
-- For each declared mark k prove
--
--       A_k(d) <= C_k * rootedShell_k(d),
--       rootedShell_k(d) <= (1/4) 2^-d.
--
-- The existing rooted-KP, scale-Cauchy, and weighted-Hessian compilers then
-- imply the correctly typed consequences
--
--   beta tail(n,k)      <= (C_beta/2) 2^-n,
--   composite tail(n,k) <= (C_OPE/2) 2^-n,
--   weighted spatial Hessian row <= C_H.
--
-- The beta and composite grades may both be RG-related but are still kept as
-- different marks because their literal source insertions differ.  The Hessian
-- grade is explicitly spatial.
--
-- The physical work is therefore ONE mark-parametric differentiated analytic
-- theorem plus same-object identification of each mark with its literal YM
-- response.  It is not a claim that the three notions of distance coincide.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanRootedKPToHessianRowBudgetExact as Hess
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Weighted
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Cauchy
import DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact as Ursell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

data MarkedResponseKind : Set where
  betaMark hessianMark compositeMark : MarkedResponseKind

record SharedMarkedAnalyticShellControl
    (Scale Volume Root : Set) : Set₁ where
  field
    -- A mark-parametric source theorem.  `depth` is interpreted only relative to
    -- the selected mark; no cross-mark equality of physical distances is used.
    kpShell : MarkedResponseKind → StepV.UniformRootedShellBound Scale Volume Root

    markedAnalyticShell :
      MarkedResponseKind → Scale → Volume → Root → Nat → ℚ
    markedConstant : MarkedResponseKind → ℚ
    markedConstantNonnegative : ∀ kind → 0ℚ ≤ markedConstant kind

    betaHistoryShell : Scale → Volume → Root → Nat → ℚ
    hessianInfluenceShell : Scale → Volume → Root → Nat → ℚ
    compositeInsertionShell : Scale → Volume → Root → Nat → ℚ

    betaHistoryShellNonnegative : ∀ scale volume root depth →
      0ℚ ≤ betaHistoryShell scale volume root depth
    hessianInfluenceShellNonnegative : ∀ scale volume root depth →
      0ℚ ≤ hessianInfluenceShell scale volume root depth
    compositeInsertionShellNonnegative : ∀ scale volume root depth →
      0ℚ ≤ compositeInsertionShell scale volume root depth

    markedAnalyticShellBelowRooted :
      ∀ kind scale volume root depth →
      markedAnalyticShell kind scale volume root depth
      ≤ markedConstant kind
        * StepV.rootedShell (kpShell kind) scale volume root depth

    betaBelowAnalytic : ∀ scale volume root depth →
      betaHistoryShell scale volume root depth
      ≤ markedAnalyticShell betaMark scale volume root depth

    hessianBelowAnalytic : ∀ scale volume root depth →
      hessianInfluenceShell scale volume root depth
      ≤ markedAnalyticShell hessianMark scale volume root depth

    compositeBelowAnalytic : ∀ scale volume root depth →
      compositeInsertionShell scale volume root depth
      ≤ markedAnalyticShell compositeMark scale volume root depth

open SharedMarkedAnalyticShellControl public

betaAnalyticConstant :
  ∀ {Scale Volume Root} → SharedMarkedAnalyticShellControl Scale Volume Root → ℚ
betaAnalyticConstant dataSet = markedConstant dataSet betaMark

hessianAnalyticConstant :
  ∀ {Scale Volume Root} → SharedMarkedAnalyticShellControl Scale Volume Root → ℚ
hessianAnalyticConstant dataSet = markedConstant dataSet hessianMark

compositeAnalyticConstant :
  ∀ {Scale Volume Root} → SharedMarkedAnalyticShellControl Scale Volume Root → ℚ
compositeAnalyticConstant dataSet = markedConstant dataSet compositeMark

responseControl :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    (kind : MarkedResponseKind)
    (response : Scale → Volume → Root → Nat → ℚ) →
    (∀ scale volume root depth →
      response scale volume root depth
      ≤ markedAnalyticShell dataSet kind scale volume root depth) →
  Hess.RootedHessianShellControl Scale Volume Root
responseControl dataSet kind response responseBelow = record
  { Hess.RootedHessianShellControl.kpShell = kpShell dataSet kind
  ; Hess.RootedHessianShellControl.hessianRowShell = response
  ; Hess.RootedHessianShellControl.derivativeConstant = markedConstant dataSet kind
  ; Hess.RootedHessianShellControl.derivativeConstantNonnegative =
      markedConstantNonnegative dataSet kind
  ; Hess.RootedHessianShellControl.hessianShellBelowActivityShell =
      λ scale volume root depth →
        ℚP.≤-trans
          (responseBelow scale volume root depth)
          (markedAnalyticShellBelowRooted
            dataSet kind scale volume root depth)
  }

betaResponseControl :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Hess.RootedHessianShellControl Scale Volume Root
betaResponseControl dataSet =
  responseControl dataSet betaMark (betaHistoryShell dataSet)
    (betaBelowAnalytic dataSet)

hessianResponseControl :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Hess.RootedHessianShellControl Scale Volume Root
hessianResponseControl dataSet =
  responseControl dataSet hessianMark (hessianInfluenceShell dataSet)
    (hessianBelowAnalytic dataSet)

compositeResponseControl :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Hess.RootedHessianShellControl Scale Volume Root
compositeResponseControl dataSet =
  responseControl dataSet compositeMark (compositeInsertionShell dataSet)
    (compositeBelowAnalytic dataSet)

betaHistoryPartial :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Scale → Volume → Root → Nat → ℚ
betaHistoryPartial dataSet =
  Hess.hessianRowPartialSum (betaResponseControl dataSet)

compositeInsertionPartial :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Scale → Volume → Root → Nat → ℚ
compositeInsertionPartial dataSet =
  Hess.hessianRowPartialSum (compositeResponseControl dataSet)

betaHistoryPartialBelowHalfAnalyticConstant :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root depth →
  betaHistoryPartial dataSet scale volume root depth
  ≤ StepV.half * betaAnalyticConstant dataSet
betaHistoryPartialBelowHalfAnalyticConstant dataSet =
  Hess.hessianRowPartialBelowHalfDerivativeConstant
    (betaResponseControl dataSet)

compositeInsertionPartialBelowHalfAnalyticConstant :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root depth →
  compositeInsertionPartial dataSet scale volume root depth
  ≤ StepV.half * compositeAnalyticConstant dataSet
compositeInsertionPartialBelowHalfAnalyticConstant dataSet =
  Hess.hessianRowPartialBelowHalfDerivativeConstant
    (compositeResponseControl dataSet)

------------------------------------------------------------------------
-- Arbitrary-start Cauchy tails for the RG-history and OPE marks.
------------------------------------------------------------------------

responseScaleMajorant :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    (kind : MarkedResponseKind)
    (response : Scale → Volume → Root → Nat → ℚ)
    (responseNonnegative : ∀ scale volume root depth →
      0ℚ ≤ response scale volume root depth)
    (responseBelow : ∀ scale volume root depth →
      response scale volume root depth
      ≤ markedAnalyticShell dataSet kind scale volume root depth)
    (scale : Scale) (volume : Volume) (root : Root) →
  Cauchy.ScaleLocalIncrementMajorant
responseScaleMajorant dataSet kind response responseNonnegative responseBelow
  scale volume root = record
  { Cauchy.ScaleLocalIncrementMajorant.coefficient = markedConstant dataSet kind
  ; Cauchy.ScaleLocalIncrementMajorant.coefficientNonnegative =
      markedConstantNonnegative dataSet kind
  ; Cauchy.ScaleLocalIncrementMajorant.incrementMagnitude =
      response scale volume root
  ; Cauchy.ScaleLocalIncrementMajorant.incrementNonnegative =
      responseNonnegative scale volume root
  ; Cauchy.ScaleLocalIncrementMajorant.incrementBelowScaleShell =
      λ depth →
        let
          first = ℚP.≤-trans
            (responseBelow scale volume root depth)
            (markedAnalyticShellBelowRooted
              dataSet kind scale volume root depth)
          rooted = StepV.rootedShellBelowMajorant
            (kpShell dataSet kind) scale volume root depth
          scaled = Norm.scaleNonnegative
            (markedConstant dataSet kind)
            (markedConstantNonnegative dataSet kind)
            rooted
          combined = ℚP.≤-trans first scaled
        in
        subst
          (λ upper → response scale volume root depth ≤ upper)
          (ℚRing.solve-∀
            (markedConstant dataSet kind)
            StepV.quarter
            (Geo.halfPower depth)
            Ursell.quarter)
          combined
  }

betaScaleMajorant :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root) →
    Scale → Volume → Root → Cauchy.ScaleLocalIncrementMajorant
betaScaleMajorant dataSet =
  responseScaleMajorant dataSet betaMark
    (betaHistoryShell dataSet)
    (betaHistoryShellNonnegative dataSet)
    (betaBelowAnalytic dataSet)

compositeScaleMajorant :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root) →
    Scale → Volume → Root → Cauchy.ScaleLocalIncrementMajorant
compositeScaleMajorant dataSet =
  responseScaleMajorant dataSet compositeMark
    (compositeInsertionShell dataSet)
    (compositeInsertionShellNonnegative dataSet)
    (compositeBelowAnalytic dataSet)

betaHistoryTail :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root) →
    Scale → Volume → Root → Nat → Nat → ℚ
betaHistoryTail dataSet scale volume root =
  Cauchy.scaleIncrementTail (betaScaleMajorant dataSet scale volume root)

compositeInsertionTail :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root) →
    Scale → Volume → Root → Nat → Nat → ℚ
compositeInsertionTail dataSet scale volume root =
  Cauchy.scaleIncrementTail
    (compositeScaleMajorant dataSet scale volume root)

betaHistoryTailVanishingModulus :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root start count →
  betaHistoryTail dataSet scale volume root start count
  ≤ betaAnalyticConstant dataSet * (Geo.half * Geo.halfPower start)
betaHistoryTailVanishingModulus dataSet scale volume root =
  Cauchy.scaleLocalCauchyTail
    (betaScaleMajorant dataSet scale volume root)

compositeInsertionTailVanishingModulus :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root start count →
  compositeInsertionTail dataSet scale volume root start count
  ≤ compositeAnalyticConstant dataSet * (Geo.half * Geo.halfPower start)
compositeInsertionTailVanishingModulus dataSet scale volume root =
  Cauchy.scaleLocalCauchyTail
    (compositeScaleMajorant dataSet scale volume root)

hessianWeightedControl :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Weighted.ExponentialWeightedHessianShellControl Scale Volume Root
hessianWeightedControl dataSet = record
  { Weighted.ExponentialWeightedHessianShellControl.hessianControl =
      hessianResponseControl dataSet
  }

hessianWeightedInfluenceBelowAnalyticConstant :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root depth →
  Weighted.weightedHessianPartial
      (hessianWeightedControl dataSet) scale volume root depth
  ≤ hessianAnalyticConstant dataSet
hessianWeightedInfluenceBelowAnalyticConstant dataSet =
  Weighted.weightedHessianRowUniformlyBelowDerivativeConstant
    (hessianWeightedControl dataSet)

sharedMarkedAnalyticThreeConsumerCompilerLevel : ProofLevel
sharedMarkedAnalyticThreeConsumerCompilerLevel = machineChecked

sharedMarkedAnalyticVanishingTailCompilerLevel : ProofLevel
sharedMarkedAnalyticVanishingTailCompilerLevel = machineChecked

-- Source-facing theorem: instantiate `markedAnalyticShell` by the literal
-- differentiated CMP99(3)/109/116 activity norm, uniformly over the three mark
-- kinds.  The proof may share one Cauchy/localization argument while retaining
-- the physically distinct depth semantics above.
physicalSharedMarkedAnalyticShellLevel : ProofLevel
physicalSharedMarkedAnalyticShellLevel = conditional

-- Same-object identification remains essential: the beta, Langevin-Hessian and
-- composite responses must really be the declared mark projections of the
-- source-native differentiated activity.
physicalSharedMarkedResponseIdentificationLevel : ProofLevel
physicalSharedMarkedResponseIdentificationLevel = conditional
