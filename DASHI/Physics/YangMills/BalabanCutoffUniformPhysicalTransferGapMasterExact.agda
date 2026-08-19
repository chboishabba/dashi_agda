module DASHI.Physics.YangMills.BalabanCutoffUniformPhysicalTransferGapMasterExact where

------------------------------------------------------------------------
-- ROUND64 MASTER THEOREM 5: CUTOFF-UNIFORM PHYSICAL TRANSFER GAP
--
-- PRIMARY SOURCES
--
-- Martin Lüscher,
-- "Construction of a Selfadjoint, Strictly Positive Transfer Matrix for
-- Euclidean Lattice Gauge Theories", Communications in Mathematical Physics
-- 54 (1977), 283--292. DOI: 10.1007/BF01614090.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- Volker Bach, Thomas Chen, Jürg Fröhlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group Methods",
-- Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- DASHI CONTRIBUTION
--
-- The terminal reference-gap theorem and the discounted Feshbach/Schur loss
-- theorem are proof decomposition.  The continuum construction consumes one
-- physical statement: after conversion to physical units, the complete cutoff
-- family has a common strictly positive lower mass floor.
--
-- This module makes that theorem the master producer and proves the exact
-- sufficient adapter from the existing finite gap-pullback recursion whenever
-- a common lower floor for the pulled-back gaps has actually been established.
-- A merely positive gap at every cutoff is deliberately NOT enough.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact as Pullback

record CutoffUniformPhysicalTransferGap : Set₁ where
  field
    physicalGapAt : Nat → ℚ
    massFloor : ℚ
    massFloorPositive : 0ℚ < massFloor
    massFloorBelowEveryCutoff : ∀ cutoff →
      massFloor ≤ physicalGapAt cutoff

open CutoffUniformPhysicalTransferGap public

physicalGapPositiveAtEveryCutoff :
  (master : CutoffUniformPhysicalTransferGap) → ∀ cutoff →
  0ℚ < physicalGapAt master cutoff
physicalGapPositiveAtEveryCutoff master cutoff =
  ℚP.<-≤-trans
    (massFloorPositive master)
    (massFloorBelowEveryCutoff master cutoff)

------------------------------------------------------------------------
-- Existing terminal/Feshbach route as a sufficient constructor.
------------------------------------------------------------------------

record UniformGapPullbackFamily : Set₁ where
  field
    terminalGapAt : Nat → ℚ
    lossesAt : Nat → Agda.Builtin.List.List ℚ
    physicalGapAt : Nat → ℚ

    transferChainAt : ∀ cutoff →
      Pullback.GapTransferChain
        (physicalGapAt cutoff)
        (lossesAt cutoff)
        (terminalGapAt cutoff)

    strictLossBudgetAt : ∀ cutoff →
      Pullback.discountedLossBudgetStrictlyAdmissible
        (terminalGapAt cutoff) (lossesAt cutoff)

    commonMassFloor : ℚ
    commonMassFloorPositive : 0ℚ < commonMassFloor

    -- This is the genuinely uniform analytic content.  It is stronger than
    -- proving each cutoff gap positive separately.
    commonFloorBelowPulledBackGap : ∀ cutoff →
      commonMassFloor
      ≤ Pullback.pullBackGap (terminalGapAt cutoff) (lossesAt cutoff)

open UniformGapPullbackFamily public

uniformGapMasterFromPullbackFamily :
  UniformGapPullbackFamily → CutoffUniformPhysicalTransferGap
uniformGapMasterFromPullbackFamily family = record
  { physicalGapAt = UniformGapPullbackFamily.physicalGapAt family
  ; massFloor = commonMassFloor family
  ; massFloorPositive = commonMassFloorPositive family
  ; massFloorBelowEveryCutoff = λ cutoff →
      ℚP.≤-trans
        (commonFloorBelowPulledBackGap family cutoff)
        (Pullback.pullBackGapBelowFine (transferChainAt family cutoff))
  }

-- Separate theorem showing the strict budget itself gives pointwise positivity;
-- this is intentionally weaker than the uniform master theorem.
pullbackFamilyGivesPointwisePositiveGap :
  (family : UniformGapPullbackFamily) → ∀ cutoff →
  0ℚ < UniformGapPullbackFamily.physicalGapAt family cutoff
pullbackFamilyGivesPointwisePositiveGap family cutoff =
  Pullback.strictBudgetImpliesFinePositive
    (transferChainAt family cutoff)
    (strictLossBudgetAt family cutoff)

cutoffUniformGapMasterCompilerLevel : ProofLevel
cutoffUniformGapMasterCompilerLevel = machineChecked

-- The hard theorem is the physical cutoff-uniform floor, not Kato/Feshbach
-- algebra and not the proposition "every finite cutoff has some positive gap".
physicalCutoffUniformTransferGapLevel : ProofLevel
physicalCutoffUniformTransferGapLevel = conditional
