module DASHI.Analysis.RiemannG2ExplicitFormulaBridgeAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFiniteExplicitFormulaBoundary as Finite
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as G2
import DASHI.Analysis.RiemannAristotleFiniteNearReflectionOrbitReturnExact as Near
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- REPOSITORY-INTERNAL EXPLICIT-FORMULA -> G2 BRIDGE AUDIT
--
-- This is DASHI integration, not an external-source theorem attribution.
-- The canonical RiemannExplicitFormula owner already has an arithmeticForm,
-- spectralZeroForm and an explicitFormula equality, but supplies no inhabitant.
-- The finite boundary separately requires a tail/limit witness before finite
-- tracked prime-power data can be promoted to the full prime-power term.
--
-- G2, meanwhile, has a literal finite zero carrier nearOffFinset(t,J) and a
-- target-centred weighted scalar integral.  The missing bridge is therefore an
-- exact identification of THAT literal consumer with an admissible
-- spectralZeroForm/test-function instance, including near/far decomposition.
------------------------------------------------------------------------

data ExistingOwner : Set where
  abstractExplicitFormulaOwner : ExistingOwner
  finitePrimeTailBoundaryOwner : ExistingOwner
  literalG2NearCarrierOwner : ExistingOwner

data BridgeObligation : Set where
  g2TaperAsWeilTest : BridgeObligation
  g2TaperAdmissibility : BridgeObligation
  spectralZeroFormEqualsLiteralZeroKernel : BridgeObligation
  nearFarZeroDecomposition : BridgeObligation
  nearOffFinsetCarrierEquality : BridgeObligation
  farRemainderCompatibility : BridgeObligation
  primeTailCompatibility : BridgeObligation

g2TargetReference : String
g2TargetReference = G2.firstUnprovedHarmonicAnalysisTheorem G2.canonicalAristotleG2CurrentCut

------------------------------------------------------------------------
-- Positive reuse already available.
------------------------------------------------------------------------

nearCarrierReflectionStable :
  Near.finiteNearCarrierReflectionStableBySource Near.canonicalFiniteNearReflectionOrbitReturn
  ≡ true
nearCarrierReflectionStable =
  Near.finiteNearCarrierReflectionStableBySourceIsTrue
    Near.canonicalFiniteNearReflectionOrbitReturn

explicitFormulaOwnerExists : Bool
explicitFormulaOwnerExists = true

finiteTailBoundaryExists : Bool
finiteTailBoundaryExists = true

------------------------------------------------------------------------
-- Current missing same-object bridge.
------------------------------------------------------------------------

record LiteralG2ExplicitFormulaWeld : Set₁ where
  constructor literalG2ExplicitFormulaWeld
  field
    Space : Set
    Formula : Set
    g2TaperTest : Set
    g2TaperAdmissible : Set
    spectralToLiteralKernelEquality : Set
    nearFarDecompositionProof : Set
    nearCarrierEquality : Set
    farRemainderEquality : Set
    finiteTailReceipt : Set

-- No constructor from RiemannExplicitFormula's abstract record alone is exposed.

currentRelation : Relation.RelationKind
currentRelation = Relation.exactSameObjectRealisation

-- Same-object realization is the exact missing seam, but by itself is not
-- theorem-closing authority; the G2 harmonic estimate would still have to be
-- proved on the welded object.
sameObjectRealisationAloneCannotCloseG2 :
  Relation.TheoremTransferCapability currentRelation → ⊥
sameObjectRealisationAloneCannotCloseG2 =
  Relation.sameObjectAloneCannotDirectlyTransferTheorem

literalG2ExplicitFormulaWeldRecovered : Bool
literalG2ExplicitFormulaWeldRecovered = false

g2TargetClosedByExistingExplicitFormulaOwner : Bool
g2TargetClosedByExistingExplicitFormulaOwner = false

literalG2ExplicitFormulaWeldRecoveredIsFalse :
  literalG2ExplicitFormulaWeldRecovered ≡ false
literalG2ExplicitFormulaWeldRecoveredIsFalse = refl

g2TargetClosedByExistingExplicitFormulaOwnerIsFalse :
  g2TargetClosedByExistingExplicitFormulaOwner ≡ false
g2TargetClosedByExistingExplicitFormulaOwnerIsFalse = refl

------------------------------------------------------------------------
-- Highest-alpha consequence.
--
-- We should NOT search externally for a generic explicit formula first: the
-- repo already owns the abstract formula.  The highest-alpha task is now the
-- literal adapter from the actual determinant-taper q / nearOffFinset kernel
-- into the canonical Weil-test/spectralZeroForm surface.  If that adapter is
-- impossible, record the exact obstruction; if it exists, it creates a real
-- same-object bridge and makes arithmetic-side information relevant to G2.
------------------------------------------------------------------------

record HighestAlphaG2WeldTarget : Set where
  constructor highestAlphaG2WeldTarget
  field
    existingSourceOwner : String
    literalConsumer : String
    firstRequiredReceipt : String
    secondRequiredReceipt : String
    promotionBeforeWeld : Bool
    promotionBeforeWeldIsFalse : promotionBeforeWeld ≡ false

canonicalHighestAlphaG2WeldTarget : HighestAlphaG2WeldTarget
canonicalHighestAlphaG2WeldTarget =
  highestAlphaG2WeldTarget
    "DASHI.Analysis.RiemannExplicitFormula + RiemannFiniteExplicitFormulaBoundary"
    g2TargetReference
    "construct the literal determinant-taper q as an admissible WeilTestSpace.Test"
    "prove spectralZeroForm for that test equals the literal reflection-paired nearOffFinset kernel plus the already-owned far remainder"
    false refl
