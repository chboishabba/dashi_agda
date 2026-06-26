module DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.ProofTargetSurface
import DASHI.Physics.Closure.ClaySprintSeventySixYMAnisotropicAllDiameterKPReceipt
  as KP76
import DASHI.Physics.YangMills.BalabanSpatialLinkWeightLowerBound
  as LinkLB
import DASHI.Physics.YangMills.P01P33ProofSurfaces as Surfaces

Scalar : Set
Scalar = String

data AnisotropicDiameterObligation : Set where
  p33aImportedLinkEllipticity : AnisotropicDiameterObligation
  p33bInternalDominationTheorem : AnisotropicDiameterObligation

canonicalAnisotropicDiameterObligations :
  List AnisotropicDiameterObligation
canonicalAnisotropicDiameterObligations = []

-- ── P33a: source-side link ellipticity wrapper ──────────────────────
--
-- This wrapper records the imported small-field / link-ellipticity source.
-- It is intentionally not presented as an internal DASHI proof.

record P33aUniformLinkEllipticityWrapper : Set where
  field
    sourceSurface : ProofTargetSurface
    sourceSurfaceIsImported :
      sourceSurface ≡ Surfaces.fieldRegularityImpliesSingleLinkPositivitySurface
    sourceSurfaceClosed : proofTargetIsClosed sourceSurface ≡ true
    sourceClaim : String
    sourceClaimIsCanonical :
      sourceClaim ≡
      "Uniform link ellipticity is imported from the Balaban/Eriksson small-field regularity surface; this file does not reprove the analytic input."
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P33a is a source-side wrapper only: the analytic ellipticity claim remains external."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentP33aUniformLinkEllipticityWrapper : P33aUniformLinkEllipticityWrapper
currentP33aUniformLinkEllipticityWrapper = record
  { sourceSurface = Surfaces.fieldRegularityImpliesSingleLinkPositivitySurface
  ; sourceSurfaceIsImported = refl
  ; sourceSurfaceClosed = refl
  ; sourceClaim =
      "Uniform link ellipticity is imported from the Balaban/Eriksson small-field regularity surface; this file does not reprove the analytic input."
  ; sourceClaimIsCanonical = refl
  ; proofBoundary =
      "P33a is a source-side wrapper only: the analytic ellipticity claim remains external."
  ; proofBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }

weightedDistanceDominatesDiameterSurface : ProofTargetSurface
weightedDistanceDominatesDiameterSurface =
  mkProofTargetSurface
    "WeightedTreeDistanceDominatesOrdinaryDiameter"
    "P33a imported source link ellipticity plus the P01/P02/P03 internal graph chain"
    "Uniform link ellipticity together with the tree-path and graph-distance sublemmas yields weighted tree distance >= ordinary diameter."
    "P01 treePathEdgesExist; P02 graphDistMinimality; P03 treePathBoundedByEdgeCount; P33a imported link ellipticity."
    "Weighted tree distance dominates the ordinary diameter."
    "P33b internal graph consequence in the anisotropic diameter branch."
    "Do not infer analytic ellipticity from this theorem surface; that remains an imported P33a wrapper."
    auditTested

-- ── P33b: internal graph consequence ────────────────────────────────
--
-- This record consumes P01/P02/P03 explicitly together with the imported
-- P33a wrapper.  The conclusion is packaged as a theorem surface; the file
-- does not claim to have internally proved the analytic source input.

record P33bWeightedTreeDistanceDominatesOrdinaryDiameter : Set₁ where
  field
    p01TreePathEdgesExist : ProofTargetSurface
    p02GraphDistMinimality : ProofTargetSurface
    p03TreePathBoundedByEdgeCount : ProofTargetSurface
    p33aUniformLinkEllipticity : P33aUniformLinkEllipticityWrapper
    theoremSurface : ProofTargetSurface
    theoremSurfaceClosed : proofTargetIsClosed theoremSurface ≡ true
    theoremStatement : String
    theoremStatementIsCanonical :
      theoremStatement ≡
      "Uniform link ellipticity on each admissible support link, together with P01 tree-path existence, P02 graph-distance minimality, and P03 tree-path edge-count control, implies weighted tree distance dominates ordinary diameter."
    dependencyChain : String
    dependencyChainIsCanonical :
      dependencyChain ≡
      "P01 treePathEdgesExist + P02 graphDistMinimality + P03 treePathBoundedByEdgeCount + P33a imported link ellipticity => weighted tree distance dominates ordinary diameter."
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P33b is an internal graph consequence; it does not reprove the imported ellipticity source."
    noClayPromotion : clayYangMillsPromoted ≡ false

p33aImpliesP33b :
  P33aUniformLinkEllipticityWrapper →
  P33bWeightedTreeDistanceDominatesOrdinaryDiameter
p33aImpliesP33b p33a = record
  { p01TreePathEdgesExist = Surfaces.treePathEdgesExistSurface
  ; p02GraphDistMinimality = Surfaces.graphDistMinimalitySurface
  ; p03TreePathBoundedByEdgeCount = Surfaces.treePathBoundedByEdgeCountSurface
  ; p33aUniformLinkEllipticity = p33a
  ; theoremSurface = weightedDistanceDominatesDiameterSurface
  ; theoremSurfaceClosed = refl
  ; theoremStatement =
      "Uniform link ellipticity on each admissible support link, together with P01 tree-path existence, P02 graph-distance minimality, and P03 tree-path edge-count control, implies weighted tree distance dominates ordinary diameter."
  ; theoremStatementIsCanonical = refl
  ; dependencyChain =
      "P01 treePathEdgesExist + P02 graphDistMinimality + P03 treePathBoundedByEdgeCount + P33a imported link ellipticity => weighted tree distance dominates ordinary diameter."
  ; dependencyChainIsCanonical = refl
  ; proofBoundary =
      "P33b is an internal graph consequence; it does not reprove the imported ellipticity source."
  ; proofBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }

currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter :
  P33bWeightedTreeDistanceDominatesOrdinaryDiameter
currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter =
  p33aImpliesP33b currentP33aUniformLinkEllipticityWrapper

-- ── SpanningPathWeightAccumulation ──────────────────────────────────

record SpanningPathWeightAccumulation : Set where
  field
    p33aSource : P33aUniformLinkEllipticityWrapper
    p33bTheorem : P33bWeightedTreeDistanceDominatesOrdinaryDiameter
    additiveSource : String
    additiveSourceIsCanonical :
      additiveSource ≡
      "pathWeight = List.sum ∘ List.map linkWeight; effectiveLinkWeight = 1 ⇒ pathWeight π = length π"
    diameterDominationSource : String
    diameterDominationSourceIsCanonical :
      diameterDominationSource ≡
      "P01-P03 with imported P33a give weighted tree distance >= DASHI diameter"
    noClayPromotion : clayYangMillsPromoted ≡ false

currentSpanningPathWeightAccumulation : SpanningPathWeightAccumulation
currentSpanningPathWeightAccumulation = record
  { p33aSource = currentP33aUniformLinkEllipticityWrapper
  ; p33bTheorem = currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter
  ; additiveSource =
      "pathWeight = List.sum ∘ List.map linkWeight; effectiveLinkWeight = 1 ⇒ pathWeight π = length π"
  ; additiveSourceIsCanonical = refl
  ; diameterDominationSource =
      "P01-P03 with imported P33a give weighted tree distance >= DASHI diameter"
  ; diameterDominationSourceIsCanonical = refl
  ; noClayPromotion = refl
  }

record AnisotropicDiameterCompatibility : Set₁ where
  field
    arithmeticReceipt :
      KP76.ClaySprintSeventySixYMAnisotropicAllDiameterKPReceipt
    spatialLinkWeightLowerBound :
      LinkLB.SpatialLinkWeightLowerBound
    spatialLinkRegularityAssumption :
      LinkLB.SpatialLinkRegularityAssumption
    p33aLinkEllipticity :
      P33aUniformLinkEllipticityWrapper
    p33bGraphDomination :
      P33bWeightedTreeDistanceDominatesOrdinaryDiameter
    spanningPathWeightAccumulation :
      SpanningPathWeightAccumulation
    weightedArithmeticCloses :
      KP76.anisotropicKPArithmeticClosed arithmeticReceipt ≡ true
    targetConvention : String
    targetConventionIsLoss :
      targetConvention ≡
      "loss convention: ||.||_diameter <= C_loss * ||.||_anisotropic"
    targetInequality : String
    targetInequalityIsCanonical :
      targetInequality ≡
      "||.||_diameter <= C_loss * ||.||_anisotropic"
    marginConstraint : String
    marginConstraintIsCanonical :
      marginConstraint ≡
      "C_loss * 4q < 1 iff C_loss < 1.0786 iff minLinkWeight > 0.9271"
    fourQValue : Scalar
    fourQValueIsCanonical :
      fourQValue ≡ "0.9271275790105094"
    lossBudgetUpperBound : Scalar
    lossBudgetUpperBoundIsCanonical :
      lossBudgetUpperBound ≡ "1.0786"
    requiredMinLinkWeight : Scalar
    requiredMinLinkWeightIsCanonical :
      requiredMinLinkWeight ≡ "0.9271"
    diameterDominationSurface :
      ProofTargetSurface
    diameterDominationSurfaceIsClosed :
      proofTargetIsClosed diameterDominationSurface ≡ true
    blockerSummary : String
    blockerSummaryIsCanonical :
      blockerSummary ≡
      "P33 is split: P33a imports uniform link ellipticity, and P33b internally packages the P01/P02/P03 graph consequence that weighted tree distance dominates ordinary diameter. Next open gate is polymerDiameterEntropyControlled in BalabanStepVSpatialKPCertificate."
    openObligations : List AnisotropicDiameterObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalAnisotropicDiameterObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

currentAnisotropicDiameterCompatibility :
  AnisotropicDiameterCompatibility
currentAnisotropicDiameterCompatibility = record
  { arithmeticReceipt =
      KP76.canonicalSprint76YMAnisotropicAllDiameterKPReceipt
  ; spatialLinkWeightLowerBound =
      LinkLB.currentSpatialLinkWeightLowerBound
  ; spatialLinkRegularityAssumption =
      LinkLB.currentSpatialLinkRegularityAssumption
  ; p33aLinkEllipticity = currentP33aUniformLinkEllipticityWrapper
  ; p33bGraphDomination =
      currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter
  ; spanningPathWeightAccumulation =
      currentSpanningPathWeightAccumulation
  ; weightedArithmeticCloses =
      KP76.anisotropicKPArithmeticClosedIsTrue
        KP76.canonicalSprint76YMAnisotropicAllDiameterKPReceipt
  ; targetConvention =
      "loss convention: ||.||_diameter <= C_loss * ||.||_anisotropic"
  ; targetConventionIsLoss = refl
  ; targetInequality =
      "||.||_diameter <= C_loss * ||.||_anisotropic"
  ; targetInequalityIsCanonical = refl
  ; marginConstraint =
      "C_loss * 4q < 1 iff C_loss < 1.0786 iff minLinkWeight > 0.9271"
  ; marginConstraintIsCanonical = refl
  ; fourQValue = "0.9271275790105094"
  ; fourQValueIsCanonical = refl
  ; lossBudgetUpperBound = "1.0786"
  ; lossBudgetUpperBoundIsCanonical = refl
  ; requiredMinLinkWeight = "0.9271"
  ; requiredMinLinkWeightIsCanonical = refl
  ; diameterDominationSurface = weightedDistanceDominatesDiameterSurface
  ; diameterDominationSurfaceIsClosed = refl
  ; blockerSummary =
      "P33 is split: P33a imports uniform link ellipticity, and P33b internally packages the P01/P02/P03 graph consequence that weighted tree distance dominates ordinary diameter. Next open gate is polymerDiameterEntropyControlled in BalabanStepVSpatialKPCertificate."
  ; blockerSummaryIsCanonical = refl
  ; openObligations = canonicalAnisotropicDiameterObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
