module DASHI.Analysis.RiemannAristotleWindowSchurCrossProverSyncExact where

------------------------------------------------------------------------
-- CROSS-PROVER SYNC: ARISTOTLE / ZETA23BRIDGE -> DASHI AGDA
--
-- This module records the strongest current theorem surfaces returned by the
-- separate Lean-4.33 Aristotle project, without pretending that Lean proofs
-- are Agda kernel proofs and without introducing a cross-toolchain import.
--
-- Current Aristotle progression, in dependency order:
--
--   literal Weil EF
--     -> four-sample parity balance
--     -> reflection-pair odd cancellation
--     -> same-ordinate even cluster / two-radius height detector
--     -> projective residual decomposition
--     -> short-taper prime annihilation at both radii
--     -> projective O(r^2) residual coefficient lane
--     -> large-ordinate no-go for absolute off-ordinate mass W(t)
--     -> multi-taper Schur elimination
--     -> positive pole-null taper family
--     -> two-taper leading cross determinant
--     -> localized-window TP2/covariance separation
--     -> positive-width window-taper existence
--     -> normalized narrow-window endpoint domination frontier.
--
-- The currently live Lean obligation is not another Gram sign theorem.  It is
-- a quantitative residual-budget theorem: transport the endpoint/narrow-window
-- bounds through the explicit detRest polynomial so that the positive strict
-- cross margin dominates the residual budget.
--
-- This is exactly the generic theorem shape already owned in Agda by
-- ResidualBudgetMarginCompilerExact and structurally anticipated by G21's
-- determinant-level margin interface.  PR #627 independently arrived at the
-- same architecture for Navier--Stokes block Gram covariance: positive residual
-- covariance is admissible when quantitatively budgeted.  No #627 code is
-- imported here; this is theorem-pattern provenance only.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ResidualBudgetMarginCompilerExact as Budget
import DASHI.Analysis.RiemannG21DeterminantMarginTransferExact as Margin

------------------------------------------------------------------------
-- Cross-prover status is deliberately stronger than prose and weaker than an
-- Agda kernel theorem: it records who owns a theorem and whether the theorem
-- has been transported into this prover.
------------------------------------------------------------------------

data ProofOwner : Set where
  agdaOwner leanAristotleOwner sourceAuditOwner openObligation : ProofOwner

record CrossProverTheoremStatus : Set where
  constructor cross-prover-theorem-status
  field
    theoremName : String
    owner : ProofOwner
    machineCheckedInOwner : Bool
    transportedIntoAgda : Bool
    boundedReading : String

open CrossProverTheoremStatus public

literalWeilParityBalanceStatus : CrossProverTheoremStatus
literalWeilParityBalanceStatus =
  cross-prover-theorem-status
    "literalWeilParityQuotientDecompositionUnconditional"
    leanAristotleOwner true false
    "Lean-4.33 bridge specializes the machine-checked Zeta23 Weil EF and removes the earlier balance hypothesis. Not transported as an Agda proof."

reflectionPairOddCancellationStatus : CrossProverTheoremStatus
reflectionPairOddCancellationStatus =
  cross-prover-theorem-status
    "reflection partner cancels target odd channel"
    leanAristotleOwner true false
    "The functional-equation partner is an actual other-zero summand with opposite odd response; isolated odd parity therefore cannot prove RH."

sameOrdinateEvenClusterStatus : CrossProverTheoremStatus
sameOrdinateEvenClusterStatus =
  cross-prover-theorem-status
    "literalClusterTwoRadiusDetectsOffLine"
    leanAristotleOwner true false
    "Same-ordinate reflection pairs are purely even, but two-radius projective shape detects nonzero height and the cluster cannot cancel that positive defect."

shortTaperPrimeAnnihilationStatus : CrossProverTheoremStatus
shortTaperPrimeAnnihilationStatus =
  cross-prover-theorem-status
    "prime projective channel vanishes under short support"
    leanAristotleOwner true false
    "Support below log 2 kills the literal von-Mangoldt channel at both sampling radii. This is specific to the current short-taper lane."

absoluteMassNoGoStatus : CrossProverTheoremStatus
absoluteMassNoGoStatus =
  cross-prover-theorem-status
    "high-ordinate projective gate no-go under W(t) majorization"
    leanAristotleOwner true false
    "Projectivization repairs the radius order but absolute off-ordinate mass remains too large at high ordinate; W(t)-style majorization is structurally exhausted in this lane."

multiTaperSchurStatus : CrossProverTheoremStatus
multiTaperSchurStatus =
  cross-prover-theorem-status
    "multi-taper Schur nuisance elimination"
    leanAristotleOwner true false
    "Several individually admissible positive tapers are vectorized; selected nuisance-zero response vectors can be eliminated exactly before tail majorization, provided target Gram separation survives."

positivePoleNullFamilyStatus : CrossProverTheoremStatus
positivePoleNullFamilyStatus =
  cross-prover-theorem-status
    "positive pole-null taper family"
    leanAristotleOwner true false
    "One negative-response localized bump plus distinct positive-response bumps yields distinct nonnegative pole-null tapers while preserving each coordinate's positivity assumptions."

windowSeparationStatus : CrossProverTheoremStatus
windowSeparationStatus =
  cross-prover-theorem-status
    "positive-width localized-window covariance separation"
    leanAristotleOwner true false
    "Tent tapers exist on nondegenerate modulus windows, and strict point-window TP2 separation persists for sufficiently narrow positive-width windows."

normalizedEndpointDominationStatus : CrossProverTheoremStatus
normalizedEndpointDominationStatus =
  cross-prover-theorem-status
    "normalized narrow-window endpoint domination"
    leanAristotleOwner false false
    "Current continuation target: unit-mass self responses vanish with window width while separated-window cross responses retain a positive endpoint margin; transport these bounds through detRest."

currentAristotleStatuses : List CrossProverTheoremStatus
currentAristotleStatuses =
  literalWeilParityBalanceStatus ∷
  reflectionPairOddCancellationStatus ∷
  sameOrdinateEvenClusterStatus ∷
  shortTaperPrimeAnnihilationStatus ∷
  absoluteMassNoGoStatus ∷
  multiTaperSchurStatus ∷
  positivePoleNullFamilyStatus ∷
  windowSeparationStatus ∷
  normalizedEndpointDominationStatus ∷ []

------------------------------------------------------------------------
-- Agda theorem surfaces returned to Lean.
------------------------------------------------------------------------

residualBudgetCompilerReturned :
  (d : Budget.ResidualBudgetMargin) →
  Budget.residual d < Budget.strictSignalMargin d
residualBudgetCompilerReturned = Budget.residualStrictlyBelowSignalMargin

splitResidualBudgetCompilerReturned :
  (d : Budget.SplitResidualBudgetMargin) →
  Budget.structuredResidual d + Budget.farResidual d
    < Budget.strictSignalMargin d
splitResidualBudgetCompilerReturned = Budget.splitResidualStrictlyBelowSignalMargin

entrywiseTriangleBoundRequiredByG21Margin : Bool
entrywiseTriangleBoundRequiredByG21Margin =
  Margin.DeterminantMarginBoundary.entrywiseTriangleBoundRequiredByInterface
    Margin.canonicalDeterminantMarginBoundary

entrywiseTriangleBoundRequiredByG21MarginIsFalse :
  entrywiseTriangleBoundRequiredByG21Margin ≡ false
entrywiseTriangleBoundRequiredByG21MarginIsFalse = refl

------------------------------------------------------------------------
-- Theorem-pattern provenance from the newer NS block-covariance lane.
-- This intentionally does NOT import draft PR #627.
------------------------------------------------------------------------

record Round202PatternReturn : Set where
  constructor round202-pattern-return
  field
    donorPR : Nat
    donorCodeImported : Bool
    donorCodeImportedIsFalse : donorCodeImported ≡ false
    residualNegativityRequired : Bool
    residualNegativityRequiredIsFalse : residualNegativityRequired ≡ false
    quantitativeResidualBudgetPreferred : Bool
    quantitativeResidualBudgetPreferredIsTrue :
      quantitativeResidualBudgetPreferred ≡ true
    boundedReading : String

canonicalRound202PatternReturn : Round202PatternReturn
canonicalRound202PatternReturn =
  round202-pattern-return 627 false refl false refl true refl
    "Round202 independently confirms the architecture: exact covariance/Gram algebra first, then allow positive residual debt when a quantitative budget fits below the usable margin. Shared theorem shape does not identify Navier-Stokes with the Riemann lane."

record AristotleAgdaSyncBoundary : Set where
  constructor aristotle-agda-sync-boundary
  field
    leanProofIsAgdaProof : Bool
    leanProofIsAgdaProofIsFalse : leanProofIsAgdaProof ≡ false
    absoluteMassMajorizationStillPreferred : Bool
    absoluteMassMajorizationStillPreferredIsFalse :
      absoluteMassMajorizationStillPreferred ≡ false
    selectedNuisanceSchurBeforeTailMajorization : Bool
    selectedNuisanceSchurBeforeTailMajorizationIsTrue :
      selectedNuisanceSchurBeforeTailMajorization ≡ true
    residualSignTheoremRequired : Bool
    residualSignTheoremRequiredIsFalse : residualSignTheoremRequired ≡ false
    normalizedEndpointTransportClosed : Bool
    normalizedEndpointTransportClosedIsFalse :
      normalizedEndpointTransportClosed ≡ false
    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

canonicalAristotleAgdaSyncBoundary : AristotleAgdaSyncBoundary
canonicalAristotleAgdaSyncBoundary =
  aristotle-agda-sync-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
