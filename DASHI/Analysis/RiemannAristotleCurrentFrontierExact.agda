module DASHI.Analysis.RiemannAristotleCurrentFrontierExact where

------------------------------------------------------------------------
-- AUTHORITATIVE CURRENT FRONTIER FOR THE ARISTOTLE / RH LANE
--
-- This owner is maintained bidirectionally: forward from exact source owners
-- and backward from what a uniform off-line contradiction actually needs.
--
-- CLOSED IN THE LEAN OWNER / EXISTING BRIDGE
--
--  * the positive same-ordinate even-cone construction exists for every target
--    at nonzero ordinate and annihilates the base pole class;
--  * the two-radius cluster height defect is the actual off-line discriminator:
--    it is strictly positive if the fibre contains an off-line zero and exactly
--    zero when the fibre is entirely on-line;
--  * in the high-ordinate short-support lane, the prime channel (and hence its
--    projective defect) is exactly zero;
--  * Gamma and pole projective defects already have explicit O(r^2) envelopes;
--  * the target zero defect already has an exact r^2 leading coefficient plus
--    an explicit r^4 remainder, so the old radius-scaling mismatch is closed;
--  * generic multi-taper Schur algebra eliminates two selected response vectors
--    exactly.
--
-- BIDI CORRECTIONS
--
--  1. The conditional three-zero / three-taper theorem is not the universal RH
--     bridge: one hypothetical off-line zero does not manufacture two additional
--     smaller positive-height zeros.
--
--  2. One-radius even-cone positivity is a universal observer construction but
--     is not itself an off-line signal; on-line fibres are positive there too.
--     The two-radius projective height defect is the signal consumed by E.
--
--  3. Because the horizontal displacement can be arbitrarily small, a final
--     uniform proof cannot simply absorb fixed positive Gamma/pole coefficient
--     budgets below a target coefficient that tends to zero with displacement.
--     The highest-leverage use of the Schur machinery is therefore to eliminate
--     the deterministic projective pole and Gamma response vectors EXACTLY.
--
-- NEW SOURCE-LEVEL LEAN RETURNS (new kernel receipt pending)
--
--  * functional-equation reflection pairs cancel the odd-height sinh*sin term
--    exactly and leave a signed cosine kernel in the ordinate gap;
--  * exact involutive symmetrization rewrites the entire off-ordinate projective
--    carrier using those signed pair kernels, without choosing orbit reps;
--  * `LiteralWeilDeterministicProjectiveSchur` vectorizes three short tapers and
--    proves, once the deterministic pole/Gamma vectors are independent,
--
--      elim2 D_pole D_Gamma D_cluster = elim2 D_pole D_Gamma D_off.
--
--    Thus prime, Gamma and pole can all have ZERO residual debt in the intended
--    high-ordinate lane: prime by support, Gamma/pole by exact Schur elimination.
--
-- HIGHEST-ALPHA REMAINING CUTSET
--
--   S1. construct three short positive tapers for every high target ordinate so
--       that the projective pole/Gamma nuisance vectors have rank two AND the
--       off-line same-ordinate cluster survives their Schur quotient with a
--       quantitative margin;
--
--   S2. prove a signed estimate for the exact reflection-symmetrized off-ordinate
--       zero carrier AFTER that deterministic Schur quotient.  Do not return to
--       the exhausted absolute W(t) majorant;
--
--   S3. certify the complementary low-ordinate region independently (or replace
--       the high/low split by a universal construction);
--
--   S4. feed S1+S2+S3 into the already-owned exact margin contradiction and the
--       repository's existing, unweakened RH proposition.
--
-- No theorem here derives RH.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record AristotleCurrentFrontier : Set where
  constructor aristotle-current-frontier
  field
    universalEvenConeConstructionClosedInLean : Bool
    universalEvenConeConstructionClosedInLeanIsTrue :
      universalEvenConeConstructionClosedInLean ≡ true

    twoRadiusOffLineDiscriminatorClosedInLean : Bool
    twoRadiusOffLineDiscriminatorClosedInLeanIsTrue :
      twoRadiusOffLineDiscriminatorClosedInLean ≡ true

    highOrdinatePrimeProjectiveDebtZeroInLean : Bool
    highOrdinatePrimeProjectiveDebtZeroInLeanIsTrue :
      highOrdinatePrimeProjectiveDebtZeroInLean ≡ true

    gammaProjectiveQuadraticEnvelopeClosedInLean : Bool
    gammaProjectiveQuadraticEnvelopeClosedInLeanIsTrue :
      gammaProjectiveQuadraticEnvelopeClosedInLean ≡ true
    poleProjectiveQuadraticEnvelopeClosedInLean : Bool
    poleProjectiveQuadraticEnvelopeClosedInLeanIsTrue :
      poleProjectiveQuadraticEnvelopeClosedInLean ≡ true
    targetLeadingCoefficientAndRemainderClosedInLean : Bool
    targetLeadingCoefficientAndRemainderClosedInLeanIsTrue :
      targetLeadingCoefficientAndRemainderClosedInLean ≡ true

    conditionalTwoZeroThreeTaperClosedInLean : Bool
    conditionalTwoZeroThreeTaperClosedInLeanIsTrue :
      conditionalTwoZeroThreeTaperClosedInLean ≡ true
    conditionalTwoZeroIsUniversalRHBridge : Bool
    conditionalTwoZeroIsUniversalRHBridgeIsFalse :
      conditionalTwoZeroIsUniversalRHBridge ≡ false

    reflectionPairKernelSourceImplementedInLean : Bool
    reflectionPairKernelSourceImplementedInLeanIsTrue :
      reflectionPairKernelSourceImplementedInLean ≡ true
    reflectionSymmetrizedProjectiveCarrierSourceImplementedInLean : Bool
    reflectionSymmetrizedProjectiveCarrierSourceImplementedInLeanIsTrue :
      reflectionSymmetrizedProjectiveCarrierSourceImplementedInLean ≡ true
    deterministicProjectiveSchurCompilerSourceImplementedInLean : Bool
    deterministicProjectiveSchurCompilerSourceImplementedInLeanIsTrue :
      deterministicProjectiveSchurCompilerSourceImplementedInLean ≡ true
    newBidiLeanSourceMachineChecked : Bool
    newBidiLeanSourceMachineCheckedIsFalse : newBidiLeanSourceMachineChecked ≡ false

    deterministicNuisanceThreeTaperConstructionClosed : Bool
    deterministicNuisanceThreeTaperConstructionClosedIsFalse :
      deterministicNuisanceThreeTaperConstructionClosed ≡ false
    signedPostSchurOffOrdinateEstimateClosed : Bool
    signedPostSchurOffOrdinateEstimateClosedIsFalse :
      signedPostSchurOffOrdinateEstimateClosed ≡ false
    lowOrdinateComplementCertified : Bool
    lowOrdinateComplementCertifiedIsFalse :
      lowOrdinateComplementCertified ≡ false

    finalRHImplicationClosed : Bool
    finalRHImplicationClosedIsFalse : finalRHImplicationClosed ≡ false
    boundedReading : String

open AristotleCurrentFrontier public

canonicalAristotleCurrentFrontier : AristotleCurrentFrontier
canonicalAristotleCurrentFrontier =
  aristotle-current-frontier
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The off-line signal is the already-owned two-radius cluster height defect, not one-radius positivity. High-ordinate prime debt is exactly zero, Gamma and pole are deterministic projective nuisances, and new Lean source closes the exact compiler that Schur-eliminates those two vectors. The live research cutset is now: construct a short three-taper deterministic-nuisance rank-two observer with surviving off-line cluster; bound only the resulting signed reflection-symmetrized off-ordinate zero carrier; certify the complementary low-ordinate region; then invoke the existing margin/RH compiler."
