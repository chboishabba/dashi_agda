module DASHI.Analysis.RiemannAristotleReflectionSymmetrizationReturnExact where

------------------------------------------------------------------------
-- LEAN SOURCE RETURN: EXACT INFINITE REFLECTION SYMMETRIZATION
--
-- New Lean source owner:
--
--   LiteralWeilOffOrdinateReflectionSymmetrization.lean
--
-- The source implements the involutive reindex of the actual off-ordinate zero
-- carrier and rewrites the whole projective zero tail as
--
--   Z_off^proj
--     = 1/2 * sum_{rho off-ordinate}
--         m_rho * integral [4 h_r(u) cosh(a_rho u) cos((Im rho-t)u)] du.
--
-- No arbitrary representative from each reflection orbit is chosen.  Fixed
-- critical-line zeros and two-cycles are handled uniformly by the involutive
-- symmetrization.  This is the exact carrier on which the remaining signed
-- oscillatory estimate should be proved.
--
-- The new Lean file is source-level in this return: no new kernel receipt is
-- claimed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record ReflectionSymmetrizationReturn : Set where
  constructor reflection-symmetrization-return
  field
    sourceImplementedInLean : Bool
    sourceImplementedInLeanIsTrue : sourceImplementedInLean ≡ true
    machineCheckedInLeanForThisReturn : Bool
    machineCheckedInLeanForThisReturnIsFalse :
      machineCheckedInLeanForThisReturn ≡ false
    transportedIntoAgda : Bool
    transportedIntoAgdaIsFalse : transportedIntoAgda ≡ false

    exactInvolutionReindexUsed : Bool
    exactInvolutionReindexUsedIsTrue : exactInvolutionReindexUsed ≡ true
    arbitraryOrbitRepresentativesChosen : Bool
    arbitraryOrbitRepresentativesChosenIsFalse : arbitraryOrbitRepresentativesChosen ≡ false
    absoluteValuesTakenBeforeReflectionPairing : Bool
    absoluteValuesTakenBeforeReflectionPairingIsFalse :
      absoluteValuesTakenBeforeReflectionPairing ≡ false

    signedOscillatoryTailEstimateClosed : Bool
    signedOscillatoryTailEstimateClosedIsFalse :
      signedOscillatoryTailEstimateClosed ≡ false

    boundedReading : String

open ReflectionSymmetrizationReturn public

canonicalReflectionSymmetrizationReturn : ReflectionSymmetrizationReturn
canonicalReflectionSymmetrizationReturn =
  reflection-symmetrization-return
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
    "The exact U3 carrier is now the involutively symmetrized literal off-ordinate zero sum with the reflection-pair cosine kernel. The remaining theorem is a signed oscillatory estimate on this carrier; the old positive W(t) majorant is no longer the target object."
