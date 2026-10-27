{-# OPTIONS --safe #-}
module DASHI.Unified.TOEExistingNonPromotionReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false)
open import Data.Empty using (⊥)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Unified.GRQuantumProofTerms as GRTypes
import DASHI.Unified.GRQuantumProofTermRegression as GR
import DASHI.Physics.Closure.FiniteRegionalSpectrum as Spectrum

-- O: Attach existing exact non-promotion proofs to the TOE.
-- R: Reuse source owners. Do not copy proofs or redefine authority.
-- C: Expose precise field equalities and physical refusal.
-- S: A source-only or finite diagnostic is not terminal evidence.
-- L: This module owns only the adapter. It edits no ESD surface.
-- P: Existing owner modules and their proof terms must typecheck.
-- G: Authors of source theories and repository proof owners keep credit.
-- F: Run preflight and Agda on the consumers before kernel promotion.

toeAuthorityBundle : Authority.AuthorityNonPromotionBundle
toeAuthorityBundle = Authority.canonicalAuthorityNonPromotionBundle

toeAuthorityDoesNotPromote :
  Authority.promotesAnyAuthority toeAuthorityBundle ≡ false
toeAuthorityDoesNotPromote =
  Authority.promotesAnyAuthorityIsFalse toeAuthorityBundle

toeFiniteUVDoesNotCreateTerminalPhysicalMatch :
  GRTypes.UVSpectralClosed Spectrum.regulatedUVSurface → ⊥
toeFiniteUVDoesNotCreateTerminalPhysicalMatch =
  GR.regulatedUVCannotCloseWithoutPhysicalMatch
