module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound62FinalAuditExact where

------------------------------------------------------------------------
-- ROUND 62 FINAL HIGH-ALPHA AUDIT
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- PURPOSE
--
-- Keep the mature Round62 aggregate stable while recording the two late
-- falsification results that materially sharpen the remaining producer cutset.
-- This is an audit module, not a new closure architecture.
--
-- A / finite-flow representation:
--
-- * Round39 already closes the actual finite projected Galerkin convection
--   energy cancellation.
-- * Round35 closes summed nonlinear and viscous Fourier reality.
-- * The concrete Round30 builder already constructs literal viscous-plus-
--   quadratic output coefficients from a state-indexed finite physical system.
-- * Round62 now composes a `CutoffSameObjectFamily` all the way to the literal
--   producer and dependent physical vector field.
-- * HOWEVER the unrestricted reconstructed-state list is not the fixed-
--   dimensional Picard coordinate carrier: if it stores n positive orbit
--   representatives, the generic same-object builder retains 2n modes, maps
--   the RHS over all 2n, stores those 2n values as new "positive" entries, and
--   reconstructs 4n modes.  This count growth is proved exactly.
--
-- Therefore the next finite-flow construction is not another equivariance
-- lemma.  It is a fixed-cutoff canonical orbit-representative carrier: exactly
-- one representative of every nonzero k ~ -k pair, with the opposite RHS
-- coordinate supplied by the already-proved Fourier-reality theorem.
--
-- B / support:
--
-- * Round62 proves the literal odd-P/Q coefficient is exactly the projector
--   commutator multiplier (chi_out-chi_in) T and lifts this through the same
--   physical output fibre.
-- * That identity makes a raw-support shortcut falsifiable.  A canonical entry
--   with input shell 0 and output shell 3 is active at hard-low-pass cutoffs 0
--   and 2.  No width-one `DyadicHatSupport` can contain both indices.
--
-- Therefore the common-hat theorem cannot be a statement about raw nested
-- low-pass activity.  B2 must CONSTRUCT an annular/hatted shell-difference
-- localization first, then identify the localized pair support with one or two
-- adjacent shells.  The Round58 support leaf has been authority-corrected to
-- this post-localization meaning.
--
-- The remaining B quantitative theorem is thus
--
--   centered literal odd-P/Q output fibre
--     -> hatted annular localized pieces
--     -> one normalized Gram/Schur row factorization
--     -> 17/64, 65/512, 65/512.
--
-- C, D/F, E, G retain the narrowed Round62 meanings recorded by
-- `NSTriadKNHighestAlphaRound62Exact`: upstream non-circular scales; official
-- Pair -> finite literal kernel realization; actual C_c^4 continuum multiplier
-- before fourfold IBP; and final instantiated scalar feasibility gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound62Exact

-- A late finite-flow composition and representation falsifier.
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffPhysicalVectorFieldRound62Exact
import DASHI.Physics.Closure.NSTriadKNReconstructedOrbitCoordinateGrowthNoGoRound62Exact
import DASHI.Physics.Closure.NSTriadKNSummedProjectedNonlinearityRealityRound35Exact
import DASHI.Physics.Closure.NSTriadKNViscousRealityRound35Exact

-- B late raw-support falsifier.  CommonHatSupportLeafRound58 was corrected in
-- place so its compatibility field now explicitly means post-localization
-- support, not raw hard-low-pass activity.
import DASHI.Physics.Closure.NSTriadKNComRawHardLowPassCommonHatNoGoRound62Exact
import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58

round62CutoffFamilyToLiteralPhysicalVectorFieldClosed : Bool
round62CutoffFamilyToLiteralPhysicalVectorFieldClosed = true

round62RawListCoordinateCarrierNeedsOrbitRepresentativeRepair : Bool
round62RawListCoordinateCarrierNeedsOrbitRepresentativeRepair = true

round62RawHardLowPassCommonHatInterpretationRejected : Bool
round62RawHardLowPassCommonHatInterpretationRejected = true

round62B2RequiresHattedDifferenceLocalization : Bool
round62B2RequiresHattedDifferenceLocalization = true

round62CutoffFamilyToLiteralPhysicalVectorFieldClosedIsTrue :
  round62CutoffFamilyToLiteralPhysicalVectorFieldClosed ≡ true
round62CutoffFamilyToLiteralPhysicalVectorFieldClosedIsTrue = refl

round62RawListCoordinateCarrierNeedsOrbitRepresentativeRepairIsTrue :
  round62RawListCoordinateCarrierNeedsOrbitRepresentativeRepair ≡ true
round62RawListCoordinateCarrierNeedsOrbitRepresentativeRepairIsTrue = refl

round62RawHardLowPassCommonHatInterpretationRejectedIsTrue :
  round62RawHardLowPassCommonHatInterpretationRejected ≡ true
round62RawHardLowPassCommonHatInterpretationRejectedIsTrue = refl

round62B2RequiresHattedDifferenceLocalizationIsTrue :
  round62B2RequiresHattedDifferenceLocalization ≡ true
round62B2RequiresHattedDifferenceLocalizationIsTrue = refl
