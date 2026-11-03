{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkNambuGotoBubbleDynamicsLeanBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CROSS-KERNEL SOURCE RECEIPT
--
-- Lean owner: Synthesis/NambuGotoBubbleDynamics.lean
--
-- For the selected Nambu-Goto fixture
--   M=2/9, Lambda_in=21/64, Lambda_out=19/48, 8*pi*sigma=1/4,
-- and the standard spherical Israel jump law, Lean reduces the exact velocity
-- constraint to
--
-- Rdot^2 = (R-2)^2 (43R^4+172R^3+192R^2+256R+256)/(324R^4).
--
-- Thus R=2 is an exact turning point and the squared velocity is positive for
-- every positive R != 2.  The Israel junction law is still a physical authority
-- input; CMP119/history dynamics selecting one branch/trajectory is not derived.
------------------------------------------------------------------------

leanOwner : String
leanOwner = "Synthesis/NambuGotoBubbleDynamics.lean"

selectedBubbleJunctionFactorizationSourceWritten : Bool
selectedBubbleJunctionFactorizationSourceWritten = true

radiusTwoTurningPointSourceWritten : Bool
radiusTwoTurningPointSourceWritten = true

positiveSquaredVelocityAwayFromTurningPointSourceWritten : Bool
positiveSquaredVelocityAwayFromTurningPointSourceWritten = true

movingShellAuthorityStillRequired : Bool
movingShellAuthorityStillRequired = true

historySourceSelectsTrajectoryStillRequired : Bool
historySourceSelectsTrajectoryStillRequired = true

leanKernelReceiptClaimedInThisAgdaOwner : Bool
leanKernelReceiptClaimedInThisAgdaOwner = false
