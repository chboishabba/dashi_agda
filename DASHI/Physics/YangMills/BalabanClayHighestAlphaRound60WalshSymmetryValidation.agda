module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound60WalshSymmetryValidation where

------------------------------------------------------------------------
-- Focused Round60 validation root.
--
-- This round does not duplicate the Round57 hypercubic orbit construction.
-- It moves one level deeper: exact character cancellation is derived from the
-- SAME CMP109 source reflection symmetry before the existing four-orbit
-- representative reduction and before Bishop intervalisation.
--
-- On G2, the same sixteen-element carrier is given its independent Walsh
-- character geometry and an exact counterexample proves that degree/S4
-- symmetry alone does not justify XOR-convolution diagonalisation.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound59PositiveRGGeometryValidation
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshMobiusSeparationExact
import DASHI.Physics.YangMills.BalabanCMP109WalshCharacterOrbitCancellationExact
import DASHI.Physics.YangMills.BalabanCMP109WalshFourOrbitFactorizationExact
