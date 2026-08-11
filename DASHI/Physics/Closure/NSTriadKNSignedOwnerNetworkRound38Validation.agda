module DASHI.Physics.Closure.NSTriadKNSignedOwnerNetworkRound38Validation where

-- The main Round-38 validation root already imports the concrete cancellation
-- edge and path.  This small cumulative root additionally exercises the exact
-- reserve-gain theorem consumed by the future certified owner optimizer.
open import DASHI.Physics.Closure.NSTriadKNResidualTransportOwnerFlowRound38Validation
open import DASHI.Physics.Closure.NSTriadKNSignedOwnerReserveGainRound38Exact
