module DASHI.Physics.Gravity.KSW668AdS5MovingNeumannFluxRationalExact where

------------------------------------------------------------------------
-- Source-equivalent Agda rational witness for ORIGINAL a=t Israel
-- Neumann wall at t=4/3, using existing rational qplus and qminus.
--
-- v=-3/5, beta=1/4, qplus=1/8, source G=1/12, qminus=-7/96.
-- Positive characteristic flux into y>=0:
--    F=(1-v)qminus²-(1+v)qplus² = 13/5760.
-- Exact completed-square:
--    F+(3/10)(qplus+(5/3)G)²=(10/3)G².
-- Nonnegative square implies F <= (10/3)G² for THIS slice.
--
-- General real t in [1,2] source-level derivation is
-- F=2v beta(qplus-G/v)²-(2/v)G² <=2sqrt5 G²;
-- real sqrt, full coupled moving/temporal discretization, Agda 2.9
-- kernel run, and detector Weyl remain independent OPEN gates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5MovingNeumannCharacteristicRationalExact as N

originalRationalCharacteristicFlux : ℚ
originalRationalCharacteristicFlux =
  ((+ 8) / 5) * N.qIncoming * N.qIncoming
  + - (((+ 2) / 5) * N.qOutgoing * N.qOutgoing)

originalRationalFluxValue :
  originalRationalCharacteristicFlux ≡ (+ 13) / 5760
originalRationalFluxValue = solve []

originalRationalFluxExactSquare :
  originalRationalCharacteristicFlux
    + ((+ 3) / 10)
      * (N.qOutgoing + ((+ 5) / 3) * N.sourceG)
      * (N.qOutgoing + ((+ 5) / 3) * N.sourceG)
  ≡ ((+ 10) / 3) * N.sourceG * N.sourceG
originalRationalFluxExactSquare = solve []
