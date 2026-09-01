module DASHI.Physics.Closure.NSTriadKNLiteralMixedCellGramPairClosedRound382Exact where

------------------------------------------------------------------------
-- ROUND382 / R380 WITH THE PROJECTOR-LINEARITY SOCKET DISCHARGED
--
-- R381 constructs the exact R292 helical damped-projector linearity from old
-- finite algebra.  Therefore R380's literal R94 -> R292 -> R291 chain has no
-- remaining local algebra premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNHelicalDampedProjectorLinearityRound381Exact as R381
import DASHI.Physics.Closure.NSTriadKNLiteralMixedCellGramPairRound380Exact as R380

F : C3.RealField _
F = Rational.rationalRealField

module ClosedLiteralPair
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Pair = R380.LiteralPair
    physicalSystem S
    (R381.canonicalHelicalDampedProjectorLinearity
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S)

  open Pair public

round382LiteralR94ToR291ChainClosed : Bool
round382LiteralR94ToR291ChainClosed = true

round382ProjectorLinearityStillCallerSupplied : Bool
round382ProjectorLinearityStillCallerSupplied = false

round382FiniteOffDiagonalAggregationClosed : Bool
round382FiniteOffDiagonalAggregationClosed = false

round382LiteralR94ToR291ChainClosedIsTrue :
  round382LiteralR94ToR291ChainClosed ≡ true
round382LiteralR94ToR291ChainClosedIsTrue = refl

round382ProjectorLinearityStillCallerSuppliedIsFalse :
  round382ProjectorLinearityStillCallerSupplied ≡ false
round382ProjectorLinearityStillCallerSuppliedIsFalse = refl
