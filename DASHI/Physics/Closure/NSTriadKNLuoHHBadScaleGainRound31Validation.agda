module DASHI.Physics.Closure.NSTriadKNLuoHHBadScaleGainRound31Validation where

------------------------------------------------------------------------
-- Round Thirty-One validation root.
--
-- This root first imports the complete Round-30 concrete Galerkin flow root,
-- then exercises the new HH-bad time-scale absorption, the same-object
-- Galerkin builder interface, and the admissible remainder grammar.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalGalerkinFlowRound30Validation
import DASHI.Physics.Closure.NSTriadKNHHBadTimeScaleGainRound31Exact as HHBad
import DASHI.Physics.Closure.NSTriadKNSameCarrierSameObjectRound31Exact as SameObject
import DASHI.Physics.Closure.NSTriadKNAdmissibleRemainderGrammarRound31Exact as Remainder

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

hhBadTimeScaleRegression :
  HHBad.hhBadTimeScaleGainAlgebraClosed ≡ true
hhBadTimeScaleRegression =
  HHBad.hhBadTimeScaleGainAlgebraClosedIsTrue

hhBadFiniteOccupationRegression :
  HHBad.hhBadFiniteOccupationAbsorptionClosed ≡ true
hhBadFiniteOccupationRegression =
  HHBad.hhBadFiniteOccupationAbsorptionClosedIsTrue

hhBadCriticalOccupationRegression :
  HHBad.hhBadExactCriticalOccupationIdentityClosed ≡ true
hhBadCriticalOccupationRegression =
  HHBad.hhBadExactCriticalOccupationIdentityClosedIsTrue

sameCarrierSameObjectRegression :
  SameObject.sameCarrierSameObjectInterfaceClosed ≡ true
sameCarrierSameObjectRegression =
  SameObject.sameCarrierSameObjectInterfaceClosedIsTrue

admissibleRemainderGrammarRegression :
  Remainder.admissibleRemainderGrammarClosed ≡ true
admissibleRemainderGrammarRegression =
  Remainder.admissibleRemainderGrammarClosedIsTrue

remainderCompilerRegression :
  Remainder.grammarCompilesToOwnerLanguage ≡ true
remainderCompilerRegression =
  Remainder.grammarCompilesToOwnerLanguageIsTrue
