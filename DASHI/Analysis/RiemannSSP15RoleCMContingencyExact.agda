module DASHI.Analysis.RiemannSSP15RoleCMContingencyExact where

------------------------------------------------------------------------
-- RH ROLE-COLUMN / CM-CLASS CONTINGENCY TABLE
--
-- Using the explicitly CHOSEN 5 x 3 SSP15 role-grid indexing and the
-- independently source-backed Q(sqrt(-7)) CM splitting table:
--
--                  split   inert   ramified
--   originRole       2       2        1
--   jRole            1       4        0
--   sRole            2       3        0
--
-- Row sums are 5,5,5.  Column sums are exactly the canonical CM counts 5,9,1.
--
-- This is a repository cross-classification theorem.  It does not make the
-- chosen role grid into the CM partition; rather it quantifies their
-- transversality.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact as Codec
import DASHI.Analysis.RiemannSSP15ChosenGridTransversalityExact as Grid
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Moonshine.SSP15AffineC3TranslationExact as Native
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM

data CMClassIndex : Set where
  splitClass inertClass ramifiedClass : CMClassIndex

classIndex :
  CM.CMPrimeSplittingClass ->
  CMClassIndex
classIndex CM.split = splitClass
classIndex CM.inert = inertClass
classIndex CM.ramified = ramifiedClass

modeList : List Nonary.ComplementMode5
modeList =
  Nonary.mode09
  ∷ Nonary.mode18
  ∷ Nonary.mode27
  ∷ Nonary.mode36
  ∷ Nonary.mode45
  ∷ []

countClassForRole :
  Codec.RHDepthFiveRole ->
  CMClassIndex ->
  Nat
countClassForRole Codec.originRole splitClass = 2
countClassForRole Codec.originRole inertClass = 2
countClassForRole Codec.originRole ramifiedClass = 1
countClassForRole Codec.jRole splitClass = 1
countClassForRole Codec.jRole inertClass = 4
countClassForRole Codec.jRole ramifiedClass = 0
countClassForRole Codec.sRole splitClass = 2
countClassForRole Codec.sRole inertClass = 3
countClassForRole Codec.sRole ramifiedClass = 0

originContingency :
  (countClassForRole Codec.originRole splitClass ≡ 2)
  × (countClassForRole Codec.originRole inertClass ≡ 2)
  × (countClassForRole Codec.originRole ramifiedClass ≡ 1)
originContingency = refl , (refl , refl)

jContingency :
  (countClassForRole Codec.jRole splitClass ≡ 1)
  × (countClassForRole Codec.jRole inertClass ≡ 4)
  × (countClassForRole Codec.jRole ramifiedClass ≡ 0)
jContingency = refl , (refl , refl)

sContingency :
  (countClassForRole Codec.sRole splitClass ≡ 2)
  × (countClassForRole Codec.sRole inertClass ≡ 3)
  × (countClassForRole Codec.sRole ramifiedClass ≡ 0)
sContingency = refl , (refl , refl)

originRowSumIsFive :
  countClassForRole Codec.originRole splitClass
  + countClassForRole Codec.originRole inertClass
  + countClassForRole Codec.originRole ramifiedClass
  ≡ 5
originRowSumIsFive = refl

jRowSumIsFive :
  countClassForRole Codec.jRole splitClass
  + countClassForRole Codec.jRole inertClass
  + countClassForRole Codec.jRole ramifiedClass
  ≡ 5
jRowSumIsFive = refl

sRowSumIsFive :
  countClassForRole Codec.sRole splitClass
  + countClassForRole Codec.sRole inertClass
  + countClassForRole Codec.sRole ramifiedClass
  ≡ 5
sRowSumIsFive = refl

splitColumnSumIsFive :
  countClassForRole Codec.originRole splitClass
  + countClassForRole Codec.jRole splitClass
  + countClassForRole Codec.sRole splitClass
  ≡ 5
splitColumnSumIsFive = refl

inertColumnSumIsNine :
  countClassForRole Codec.originRole inertClass
  + countClassForRole Codec.jRole inertClass
  + countClassForRole Codec.sRole inertClass
  ≡ 9
inertColumnSumIsNine = refl

ramifiedColumnSumIsOne :
  countClassForRole Codec.originRole ramifiedClass
  + countClassForRole Codec.jRole ramifiedClass
  + countClassForRole Codec.sRole ramifiedClass
  ≡ 1
ramifiedColumnSumIsOne = refl

splitColumnMatchesCanonicalCMCount :
  countClassForRole Codec.originRole splitClass
  + countClassForRole Codec.jRole splitClass
  + countClassForRole Codec.sRole splitClass
  ≡ CM.splitCount CM.canonicalSSP15CMFieldSplittingCorrectionReceipt
splitColumnMatchesCanonicalCMCount = refl

inertColumnMatchesCanonicalCMCount :
  countClassForRole Codec.originRole inertClass
  + countClassForRole Codec.jRole inertClass
  + countClassForRole Codec.sRole inertClass
  ≡ CM.inertCount CM.canonicalSSP15CMFieldSplittingCorrectionReceipt
inertColumnMatchesCanonicalCMCount = refl

ramifiedColumnMatchesCanonicalCMCount :
  countClassForRole Codec.originRole ramifiedClass
  + countClassForRole Codec.jRole ramifiedClass
  + countClassForRole Codec.sRole ramifiedClass
  ≡ CM.ramifiedCount CM.canonicalSSP15CMFieldSplittingCorrectionReceipt
ramifiedColumnMatchesCanonicalCMCount = refl

------------------------------------------------------------------------
-- Concrete table calibration against the actual chosen prime columns.
------------------------------------------------------------------------

origin09Class :
  Native.cmClass (Grid.originPrimeAt Nonary.mode09) ≡ CM.split
origin09Class = refl

origin18Class :
  Native.cmClass (Grid.originPrimeAt Nonary.mode18) ≡ CM.ramified
origin18Class = refl

origin27Class :
  Native.cmClass (Grid.originPrimeAt Nonary.mode27) ≡ CM.inert
origin27Class = refl

origin36Class :
  Native.cmClass (Grid.originPrimeAt Nonary.mode36) ≡ CM.split
origin36Class = refl

origin45Class :
  Native.cmClass (Grid.originPrimeAt Nonary.mode45) ≡ CM.inert
origin45Class = refl

j09Class :
  Native.cmClass (Grid.jPrimeAt Nonary.mode09) ≡ CM.inert
j09Class = refl

j18Class :
  Native.cmClass (Grid.jPrimeAt Nonary.mode18) ≡ CM.split
j18Class = refl

j27Class :
  Native.cmClass (Grid.jPrimeAt Nonary.mode27) ≡ CM.inert
j27Class = refl

j36Class :
  Native.cmClass (Grid.jPrimeAt Nonary.mode36) ≡ CM.inert
j36Class = refl

j45Class :
  Native.cmClass (Grid.jPrimeAt Nonary.mode45) ≡ CM.inert
j45Class = refl

s09Class :
  Native.cmClass (Grid.sPrimeAt Nonary.mode09) ≡ CM.inert
s09Class = refl

s18Class :
  Native.cmClass (Grid.sPrimeAt Nonary.mode18) ≡ CM.inert
s18Class = refl

s27Class :
  Native.cmClass (Grid.sPrimeAt Nonary.mode27) ≡ CM.split
s27Class = refl

s36Class :
  Native.cmClass (Grid.sPrimeAt Nonary.mode36) ≡ CM.inert
s36Class = refl

s45Class :
  Native.cmClass (Grid.sPrimeAt Nonary.mode45) ≡ CM.split
s45Class = refl

record RiemannSSP15RoleCMContingencyBoundary : Set where
  constructor riemann-ssp15-role-cm-contingency-boundary
  field
    completeThreeByThreeCountTableOwned : Bool
    everyRoleRowSumsToFive : Bool
    cmColumnSumsFiveNineOne : Bool
    cmColumnSumsMatchCanonicalReceipt : Bool
    chosenGridIdentifiedWithCMPartition : Bool

canonicalRiemannSSP15RoleCMContingencyBoundary :
  RiemannSSP15RoleCMContingencyBoundary
canonicalRiemannSSP15RoleCMContingencyBoundary =
  riemann-ssp15-role-cm-contingency-boundary
    true true true true false
