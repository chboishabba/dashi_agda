module DASHI.Physics.Closure.NSCompactGammaInwardBoundaryEstimates where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Nullary using (¬_)

open import DASHI.Physics.Closure.NSCompactGammaAdmissiblePreservation

------------------------------------------------------------------------
-- Theorem-facing A1--A12 refinement of compact-Gamma preservation.
--
-- The analytic inequalities remain explicit inputs.  This module owns their
-- exact logical composition into one-sided boundary signs, no-first-exit,
-- cutoff-uniform Galerkin preservation, and closed continuum-limit passage.
------------------------------------------------------------------------

record ScalarOperations {s : Level} (O : OrderedScalar s) : Set (lsuc s) where
  field
    zero : Scalar O
    _+_ _-_ _*_ _/_ : Scalar O → Scalar O → Scalar O
    abs : Scalar O → Scalar O
open ScalarOperations public

------------------------------------------------------------------------
-- A1--A2: regularity of all defining functionals.
------------------------------------------------------------------------

A1-continuity-along-selected-path :
  ∀ {t s st sh}
    {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s} {C : ContinuityStructure Time O}
    {S : CompactGammaSystem O State Shell}
    {p : Path Time State} {K : Shell} →
  CompactGammaPathContinuity C S p K →
  Σ (Continuous C (λ τ → packetEnergy S K (at p τ))) (λ _ →
  Σ (Continuous C (λ τ → gamma S K (at p τ))) (λ _ →
  Σ (Continuous C (λ τ → stateSize S (at p τ))) (λ _ →
      Continuous C (λ τ → offPacketRatio S K (at p τ)))))
A1-continuity-along-selected-path c =
  packetEnergyContinuous c , gammaContinuous c ,
  sizeContinuous c , offPacketRatioContinuous c

record DiniDerivativeStructure {t s : Level}
    (Time : Set t) (O : OrderedScalar s) : Set (lsuc (t ⊔ s)) where
  field
    lowerDini upperDini : (Time → Scalar O) → Time → Scalar O
open DiniDerivativeStructure public

record StrongIntervalDiniRegularity
    {t s st sh : Level}
    {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s}
    (D : DiniDerivativeStructure Time O)
    (S : CompactGammaSystem O State Shell)
    (p : Path Time State) (K : Shell) : Set (lsuc (t ⊔ s ⊔ st ⊔ sh)) where
  field
    energyLowerDiniExists gammaLowerDiniExists : Time → Set s
    sizeUpperDiniExists ratioUpperDiniExists : Time → Set s
open StrongIntervalDiniRegularity public

A2-dini-derivatives-available :
  ∀ {t s st sh}
    {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s} {D : DiniDerivativeStructure Time O}
    {S : CompactGammaSystem O State Shell}
    {p : Path Time State} {K : Shell} →
  StrongIntervalDiniRegularity D S p K → ∀ τ →
  Σ (Set s) (λ _ → Σ (Set s) (λ _ → Σ (Set s) (λ _ → Set s)))
A2-dini-derivatives-available r τ =
  energyLowerDiniExists r τ , gammaLowerDiniExists r τ ,
  sizeUpperDiniExists r τ , ratioUpperDiniExists r τ

------------------------------------------------------------------------
-- A3--A4: packet-energy boundary.
------------------------------------------------------------------------

record PacketEnergyBoundary {t s : Level}
    {O : OrderedScalar s} (A : ScalarOperations O) (Time : Set t) :
    Set (lsuc (t ⊔ s)) where
  field
    boundaryActive : Time → Set s
    twiceViscousDissipation nearTransfer farTransfer : Time → Scalar O
    energyDerivative deltaEnergy : Scalar O
    exactEnergyEquation : ∀ τ →
      energyDerivative ≡
      ((nearTransfer τ + farTransfer τ) A - twiceViscousDissipation τ) A
    nearReplenishes : ∀ τ → boundaryActive τ →
      _≤_ O
        (((twiceViscousDissipation τ + deltaEnergy) A +
          abs A (farTransfer τ)) A)
        (nearTransfer τ)
    inwardEnergy : ∀ τ → boundaryActive τ →
      _≤_ O deltaEnergy energyDerivative
open PacketEnergyBoundary public

A3-near-replenishment-lower-bound :
  ∀ {t s} {Time : Set t} {O : OrderedScalar s}
    {A : ScalarOperations O} →
  (E : PacketEnergyBoundary A Time) → ∀ τ → boundaryActive E τ →
  _≤_ O
    (((twiceViscousDissipation E τ + deltaEnergy E) A +
      abs A (farTransfer E τ)) A)
    (nearTransfer E τ)
A3-near-replenishment-lower-bound E = nearReplenishes E

A4-inward-packet-energy-derivative :
  ∀ {t s} {Time : Set t} {O : OrderedScalar s}
    {A : ScalarOperations O} →
  (E : PacketEnergyBoundary A Time) → ∀ τ → boundaryActive E τ →
  _≤_ O (deltaEnergy E) (energyDerivative E)
A4-inward-packet-energy-derivative E = inwardEnergy E

------------------------------------------------------------------------
-- A5--A7: compact-Gamma near gain and absorbed far tail.
------------------------------------------------------------------------

record CompactGammaBoundary {t s : Level}
    {O : OrderedScalar s} (A : ScalarOperations O) (Time : Set t) :
    Set (lsuc (t ⊔ s)) where
  field
    boundaryActive : Time → Set s
    inwardContribution nearError tailError lowerDiniGamma : Time → Scalar O
    deltaGamma halfDeltaGamma : Scalar O
    decompositionLowerBound : ∀ τ →
      _≤_ O
        (((inwardContribution τ - nearError τ) A - tailError τ) A)
        (lowerDiniGamma τ)
    nearShellGain : ∀ τ → boundaryActive τ →
      _≤_ O ((deltaGamma + tailError τ) A)
        ((inwardContribution τ - nearError τ) A)
    tailAbsorbed : ∀ τ → _≤_ O (tailError τ) halfDeltaGamma
    strictInward : ∀ τ → boundaryActive τ →
      _≤_ O halfDeltaGamma (lowerDiniGamma τ)
open CompactGammaBoundary public

record TailRadiusChoice {s : Level} {O : OrderedScalar s}
    (A : ScalarOperations O) : Set (lsuc s) where
  field
    radius decayAtRadius admissibleConstant halfDelta : Scalar O
    chosen : _≤_ O ((decayAtRadius * admissibleConstant) A) halfDelta
open TailRadiusChoice public

A5-near-shell-boundary-gain :
  ∀ {t s} {Time : Set t} {O : OrderedScalar s}
    {A : ScalarOperations O} →
  (G : CompactGammaBoundary A Time) → ∀ τ → boundaryActive G τ →
  _≤_ O ((deltaGamma G + tailError G τ) A)
    ((inwardContribution G τ - nearError G τ) A)
A5-near-shell-boundary-gain G = nearShellGain G

A6-absorbed-far-tail-estimate :
  ∀ {t s} {Time : Set t} {O : OrderedScalar s}
    {A : ScalarOperations O} →
  (G : CompactGammaBoundary A Time) → ∀ τ →
  _≤_ O (tailError G τ) (halfDeltaGamma G)
A6-absorbed-far-tail-estimate G = tailAbsorbed G

A7-strict-inward-compact-gamma-boundary :
  ∀ {t s} {Time : Set t} {O : OrderedScalar s}
    {A : ScalarOperations O} →
  (G : CompactGammaBoundary A Time) → ∀ τ → boundaryActive G τ →
  _≤_ O (halfDeltaGamma G) (lowerDiniGamma G τ)
A7-strict-inward-compact-gamma-boundary G = strictInward G

------------------------------------------------------------------------
-- A8--A9: expenditure-margin alternative.
------------------------------------------------------------------------

record GammaExpenditureMargin
    {t s st sh : Level}
    {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s}
    (A : ScalarOperations O)
    (S : CompactGammaSystem O State Shell)
    (p : Path Time State) (K : Shell) : Set (lsuc (t ⊔ s ⊔ st ⊔ sh)) where
  field
    initialTime : Time
    accumulatedLoss : Time → Scalar O
    reserveBudget gammaFloorValue : Scalar O
    lossBound : ∀ τ →
      _≤_ O
        ((gamma S K (at p initialTime) - accumulatedLoss τ) A)
        (gamma S K (at p τ))
    initialReserveSufficient :
      _<_ O reserveBudget
        ((gamma S K (at p initialTime) - gammaFloorValue) A)
    lossBelowBudget : ∀ τ → _≤_ O (accumulatedLoss τ) reserveBudget
    strictFloor : ∀ τ → _<_ O gammaFloorValue (gamma S K (at p τ))
    backwardReserve : Time → Scalar O
    backwardReservePositiveInitially : Set s
    backwardReserveRemainsPositive : ∀ τ → Set s
open GammaExpenditureMargin public

A8-accumulated-loss-bound :
  ∀ {t s st sh}
    {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s} {A : ScalarOperations O}
    {S : CompactGammaSystem O State Shell}
    {p : Path Time State} {K : Shell} →
  (M : GammaExpenditureMargin A S p K) → ∀ τ →
  _≤_ O
    ((gamma S K (at p (initialTime M)) - accumulatedLoss M τ) A)
    (gamma S K (at p τ))
A8-accumulated-loss-bound M = lossBound M

A9-sufficient-initial-reserve :
  ∀ {t s st sh}
    {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s} {A : ScalarOperations O}
    {S : CompactGammaSystem O State Shell}
    {p : Path Time State} {K : Shell} →
  (M : GammaExpenditureMargin A S p K) → ∀ τ →
  _<_ O (gammaFloorValue M) (gamma S K (at p τ))
A9-sufficient-initial-reserve M = strictFloor M

------------------------------------------------------------------------
-- A10--A11: upper norm and off-packet-ratio boundaries.
------------------------------------------------------------------------

record XNormBoundary {t s : Level} {O : OrderedScalar s}
    (Time : Set t) : Set (lsuc (t ⊔ s)) where
  field
    boundaryActive : Time → Set s
    upperDiniSizeSquared negativeMargin : Scalar O
    strictInward : ∀ τ → boundaryActive τ →
      _≤_ O upperDiniSizeSquared negativeMargin
open XNormBoundary public

A10-X-norm-inward-estimate :
  ∀ {t s} {Time : Set t} {O : OrderedScalar s} →
  (X : XNormBoundary {O = O} Time) → ∀ τ → boundaryActive X τ →
  _≤_ O (upperDiniSizeSquared X) (negativeMargin X)
A10-X-norm-inward-estimate X = strictInward X

record OffPacketRatioBoundary {t s : Level} {O : OrderedScalar s}
    (Time : Set t) : Set (lsuc (t ⊔ s)) where
  field
    boundaryActive positiveDenominator divisionFreeContinuation : Time → Set s
    upperDiniRatio negativeMargin : Scalar O
    strictInward : ∀ τ → boundaryActive τ → positiveDenominator τ →
      _≤_ O upperDiniRatio negativeMargin
    zeroDenominatorContinues : ∀ τ →
      ¬ positiveDenominator τ → divisionFreeContinuation τ
open OffPacketRatioBoundary public

A11-inward-off-packet-derivative :
  ∀ {t s} {Time : Set t} {O : OrderedScalar s} →
  (R : OffPacketRatioBoundary {O = O} Time) → ∀ τ →
  boundaryActive R τ → positiveDenominator R τ →
  _≤_ O (upperDiniRatio R) (negativeMargin R)
A11-inward-off-packet-derivative R = strictInward R

------------------------------------------------------------------------
-- A12: invariant region, cutoff uniformity, and continuum closedness.
------------------------------------------------------------------------

record CompactGammaInvariantRegionInputs
    {t s st sh : Level}
    {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s}
    (C : ContinuityStructure Time O)
    (S : CompactGammaSystem O State Shell)
    (B : CompactGammaThresholds O)
    (p : Path Time State) (K : Shell) : Set (lsuc (t ⊔ s ⊔ st ⊔ sh)) where
  field
    definingFunctionalsContinuous : CompactGammaPathContinuity C S p K
    initialInterior : Set (s ⊔ st)
    activeLowerBoundariesHaveNonnegativeLowerDini : Time → Set s
    activeUpperBoundariesHaveNonpositiveUpperDini : Time → Set s
    denominatorZeroUsesDivisionFreeBranch : Time → Set s
    firstExitComplete : FirstExitCompleteness S B p K
    firstExitContradiction : NoFirstExitInputs {S = S} {B = B} p K
open CompactGammaInvariantRegionInputs public

A12-compact-gamma-invariant-region :
  ∀ {t s st sh}
    {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s} {C : ContinuityStructure Time O}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State} {K : Shell} →
  CompactGammaInvariantRegionInputs C S B p K →
  ∀ τ → CompactGammaAdmissible S B K (at p τ)
A12-compact-gamma-invariant-region I =
  compactGammaInvariantRegion (firstExitComplete I) (firstExitContradiction I)

record UniformInwardBoundaryGalerkinCertificate
    {n t s st sh : Level}
    {Cutoff : Set n} {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s}
    (S : CompactGammaSystem O State Shell)
    (B : CompactGammaThresholds O)
    (selection : ShellSelection Shell)
    (G : GalerkinFamily Cutoff Time State) :
    Set (lsuc (n ⊔ t ⊔ s ⊔ st ⊔ sh)) where
  field
    constantsIndependentOfCutoff : Set s
    invariantAtEveryCutoff : ∀ N τ →
      ShellFamilyAdmissible S B selection (at (galerkinPath G N) τ)
open UniformInwardBoundaryGalerkinCertificate public

uniform-boundary-certificate-gives-preservation :
  ∀ {n t s st sh}
    {Cutoff : Set n} {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {selection : ShellSelection Shell}
    {G : GalerkinFamily Cutoff Time State} →
  UniformInwardBoundaryGalerkinCertificate S B selection G →
  UniformGalerkinPreservation S B selection G
uniform-boundary-certificate-gives-preservation U = record
  { preservedUniformlyInCutoff = invariantAtEveryCutoff U }

closed-inward-region-passes-to-continuum :
  ∀ {n t s st sh}
    {Cutoff : Set n} {Time : Set t} {State : Set st} {Shell : Set sh}
    {O : OrderedScalar s}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {selection : ShellSelection Shell}
    {G : GalerkinFamily Cutoff Time State}
    {limitPath : Path Time State}
    {L : GalerkinCompactnessLimit G limitPath} →
  UniformInwardBoundaryGalerkinCertificate S B selection G →
  ClosedAdmissibleInequalities S B selection G limitPath L →
  ∀ τ → ShellFamilyAdmissible S B selection (at limitPath τ)
closed-inward-region-passes-to-continuum uniform closed =
  galerkinPreservationPassesToLimit
    (uniform-boundary-certificate-gives-preservation uniform) closed
