module DASHI.Reasoning.Trialectic369LinearMultiplicityBasisSpecialisationCompilerExact where

------------------------------------------------------------------------
-- LINEAR MULTIPLICITY -> OPTIONAL FIN90 / 10x9 BASIS SPECIALISATION
--
-- DASHI CONTRIBUTION
--
-- The canonical Monster multiplicity route is linear:
--
--   S_zeta = Hom_E(H_zeta , W_zeta)
--
-- with an actual linear inertia action.
--
-- The repo's WrongType correction allows the historical finite-basis route
-- only after an EXPLICIT proof that the full action preserves a chosen basis.
-- Once that receipt is supplied, this module compiles the existing finite
-- trialectic coordinate machinery legitimately:
--
--   linear S_zeta action
--     + basis-preservation receipt
--       -> Fin90 basis permutation
--       -> Fine10 x SecondarySheet9
--       -> optional selected-9-sheet or Fricke-stable 18-block diagnostics.
--
-- No basis specialisation is manufactured from dimension or character data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Mixed
import DASHI.Reasoning.Trialectic369OutgoingSheet9MultiplicityRecognitionExact as Outgoing
import DASHI.Reasoning.Trialectic369OutgoingFineFrickeInvariantNoGoExact as FineFricke
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Geometry.HilbertLorentzForcing as Linear

------------------------------------------------------------------------
-- 1. Extract the basis permutation from the explicit specialisation receipt.
------------------------------------------------------------------------

LinearRouteGroup :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  Set
LinearRouteGroup route =
  Linear.Group
    (WrongType.linearAction
      (WrongType.linearRepresentation route))

basisSpecialisation :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  WrongType.PermutationBasisPromotionReceipt route ->
  WrongType.PermutationBasisSpecialisation
    (WrongType.linearRepresentation route)
basisSpecialisation =
  WrongType.oldFinNinetyRouteRequiresBasisPreservation

basisIndexAct :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  WrongType.PermutationBasisPromotionReceipt route ->
  LinearRouteGroup route ->
  Fin 90 ->
  Fin 90
basisIndexAct route receipt =
  WrongType.basisPermutation
    (basisSpecialisation route receipt)

basisActionAgreesWithLinearAction :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  (receipt : WrongType.PermutationBasisPromotionReceipt route) ->
  (g : LinearRouteGroup route) ->
  (i : Fin 90) ->
  Linear.act
    (WrongType.linearAction
      (WrongType.linearRepresentation route))
    g
    (WrongType.basisVector
      (basisSpecialisation route receipt)
      i)
  ≡
  WrongType.basisVector
    (basisSpecialisation route receipt)
    (basisIndexAct route receipt g i)
basisActionAgreesWithLinearAction route receipt =
  WrongType.actionPreservesChosenBasis
    (basisSpecialisation route receipt)

------------------------------------------------------------------------
-- 2. Compile canonical Fine10 x SecondarySheet9 coordinates.
------------------------------------------------------------------------

TenByNineSurface : Set
TenByNineSurface =
  Pointed.Fine10 × Pointed.SecondarySheet9

compiledTenByNineAct :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  (receipt : WrongType.PermutationBasisPromotionReceipt route) ->
  LinearRouteGroup route ->
  TenByNineSurface ->
  TenByNineSurface
compiledTenByNineAct route receipt g surface =
  Mixed.fin90ToTenByNine
    (basisIndexAct
      route receipt g
      (Mixed.tenByNineToFin90 surface))

compiledTenByNineIntertwines :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  (receipt : WrongType.PermutationBasisPromotionReceipt route) ->
  (g : LinearRouteGroup route) ->
  (i : Fin 90) ->
  Mixed.fin90ToTenByNine
    (basisIndexAct route receipt g i)
  ≡
  compiledTenByNineAct
    route receipt g
    (Mixed.fin90ToTenByNine i)
compiledTenByNineIntertwines route receipt g i
  rewrite Mixed.tenByNineAfterFin90 i = refl

------------------------------------------------------------------------
-- 3. Optional selected Fine10 fibre -> 9-state residual action.
------------------------------------------------------------------------

record SelectedFineBasisInvariant
    (route : WrongType.CanonicalLinearMultiplicityRoute)
    (receipt : WrongType.PermutationBasisPromotionReceipt route)
    : Set₁ where
  field
    selectedFine : Pointed.Fine10

    selectedFinePreserved :
      (g : LinearRouteGroup route) ->
      (sheet : Codec.Sheet9) ->
      proj₁
        (compiledTenByNineAct
          route receipt g
          (Outgoing.embedSecondaryAt selectedFine sheet))
      ≡ selectedFine

open SelectedFineBasisInvariant public

compiledSheet9Act :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  (receipt : WrongType.PermutationBasisPromotionReceipt route) ->
  SelectedFineBasisInvariant route receipt ->
  LinearRouteGroup route ->
  Codec.Sheet9 ->
  Codec.Sheet9
compiledSheet9Act route receipt invariant g sheet =
  Outgoing.projectSecondary
    (compiledTenByNineAct
      route receipt g
      (Outgoing.embedSecondaryAt
        (selectedFine invariant)
        sheet))

compiledSheet9Intertwines :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  (receipt : WrongType.PermutationBasisPromotionReceipt route) ->
  (invariant : SelectedFineBasisInvariant route receipt) ->
  (g : LinearRouteGroup route) ->
  (sheet : Codec.Sheet9) ->
  compiledTenByNineAct
    route receipt g
    (Outgoing.embedSecondaryAt
      (selectedFine invariant)
      sheet)
  ≡
  Outgoing.embedSecondaryAt
    (selectedFine invariant)
    (compiledSheet9Act
      route receipt invariant g sheet)
compiledSheet9Intertwines route receipt invariant g sheet
  with compiledTenByNineAct
        route receipt g
        (Outgoing.embedSecondaryAt
          (selectedFine invariant)
          sheet)
... | fine , secondary
  rewrite selectedFinePreserved invariant g sheet
        | Outgoing.secondaryCodecRoundTrip secondary = refl

------------------------------------------------------------------------
-- 4. Optional Fricke-like basis element -> 18-state stable mode block.
------------------------------------------------------------------------

record FineFrickeBasisElement
    (route : WrongType.CanonicalLinearMultiplicityRoute)
    (receipt : WrongType.PermutationBasisPromotionReceipt route)
    : Set₁ where
  field
    frickeGroupElement : LinearRouteGroup route

    fineProjectionIsFiniteFricke :
      (fine : Pointed.Fine10) ->
      (sheet : Codec.Sheet9) ->
      proj₁
        (compiledTenByNineAct
          route receipt frickeGroupElement
          (Outgoing.embedSecondaryAt fine sheet))
      ≡ FineFricke.fine10FiniteFricke fine

open FineFrickeBasisElement public

fineFrickeBasisElementRejectsSelectedFine :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  (receipt : WrongType.PermutationBasisPromotionReceipt route) ->
  FineFrickeBasisElement route receipt ->
  SelectedFineBasisInvariant route receipt ->
  ⊥
fineFrickeBasisElementRejectsSelectedFine
  route receipt element invariant =
  FineFricke.fine10FiniteFrickeNoFixedPoint
    (selectedFine invariant)
    fixed
  where
    zeroSheet : Codec.Sheet9
    zeroSheet = FineFricke.zeroOutgoingSheet

    fixed :
      FineFricke.fine10FiniteFricke
        (selectedFine invariant)
      ≡ selectedFine invariant
    fixed =
      trans
        (sym
          (fineProjectionIsFiniteFricke
            element
            (selectedFine invariant)
            zeroSheet))
        (selectedFinePreserved
          invariant
          (frickeGroupElement element)
          zeroSheet)

ModeBlock18 : Set
ModeBlock18 =
  Nonary.BinaryPhase × Codec.Sheet9

modeBlock18Count : Nat
modeBlock18Count = 2 * 9

modeBlock18CountIsEighteen :
  modeBlock18Count ≡ 18
modeBlock18CountIsEighteen = refl

fineAtModePhase :
  Nonary.ComplementMode5 ->
  Nonary.BinaryPhase ->
  Pointed.Fine10
fineAtModePhase mode phase =
  FineFricke.decimalToFine10
    (Nonary.decodeModePhase (mode , phase))

embedModeBlock18 :
  Nonary.ComplementMode5 ->
  ModeBlock18 ->
  TenByNineSurface
embedModeBlock18 mode (phase , sheet) =
  Outgoing.embedSecondaryAt
    (fineAtModePhase mode phase)
    sheet

fineFrickeAtModePhase :
  (mode : Nonary.ComplementMode5) ->
  (phase : Nonary.BinaryPhase) ->
  FineFricke.fine10FiniteFricke
    (fineAtModePhase mode phase)
  ≡
  fineAtModePhase mode
    (Nonary.flipBinaryPhase phase)
fineFrickeAtModePhase Nonary.mode09 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode09 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode18 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode18 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode27 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode27 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode36 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode36 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode45 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode45 Nonary.counterPhase = refl

compiledModeBlock18Act :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  (receipt : WrongType.PermutationBasisPromotionReceipt route) ->
  FineFrickeBasisElement route receipt ->
  Nonary.ComplementMode5 ->
  ModeBlock18 ->
  ModeBlock18
compiledModeBlock18Act
  route receipt element mode (phase , sheet) =
  Nonary.flipBinaryPhase phase ,
  Outgoing.projectSecondary
    (compiledTenByNineAct
      route receipt
      (frickeGroupElement element)
      (embedModeBlock18 mode (phase , sheet)))

compiledModeBlock18Intertwines :
  (route : WrongType.CanonicalLinearMultiplicityRoute) ->
  (receipt : WrongType.PermutationBasisPromotionReceipt route) ->
  (element : FineFrickeBasisElement route receipt) ->
  (mode : Nonary.ComplementMode5) ->
  (state : ModeBlock18) ->
  compiledTenByNineAct
    route receipt
    (frickeGroupElement element)
    (embedModeBlock18 mode state)
  ≡
  embedModeBlock18 mode
    (compiledModeBlock18Act
      route receipt element mode state)
compiledModeBlock18Intertwines
  route receipt element mode (phase , sheet)
  with compiledTenByNineAct
        route receipt
        (frickeGroupElement element)
        (embedModeBlock18 mode (phase , sheet))
... | fine , secondary
  rewrite fineProjectionIsFiniteFricke
            element
            (fineAtModePhase mode phase)
            sheet
        | fineFrickeAtModePhase mode phase
        | Outgoing.secondaryCodecRoundTrip secondary = refl

------------------------------------------------------------------------
-- 5. Firewalls.
------------------------------------------------------------------------

data LinearRouteCreatesBasisSpecialisation : Set where
data CharacterCreatesBasisSpecialisation : Set where
data Sheet9BasisChartCreatesLinearInvariantSubspace : Set where

linearRouteDoesNotCreateBasisSpecialisation :
  LinearRouteCreatesBasisSpecialisation -> ⊥
linearRouteDoesNotCreateBasisSpecialisation ()

characterDoesNotCreateBasisSpecialisation :
  CharacterCreatesBasisSpecialisation -> ⊥
characterDoesNotCreateBasisSpecialisation ()

sheet9ChartDoesNotCreateLinearInvariantSubspace :
  Sheet9BasisChartCreatesLinearInvariantSubspace -> ⊥
sheet9ChartDoesNotCreateLinearInvariantSubspace ()

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

record Trialectic369LinearMultiplicityBasisSpecialisationBoundary : Set where
  constructor trialectic-369-linear-multiplicity-basis-specialisation-boundary
  field
    canonicalLinearRouteUsed : Bool
    explicitBasisPreservationReceiptRequired : Bool
    fin90BasisActionCompiledFromReceipt : Bool
    tenByNineActionCompiled : Bool
    selectedNineSheetCompilerAvailable : Bool
    frickeLikeNineSheetNoGoAvailable : Bool
    frickeStableEighteenBlockCompilerAvailable : Bool
    basisSpecialisationInhabitedHere : Bool
    sheet9PromotedToLinearInvariantSubspace : Bool

canonicalTrialectic369LinearMultiplicityBasisSpecialisationBoundary :
  Trialectic369LinearMultiplicityBasisSpecialisationBoundary
canonicalTrialectic369LinearMultiplicityBasisSpecialisationBoundary =
  trialectic-369-linear-multiplicity-basis-specialisation-boundary
    true true true true true true true false false
