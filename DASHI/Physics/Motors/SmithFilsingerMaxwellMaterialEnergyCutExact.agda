module DASHI.Physics.Motors.SmithFilsingerMaxwellMaterialEnergyCutExact where

-- F10/F13 -> F15: exact energy-interface CANCEL and storage RETURN.
-- This is an Agda proof consumer of selected boundary/port identities.
-- It is not a Maxwell PDE solver or a claim about Filsinger hardware.
--
-- Source attribution: user-origin Smith/Filsinger nonlinear source/sink
-- steelman; existing MaxwellExteriorCalculusAdapter and finite exact
-- energy owners; #1521 dispersive-material port is an UNMERGED donor.
-- The field/material interface is an identified work port, not an
-- invented source. Material modulation and recovery remain independent.

open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_)

import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell

-- Exact equality transport and shared internal-port cancellation,
-- established without subtracting natural numbers.
cancelSharedInterface :
  (a fieldRest materialRest delivered interface : Nat) →
  a ≡ interface + fieldRest →
  interface + materialRest ≡ delivered →
  a + materialRest ≡ fieldRest + delivered
cancelSharedInterface a b c d x eField eMaterial =
  Cycle.trans
    (Cycle.cong (λ z → z + c) eField)
    (Cycle.trans
      (solve 3
        (λ i f m →
          ((i :+ f) :+ m) := (f :+ (i :+ m)))
        refl x b c)
      (Cycle.cong (λ z → b + z) eMaterial))

-- F10 demands TWO independent balances on the SAME selected original
-- object: field-source energy and material/receiver energy.
-- Neither field energy nor material parameter work can be suppressed.
record FieldMaterialEnergyWeld
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (sourceCycle : Weld.SignedSourceCycleWeld b f) : Set₂ where
  field
    naturalInput driverInput : Nat
    fieldStoredInitially fieldStoredFinally : Nat
    interiorFieldToMaterialWork fieldDissipationAndOutgoing : Nat
    modulationInput materialStoredInitially materialStoredFinally : Nat
    usefulLoad materialDissipation modulationRecovery : Nat

    -- The actual field Poynting/current/surface identity is AUTHORITY.
    -- The repository symbolic Maxwell adapter alone CANNOT supply it.
    fieldSourceBoundary :
      (naturalInput + driverInput) + fieldStoredInitially
      ≡ interiorFieldToMaterialWork
        + (fieldDissipationAndOutgoing + fieldStoredFinally)

    -- A material constitutive theorem (the #1521 donor when integrated)
    -- must supply this balance incl. relaxation and material modulation.
    materialReceiverBoundary :
      interiorFieldToMaterialWork
        + (modulationInput + materialStoredInitially)
      ≡ usefulLoad
        + (materialDissipation + (modulationRecovery + materialStoredFinally))

    -- True source input and delivered load must be SAME as actual
    -- selected terminal work, not merely equal numbers from unrelated
    -- experimental machines or incompatible boundary conventions.
    -- Full port conservation already subtracts natural/controller
    -- OUTGOING flux; attach net real work, NOT gross incident waves.
    sameNetNaturalWork :
      naturalInput ≡
        Cycle.RepeatableSourceCycle.naturalSourceWork
          (Cycle.AdmittedSourceCapCycle.repeatable
            (Weld.SignedSourceCycleWeld.cycleWithSourceCap sourceCycle))
    sameNetPoweredWork :
      driverInput ≡
        Cycle.RepeatableSourceCycle.controllerWork
          (Cycle.AdmittedSourceCapCycle.repeatable
            (Weld.SignedSourceCycleWeld.cycleWithSourceCap sourceCycle))
    sameOriginalLoad :
      usefulLoad ≡
        Port.MidpointTwoPortWorkWindow.usefulWork
          (Weld.FormalFieldToPort.portWindow f)

    -- Require explicit physical authority for the selected original.
    SpecifiedFieldMetricAndCurrent : Set
    RetardedMaxwellAndMaterialWorkIdentity : Set
    SameOriginalPortAndMaterialParameters : Set
    metricCurrent : SpecifiedFieldMetricAndCurrent
    retardedFieldIdentity : RetardedMaxwellAndMaterialWorkIdentity
    originalMaterialAndPins : SameOriginalPortAndMaterialParameters

-- Nontrivial F10 interface-cut lemma: the internal field/material
-- transfer is eliminated, leaving exactly the external contributions.
-- No original PDE has been assumed to hold by definition: each energy
-- equation is a separate required witness above.
fieldMaterialCombinedWork :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (sourceCycle : Weld.SignedSourceCycleWeld b f)
  (w : FieldMaterialEnergyWeld b f sourceCycle) →
  ((FieldMaterialEnergyWeld.naturalInput w
      + FieldMaterialEnergyWeld.driverInput w)
      + FieldMaterialEnergyWeld.modulationInput w)
    + (FieldMaterialEnergyWeld.fieldStoredInitially w
      + FieldMaterialEnergyWeld.materialStoredInitially w)
  ≡ FieldMaterialEnergyWeld.usefulLoad w
    + (FieldMaterialEnergyWeld.fieldDissipationAndOutgoing w
      + (FieldMaterialEnergyWeld.materialDissipation w
        + (FieldMaterialEnergyWeld.modulationRecovery w
          + (FieldMaterialEnergyWeld.fieldStoredFinally w
            + FieldMaterialEnergyWeld.materialStoredFinally w))))
fieldMaterialCombinedWork b f sourceCycle w =
  Cycle.trans
    (solve 6
      (λ n d m fi mi x →
        (((n :+ d) :+ m) :+ (fi :+ mi))
          := (((n :+ d) :+ fi) :+ (m :+ mi)))
      refl n d m fi mi interior)
    (Cycle.trans
      (cancelSharedInterface _ _ _ _ interior
        (FieldMaterialEnergyWeld.fieldSourceBoundary w)
        (FieldMaterialEnergyWeld.materialReceiverBoundary w))
      (solve 7
        (λ fl ff l ml rec mf k →
          ((fl :+ ff) :+ (l :+ (ml :+ (rec :+ mf))))
            := (l :+ (fl :+ (ml :+ (rec :+ (ff :+ mf))))))
        refl fieldLoss fieldFinal load matLoss recovery matFinal interior))
  where
    open FieldMaterialEnergyWeld w renaming
      (naturalInput to n; driverInput to d;
       modulationInput to m; fieldStoredInitially to fi;
       materialStoredInitially to mi;
       interiorFieldToMaterialWork to interior;
       fieldDissipationAndOutgoing to fieldLoss;
       fieldStoredFinally to fieldFinal;
       usefulLoad to load;
       materialDissipation to matLoss;
       modulationRecovery to recovery;
       materialStoredFinally to matFinal)

-- Restore ALL field and material storage, not just the output capacitor.
-- The original two independent balance equations then prove the
-- sustained external work statement, WITHOUT an assumed aggregate law.
fieldMaterialRepeatableWork :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (sourceCycle : Weld.SignedSourceCycleWeld b f)
  (w : FieldMaterialEnergyWeld b f sourceCycle) →
  FieldMaterialEnergyWeld.fieldStoredInitially w
    + FieldMaterialEnergyWeld.materialStoredInitially w
  ≡ FieldMaterialEnergyWeld.fieldStoredFinally w
    + FieldMaterialEnergyWeld.materialStoredFinally w →
  ((FieldMaterialEnergyWeld.naturalInput w
     + FieldMaterialEnergyWeld.driverInput w)
     + FieldMaterialEnergyWeld.modulationInput w)
  ≡ FieldMaterialEnergyWeld.usefulLoad w
    + (FieldMaterialEnergyWeld.fieldDissipationAndOutgoing w
      + (FieldMaterialEnergyWeld.materialDissipation w
        + FieldMaterialEnergyWeld.modulationRecovery w))
fieldMaterialRepeatableWork b f sourceCycle w restored =
  Cycle.+-cancelRight _ _ finalStored
    (Cycle.trans
      (Bound.sym (Cycle.cong (λ z → input + z) restored))
      (Cycle.trans
        (fieldMaterialCombinedWork b f sourceCycle w)
        (Bound.sym
          (solve 6
            (λ l fl ml rec fs ms →
              (l :+ (fl :+ (ml :+ (rec :+ (fs :+ ms)))))
              := ((l :+ (fl :+ (ml :+ rec))) :+ (fs :+ ms)))
            refl load fieldLoss matLoss recovery fieldFinal matFinal)))
  where
    open FieldMaterialEnergyWeld w renaming
      (naturalInput to n; driverInput to d;
       modulationInput to m;
       usefulLoad to load;
       fieldDissipationAndOutgoing to fieldLoss;
       materialDissipation to matLoss;
       modulationRecovery to recovery;
       fieldStoredFinally to fieldFinal;
       materialStoredFinally to matFinal)
    input : Nat
    input = (n + d) + m
    finalStored : Nat
    finalStored = fieldFinal + matFinal

-- Formal F15 statement: the total load does not exceed paid natural,
-- driver and material-modulation inputs when all stores return.
-- The independent modulation work is NEVER misclassified as natural.
fieldMaterialLoadBoundOnRepeatableCycle :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (sourceCycle : Weld.SignedSourceCycleWeld b f)
  (w : FieldMaterialEnergyWeld b f sourceCycle) →
  FieldMaterialEnergyWeld.fieldStoredInitially w
    + FieldMaterialEnergyWeld.materialStoredInitially w
  ≡ FieldMaterialEnergyWeld.fieldStoredFinally w
    + FieldMaterialEnergyWeld.materialStoredFinally w →
  Bound._≤_ (FieldMaterialEnergyWeld.usefulLoad w)
    ((FieldMaterialEnergyWeld.naturalInput w
      + FieldMaterialEnergyWeld.driverInput w)
      + FieldMaterialEnergyWeld.modulationInput w)
fieldMaterialLoadBoundOnRepeatableCycle b f sourceCycle w restored =
  Bound.transportUpper
    (Bound.sym (fieldMaterialRepeatableWork b f sourceCycle w restored))
    (Bound.≤-append
      (FieldMaterialEnergyWeld.usefulLoad w)
      (FieldMaterialEnergyWeld.fieldDissipationAndOutgoing w
       + (FieldMaterialEnergyWeld.materialDissipation w
         + FieldMaterialEnergyWeld.modulationRecovery w)))

-- Preserve the trusted repo Maxwell authority boundary: this module does
-- not derive a physical source-current or inhomogeneous Maxwell equation.
maxwellSourceEquationStillOpen :
  Maxwell.MaxwellExteriorCalculusAdapter.sourceEquationPromoted
    Maxwell.canonicalMaxwellExteriorCalculusAdapter ≡
      false
maxwellSourceEquationStillOpen = refl
