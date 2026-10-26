#!/usr/bin/env python3
"""Actual-source owners preserved; finite MODEL only, no Agda/GAP promotion."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import monster3b_zeta_appraisal_dual_square_model as sq

def test_all_90_multiplicity_slices():
    r=sq.verify()
    assert r["states"]==131220 and r["total_checks"]==1837080
    assert r["translation_square_checks"]==787320
    assert r["modulation_square_checks"]==787320
    assert not r["same_source_Monster_Hom_selected"]

def test_single_zeta_sector_not_closed_under_inverter():
    q=sq.Q[0]
    assert sq.mirror_actual(sq.evaluate(1,q,0))[0]==2
    assert sq.mirror_actual(sq.evaluate(2,q,0))[0]==1

def test_mirror_involution():
    assert all(sq.on_q(sq.on_q(q))==q for q in sq.Q)
    for s in (1,2):
        assert all(sq.mirror_actual(sq.mirror_actual(sq.evaluate(s,q,0)))
                   ==sq.evaluate(s,q,0) for q in sq.Q)

def test_source_conditional_theorem_remains_explicit():
    source=(Path(__file__).resolve().parents[1]/
      "DASHI/Moonshine/Monster3BActualDualZetaAppraisalSquareConsumerExact.agda").read_text()
    for name in ("Monster3BCentralCharacterInertiaExact",
                 "Base369Monster3BActualMultiplicitySliceAppraisalBidiExact",
                 "inverterSendsZetaToZetaSquared",
                 "actualStateAtAppraisalToModel",
                 "sameModelCoordinateImpliesSameActualState",
                 "actualModelMirrorSquare :",
                 "modelAppraisalMirrorSquare :",
                 "centreInverter : Inertia.CentralInverter action"):
        assert name in source
    assert "postulate" not in source.split("-- No new appraisal carrier")[1]
