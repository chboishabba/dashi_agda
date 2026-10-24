#!/usr/bin/env python3
"""Exact identifiability gate for proposed Field Loom S1 polarity experiments.

Source: design-only DASHI adaptation of classical factorial experiment design.
No experimental outcome, biological exposure, or antigravity is inferred.
"""
from fractions import Fraction
from psychotronics_design_rank_audit import rank_exact


COLUMNS = ('intercept','coil_sign','dipole_sign','coil_times_dipole','coil_heating_proxy')


def model_row(coil_sign, dipole_sign):
    if type(coil_sign) is not int or coil_sign not in (-1, 0, 1):
        raise ValueError('coil sign must be -1, 0, or 1')
    if type(dipole_sign) is not int or dipole_sign not in (-1, 1):
        raise ValueError('dipole sign must be -1 or 1')
    return (1, coil_sign, dipole_sign, coil_sign * dipole_sign, coil_sign ** 2)


def audit_settings(settings):
    """Settings are *verified* physical coordinates, never nominal app states."""
    if not isinstance(settings, list) or not settings:
        raise ValueError('nonempty settings needed')
    rows = [model_row(s['coil_sign'],s['dipole_sign']) for s in settings]
    r = rank_exact(rows)
    return {'rows':len(rows),'parameters':len(COLUMNS),'rank':r,
            'interaction_identifiable_with_separated_thermal_proxy':r==len(COLUMNS),
            'actual_coil_current_measured':False,
            'dipole_polarity_experimentally_verified':False,
            'claimed_anomalous_force_established':False}


def _selftest():
    all_six=[{'coil_sign':c,'dipole_sign':m} for c in (-1,0,1) for m in (-1,1)]
    assert audit_settings(all_six)['rank']==5
    only_on_off=[{'coil_sign':c,'dipole_sign':1} for c in (0,1)]
    assert audit_settings(only_on_off)['rank']==2
    # Repetitions do not create independent identifiable physical parameters.
    assert audit_settings(only_on_off*10)['rank']==2
    # Coil sign reversal without dipole reversal conflates the 2 linear terms.
    assert audit_settings([{'coil_sign':c,'dipole_sign':1} for c in (-1,0,1)])['rank']==3
    try:
        model_row(True,1)
    except ValueError:
        pass
    else:
        raise AssertionError('boolean coil direction accepted')
    print('S1 factorial: exact 5-parameter rank, sham and polarity regressions passed (synthetic)')


if __name__ == '__main__':
    import json
    _selftest()
    print(json.dumps(audit_settings([
        {'coil_sign':c,'dipole_sign':m} for c in (-1,0,1) for m in (-1,1)
    ]),indent=2))
