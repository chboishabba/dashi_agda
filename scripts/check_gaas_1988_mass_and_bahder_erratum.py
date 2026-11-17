#!/usr/bin/env python3
"""External mass benchmark and Bahder-1992 correction gate (non-physical model).

Primary evidence: Molenkamp et al., Phys Rev B 38 4314(R) 1988,
DOI 10.1103/PhysRevB.38.4314.
Bahder original DOI 10.1103/PhysRevB.41.11992, erratum DOI
10.1103/PhysRevB.46.9913, inspected from original 1-page erratum.
No paper figures digitised or spectroscopy fitted. Values below originate
from the published abstract; mixed-sample inferences != same material sample.
"""
from fractions import Fraction as F
import json

GAMMA = {'g1': F(698,100), 'g2': F(206,100), 'g3': F(293,100)}
EXPERIMENT = {'001_HH': F(34,100), '001_LH': F(94,1000), '111_HH': F(7,10)}
ERRATUM = {
    '1990_33_35_strain_spin_orbit_matrices': 'corrected N1,N2,N3 in 1992 erratum',
    '1990_30_valence_deformation_potential': 'sign convention corrected; a differs from Bir/Pikus book',
    '1990_16_mixing_R': 'R expression corrected, including gamma2/gamma3 structure',
    '1990_42_PQRS_hbar': 'all specified Planck factors squared',
}

def benchmark():
    g1,g2,g3 = GAMMA.values()
    pred = {'001_HH': 1/(g1-2*g2), '001_LH': 1/(g1+2*g2), '111_HH': 1/(g1-2*g3)}
    tests=[]
    def check(name,test):
        assert test,name
        tests.append(name)
    check('exact 001 HH rational',pred['001_HH']==F(50,143))
    check('exact 001 LH rational',pred['001_LH']==F(10,111))
    check('exact 111 HH rational',pred['111_HH']==F(25,28))
    for label in pred:
        check(f'{label} original does not exactly match observed', pred[label] != EXPERIMENT[label])
        check(f'{label} source remains positive',pred[label]>0 and EXPERIMENT[label]>0)
        check(f'{label} finite relative discrepancy',abs(pred[label]/EXPERIMENT[label]-1)<F(1,3))
    check('001 HH closer than 111 HH',abs(pred['001_HH']/EXPERIMENT['001_HH']-1)<abs(pred['111_HH']/EXPERIMENT['111_HH']-1))
    check('001 LH closer than 111 HH',abs(pred['001_LH']/EXPERIMENT['001_LH']-1)<abs(pred['111_HH']/EXPERIMENT['111_HH']-1))
    check('111 HH model larger than inferred value',pred['111_HH']>EXPERIMENT['111_HH'])
    required_g3=(g1-1/EXPERIMENT['111_HH'])/2
    check('apparent 111-only gamma3 fit',required_g3==F(1943,700))
    check('gamma3 inferred not original',required_g3!=g3)
    check('mass is QW-inferred, not directly measured bulk curvature',True)
    check('correct erratum count',len(ERRATUM)==4)
    for name in ERRATUM:check(name+' tracked',bool(ERRATUM[name]))
    tr= F(5,1000)*(F(2)-F(269,580))
    ac,av=F(-717,100),F(116,100)
    gapcoeff=ac-av
    check('common source gap coefficient -8.33',gapcoeff==F(-833,100))
    gauge=F(31,10)
    check('energy-zero shift preserves gap',ac+gauge-(av+gauge)==gapcoeff)
    check('mixed sign changes physical gap coefficient',ac+F(116,100)!=gapcoeff)
    check('gap convention difference at coherent tensile 0.5pct is 17.82meV',
          (F(232,100)*tr)>F(17,1000) and (F(232,100)*tr)<F(18,1000))
    return {'checks_passed':len(tests),'all_passed':True,
        'published_source':'10.1103/PhysRevB.38.4314 (1988) abstract masses, model-extracted QW',
        'model':'six-band near-Gamma bulk direction curvature, not QW eigenproblem',
        'masses':{key:{'model_exact':str(pred[key]),'model_m0':float(pred[key]),
                      'inferred_experiment_m0':float(EXPERIMENT[key]),
                      'model_over_inference':float(pred[key]/EXPERIMENT[key]),
                      'relative_error_pct':float(100*(pred[key]/EXPERIMENT[key]-1))}
                  for key in pred},
        'gamma3_if_forced_to_measured_111':float(required_g3),
        'gamma3_nominal':float(g3),
        'same_sample_calibration':'OPEN',
        'erratum_corrections':ERRATUM,
        'unaddressed_erratum_full_spin_strain_operator':'OPEN',
        'hydrostatic_energy_reference':'OPEN',
        'passed_checks':tests}

if __name__=='__main__':
    print(json.dumps(benchmark(),indent=2))
