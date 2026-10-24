#!/usr/bin/env python3
"""S6 inverse-control gate using the existing two-coil Biot-Savart owner.

Only a numerical instrument-design test, not hardware, an Agda proof or a
27-dimensional physical field. Two independently driven coil currents
cannot span 27 arbitrary target fields; measured components/placement matter.
"""
from math import sqrt
from itertools import combinations
from psychotronics_field_loom_coils import loop_b


def gram_2x2(response):
    """Singular values of N x 2 real response by analytic Gram eigenvalues."""
    a = sum(u*u for u,v in response)
    b = sum(u*v for u,v in response)
    d = sum(v*v for u,v in response)
    delta = sqrt((a-d)**2+4*b*b)
    lmax = max(0., (a+d+delta)/2)
    lmin = max(0., (a+d-delta)/2)
    smax,smin = sqrt(lmax),sqrt(lmin)
    return {'measurement_rows':len(response),'parameter_count':2,
            'numerical_rank':int(smax>1e-12)+int(smin>max(1e-14,1e-6*smax)),
            'condition_number':smax/smin if smin>0 else None,
            'singular_values_t_per_A':(smax,smin)}


def response_grid(z_levels,channels=('z',),xy=(-.015,0,.015)):
    response=[]
    for z in z_levels:
        for x in xy:
            for y in xy:
                lower=loop_b(x,y,z,.1,-.05,100,1.)
                upper=loop_b(x,y,z,.1,+.05,100,1.)
                for channel in channels:
                    k={'x':0,'y':1,'z':2}[channel]
                    response.append((lower[k],upper[k]))
    return response



def fault_tolerant_four_sensor_layout():
    """Brute-force ideal Bz placements maximizing min singular value after 1 loss.

    Uniform sensor noise and individual sensor failures are assumptions;
    this static problem is not a full McCasland Gramian design or a safe build.
    """
    coords = tuple((x, y, z) for z in (-.015,0.,.015)
                   for x in (-.015,0.,.015) for y in (-.015,0.,.015))
    matrix = response_grid((-.015,0.,.015))
    best = (-1., None, None)
    for indices in combinations(range(len(coords)),4):
        survivors = [gram_2x2([matrix[i] for i in indices if i != lost])
                     for lost in indices]
        score = min(r['singular_values_t_per_A'][1] for r in survivors)
        # Maximise minimum survivor sensitivity; tie-break deterministically.
        if score > best[0] + 1e-15:
            best = (score, indices, survivors)
    sensitivity, indices, survivors = best
    return {'coordinates_m': [coords[i] for i in indices],
            'one_sensor_failure_maximin_min_singular_t_per_A': sensitivity,
            'all_single_failure_cases_rank_2': all(r['numerical_rank'] == 2 for r in survivors),
            'worst_single_failure_condition': max(r['condition_number'] for r in survivors),
            'examined_layouts': 17550,
            'calibration_and_failure_independence_measured': False}


def audit():
    mid=gram_2x2(response_grid((0.,)))
    volume=gram_2x2(response_grid((-.015,0.,.015)))
    vector=gram_2x2(response_grid((-.015,0.,.015),('x','y','z')))
    assert mid['numerical_rank']==1
    assert volume['numerical_rank']==2
    assert vector['numerical_rank']==2
    assert mid['measurement_rows']==9 and volume['measurement_rows']==27 and vector['measurement_rows']==81
    robust = fault_tolerant_four_sensor_layout()
    assert robust['all_single_failure_cases_rank_2']
    return {'Bz_midplane_9_sensors':mid,'Bz_volume_27_sensors':volume,
            'full_vector_volume_27_sensors_81_channels':vector,
            'four_Bz_sensors_optimised_for_one_failure':robust,
            'actuator_controls':2,'max_independent_static_field_patterns':2,
            'field_manifold_arbitrary_27_site_target_reachable':False,
            'material_response_modelled':False,'experimentally_calibrated':False,
            'design_lessons':('A 9-sensor midplane Bz-only layout cannot distinguish coil currents.',
                              'Sampling different z levels can identify both currents, not 27 degrees of freedom.',
                              'True observability needs field calibration, noise-weighted rank and thermal/safety constraints.')}


if __name__=='__main__':
    import json
    print(json.dumps(audit(),indent=2))
