#!/usr/bin/env python3
"""S1 generalised least-squares residual with correlated calibration errors.

This is a covariance calculation, not evidence of an anomalous force.
Independence assumptions are explicit; statistical significance/physical
acceptance require separately justified error models and lab provenance.
No third-party dependencies.
"""
from math import sqrt, fsum, isfinite


def _chol_solve(matrix, rhs):
    n = len(rhs)
    l = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            value = matrix[i][j] - fsum(l[i][k] * l[j][k] for k in range(j))
            if i == j:
                if value <= 0 or not isfinite(value):
                    raise ValueError('covariance matrix not positive definite')
                l[i][j] = sqrt(value)
            else:
                l[i][j] = value / l[j][j]
    y = [0.0] * n
    for i in range(n):
        y[i] = (rhs[i] - fsum(l[i][k] * y[k] for k in range(i))) / l[i][i]
    x = [0.0] * n
    for i in range(n - 1, -1, -1):
        x[i] = (y[i] - fsum(l[k][i] * x[k] for k in range(i + 1, n))) / l[i][i]
    return x


def correlated_residual_gls(pairs, *, common_force_std_n=0.,
                            gradient_calibration_fractional_std=0.):
    """Estimate constant residual with pair-specific noise and shared errors.

    Each pair dict must provide residual_n, random_std_n (excluding moment
    uncertainty), moment_gradient_t_m, moment_am2, moment_std_am2,
    moment_calibration_id. Identical calibration ID denotes *the same shared*
    magnetic-moment estimate across pairs, so its error NEVER averages away.
    The common force offset is one shared random variable. Fractional field
    calibration, if given, is a single shared multiplier of dipole prediction.
    Different calibration ID is a proposed independence assumption, not
    automatically authenticated by the algorithm.

    This is the best linear unbiased constant-residual estimator *conditional*
    on this covariance model; it is not a discovery significance calculator.
    """
    if not pairs:
        raise ValueError('at least one pair required')
    for value in (common_force_std_n, gradient_calibration_fractional_std):
        if not isfinite(value) or value < 0:
            raise ValueError('invalid common uncertainty')
    n = len(pairs)
    ids = {}
    for p in pairs:
        for key in ('residual_n', 'random_std_n', 'moment_gradient_t_m',
                    'moment_am2', 'moment_std_am2'):
            v = p[key]
            if isinstance(v, bool) or not isinstance(v, (int, float)) or not isfinite(v):
                raise ValueError('invalid numeric '+key)
        if p['random_std_n'] <= 0 or p['moment_std_am2'] < 0:
            raise ValueError('invalid pair uncertainty')
        cal = p.get('moment_covariance_group_id', p['moment_calibration_id'])
        if not isinstance(cal, str) or not cal.strip():
            raise ValueError('shared magnet calibration ID required')
        if p['moment_am2'] == 0:
            raise ValueError('zero or unknown moment orientation')
        # Opposite orientations of one physical magnet share magnitude error.
        # Signed derivatives propagate anticorrelation under reversal.
        signature = (abs(p['moment_am2']), p['moment_std_am2'])
        if cal in ids and ids[cal] != signature:
            raise ValueError('conflicting moment or uncertainty for shared calibration ID')
        ids[cal] = signature
    # Covariance in newtons squared.
    force_vector = [p['moment_am2'] * p['moment_gradient_t_m'] for p in pairs]
    shared_groups = [p.get('moment_covariance_group_id', p['moment_calibration_id']) for p in pairs]
    signed_grads = [p['moment_gradient_t_m'] * (1 if p['moment_am2'] > 0 else -1)
                    for p in pairs]
    cov = [[(pairs[i]['random_std_n'] ** 2 if i == j else 0.0)
            + common_force_std_n ** 2
            + gradient_calibration_fractional_std ** 2 * force_vector[i] * force_vector[j]
            + ((pairs[i]['moment_std_am2'] ** 2
                * signed_grads[i] * signed_grads[j])
               if shared_groups[i] == shared_groups[j] else 0.0)
            for j in range(n)] for i in range(n)]
    inv_ones = _chol_solve(cov, [1.0] * n)
    denom = fsum(inv_ones)
    if denom <= 0 or not isfinite(denom):
        raise ValueError('unusable covariance for constant-residual estimate')
    weights = [w / denom for w in inv_ones]
    estimate = fsum(w * p['residual_n'] for w, p in zip(weights, pairs))
    independent_var = fsum((w * p['random_std_n']) ** 2 for w, p in zip(weights, pairs))
    moment_var = fsum(
        sigma ** 2 * fsum(
            weights[i] * signed_grads[i]
            for i in range(n) if shared_groups[i] == group
        ) ** 2 for group, (_mean, sigma) in ids.items())
    common_var = common_force_std_n ** 2 * fsum(weights) ** 2
    gradient_var = gradient_calibration_fractional_std ** 2 * fsum(
        w * x for w, x in zip(weights, force_vector)) ** 2
    components = [independent_var, moment_var, common_var, gradient_var]
    total_var = fsum(components)
    expected_var = 1. / denom
    if abs(total_var - expected_var) > max(1e-22, total_var * 1e-6):
        raise AssertionError('covariance decomposition mismatch')
    return {
        'weighted_residual_n': estimate,
        'random_std_n': sqrt(independent_var),
        'shared_moment_calibration_std_n': sqrt(moment_var),
        'shared_force_offset_std_n': sqrt(common_var),
        'shared_gradient_scale_std_n': sqrt(gradient_var),
        'total_std_n': sqrt(total_var),
        'abs_residual_over_total_std': abs(estimate) / sqrt(total_var),
        'calibration_group_count': len(ids),
        'method': 'constant-residual GLS with explicitly shared moment, force and field-scale errors',
        'statistical_discovery_certified': False,
        'physical_claim_certified': False,
    }


def _selftest():
    pair = {'residual_n': 1e-7, 'random_std_n': 2e-7,
            'moment_am2': .01, 'moment_gradient_t_m': -.01,
            'moment_std_am2': .001, 'moment_calibration_id': 'single_cal'}
    one = correlated_residual_gls([pair], common_force_std_n=4e-6)
    repeated = correlated_residual_gls([pair] * 16, common_force_std_n=4e-6)
    assert repeated['random_std_n'] < one['random_std_n']
    assert abs(repeated['shared_moment_calibration_std_n'] - 1e-5) < 1e-17
    assert abs(repeated['shared_force_offset_std_n'] - 4e-6) < 1e-17
    assert repeated['total_std_n'] > 1e-5
    independent = correlated_residual_gls([
        {**pair, 'moment_calibration_id': str(i)} for i in range(4)])
    assert abs(independent['shared_moment_calibration_std_n'] - 5e-6) < 1e-17
    reverse = {**pair, 'moment_am2': -.01, 'moment_calibration_id':'minus',
               'moment_covariance_group_id':'physical_magnet'}
    forward = {**pair, 'moment_covariance_group_id':'physical_magnet'}
    opposed = correlated_residual_gls([forward, reverse])
    assert opposed['shared_moment_calibration_std_n'] < 1e-12
    assert opposed['calibration_group_count'] == 1
    with_field = correlated_residual_gls([pair] * 4,
               gradient_calibration_fractional_std=.1)
    assert abs(with_field['shared_gradient_scale_std_n'] - 1e-5) < 1e-17
    try:
        correlated_residual_gls([pair, {**pair, 'moment_am2': .02}])
    except ValueError:
        pass
    else:
        raise AssertionError('conflicting common calibration accepted')
    print('S1 correlated GLS: repeated/common/independent-moment/field-scale/conflict tests passed (synthetic)')


if __name__ == '__main__':
    _selftest()
