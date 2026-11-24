"""Common positive Kähler forms of arbitrary finite tuples of marked fluxes."""
import json
from collections import Counter
from itertools import combinations, product
from math import gcd
from pathlib import Path

import numpy as np

from cat_tidal_crossing import integer_kernel, kahler_constraints
from cat_vacua_sky import torus_fluxes


def primitive(vector):
    numbers = tuple(int(x) for x in vector)
    divisor = gcd(*numbers)
    if next(x for x in numbers if x) < 0:
        divisor = -divisor
    return tuple(x // divisor for x in numbers)


def directions_on_anchor(matrices):
    """Intersections in the two- or three-dimensional quotient by common scale."""
    dimension = matrices.shape[-1]
    gram = matrices.transpose(0, 2, 1) @ matrices
    trace = np.trace(gram, axis1=1, axis2=2)
    bound = int(np.abs(gram).max())
    assert 6 * bound**3 < np.iinfo(np.int64).max
    second = sum(gram[:, i, i]*gram[:, j, j] - gram[:, i, j]**2
                 for i, j in combinations(range(dimension), 2))
    ranks = (trace > 0).astype(int) + (second > 0)
    if dimension == 3:
        a, b, c, d, e, f = (gram[:, i, j] for i, j in
                             ((0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)))
        determinant = a*(d*f-e*e) - b*(b*f-e*c) + c*(b*e-d*c)
        ranks += determinant > 0
    else:
        assert dimension == 2
    np.testing.assert_array_equal(ranks, np.linalg.matrix_rank(matrices))

    lines, planes = Counter(), Counter()
    for matrix in gram[ranks == 1]:
        row = next(row for row in matrix if row.any())
        if dimension == 2:
            lines[primitive((-row[1], row[0]))] += 1
        else:
            planes[primitive(row)] += 1  # plane indexed by its normal
    if dimension == 3:
        for matrix in gram[ranks == 2]:
            directions = (np.cross(a, b) for a, b in combinations(matrix, 2))
            lines[primitive(next(v for v in directions if v.any()))] += 1
        for a, b in combinations(planes, 2):
            lines.setdefault(primitive(np.cross(a, b)), 0)
    return int((ranks == 0).sum()), planes, lines


def anchored_counts(matrices, layer_counts, power_weights=None):
    number, dimension = len(matrices), matrices.shape[-1]
    full, planes, lines = directions_on_anchor(matrices)
    containing = {line: [p for p in planes if sum(a*b for a, b in zip(p, line)) == 0]
                  for line in lines}
    if power_weights is not None:
        # Sum the nonzero exact subspaces, collecting equal integer bases.
        power_weights[full] += 1 - len(planes) - len(lines)
        for size in planes.values():
            power_weights[full + size] += 1
        for line, size in lines.items():
            above = containing[line]
            power_weights[full + size + sum(planes[p] for p in above)] += 1
            for p in above:
                power_weights[full + planes[p]] -= 1
            power_weights[full] += len(above)
    output = {}
    for count in layer_counts:
        power = count - 1  # the anchored first layer is already present
        whole = full**power
        exact_planes = {p: (full + size)**power - whole for p, size in planes.items()}
        exact_lines = {}
        for line, size in lines.items():
            above = containing[line]
            supersets = full + size + sum(planes[p] for p in above)
            exact_lines[line] = supersets**power - whole - sum(exact_planes[p] for p in above)
        assert all(v >= 0 for v in exact_lines.values())
        counts = [0] * 5  # index includes the common positive scale
        counts[1+dimension] = whole
        if dimension == 3:
            counts[3] = sum(exact_planes.values())
        counts[2] = sum(exact_lines.values())
        counts[1] = number**power - sum(counts)
        assert counts[1] >= 0
        output[count] = counts
    return output


def small_direct_check():
    # Explicit enumeration of ordered triples, with planes that meet in a new
    # line, a line already present, repeated subspaces, and the zero subspace.
    rng = np.random.default_rng(1305)
    for d in (2, 3):
        samples = []
        for r in (0, 1, 1, 1, 2, 2, d):
            shape = np.zeros((3, d), dtype=np.int64)
            shape[:r] = rng.integers(-3, 4, (r, d))
            samples.append(shape)
        family = np.array(samples)
        predicted = anchored_counts(family, (2, 3, 4))
        for count, expected in predicted.items():
            observed = [0] * 5
            for subset in product(family, repeat=count-1):
                nullity = integer_kernel(np.vstack(subset)).shape[1]
                observed[1+nullity] += 1
            assert expected == observed


def calculate():
    small_direct_check()
    fluxes, orbits, hodge, triples, fixed = torus_fluxes(include_marked=True)
    constraints = kahler_constraints(hodge, triples)
    marked = fluxes[fixed].astype(np.int64)
    equations = constraints(marked)
    number = len(equations)
    axes = np.eye(9, dtype=np.int64)
    test_shapes = list(axes) + [axes[0]-axes[1]]
    support_sizes = [int(np.all(equations @ axis == 0, axis=1).sum()) for axis in test_shapes]
    axis_supports = np.array([np.all(equations @ axis == 0, axis=1) for axis in axes[:3]])
    common_axes = int(axis_supports.all(axis=0).sum())
    for left, right in combinations(axis_supports, 2):
        np.testing.assert_array_equal(left & right, axis_supports.all(axis=0))
    ordered = sorted(range(number), key=lambda j: tuple(marked[j]))
    first = ordered[0]
    basis = integer_kernel(equations[first])
    second = next(j for j in ordered if integer_kernel(equations[j] @ basis).shape[1] == 1)
    assert integer_kernel(np.vstack((equations[first], equations[second]))).shape[1] == 1
    counts = (1, 2, 3, 4, 6, 8, 12, 20, 32)
    measure = {n: [0]*5 for n in counts}
    power_weights = Counter()
    origins = 0
    for orbit in orbits:
        if not fixed[orbit[0]]:
            continue
        origins += 1
        first = constraints(fluxes[orbit[:1]].astype(np.int64))[0]
        # J_0 has first coordinate one. Subtract that multiple from every
        # candidate; the unique representative of a shape now has coordinate 0.
        basis = integer_kernel(np.vstack((first, np.eye(9, dtype=np.int64)[0])))
        coefficients = Counter()
        results = anchored_counts(equations @ basis, counts, coefficients)
        for base, weight in coefficients.items():
            power_weights[base] += len(orbit)*weight
        for n, bins in results.items():
            for d, size in enumerate(bins):
                measure[n][d] += len(orbit)*size
    assert number == 12048 and origins == 49
    assert measure[1][1:] == [0, 0, 11136, 912]
    assert measure[2][1:] == [135830016, 8365056, 941568, 17664]
    output = {}
    for n, bins in measure.items():
        total = number**n
        assert sum(bins) == total
        shape = sum(bins[2:])
        assert sum(weight*base**(n-1) for base, weight in power_weights.items()) == shape
        previous = sum(measure[2][2:])
        assert shape*(number**2)**(n//2) <= total*previous**(n//2)
        output[n] = dict(ordered_tuples=total, dimensions=bins[1:],
                         fraction_retaining_shape=shape/total)
    coefficients = {b: w for b, w in sorted(power_weights.items()) if w}
    assert coefficients[max(coefficients)] > 0
    return dict(marked_fluxes=number, simultaneous_symmetry_orbits=origins,
                shape_power_coefficients=coefficients,
                coordinate_support_counts=support_sizes,
                shared_support_of_coordinate_axes=common_axes,
                two_flux_witness=[marked[first].tolist(), marked[second].tolist()],
                metric_comparison="entire marked internal metric on a connected set",
                counting="ordered tuples with replacement; no physical layer measure", rows=output)


if __name__ == "__main__":
    destination = Path(__file__).resolve().parents[1]/"verification"/"cat-layer-contacts-results.json"
    destination.write_text(json.dumps(calculate(), indent=2) + "\n", encoding="utf8")
