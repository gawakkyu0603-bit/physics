"""Spacelike work for a gravitational contrast and a circle with antipodal sources."""
import math

import numpy as np
from scipy.integrate import quad

from fractions import Fraction

from decimal import Decimal, localcontext


def divided_difference(nodes, values):
    current = list(values)
    for order in range(1, len(nodes)):
        current = [(current[i+1]-current[i])/(nodes[i+order]-nodes[i])
                   for i in range(len(current)-1)]
    return current[0]


def spectral_moments(z, work):
    def coefficient(order):
        return (-1)**(order+1)*divided_difference(z[:order+1], work[:order+1])
    second, third, fourth = [coefficient(order) for order in (2, 3, 4)]
    first_moment = third-z[4]*fourth
    second_moment = second-(z[3]+z[4])*first_moment-z[3]*z[4]*fourth
    return [fourth, first_moment, second_moment]


def invert_ring(source):
    """Invert the periodic graph Laplacian on its mean-zero subspace exactly."""
    size = len(source)
    assert sum(source) == 0
    prefix = []
    total = Fraction(0)
    for value in source:
        prefix.append(total)
        total += value
    first_difference = sum(prefix)/size
    solution = [Fraction(0)]
    for j in range(1, size):
        solution.append(solution[-1]+first_difference-prefix[j])
    average = sum(solution)/size
    solution = [value-average for value in solution]
    assert all(2*solution[j]-solution[j-1]-solution[(j+1) % size] == source[j]
               for j in range(size))
    return solution


def matrix_contrast_checks():
    # The polynomial and trace are evaluated as matrices, separately from the spectral sum.
    rng = np.random.default_rng(867)
    for size in (4, 6, 10):
        shift = np.roll(np.eye(size), 1, axis=0)
        first = (shift+shift.T)/2
        second = (shift-shift.T)/(2j)
        values = rng.normal(size=size)
        probe = np.diag(values)
        links = sum(np.linalg.norm(b @ probe-probe @ b)**2 for b in (first, second))
        assert abs(links-np.sum((np.roll(values, 1)-values)**2)) < 2e-13
        phases = np.exp(2j*math.pi*np.arange(size)/size)
        v = np.diag(phases**(size//2))
        q = np.diag(np.exp(1j*rng.uniform(-math.pi, math.pi, size)))
        def transverse():
            raw = rng.normal(size=(size, size))+1j*rng.normal(size=(size, size))
            return (raw+raw.conj().T)/2
        d, z = transverse(), transverse()
        def source(a, b):
            return np.vdot(v @ a-a @ v, v @ b-b @ v).real
        assert abs(source(d, z)-source(q @ d @ q.conj().T, q @ z @ q.conj().T)) < 2e-13
        assert abs(source(np.diag(values), z)) < 1e-14
    beta = []
    for k in (2, 3, 4):
        feynman = quad(lambda u: (u*(1-u))**k/k, 0., 1.)[0]
        spectral = quad(lambda t: math.sqrt(1-t)*t**(k-1)/4**k, 0., 1.)[0]
        assert abs(feynman-spectral) < 2e-12
        beta.append(feynman)
    assert abs(beta[0]*beta[2]/beta[1]**2-7/6) < 4e-14
    # Infinite sums for the free, charge-neutral two-oscillator source in matrix quantum mechanics.
    odds = np.arange(1., 1200., 2.)
    qm = sum(odds**-7)*sum(odds**-11)/sum(odds**-9)**2-1
    return dict(feynman_coefficients=beta, one_mass_pair=1/6, circle_pair=13/72,
                matrix_quantum_mechanics_pair=qm)


def ring_response_checks():
    curves = []
    for size in (2, 4, 6, 8, 12, 24, 48, 96, 192, 384, 768):
        source = [Fraction(0)]*size
        source[0], source[size//2] = Fraction(1), Fraction(-1)
        solution = source
        moments = []
        for _ in range(5):
            solution = invert_ring(solution)
            moments.append(solution[0]-solution[size//2])
        ratio = moments[2]*moments[4]/moments[3]**2-1
        p = Fraction(1, size**2)
        numerator = (1-4*p)*(1-16*p)*(1+132*p+12768*p**2+71168*p**3+147456*p**4)
        denominator = 3*(17+224*p+1568*p**2+9216*p**3)**2
        assert ratio == numerator/denominator
        assert (ratio > 0) == (size >= 6)
        pair = Fraction(7, 6)*moments[1]*moments[3]/moments[2]**2-1
        pair_closed = 5*(1+8*p)*(17+224*p+1568*p**2+9216*p**3)/(18*(2+20*p+128*p**2)**2)-1
        assert pair == pair_closed
        scaled = (ratio-Fraction(1, 867))*size**2
        # Fixed lattice spacing a=1. Check the finite-momentum solution separately.
        for z in (.02, .4, 1.7):
            modes = sum(4/(z+4*math.sin(math.pi*j/size)**2)
                        for j in range(1, size, 2))/size
            eta = 2*math.asinh(math.sqrt(z)/2)
            green = math.tanh(size*eta/4)/math.sinh(eta)
            assert abs(modes-green) < 1e-12
        curves.append(dict(layers=size, normalized_variance=float(ratio),
                           first_correction=float(scaled), neutral_pair=float(pair)))
    t2, t3, t4 = Fraction(2, 15), Fraction(-17, 315), Fraction(62, 2835)
    # Coefficients of p=1/N^2 in the z^2,z^3,z^4 Taylor terms at fixed circumference.
    dt2, dt3, dt4 = Fraction(4, 3), Fraction(-32, 45), Fraction(68, 189)
    first_correction = t2*t4/t3**2*(dt2/t2+dt4/t4-2*dt3/t3)
    assert abs(curves[-1]["first_correction"]-float(first_correction)) < 3e-5
    return dict(points=curves, first_correction=str(first_correction))


def spectral_checks():
    # Finite equally or unequally spaced samples can be evaluated exactly.
    nodes = [Fraction(j, 7) for j in (1, 3, 6, 8, 14)]
    cases = []
    for poles in ([], [(2, 3)], [(2, 3), (7, 4)]):
        work = [5-2*z-sum(w/(s+z) for s, w in poles) for z in nodes]
        moments = spectral_moments(nodes, work)
        direct = [sum(Fraction(w)*s**k/math.prod(s+z for z in nodes)
                      for s, w in poles) for k in range(3)]
        assert moments == direct
        determinant = moments[0]*moments[2]-moments[1]**2
        assert (determinant > 0) == (len(poles) == 2)
        cases.append(dict(poles=len(poles), moments=[float(x) for x in moments],
                          determinant=float(determinant)))
    slopes = []
    with localcontext() as context:
        context.prec = 68
        pi = Decimal("3.141592653589793238462643383279502884197169399375105820974944592308")
        for step in map(Decimal, (".1", ".01", ".0001", ".000001")):
            z = [j*step for j in (1, 2, 4, 7, 11)]
            # Units R=1. The direct terms cancel from all three recovered moments.
            work = []
            for x in z:
                exponential = (pi*x.sqrt()).exp()
                work.append(2+3*x-(exponential-1)/((exponential+1)*x.sqrt()))
            m0, m1, m2 = spectral_moments(z, work)
            expected = [Decimal(0) for k in range(3)]
            for j in range(1024):
                mass2 = (2*j+1)**2
                measure = (4/pi)/math.prod(mass2+x for x in z)
                for k in range(3):
                    expected[k] += mass2**k*measure
            # Each omitted term is at most (4/pi)/(2j+1)^6 for these three moments.
            assert max(abs(w-v) for w, v in zip((m0, m1, m2), expected)) < Decimal("1e-17")
            contrast = m0*m2/m1**2-1
            slopes.append(dict(step=float(step), mass_squared_mean=float(m1/m0),
                               relative_variance=float(contrast)))
        assert abs(contrast-Decimal(1)/867) < Decimal("4e-8")
    # The Taylor coefficients follow from tanh'(t)=1-tanh(t)^2.
    coefficients = [Fraction(1)]
    for j in range(1, 5):
        convolution = sum(coefficients[i]*coefficients[j-1-i] for i in range(j))
        coefficients.append(-convolution/(2*j+1))
    assert coefficients[2]*coefficients[4]/coefficients[3]**2-1 == Fraction(1, 867)
    return dict(five_spacelike_samples=cases, antipodal_circle=slopes,
                taylor=[str(v) for v in coefficients], circle_limit="1/867",
                direct_ring=ring_response_checks(), neutral_matrix_source=matrix_contrast_checks())
