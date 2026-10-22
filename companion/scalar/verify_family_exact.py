#!/usr/bin/env python3
"""Exact-integer certificate for the paper's edge lemma, r=3,...,14.
Standard-library only. All interval endpoints are integers / 10**50.
Logarithms use rational atanh sums and an explicit positive remainder.
No floating point, numerical optimizer, or assertions control acceptance.
"""
import argparse
import hashlib
import json
from fractions import Fraction as F
from functools import lru_cache

S = 10**50
TERMS = 100

def ceildiv(a, b):
    return -((-a)//b)

class I:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo, hi=None):
        self.lo, self.hi = lo, lo if hi is None else hi
        if self.lo > self.hi:
            raise ValueError('inverted interval')
    @staticmethod
    def of(x):
        if isinstance(x, I):
            return x
        q = F(x)
        return I(q.numerator*S//q.denominator,
                 ceildiv(q.numerator*S, q.denominator))
    def __add__(self, y):
        y = I.of(y)
        return I(self.lo+y.lo, self.hi+y.hi)
    __radd__ = __add__
    def __neg__(self):
        return I(-self.hi, -self.lo)
    def __sub__(self, y):
        return self + (-I.of(y))
    def __rsub__(self, y):
        return I.of(y) + (-self)
    def __mul__(self, y):
        y = I.of(y)
        ps = (self.lo*y.lo, self.lo*y.hi, self.hi*y.lo, self.hi*y.hi)
        return I(min(ps)//S, ceildiv(max(ps), S))
    __rmul__ = __mul__
    def __truediv__(self, y):
        y = I.of(y)
        if y.lo <= 0 <= y.hi:
            raise ZeroDivisionError('interval contains zero')
        if y.hi < 0:
            return (-self)/(-y)
        return self * I(S*S//y.hi, ceildiv(S*S, y.lo))
    def __pow__(self, n):
        if not isinstance(n, int) or n < 0:
            raise ValueError('nonnegative integer exponent required')
        z = I.of(1)
        for _ in range(n):
            z = z*self
        return z

@lru_cache(None)
def small_log(q):
    """Rational lower/upper bounds for log(q), 1 <= q <= 2."""
    q = F(q)
    if not 1 <= q <= 2:
        raise ValueError('range reduction failed')
    z = (q-1)/(q+1)
    acc, p = F(0), z
    for k in range(TERMS):
        acc += 2*p/(2*k+1)
        p *= z*z
    rem = 2*p/((2*TERMS+1)*(1-z*z))
    return acc, acc+rem

@lru_cache(None)
def log_bounds(q):
    q = F(q)
    if q <= 0:
        raise ValueError('logarithm requires positive input')
    if q < 1:
        a, b = log_bounds(1/q)
        return -b, -a
    k = 0
    while q > 2:
        q /= 2
        k += 1
    a, b = small_log(q)
    c, d = small_log(F(2))
    return a+k*c, b+k*d

def logi(q):
    a, b = log_bounds(F(q))
    return I(a.numerator*S//a.denominator, ceildiv(b.numerator*S, b.denominator))

PLAN = {r: ('linear', 1 if r <= 10 else 2) for r in range(3, 15)}
PLAN[10] = ('quadratic', 1)
for r in (12, 13, 14):
    PLAN[r] = ('cubic', 2)

def anchor(x, r, name):
    if name == 'linear':
        return I.of(F(2, 5*r)) + F(3, 5)*x
    if name == 'quadratic':
        return I.of(F(-1, 100)) + F(6, 5)*x - x*x
    if name == 'cubic':
        h = x-I.of(F(1, r))
        return x-F(2, 3)*h*h-F(3, 2)*h*h*h
    raise ValueError(name)

def certify(r, name=None, K=None):
    default_name, default_K = PLAN[r]
    name = name or default_name
    K = default_K if K is None else K
    t, R, v = r-1, r*r, r*r-r+1
    gamma = (I.of(F(v, t))-logi(F(R, t)))/(v*v)
    alpha = I.of(F(1, r)-F(1, 2*t)) + F(2*r-1, 2)*gamma
    ell = (logi(F(r))+F(v-1, 2)*logi(F(t)))/v
    b = I.of(F(1, t))+2*t*gamma
    F0 = b*F(R, 2*r)-gamma*F(2*R-r, 2)
    if min(gamma.lo, alpha.lo) <= 0:
        raise ArithmeticError('coefficient sign failure')
    margins = [(ell-alpha*(r-k)-logi(F(k))).lo for k in range(1, K+1)]
    if min(margins) <= 0:
        return {'r': r, 'ok': False, 'failure': 'peeling'}
    N = 12*r
    # Cache x, anchor(x), and x log(r x) for exact reciprocal points.
    points = {}
    for d in range(K+1, N+1):
        x = I.of(F(1, d))
        points[d] = (x, anchor(x, r, name), x*logi(F(r, d)))
    # The rounded-up endpoint still has r*h < 1/3. Since log 3 > 1,
    # x log(r*x) decreases on this entire tail. Its maximum is 0.
    h = I.of(F(1, N+1)).hi
    if 3*r*h >= S or logi(F(3)).lo <= S:
        raise ArithmeticError('tail monotonicity check failed')
    H = F(h, S)
    x = I(0, h)
    tail = (x, anchor(x, r, name), I((I.of(H)*logi(r*H)).lo, 0))
    def T(X, Y):
        x, ax, fx = X
        y, ay, fy = Y
        xy = x*y
        return (2*alpha+(F0-r*alpha)*(x+y)+fx+fy-b*R*xy
                +gamma*R*R*(2*xy*(ax+ay)-x*ax*ax-y*ay*ay
                            -F(1, 2)*xy*(x*x+y*y)))
    least, argmin, count = None, None, 0
    for d in points:
        for c in points:
            if c < d or (d == r and c == r):
                continue
            lo = T(points[d], points[c]).lo
            count += 1
            if least is None or lo < least:
                least, argmin = lo, [d, c]
    if least <= 0:
        return {'r': r, 'ok': False, 'failure': 'finite window', 'argmin': argmin,
                'lower_numerator': str(least)}
    tail_lows = [T(points[d], tail).lo for d in points]
    tail_lows.append(T(tail, tail).lo)
    plane = T(points[r], points[r])
    if not plane.lo <= 0 <= plane.hi:
        raise ArithmeticError('plane tangency control failed')
    # Plane equality is established algebraically in the paper, not by this enclosure.
    return {'r': r, 'anchor': name, 'K': K, 'N': N, 'ok': min(tail_lows) > 0,
            'window_unordered_pairs': count, 'window_lower_numerator': str(least),
            'window_argmin': argmin, 'tail_boxes': len(tail_lows),
            'tail_lower_numerator': str(min(tail_lows)),
            'peeling_lower_numerators': [str(m) for m in margins]}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output')
    args = ap.parse_args()
    rows = [certify(r) for r in range(3, 15)]
    mutations = [certify(10, 'linear', 1), certify(12, 'linear', 2),
                 certify(13, 'cubic', 1)]
    ok = all(x['ok'] for x in rows) and all(not x['ok'] for x in mutations)
    out = {'schema': 'sparse-family-exact-integer-certificate-v1',
           'scale': str(S), 'log_series_terms': TERMS,
           'source_sha256': hashlib.sha256(open(__file__, 'rb').read()).hexdigest(),
           'rows': rows, 'negative_controls': mutations, 'all_passed': ok}
    s = json.dumps(out, indent=2, sort_keys=True)+'\n'
    if args.output:
        with open(args.output, 'w') as f:
            f.write(s)
    else:
        print(s, end='')
    if not ok:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
