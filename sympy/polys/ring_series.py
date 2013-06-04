from sympy.polys.rings import ring, PolyElement
from sympy.polys.monomialtools import monomial_min, monomial_mul
from sympy.mpmath.libmp.libintmath import ifac
import math

def invert_monoms(p1):
    terms = p1.items()
    terms.sort()
    deg = p1.degree()
    ring = p1.ring
    p = ring.zero
    cv = p1.listcoeffs()
    mv = p1.listmonoms()
    for i in range(len(mv)):
        p[(deg - mv[i][0],)] = cv[i]
    return p

def monomial_basis(i, n):
    """return the ith-basis element
    """
    a = [0]*n
    a[i] = 1
    return tuple(a)

def integrate(p, i):
    ring = p.ring
    if isinstance(i, PolyElement):
        try:
            iv = ring.gens.index(i)
        except ValueError:
            raise ValueError('%s is not a generator of %s' %(x, s))
    else:
        iv = i
    p1 = ring.zero
    mn = monomial_basis(iv, ring.ngens)
    for expv in p:
        e = monomial_mul(expv, mn)
        p1[e] = p[expv]/(expv[iv] + 1)
    return p1

def giant_steps(target):
    """list of precision steps for the Newton's method

    code adapted from mpmath/libmp/libintmath.py
    """
    L = [target]
    start = 2
    while 1:
        Li = L[-1]//2 + 2
        if Li >= L[-1] or Li < start:
            if L[-1] != start:
                L.append(start)
            break
        L.append(Li)
    return L[::-1]

def trunc(p1, i, prec):
    ring = p1.ring
    p = ring.zero
    if isinstance(i, PolyElement):
        try:
            i = ring.gens.index(i)
        except ValueError:
            raise ValueError('%s is not a generator of %s' %(x, s))
    for exp1 in p1:
        if exp1[i] >= prec:
            continue
        p[exp1] = p1[exp1]
    return p


def mul_trunc(p1, p2, i, prec):
    ring = p1.ring
    p = ring.zero
    if isinstance(i, PolyElement):
        try:
            iv = ring.gens.index(i)
        except ValueError:
            raise ValueError('%s is not a generator of %s' %(x, s))
    else:
        iv = i
    if not isinstance(p2, PolyElement):
        raise ValueError('p1 and p2 must have the same ring')
    if ring == p2.ring:
        get = p.get
        items2 = list(p2.items())
        items2.sort(key=lambda e: e[0][iv])
        if ring.ngens == 1:
            for exp1, v1 in p1.iteritems():
                for exp2, v2 in items2:
                    exp = exp1[0] + exp2[0]
                    if exp < prec:
                        exp = (exp, )
                        p[exp] = get(exp, 0) + v1*v2
                    else:
                        break
        else:
            raise NotImplementedError
    p.strip_zero()
    return p

def square_trunc(p1, i, prec):
    ring = p1.ring
    p = ring.zero
    if isinstance(i, PolyElement):
        try:
            iv = ring.gens.index(i)
        except ValueError:
            raise ValueError('%s is not a generator of %s' %(x, s))
    else:
        iv = i
    get = p.get
    items = list(p1.items())
    items.sort(key=lambda e: e[0][iv])
    #monomial_mul = ring.monomial_mul
    for i in range(len(items)):
        exp1, v1 = items[i]
        for j in range(i):
            exp2, v2 = items[j]
            if exp1[iv] + exp2[iv] < prec:
                exp = monomial_mul(exp1, exp2)
                p[exp] = get(exp, 0) + v1*v2
            else:
                break
    p = p.imul_num(2)
    get = p.get
    for expv, v in p1.iteritems():
        if 2*expv[iv] < prec:
            e2 = monomial_mul(expv, expv)
            p[e2] = get(e2, 0) + v**2
    p.strip_zero()
    return p

def pow_trunc(p1, n, i, prec):
    ring = p1.ring
    p = ring.zero
    if isinstance(i, PolyElement):
        try:
            iv = ring.gens.index(i)
        except ValueError:
            raise ValueError('%s is not a generator of %s' %(x, s))
    else:
        iv = i
    assert n == int(n)
    n = int(n)
    if n == 0:
        if p1:
            return lp(1)
        else:
            raise ValueError
    if n < 0:
        p1 = self.pow_trunc(-n, i, prec)
        return series_inversion(p1, i, prec)
    if n == 1:
        return trunc(p1, i, prec)
    if n == 2:
        return square_trunc(p1, i, prec)
    if n == 3:
        p2 = square_trunc(p1, i, prec)
        return mul_trunc(p1, p2, i, prec)
    p = ring(1)
    while 1:
        if n&1:
            p = mul_trunc(p1, p, i, prec)
            n -= 1
            if not n:
                break
        p1 = square_trunc(p1, i, prec)
        n = n // 2
    return p

def has_constant_term(p, i):
    ring = p.ring
    if isinstance(i, PolyElement):
        try:
            iv = ring.gens.index(i)
        except ValueError:
            raise ValueError('%s is not a generator of %s' %(x, s))
    else:
        iv = i
    zm = ring.zero_monom
    a = [0]*ring.ngens
    a[iv] = 1
    miv = tuple(a)
    for expv in p:
        if monomial_min(expv, miv) == zm:
            return True
    return False

def _series_inversion1(p, iv, prec):
    """univariate series inversion 1/p

    iv name of the series variable
    prec precision of the series

    The Newton method is used.
    """
    ring = p.ring
    zm = ring.zero_monom
    if zm not in p:
        raise ValueError('no constant term in series')
    if has_constant_term(p - p[zm], iv):
        raise ValueError('p cannot contain a constant term depending on parameters')
    if p[zm] != ring.domain(1):
        # TODO add check that it is a unit
        p1 = ring(1)/p[zm]
    else:
        p1 = ring(1)
    for precx in giant_steps(prec):
        tmp = p1.square()
        tmp = mul_trunc(tmp, p, iv, precx)
        p1 = 2*p1 - tmp
    return p1

def series_inversion(p, i, prec):
    """multivariate series inversion 1/p
    """
    ring = p.ring
    zm = ring.zero_monom
    if isinstance(i, PolyElement):
        try:
            iv = ring.gens.index(i)
        except ValueError:
            raise ValueError('%s is not a generator of %s' %(x, s))
    if zm not in p:
        raise NotImplementedError('no constant term in series')
    if has_constant_term(p - p[zm], iv):
        raise NotImplementedError('p - p[0] must not have a constant term in the series variables')
    return _series_inversion1(p, iv, prec)

def series_from_list(p, c, iv, prec, concur=1):
    ring = p.ring
    zm = ring.zero_monom
    assert zm not in p
    n = len(c)
    if not concur:
        q = lp(1)
        s = c[0]*q
        for i in range(1, n):
            q = mul_trunc(q, p, iv, prec)
            s += c[i]*q
        return s
    J = int(math.sqrt(n) + 1)
    K, r = divmod(n, J)
    if r:
        K += 1
    ax = [ring(1)]
    b = 1
    q = ring(1)
    # TODO get a good value
    if len(p) < 20:
        for i in range(1, J):
            q = mul_trunc(q, p, iv, prec)
            ax.append(q)
    else:
        for i in range(1, J):
            if i % 2 == 0:
                q = square_trunc(ax[i//2], iv, prec)
            else:
                q = mul_trunc(q, p, iv, prec)
            ax.append(q)
    # optimize using square_trunc
    pj = mul_trunc(ax[-1], p, iv, prec)
    b = ring(1)
    s = ring(0)
    for k in range(K - 1):
        r = J*k
        s1 = c[r]
        for j in range(1, J):
            s1 += c[r + j]*ax[j]
        s1 = mul_trunc(s1, b, iv, prec)
        s += s1
        b = mul_trunc(b, pj, iv, prec)
        if not b:
            break
    k = K - 1
    r = J*k
    if r < n:
        s1 = c[r]*ring(1)
        for j in range(1, J):
            if r + j >= n:
                break
            s1 += c[r + j]*ax[j]
        s1 = mul_trunc(s1, b, iv, prec)
        s += s1
    return s

def _exp1(p, iv, prec):
    ring = p.ring
    zm = ring.sero_monom
    p1 = ring(1)


def exp_trunc(p, i, prec):
    ring = p.ring
    if isinstance(i, PolyElement):
        try:
            iv = ring.gens.index(i)
        except ValueError:
            raise ValueError('%s is not a generator of %s' %(x, s))
    zm = ring.zero_monom
    if has_constant_term(p, iv):
        raise NotImplementedError
    #if len(p) > 20:
    #    return _exp1(p, iv, prec)
    one = ring(1)
    n = 1
    k = 1
    c = []
    for k in range(prec):
        c.append(one/n)
        k += 1
        n *= k

    r = series_from_list(p, c, iv, prec)
    return r

def newton1(p, x, prec):
    deg = p.degree()
    p1 = invert_monoms(p)
    p2 = series_inversion(p1, x, prec)
    p3 = mul_trunc(p1.diff(x), p2, x, prec)
    return p3

def newton(p, x, prec):
    deg = p.degree()
    p1 = invert_monoms(p)
    p2 = series_inversion(p1, x, prec)
    p3 = mul_trunc(p1.diff(x), p2, x, prec)
    res = deg - p3*x
    return res

def hadamard_product(p1, p2):
    ring = p1.ring
    p = ring.zero
    for exp1, v1 in p1.iteritems():
        if exp1 in p2:
            v = v1*p2[exp1]
            p[exp1] = v
    return p

def hadamard_exp(p1, inverse=False):
    ring = p1.ring
    p = ring.zero
    if not inverse:
        for exp1, v1 in p1.iteritems():
            p[exp1] = v1/ifac(exp1[0])
    else:
        for exp1, v1 in p1.iteritems():
            p[exp1] = v1*ifac(exp1[0])
    return p

def compose_add(p1, p2):
    ring = p1.ring
    x = ring.gens[0]
    prec = p1.degree() * p2.degree() + 1
    np1 = newton(p1, x, prec)
    np1e = hadamard_exp(np1)
    np2 = newton(p2, x, prec)
    np2e = hadamard_exp(np2)
    np3e = mul_trunc(np1e, np2e, x, prec)
    np3 = hadamard_exp(np3e, True)
    np3a = (np3[(0,)] - np3)/x
    q = integrate(np3a, x)
    q = exp_trunc(q, x, prec)
    q = invert_monoms(q)
    return q.primitive()[1]
    return q

def composed_product(p1, p2):
    ring = p1.ring
    x = ring.gens[0]
    prec = p1.degree()*p2.degree() + 1
    print 'DB11 prec=', prec
    np1 = newton1(p1, x, prec)
    np2 = newton1(p2, x, prec)
    np = hadamard_product(np1, np2)
    q = integrate(np, x)
    q = exp_trunc(-q, x, prec)
    q = invert_monoms(q)
    return q.primitive()[1]

