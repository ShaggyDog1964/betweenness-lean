"""Certificate for Lemma 83 (app:lem:sepcert) of the working paper "Axioms That Do Not Combine".

Lemma 83 is used in the proof of Theorem 31 (Appendix A.20): the chain-first slice rankings
T_m = T(m, n_m, xi_m) are critical for every m >= 2, have at least 17 m^2 n_m lotteries, and
have separation at least xi_m = 11/(500 m).

Run from the root of the repository:  python3 certificates/certificate.py
It needs only the Python standard library, runs in about 30 seconds, and its last line is the JSON
{"verdict": "CERTIFIED", ...} when every check passes.

All arithmetic is exact (fractions.Fraction); interval arithmetic uses Fraction endpoints.
Notation: delta (or d) for the face functions is tau_m = 1/(2m+1) of the paper, ds is xi, ns is n_s,
V is Z, and x = g/H. The parts of the script and the parts of Lemma 83:
  A  Lemma 83(1): the face functions of Table 4 are positive on their domains, for all
     tau in [0, 1/5] and x = g/H in [0, 1/75] (interval branch-and-bound).
  C  Lemma 83(2) (size, used in Lemma 81): a rigorous lower bound on J_m for 2 <= m <= 400 by the
     slot-cycle formula with outward rounding, and the Riemann tail for m > 400.
  D  Lemma 83(3) (separation, used in Lemma 82): the adjacent-slot constant, Q_min on a grid of
     heights, the per-m average check for m <= 400 and the Riemann tail for m > 400.
  S  The scalar inequalities that the paper also verifies by hand (13^20 >= 2^74, the constants K,
     phibar, HOM, R-separation).
  E  The constants of Theorem 31: n delta^3 >= 6.85e-4 for T_m at delta = 11/(500 m), and the
     interpolated constant 2.03e-4.
  B  Cross-check, not used by the proof: the exact instance T(2, 8, 11/1000) (n = 562), with the
     normalization of Lemma 73, every relation of the tight chain and of every patched deletion
     chain, the identities of Lemma 75, c_s o1 < 1, and the inequality mu* Z > 1 of Lemma 79.
  F  Cross-check, not used by the proof: the construction of Lemma 80 carried out exactly for
     sampled deletions of T(2, 8, 11/1000), each verified against Definition 32.
The last stdout line is JSON {"verdict": ..., "detail": ...}.
"""
from __future__ import annotations

import json
import math
import time
from fractions import Fraction as F

T0 = time.time()
FAIL: list[str] = []
NOTES: list[str] = []


def need(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg, flush=True)
    return cond


# ----------------------------------------------------------------------------------------------
# Interval arithmetic with exact rational endpoints
# ----------------------------------------------------------------------------------------------
class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = F(lo); self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(s, o):
        o = o if isinstance(o, I) else I(o); return I(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__

    def __neg__(s):
        return I(-s.hi, -s.lo)

    def __sub__(s, o):
        o = o if isinstance(o, I) else I(o); return I(s.lo - o.hi, s.hi - o.lo)

    def __rsub__(s, o):
        return I(o) - s

    def __mul__(s, o):
        o = o if isinstance(o, I) else I(o)
        p = (s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi); return I(min(p), max(p))
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = o if isinstance(o, I) else I(o)
        if not (o.lo > 0 or o.hi < 0):
            raise ZeroDivisionError("interval division by an interval containing 0")
        return s * I(1 / o.hi, 1 / o.lo)

    def __rtruediv__(s, o):
        return I(o) / s


# ----------------------------------------------------------------------------------------------
# Normalized gadget geometry (Appendix A.20, Lemma 73); u = slot parameter, d = tau_m = 1/(2m+1)
# ----------------------------------------------------------------------------------------------
def geom(u, d):
    a = F(1, 50) + F(7, 25) * u          # t(xb)
    b = F(31, 50) + F(9, 25) * u         # t(ya)
    a1 = a + F(7, 25) * d                # t(xa)
    b1 = b + F(9, 25) * d                # t(yb)
    eps = F(3, 4) * a1 / b
    sA = -eps / (b - a1)
    sB = (eps - 1) / (b1 - a)
    dd = F(13, 10) + (1 - b1) / (b1 - a) + eps
    return dict(a=a, a1=a1, b=b, b1=b1, eps=eps, sA=sA, sB=sB, d=dd)


GX = F(1, 75)          # x = g/H ranges over [0, GX]   (g <= 1/80, H >= 1)
KC = F(39, 88)         # K = c* o0 (13/4) with c* = 1/11, o0 = 3/2
BETA = F(17, 20)


def internal(u, d, x):
    G = geom(u, d)
    A = lambda t: G['sA'] * (t - G['b'])
    B = lambda t: -1 + G['sB'] * (t - G['b1'])
    A0, A1, B0, B1 = A(0), A(1), B(0), B(1)
    c1 = (B0 - B1) - (A0 - A1); c2 = B0 * A1 - A0 * B1
    P = A0 - B0
    eps, dd = G['eps'], G['d']
    one = I(1) if isinstance(x, I) else 1
    return {
        'EPS': eps, 'N1': 1 - eps,
        'G3a0': A0 - B0, 'G3a1': A1 - B1,
        'L2a': A(G['b1']) + 1 - KC * 2 * P,
        'L2b': A(G['a']) + eps - KC * 2 * P,
        'L2c': eps - B(G['a1']) - KC * (2 + x * eps) * P,
        'L2d': -B(G['b']) - KC * 2 * P,
        'BET': BETA * dd * (one + x * A0) * (one + x * B1) - (c1 + x * c2),
        'KAP': (c1 + x * c2) - F(1, 2) * (one + x * A0) * (one + x * B1),
        'A1lo': A1 + 2, 'B1lo': B1 + 2, 'B1hi': -B1,
        'DMAX': 3 - dd,
        'Dyb': 8 - (A(G['b1']) + 1), 'Dxb': 8 - (A(G['a']) + eps),
    }


def transition(u, un, d, x):
    G = geom(u, d); N = geom(un, d)
    B = lambda t: -1 + G['sB'] * (t - G['b1'])
    An = lambda t: -G['d'] + N['sA'] * (t - N['b'])
    B0, B1, An0, An1 = B(0), B(1), An(0), An(1)
    c1 = (B0 - B1) - (An0 - An1); c2 = B0 * An1 - An0 * B1
    P = B1 - An1
    dd = G['d']
    return {
        'G3b0': B0 - An0, 'G3b1': P,
        'L4': B(N['a1']) - (N['eps'] - dd) - KC * (2 + x * N['eps']) * P,
        'LR1': B(N['b']) + dd - KC * 2 * P,
        'L5a': -1 - An(G['b1']) - KC * (2 + x * (dd - 1)) * P,
        'L5b': -G['eps'] - An(G['a']) - KC * (2 + x * (dd - G['eps'])) * P,
        'RHOtr': c1 + x * c2,
    }


def bnb(evalf, key, dmax, one_dim=False, maxdepth=60):
    """Prove evalf(w, d)[key] > 0 for all w in [0,1], d in [0,dmax]; returns (ok, boxes, min lower bound)."""
    stack = [(F(0), F(1), F(0), dmax, 0)]
    nbox, worst = 0, None
    while stack:
        wl, wh, dl, dh, dep = stack.pop(); nbox += 1
        v = evalf(I(wl, wh), I(dl, dh))[key]
        if v.lo > 0:
            worst = v.lo if worst is None else min(worst, v.lo); continue
        if dep > maxdepth:
            return False, nbox, (wl, wh, dl, dh)
        if one_dim or (dh - dl) * 4 > (wh - wl):
            mid = (dl + dh) / 2; stack += [(wl, wh, dl, mid, dep + 1), (wl, wh, mid, dh, dep + 1)]
        else:
            mid = (wl + wh) / 2; stack += [(wl, mid, dl, dh, dep + 1), (mid, wh, dl, dh, dep + 1)]
    return True, nbox, worst


def part_A():
    print("== Part A: Lemma 83(1), interval branch-and-bound over delta in [0,1/5], x in [0,1/75] ==", flush=True)
    xI = I(0, GX)
    dmax = F(1, 5)
    fi = lambda w, d: internal((1 - d) * w, d, xI)
    fs = lambda w, d: transition((1 - d) * w, (1 - d) * w, d, xI)                 # same slot pair
    fr = lambda w, d: transition((1 - 3 * d) * w, (1 - 3 * d) * w + 2 * d, d, xI)  # class i -> i+1
    fw = lambda w, d: transition(1 - d, I(0), d, xI)                              # class m -> 0
    tot = 0
    for k in internal(I(0), I(F(1, 9)), xI):
        ok, nb, w = bnb(fi, k, dmax); tot += nb
        need(ok, f"A: internal {k} not certified (box {w})")
        print(f"  internal   {k:6s} ok={ok} boxes={nb:4d} min_lower={float(w) if ok else w}", flush=True)
    for k in transition(I(0), I(0), I(F(1, 9)), xI):
        for nm, f, od in (('stay', fs, False), ('step', fr, False), ('wrap', fw, True)):
            ok, nb, w = bnb(f, k, dmax, one_dim=od); tot += nb
            need(ok, f"A: transition[{nm}] {k} not certified (box {w})")
            print(f"  transition {k:6s} {nm:4s} ok={ok} boxes={nb:4d} min_lower={float(w) if ok else w}", flush=True)
    print(f"  total boxes {tot}", flush=True)


# ----------------------------------------------------------------------------------------------
# Part S: scalar facts (also verified by hand in the paper)
# ----------------------------------------------------------------------------------------------
def part_S():
    print("== Part S: scalar facts (also verified by hand) ==", flush=True)
    need(13 ** 20 >= 2 ** 74, "S: (13/4)^20 >= 4^17")                      # 4^(17/20) <= 13/4
    need(F(1, 11) * F(3, 2) * F(13, 4) == KC, "S: K = 39/88")
    # H_J >= 1 - 3g >= 24/25 (g <= 1/75);  o1 <= o0 * 4/H_J <= 25/4;  phibar = o1/11 <= 25/44
    o1max = F(3, 2) * 4 / (1 - 3 * GX)
    need(o1max == F(25, 4), "S: o1max = 25/4")
    phib = o1max / 11
    need(phib == F(25, 44) and phib < 1, "S: phibar = 25/44 < 1")
    # HOM: sigma = 1 - 2/75;  Hlow = sigma (1-phib)/(1+phib sigma);  Hlow*(3/2 sigma - 1) > 8/75
    sig = 1 - 2 * GX
    Hl = sig * (1 - phib) / (1 + phib * sig)
    need(Hl * (F(3, 2) * sig - 1) > 8 * GX, "S: HOM inequality")
    need(F(3, 2) * sig > 1, "S: (3/2)(1 - 2/75) > 1  (V > 1 on tight vectors)")
    print(f"  HOM: Hlow={float(Hl):.5f}, Hlow*(1.5 sigma-1)={float(Hl * (F(3, 2) * sig - 1)):.5f} > {float(8 * GX):.5f}")
    # R separation: Lambda - 1 >= J g/8 >= (1.7 - 0.2/30)/8 ; x3(R0)-x3(Rend) >= ds_max = 11/1000
    Jg = F(17, 10) - F(2, 10) / 30
    lam1 = Jg / 8
    o1lo = F(3, 2) * (1 + lam1)
    gap = (o1lo - F(3, 2)) / ((1 + F(3, 2)) * (1 + o1lo))
    need(gap >= F(11, 1000), "S: R0/Rend x3 gap >= 11/1000")
    gapR = 1 / (1 + o1max) - F(1, 12)
    need(gapR >= F(11, 1000), "S: Rend x3 - top slice >= 11/1000")
    print(f"  R0-Rend gap >= {float(gap):.5f}; Rend-slice gap >= {float(gapR):.5f}")


# ----------------------------------------------------------------------------------------------
# Part B (cross-check, not used by the proof): exact instance T(2, 8, 11/1000)
# ----------------------------------------------------------------------------------------------
def build_T(m, ns, ds):
    g = F(2, 5) / (m * m * ns)
    p = 2 * m + 2
    sl = [F(1, 50) + F(7, 25) * F(k, p - 1) for k in range(p)]
    sr = [F(31, 50) + F(9, 25) * F(k, p - 1) for k in range(p)]
    gad, H, j = [], F(4), 0
    while True:
        pp = j // ns
        txa, txb = sl[(2 * pp + 1) % p], sl[(2 * pp) % p]
        tya, tyb = sr[(2 * pp) % p], sr[(2 * pp + 1) % p]
        e2 = F(3, 4) * g * max(txa, txb) / min(tya, tyb)
        if H - e2 < 1:
            break
        gad.append(dict(j=j, cls=pp % (m + 1), H=H, s=(j % ns) * ds,
                        v=[(txa, H + e2), (tya, H), (tyb, H - g), (txb, H - e2)]))
        H -= g * (F(13, 10) + (1 - tyb) / (tyb - txb)) + e2
        j += 1

    def chord(P, Q):
        sl_ = (Q[1] - P[1]) / (Q[0] - P[0]); U = P[1] - sl_ * P[0]
        return (U, U + sl_)
    w = F(3, 2)
    for G in gad:
        xa, ya, yb, xb = G['v']
        A, B = chord(xa, ya), chord(yb, xb)
        wA = w; wB = w * (B[0] / B[1]) / (A[0] / A[1])
        G.update(A=A, B=B, wA=wA, wB=wB, TA=(-A[0], -A[1], F(1), wA * A[1]), TB=(-B[0], -B[1], F(1), wB * B[1]))
        s = G['s']; cs = s / (1 - s)
        pts, Hp = [], []
        for (t, Hv), L, wL in ((xa, A, wA), (ya, A, wA), (yb, B, wB), (xb, B, wB)):
            kap = cs * wL * L[1]
            h1 = (L[0] * (1 - t) + L[1] * t - kap) / (1 + kap)      # H'
            hh = h1 / (1 + h1)
            pts.append(((1 - s) * (1 - hh) * (1 - t), (1 - s) * (1 - hh) * t, (1 - s) * hh, s))
            Hp.append(h1)
        G.update(pts=pts, Hp=Hp)
        w = wB
    return gad, g, w


def dot(W, x):
    return sum(a * b for a, b in zip(W, x))


def Rpt(o):
    return (F(0), o / (1 + o), F(0), 1 / (1 + o))


def part_B():
    m, ns, ds = 2, 8, F(11, 1000)
    print(f"== Part B (cross-check): exact instance T({m},{ns},{ds}) ==", flush=True)
    gad, g, o1 = build_T(m, ns, ds)
    J = len(gad); n = 4 * J + 2
    need(n == 562, f"B: n = {n} != 562")
    need(g <= F(1, 80), "B: g <= 1/80")
    dl = F(1, 2 * m + 1)
    smax = max(G['s'] for G in gad)
    need(smax <= F(1, 12), "B: s_max <= 1/12")
    cmax = smax / (1 - smax)
    need(cmax * o1 < 1, "B: c_s o1 < 1")
    o0 = F(3, 2)
    # normalization (Lemma 73) and gadget facts
    for k, G in enumerate(gad):
        Gm = geom(2 * G['cls'] * dl, dl)
        H = G['H']
        need(G['A'] == (H + g * Gm['sA'] * (0 - Gm['b']), H + g * Gm['sA'] * (1 - Gm['b'])), f"B: A_{k} normalization")
        need(G['B'] == (H + g * (-1 + Gm['sB'] * (0 - Gm['b1'])), H + g * (-1 + Gm['sB'] * (1 - Gm['b1']))),
             f"B: B_{k} normalization")
        if k + 1 < J:
            need(gad[k + 1]['H'] == H - g * Gm['d'], f"B: height step {k}")
        A, B = G['A'], G['B']
        need(A[0] > A[1] > 0 and B[0] > B[1] > 0, f"B: U>S>0 at {k}")
        need(A[0] > B[0] and A[1] > B[1], f"B: G3in at {k}")
        need(B[0] / B[1] > A[0] / A[1], f"B: G6in at {k}")
        need(G['wA'] * A[1] > 1 and G['wB'] * B[1] > 1, f"B: V>1 at {k}")
        # on-relations: each point on its own tight vector
        for idx, T in ((0, 'TA'), (1, 'TA'), (2, 'TB'), (3, 'TB')):
            need(dot(G[T], G['pts'][idx]) == 0, f"B: point {idx} of gadget {k} not on its vector")
            need(G['Hp'][idx] <= G['v'][idx][1], f"B: H' <= L(t) at {k},{idx}")
        xa, ya, yb, xb = G['pts']
        need(dot(G['TA'], yb) < 0 and dot(G['TA'], xb) < 0, f"B: G2a/G2b at {k}")
        need(dot(G['TB'], xa) > 0 and dot(G['TB'], ya) > 0, f"B: G2c/G2d at {k}")
        if k + 1 < J:
            N = gad[k + 1]; A2 = N['A']
            need(B[0] > A2[0] and B[1] > A2[1], f"B: G3tr at {k}")
            need(B[0] / B[1] > A2[0] / A2[1], f"B: G6tr at {k}")
            need(dot(G['TB'], N['pts'][0]) < 0, f"B: G4 at {k}")
            need(dot(G['TB'], N['pts'][1]) < 0, f"B: R1 at {k}")
            need(dot(N['TA'], yb) > 0 and dot(N['TA'], xb) > 0, f"B: G5 at {k}")
            need(N['wA'] == G['wB'], "B: w continuity")
        # lifting identity on every cross item (Lemma 75)
        s = G['s']; cs = s / (1 - s)
        for idx, own in ((0, 'TA'), (1, 'TA'), (2, 'TB'), (3, 'TB')):
            p = G['pts'][idx]; Hp = G['Hp'][idx]; t = G['v'][idx][0]
            Lown = G['A'] if own == 'TA' else G['B']
            for other in ('TA', 'TB'):
                M = G['A'] if other == 'TA' else G['B']
                lhs = dot(G[other], p) * (1 + Hp) / ((1 - s) * g)
                rhs = ((Lown[0] * (1 - t) + Lown[1] * t) - (M[0] * (1 - t) + M[1] * t)) / g + cs * (1 + Hp) * (G[other][3] - G[own][3]) / g
                need(lhs == rhs, f"B: lifting identity at gadget {k} point {idx}")
    # R conditions of the tight chain: V/S at the first vector equals o0, at the last equals o1
    need(gad[0]['s'] == 0 and gad[0]['wA'] == o0, "B: first gadget in slice 0 with w = o0")
    need(gad[-1]['wB'] == o1, "B: o1 = w_B(J-1)")
    # HOM for the last gadget: mu* V_A > 1 for p in {yb, xb}
    G = gad[-1]; Y = G['TA']
    for idx in (2, 3):
        p = G['pts'][idx]
        # X(mu) = mu * (U,S,V) with third coordinate 1: X.p = mu*(Y.p - p2) + p2 ;  Y.p - p2 = -U p0 - S p1 + V p3
        lin = Y[0] * p[0] + Y[1] * p[1] + Y[3] * p[3]
        mu = -p[2] / lin
        need(0 < mu < 1, "B: 0 < mu* < 1")
        need(mu * Y[3] > 1, "B: HOM mu* V_A > 1")
        need(mu * (Y[3] - o1 * (-Y[1])) < 0, "B: R_end strictly below X")
    # separation sanity on the instance: cross-slice x3 exact; R points
    R0, R1 = Rpt(o0), Rpt(o1)
    need(R0[3] - R1[3] >= ds, "B: R0-Rend separation")
    print(f"  n={n} J={J} o1={float(o1):.5f} c_smax*o1={float(cmax * o1):.4f}: all exact checks passed", flush=True)
    return o1


# ----------------------------------------------------------------------------------------------
# Part C: size, Lemma 83(2)
# ----------------------------------------------------------------------------------------------
def ns_of(m):
    return 1 + (125 * m) // 33


def dyad_up(x, k=64):
    return F(-((-x.numerator * 2 ** k) // x.denominator), 2 ** k)


def dyad_dn(x, k=64):
    return F((x.numerator * 2 ** k) // x.denominator, 2 ** k)


def class_data(m):
    dl = F(1, 2 * m + 1)
    out = []
    for i in range(m + 1):
        G = geom(2 * i * dl, dl)
        out.append((G['d'], G['eps']))
    return out


def J_lower(m, exact=False):
    """Lower bound on J_m: first failure of the recursion with drops rounded up (Lemma 81)."""
    ns = ns_of(m); g = F(2, 5) / (m * m * ns)
    cd = class_data(m)
    dbar = [d if exact else dyad_up(d) for d, _ in cd]
    CS = g * ns * sum(dbar)
    P = ns * (m + 1)
    best, pre = None, F(0)
    for i, (d, e) in enumerate(cd):
        X = (3 - g * ns * pre - g * (ns - 1) * dbar[i] - g * e) / CS
        q = max(0, math.floor(X) + 1)
        Y = (3 - q * CS - g * ns * pre - g * e) / (g * dbar[i])
        l = max(0, math.floor(Y) + 1)
        assert l <= ns - 1
        k = q * P + i * ns + l
        best = k if best is None else min(best, k)
        pre += dbar[i]
    return best


def literal_J(m, ns):
    gad, g, _ = build_T_heights(m, ns)
    return gad


def build_T_heights(m, ns):
    g = F(2, 5) / (m * m * ns)
    p = 2 * m + 2
    sl = [F(1, 50) + F(7, 25) * F(k, p - 1) for k in range(p)]
    sr = [F(31, 50) + F(9, 25) * F(k, p - 1) for k in range(p)]
    H, j = F(4), 0
    while True:
        pp = j // ns
        txa, txb = sl[(2 * pp + 1) % p], sl[(2 * pp) % p]
        tya, tyb = sr[(2 * pp) % p], sr[(2 * pp + 1) % p]
        e2 = F(3, 4) * g * txa / tya
        if H - e2 < 1:
            break
        H -= g * (F(13, 10) + (1 - tyb) / (tyb - txb)) + e2
        j += 1
    return j, g, H


def psi_bar(u, d1):      # upper envelope of psi(u, delta) = d - 13/10 for delta <= d1
    return (F(19, 50) - F(9, 25) * u) / (F(3, 5) + F(2, 25) * u) + F(3, 4) * (F(1, 50) + F(7, 25) * u + F(7, 25) * d1) / (F(31, 50) + F(9, 25) * u)


def psi_low(u, d1):      # lower envelope of psi(u, delta) for delta <= d1
    return (F(19, 50) - F(9, 25) * d1 - F(9, 25) * u) / (F(3, 5) + F(9, 25) * d1 + F(2, 25) * u) + F(3, 4) * (F(1, 50) + F(7, 25) * u) / (F(31, 50) + F(9, 25) * u)


def dpsi_bar(u, d1):
    return -F(154, 625) / ((F(3, 5) + F(2, 25) * u) * (F(3, 5) + F(2, 25) * u)) + F(3, 4) * (F(7, 25) * F(31, 50) - F(9, 25) * (F(1, 50) + F(7, 25) * d1)) / ((F(31, 50) + F(9, 25) * u) * (F(31, 50) + F(9, 25) * u))


def dpsi_low(u, d1):
    N0 = F(19, 50) - F(9, 25) * d1; D0 = F(3, 5) + F(9, 25) * d1
    return -(F(9, 25) * D0 + F(2, 25) * N0) / ((D0 + F(2, 25) * u) * (D0 + F(2, 25) * u)) + F(3, 4) * (F(7, 25) * F(31, 50) - F(9, 25) * F(1, 50)) / ((F(31, 50) + F(9, 25) * u) * (F(31, 50) + F(9, 25) * u))


def neg_on(fun, lo, hi, pieces):
    step = (hi - lo) / pieces
    return all(fun(I(lo + k * step, lo + (k + 1) * step)).hi < 0 for k in range(pieces))


def pos_on(fun, lo, hi, pieces):
    step = (hi - lo) / pieces
    return all(fun(I(lo + k * step, lo + (k + 1) * step)).lo > 0 for k in range(pieces))


def check_psi_formula():
    """psi(u, delta) = d - 13/10 lies between psi_low and psi_bar (spot check of the envelope algebra)."""
    for m in (401, 500, 1000):
        dl = F(1, 2 * m + 1); d1 = F(1, 803)
        for i in (0, m // 3, m):
            u = 2 * i * dl
            ps = geom(u, dl)['d'] - F(13, 10)
            need(psi_low(u, d1) <= ps <= psi_bar(u, d1), f"C: psi envelope at m={m}, i={i}")


def part_C(M1=400, K=4000):
    print(f"== Part C: Lemma 83(2), size. rigorous J lower bound for 2 <= m <= {M1}; Riemann tail for m > {M1} ==", flush=True)
    for m in (2, 3, 4):
        Jl = literal_J(m, ns_of(m))
        need(J_lower(m, exact=True) == Jl, f"C: cycle formula != literal recursion at m={m}")
        need(J_lower(m) <= Jl, f"C: rounded bound exceeds J at m={m}")
    worst = None
    for m in range(2, M1 + 1):
        ns = ns_of(m)
        n = 4 * J_lower(m) + 2
        r = F(n, m * m * ns)
        worst = (r, m) if worst is None or r < worst[0] else worst
        need(n >= 17 * m * m * ns, f"C: m={m}: n >= {n} < 17 m^2 ns")
    print(f"  min n/(m^2 ns) over 2<=m<={M1}: {float(worst[0]):.5f} at m={worst[1]}", flush=True)
    m0 = M1 + 1; d1 = F(1, 2 * m0 + 1)
    need(neg_on(lambda u: dpsi_bar(u, d1), F(0), F(1), 64), "C: psi_bar not decreasing")
    need(pos_on(lambda u: psi_bar(u, d1), F(0), F(1), 16), "C: psi_bar not positive")
    check_psi_formula()
    Ibar = sum(psi_bar(F(k, K), d1) for k in range(K)) / K
    au = F(13, 10) + Ibar + (psi_bar(F(0), d1) - Ibar / 2) / (m0 + 1)
    need(psi_bar(F(0), d1) - Ibar / 2 > 0, "C: avg_upper decreasing in m")
    lhs = 30 / au - F(4 * (m0 + 1), m0 * m0) - F(2, m0 * m0 * ns_of(m0))
    need(lhs >= 17, f"C: tail fails at m={m0}: {float(lhs)}")
    print(f"  tail: Ibar={float(Ibar):.6f} avg_upper={float(au):.6f} 30/avg - 4(m+1)/m^2 - 2/(m^2 ns) = {float(lhs):.5f} >= 17",
          flush=True)


# ----------------------------------------------------------------------------------------------
# Part D: separation, Lemma 83(3)
# ----------------------------------------------------------------------------------------------
def pow_up(z):
    """Rational r with r >= (4/z)^(17/20), verified exactly."""
    x = (4 / float(z)) ** 0.85
    r = F(math.ceil(x * (1 + 1e-9) * 10 ** 9), 10 ** 9)
    need(r ** 20 >= (4 / z) ** 17, "D: pow_up")
    return r


def Qmin(gb, pieces=1200):
    """min over y in [1,4] of [1 - (1/12)(1 + (3/2) r(y-3g) (1+3g))]/(1+y+g)^2, g <= gb (Lemma 82)."""
    best = None
    for k in range(pieces):
        yl = 1 + F(3 * k, pieces); yh = 1 + F(3 * (k + 1), pieces)
        r = pow_up(yl - 3 * gb)
        num = 1 - F(1, 12) * (1 + F(3, 2) * r * (1 + 3 * gb))
        q = num / ((1 + yh + gb) * (1 + yh + gb))
        best = q if best is None or q < best else best
    return best


def part_D(M1=400, K=4000):
    print("== Part D: Lemma 83(3), separation ==", flush=True)
    # adjacent slots: 0.28 delta_m/(5+g) >= 11/(500 m) for m >= 2 (checked at m=2, LHS*m increasing)
    m = 2
    need(F(7, 25) * F(1, 2 * m + 1) / (5 + F(1, 80)) >= F(11, 500 * m), "D: adjacent-slot bound at m = 2")
    need(F(8, 25) / (5 + F(1, 80)) >= F(11, 1000), "D: left/right bound")
    q1 = Qmin(F(1, 80)); q2 = Qmin(F(1, 9000))
    print(f"  Q_min(g<=1/80)={float(q1):.6f}  Q_min(g<=1/9000)={float(q2):.6f}", flush=True)
    for m in range(2, M1 + 1):
        ns = ns_of(m); g = F(2, 5) / (m * m * ns)
        q = q1 if m < 10 else q2
        if m >= 10:
            need(g <= F(1, 9000), "D: g <= 1/9000 for m >= 10")
        need(g <= F(1, 80), "D: g <= 1/80")
        S = sum(dyad_dn(d) for d, _ in class_data(m))
        CS = F(2, 5) * S / (m * m)                      # cycle drop = g ns sum_i d_i
        need(q * CS >= F(11, 500 * m), f"D: same-slot separation at m={m}")
    m0 = M1 + 1; d1 = F(1, 2 * m0 + 1)
    need(neg_on(lambda u: dpsi_low(u, d1), F(0), F(11, 10), 64), "D: psi_low not decreasing")
    need(pos_on(lambda u: psi_low(u, d1), F(0), F(11, 10), 16), "D: psi_low not positive")
    Ilow = sum(psi_low(F(k, K), d1) for k in range(1, K + 1)) / K
    al = F(13, 10) + Ilow * (2 * m0 + 1) / (2 * m0 + 2)
    # for m >= m0: CS = 0.4 (m+1) avg/m^2 >= 0.4 avg/m, and avg >= 1.3 + Ilow (2m+1)/(2m+2) >= al
    need(q2 * F(2, 5) * al >= F(11, 500), f"D: same-slot tail: {float(q2 * F(2, 5) * al)}")
    print(f"  tail: Ilow={float(Ilow):.6f} avg_lower={float(al):.6f} Q*0.4*avg={float(q2 * F(2, 5) * al):.6f} >= 0.022", flush=True)


# ----------------------------------------------------------------------------------------------
# Part F (cross-check, not used by the proof): the construction of Lemma 80 carried out literally
# ----------------------------------------------------------------------------------------------
ROT = {'rmp': (-1, 1), 'low': (-2, -2), 'rpm': (1, -1), 'raise': (2, 2)}


def is_chain(X, W):
    if len(W) != len(X) - 1:
        return False, "length"
    for i, w in enumerate(W):
        if not all(w[k] < w[k + 1] for k in range(3)):
            return False, f"coords {i}"
        if i + 1 < len(W) and not all(w[k] <= W[i + 1][k] for k in range(4)):
            return False, f"nesting {i}"
        if not (dot(w, X[i]) > 0 > dot(w, X[i + 1])):
            return False, f"separation {i}"
    return True, ""


def scheme_chain(gad, o0, o1, deleted, eta, th0, ths):
    """deleted: ('R0',), ('Rend',) or (j, k) with k in 0..3 (xa, ya, yb, xb)."""
    J = len(gad)
    # remaining points with (label line, rotation)
    seq = []          # entries: (point, gadget index of line, 'A'/'B'/'X', rot, saving_into)
    for j in range(J):
        types = [0, 1, 2, 3]
        lab = {0: (j, 'A', 'rmp'), 1: (j, 'A', 'low'), 2: (j, 'B', 'rpm'), 3: (j, 'B', 'low')}
        sav = None
        if len(deleted) == 2 and deleted[0] == j:
            k = deleted[1]; types.remove(k)
            if k == 0:
                lab[1] = (j, 'B', 'raise'); sav = 1
            elif k == 1:
                lab[0] = (j, 'B', 'raise'); sav = 0
            elif k == 2:
                lab[3] = (j + 1, 'A', 'raise') if j < J - 1 else (j, 'X', None); sav = 3 if j < J - 1 else 'end'
            else:
                lab[2] = (j + 1, 'A', 'raise') if j < J - 1 else (j, 'X', None); sav = 2 if j < J - 1 else 'end'
        for k in types:
            seq.append((gad[j]['pts'][k], lab[k], sav == k))
    hasR0 = deleted != ('R0',); hasRe = deleted != ('Rend',)
    front_saving = (not hasR0) or (len(deleted) == 2 and deleted[0] == 0 and deleted[1] in (0, 1))
    end_slack = (not hasRe) or (len(deleted) == 2 and deleted[0] == J - 1 and deleted[1] in (2, 3))
    vecs = []         # (U, S, V, lam)
    prev = None
    for idx, (p, (jl, LT, rot), sav) in enumerate(seq):
        if LT == 'X':
            U, S, V, lam = prev
            Y = (-U, -S, F(1), V)
            lin = Y[0] * p[0] + Y[1] * p[1] + Y[3] * p[3]
            mu = (-p[2] / lin) * (1 - eta)
            vecs.append((mu * U, mu * S, mu * V, lam / mu)); prev = vecs[-1]; continue
        G = gad[jl]; L = G[LT]; wL = G['w' + LT]; s = G['s']; c = s / (1 - s)
        Vt = wL * L[1]; kap = c * Vt
        E = ((L[0] - kap) / (1 + kap) + eta * ROT[rot][0], (L[1] - kap) / (1 + kap) + eta * ROT[rot][1])
        if prev is None:
            V = Vt * (1 - ths) if front_saving else (Vt * (1 + th0) if hasR0 else Vt)
            lam = F(1)
        else:
            U0, S0, V0, lam0 = prev
            same = (jl, LT) == prev_lab
            if same:
                V = V0; mu = F(1)
            elif sav:
                V = Vt * (1 - ths)
                Ut = E[0] * (1 + c * V) + c * V; St = E[1] * (1 + c * V) + c * V
                mu = max(Ut / U0, St / S0)
            else:
                cands = []
                for Ei, Xi in ((E[0], U0), (E[1], S0)):
                    den = Xi / V0 - c * (Ei + 1)
                    assert den > 0
                    cands.append(Ei / den)
                V = dyad_up(max(cands), 200)
                mu = V / V0
            lam = lam0 / mu
        U = E[0] * (1 + c * V) + c * V; S = E[1] * (1 + c * V) + c * V
        vecs.append((U, S, V, lam)); prev = vecs[-1]; prev_lab = (jl, LT)
    W = []
    if hasR0:
        U, S, V, lam = vecs[0]; W.append((-lam * U, -lam * S, F(0), lam * V))
    for U, S, V, lam in vecs:
        W.append((-lam * U, -lam * S, lam, lam * V))
    if not hasRe:
        W.pop()
    X = ([Rpt(o0)] if hasR0 else []) + [p for p, _, _ in seq] + ([Rpt(o1)] if hasRe else [])
    return is_chain(X, W)


def part_F():
    print("== Part F (cross-check): explicit strict chains for sampled deletions of T_2 by the construction of Lemma 80 ==", flush=True)
    gad, g, o1 = build_T(2, 8, F(11, 1000))
    J = len(gad)
    eta = F(1, 2 ** 60); ths = F(1, 2 ** 24)
    th0 = 3 * eta / gad[0]['A'][1]
    dels = [('R0',), ('Rend',)] + [(j, k) for j in (0, 1, 2, 9, 70, J - 2, J - 1) for k in range(4)]
    bad = 0
    for D in dels:
        ok, why = scheme_chain(gad, F(3, 2), o1, D, eta, th0, ths)
        if not ok:
            bad += 1; print("  scheme chain failed for deletion", D, why, flush=True)
    need(bad == 0, f"F: {bad} sampled deletion chains failed")
    # negative control: with no deletion (no saving) the same scheme must fail, at R_end
    ok, why = scheme_chain(gad, F(3, 2), o1, (), eta, th0, ths)
    need(not ok and why == f"separation {4 * J}", f"F: negative control did not fail at R_end ({ok}, {why})")
    print(f"  negative control (full ranking): scheme fails at '{why}' as it must", flush=True)
    print(f"  {len(dels) - bad}/{len(dels)} sampled deletions: exact chains verified (Definition 32)", flush=True)


def part_E():
    print("== Part E: constants of Theorem 31 ==", flush=True)
    c = 17 * F(125, 33) * F(11, 500) ** 3
    need(c >= F(685, 10 ** 6), f"E: 17(125/33)(11/500)^3 = {float(c)}")
    need(c * F(8, 27) >= F(203, 10 ** 6), "E: interpolation constant (2/3)^3 c >= 2.03e-4")
    print(f"  n delta^3 >= {float(c):.6e};  interpolated constant {float(c * F(8, 27)):.4e} >= 2.03e-4", flush=True)


def main():
    part_A()
    part_S()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    el =time.time() - T0
    verdict = "CERTIFIED" if not FAIL else "FAILED"
    detail = (f"all parts passed in {el:.0f}s" if not FAIL else f"{len(FAIL)} failures; first: {FAIL[0]}")
    print(json.dumps({"verdict": verdict, "detail": detail}))


if __name__ == "__main__":
    main()
