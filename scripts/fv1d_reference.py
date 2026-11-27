"""Finite-volume WENO reference using cell moments and polynomial solves."""
import math


def solve(matrix, rhs):
    a = [list(row) + [v] for row, v in zip(matrix, rhs, strict=True)]
    for k in range(len(a)):
        pivot = max(range(k, len(a)), key=lambda j: abs(a[j][k]))
        a[k], a[pivot] = a[pivot], a[k]
        scale = a[k][k]
        a[k] = [x / scale for x in a[k]]
        for j in range(len(a)):
            if j != k:
                factor = a[j][k]
                a[j] = [x - factor*y for x,y in zip(a[j], a[k], strict=True)]
    return [row[-1] for row in a]


def weno(widths, values, epsilon):
    # Unit owner width, center at zero. Solve for polynomial averages on each actual interval.
    unit = widths[2] / widths[2]
    left = -unit/2 - (widths[0]+widths[1])/widths[2]
    moments = []
    for width in widths:
        right = left + width/widths[2]
        moments.append([(right**(k+1)-left**(k+1))/((k+1)*(right-left)) for k in range(5)])
        left = right
    def candidates(data):
        return [solve([row[:3] for row in moments[j:j+3]], data[j:j+3]) for j in range(3)]
    def endpoint(poly):
        c,b,a = poly
        return c + b/2 + a/4
    # Solve for the ideal weights by reproducing x^3 and x^4 from their exact averages.
    rows = [[unit]*3]
    for k in (3,4):
        rows.append([endpoint(q) for q in candidates([m[k] for m in moments])])
    ideal = solve(rows, [unit, unit/8, unit/16])
    polys = candidates(values)
    weights = [d/(epsilon + b*b + 13*a*a/3)**2 for d,(_,b,a) in zip(ideal,polys)]
    return sum(w*endpoint(q) for w,q in zip(weights,polys))/sum(weights)


def pressure(q):
    rho, momentum, energy = q
    return energy - momentum**2 / (2*rho)  # gamma = 2


def speed(q):
    if len(q) == 1:
        return abs(q[0])
    return abs(q[1]/q[0]) + math.sqrt(2*pressure(q)/q[0])


def physical_flux(q):
    if len(q) == 1:
        return [q[0]**2/2]
    rho, momentum, energy = q
    v = momentum/rho
    p = pressure(q)
    return [momentum, momentum*v + p, (energy+p)*v]


def endpoints(widths, cells, method, i):
    n = len(cells)
    left, center, right = cells[i-1], cells[i], cells[(i+1) % n]
    if method == "first":
        return center, center
    if method == "muscl":
        minus, plus = [], []
        for l, c, r in zip(left, center, right, strict=True):
            a = 2*widths[i]*(c-l)/(widths[i-1]+widths[i])
            b = 2*widths[i]*(r-c)/(widths[i]+widths[(i+1) % n])
            slope = math.copysign(min(abs(a), abs(b)), a) if a*b > 0 else 0
            minus.append(c - slope/2)
            plus.append(c + slope/2)
    else:
        def endpoint(direction):
            js = [(i+direction*k) % n for k in range(-2, 3)]
            return [weno([widths[j] for j in js], [cells[j][k] for j in js], 1e-6)
                    for k in range(len(center))]
        minus, plus = endpoint(-1), endpoint(1)
    if len(center) == 3 and any(q[0] <= 0 or pressure(q) <= 0 for q in (minus, plus)):
        return center, center
    return minus, plus


def advance(widths, cells, method, dt):
    pairs = [endpoints(widths, cells, method, i) for i in range(len(cells))]
    fluxes = []
    for i, (_, l) in enumerate(pairs):
        r = pairs[(i+1) % len(cells)][0]
        a = max(speed(l), speed(r))
        fluxes.append([(fl+fr-a*(v-u))/2 for fl, fr, u, v in
                       zip(physical_flux(l), physical_flux(r), l, r, strict=True)])
    return [[u - dt*(f-g)/w for u, f, g in zip(q, fluxes[i], fluxes[i-1], strict=True)]
            for i, (w, q) in enumerate(zip(widths, cells, strict=True))]


def replay(model, widths, method):
    left = 0
    initial = []
    for w in widths:
        if model == "burgers":
            initial.append([.5 + math.sin(math.tau*(left+w/2))])
        else:
            rho = 1 + (math.cos(math.tau*left)-math.cos(math.tau*(left+w)))/(16*w)
            initial.append([rho, 2*rho, 1+2*rho])
        left += w
    cells = initial
    if model == "euler":
        t = 0
        while t < .125:
            dt = min(.125-t, .4*min(widths)/max(map(speed, cells)))
            cells = advance(widths, cells, method, dt)
            t += dt
    else:
        dt = .12*min(widths)/max(map(speed, cells))
        for _ in range(2):
            first = advance(widths, cells, method, dt)
            twice = advance(widths, first, method, dt)
            mid = [[(3*u[0]+v[0])/4] for u, v in zip(cells, twice, strict=True)]
            third = advance(widths, mid, method, dt)
            cells = [[(u[0]+2*v[0])/3] for u, v in zip(cells, third, strict=True)]
    return initial, cells
