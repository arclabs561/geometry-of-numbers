def try_reduce(n, k, x, y, z):
    if k == 1: return None
    
    # Pick x0, y0, z0 in [-k/2, k/2] such that x0 = x mod k, etc.
    def best_mod(v, k):
        r = v % k
        if r > k // 2: r -= k
        return r
    
    x0 = best_mod(x, k)
    y0 = best_mod(y, k)
    z0 = best_mod(z, k)
    
    # x0^2 + y0^2 + z0^2 = km
    m_k = (x0**2 + y0**2 + z0**2)
    if m_k % k != 0:
        print("ERROR: mod k failed")
        return None
    m = m_k // k
    
    if m == 0:
        # All x0, y0, z0 are 0, so k divides x, y, z.
        # We can divide x, y, z by k and get k^2 n = k^2 (X^2+Y^2+Z^2) => n = X^2+Y^2+Z^2
        return (1, x//k, y//k, z//k)
    
    # Use Lagrange identity:
    # (x^2+y^2+z^2+0)(x0^2+y0^2+z0^2+0) = k^2 nm = A^2 + B^2 + C^2 + D^2
    # A = xx0 + yy0 + zz0
    # B = xy0 - yx0
    # C = xz0 - zx0
    # D = yz0 - zy0
    A = x*x0 + y*y0 + z*z0
    B = x*y0 - y*x0
    C = x*z0 - z*x0
    D = y*z0 - z*y0
    
    # We have A^2 + B^2 + C^2 + D^2 = k^2 nm
    # So (A/k)^2 + (B/k)^2 + (C/k)^2 + (D/k)^2 = nm
    # If we want 3 squares, one of them must be 0 mod k and we drop it?
    # No, we need one of them to be ZERO.
    
    if A % k == 0 and B % k == 0 and C % k == 0 and D % k == 0:
        return (m, A//k, B//k, C//k, D//k)
    else:
        return None

def test_descent(n):
    print(f"Testing descent for n={n}...")
    # Find initial k
    best_u, best_v = -1, -1
    for u in range(n):
        for v in range(n):
            if (u**2 + v**2 + 1) % n == 0:
                best_u, best_v = u, v
                break
        if best_u != -1: break
    
    if best_u == -1: return
    
    # Initial point: x=u, y=v, z=1 => x^2+y^2+z^2 = u^2+v^2+1 = kn
    x, y, z = best_u, best_v, 1
    k = (x**2 + y**2 + z**2) // n
    
    path = [(k, x, y, z)]
    while k > 1:
        res = try_reduce(n, k, x, y, z)
        if res is None:
            print(f"  STUCK at k={k}")
            break
        m, A, B, C, D = res
        # We got m*n = (A/k)^2 + (B/k)^2 + (C/k)^2 + (D/k)^2
        # This is 4 squares!
        print(f"  Reduced k={k} -> m={m} (but now 4 squares: {A}, {B}, {C}, {D})")
        # In 3-square descent, we need a different trick.
        break

test_descent(11)
