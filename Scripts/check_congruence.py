def find_uv(n):
    for u in range(n):
        for v in range(n):
            if (u**2 + v**2 + 1) % n == 0:
                return u, v
    return None

def check_odd_n(limit):
    for n in range(1, limit, 2):
        res = find_uv(n)
        if res is None:
            print(f"FAILED for n={n}")
            return
    print(f"SUCCESS: All odd n < {limit} have u^2+v^2+1 = 0 mod n")

check_odd_n(100)
