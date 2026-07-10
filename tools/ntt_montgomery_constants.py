MODS = [
    (469762049, 3),
    (1811939329, 13),
    (2013265921, 31),
]

R = 1 << 32

def mont_inv32(a):
    x = 1
    for _ in range(5):
        x = (x * (2 - a * x)) & 0xFFFFFFFF
    return (-x) & 0xFFFFFFFF

def mont_reduce(mod, ninv, x):
    m = (x & 0xFFFFFFFF) * ninv & 0xFFFFFFFF
    t = (x + m * mod) >> 32
    if t >= mod:
        t -= mod
    return t

def mont_r2(mod):
    return (R * R) % mod

def mont_in(mod, ninv, x):
    return mont_reduce(mod, ninv, (x % mod) * mont_r2(mod))

def two_adicity(n):
    k = 0
    while n % 2 == 0:
        k += 1
        n //= 2
    return k, n

print("static const mont_ctx_t NTT_CTX[] = {")
for mod, root in MODS:
    ninv = mont_inv32(mod)
    r2 = mont_r2(mod)
    one = mont_in(mod, ninv, 1)
    twos, odd = two_adicity(mod - 1)
    print(f"    {{{mod}u, {root}u, {ninv}u, {r2}u, {one}u}}, // 2^{twos} * {odd}")
print("};")
