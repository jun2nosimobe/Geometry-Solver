
# ==========================================
# 1. 有限体 (ModInt) クラスと数学エンジン
# ==========================================
class ModInt:
    MOD = 998244353 
    I = 911660635
    def __init__(self, value):
        if isinstance(value, ModInt): self.value = value.value
        elif isinstance(value, complex): self.value = (int(value.real) + int(value.imag) * ModInt.I) % ModInt.MOD
        else: self.value = int(value) % ModInt.MOD
    def __add__(self, other): return ModInt(self.value + (other.value if isinstance(other, ModInt) else int(other)))
    def __radd__(self, other): return self.__add__(other)
    def __sub__(self, other): return ModInt(self.value - (other.value if isinstance(other, ModInt) else int(other)))
    def __rsub__(self, other): return ModInt((other.value if isinstance(other, ModInt) else int(other)) - self.value)
    def __mul__(self, other): return ModInt(self.value * (other.value if isinstance(other, ModInt) else int(other)))
    def __rmul__(self, other): return self.__mul__(other)
    def __truediv__(self, other):
        ov = other.value if isinstance(other, ModInt) else int(other)
        if ov == 0: raise ZeroDivisionError()
        return ModInt(self.value * pow(ov, self.MOD - 2, self.MOD))
    def __rtruediv__(self, other):
        ov = other.value if isinstance(other, ModInt) else int(other)
        if self.value == 0: raise ZeroDivisionError()
        return ModInt(ov * pow(self.value, self.MOD - 2, self.MOD))
    def __pow__(self, power): return ModInt(pow(self.value, int(power), self.MOD))
    def __neg__(self): return ModInt(-self.value)
    def __eq__(self, other):
        if isinstance(other, ModInt):
            return self.value == other.value
        try:
            return self.value == (int(other) % self.MOD)
        except (TypeError, ValueError):
            return False
    def __abs__(self): return abs(self.value)
    def __repr__(self): return str(self.value)

def matrix_rank_mod(matrix_mod):
    rows, cols = len(matrix_mod), len(matrix_mod[0]) if matrix_mod else 0
    rank = 0
    M = [[matrix_mod[r][c] for c in range(cols)] for r in range(rows)]
    for c in range(cols):
        pivot_r = next((r for r in range(rank, rows) if M[r][c].value != 0), -1)
        if pivot_r == -1: continue
        M[rank], M[pivot_r] = M[pivot_r], M[rank]
        inv_val = ModInt(1) / M[rank][c]
        for j in range(c, cols): M[rank][j] = M[rank][j] * inv_val
        for r in range(rows):
            if r != rank and M[r][c].value != 0:
                factor = M[r][c]
                for j in range(c, cols): M[r][j] = M[r][j] - factor * M[rank][j]
        rank += 1
        if rank == rows: break
    return rank

def get_numerical_degree(t_values, x_values, max_d, mode='mod', tolerance=1e-8):
    N = len(t_values)
    if mode == 'mod':
        for d in range(max_d + 1):
            if N < 2 * d + 2: continue
            A = [[ModInt(0) for _ in range(2 * d + 2)] for _ in range(N)]
            for i in range(N):
                t, x = t_values[i], x_values[i]
                for k in range(d + 1):
                    A[i][k] = t**k
                    A[i][d + 1 + k] = -x * (t**k)
            if matrix_rank_mod(A) < 2 * d + 2: return d
        return max_d
    return max_d
    