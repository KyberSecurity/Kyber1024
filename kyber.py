

# An implementation of Kyber1024 based around the 20210804 specification.
# This is implementation is intended for educational/research purposes.
# It should not be used for the protection of sensitive information.
# Typically: - qint denotes a F_q element (integer mod 3329)
#            - element denotes a member of R_q (list of 256 qints)
#            - dint denotes a compressed F_q element (integer mod 2^d)
#            - short_elt is a compressed element (list of 256 dints)


import secrets
import hashlib
from math import floor

q = 3329
zeta = [pow(17,n,q) for n in range(256)] 
i128 = pow(128,-1,q)      # 1/128 mod q

# Rounding per the definition on page 4
def roundu(x):
     return floor(x+0.5)

# Compress function from page 5
def compress(x,d):
    return roundu(x*2**d/q)%2**d

# Decompress function from page 5
def decompress(x,d):
     return roundu(q*x/2**d)

# Bit reversal of a 7-bit number
def br7(a):
     result = 0
     for n in range(7):
         result <<= 1
         result += a&1
         a >>= 1
     return result

# The Kyber NTT (equations (4) and (5) on page 6)
def NTT(f):
    ans = [0]*256
    # Even-numbered terms
    ans[::2] = [ sum(f[2*j]*zeta[((2*br7(i)+1)*j)%256] for j in range(128))%q for i in range(128) ]
    # Odd-numbered terms
    ans[1::2] =  [ sum(f[2*j+1]*zeta[((2*br7(i)+1)*j)%256] for j in range(128))%q for i in range(128) ]
    return ans

# The Kyber NTT inverse (inferred)
def NTTinv(f):
    ans = [0]*256
    # Even-numbered terms
    ans[::2] = [ (i128*sum(f[2*i]*zeta[(-(2*br7(i)+1)*j)%256] for i in range(128)))%q for j in range(128) ]
    # Odd-numbered terms
    ans[1::2] =  [ (i128*sum(f[2*i+1]*zeta[(-(2*br7(i)+1)*j)%256] for i in range(128)))%q for j in range(128) ]
    return ans

# The NTT multiplication (unlabelled equation on page 6)
def NTT_mul(f,g):
     hat_h = [0]*256
     # Even-numbered terms
     hat_h[::2] = [(f[2*i]*g[2*i] + zeta[2*br7(i)+1]*f[2*i+1]*g[2*i+1])%q for i in range(128)]
     # Odd-numbered terms
     hat_h[1::2] = [(f[2*i+1]*g[2*i] + f[2*i]*g[2*i+1])%q for i in range(128) ]
     return hat_h

# Addition of elements of R_q
def Rq_add(f,g):
     return [ (f[i]+g[i])%q for i in range(256) ]

# Sampling elements of Rq (algorithm 1 page 6)
def parse(bytes):
    hat_a = 256*[0]
    i = j = 0
    while j<256 and i< 557:
        d1 = int(bytes[i])+(int(bytes[i+1])%16)*256
        d2 = int(bytes[i+1])//16 + 16*int(bytes[i+2])
        if d1 < q:
            hat_a[j] = d1 
            j += 1
        if d2 < q and j<256 :
            hat_a[j] = d2 
            j += 1
        i += 3
    if i > 557:
        print("Byte array ran out while generating hat a!")
    return hat_a

# Error sampling from centred binomial parameter 2 (algorithm 2 page 7)
def cbd(bytes):
    bits = 0
    for b in bytes[::-1]:
        bits = 256*bits + b
    f = []
    for i in range(256):
        a = bits%4
        bits >>= 2
        b = bits%4
        bits >>= 2
        f.append(bin(a).count('1')-bin(b).count('1'))
    return f     

# Decode byte array to element of Rq (algorithm 3 page 7)
def decode(l,bytes):
    element = []
    iters = len(bytes)//l
    for i in range(iters):
        bits = 0
        for j in range(l):
            bits += bytes[l*i+j]<<(8*j)
        for j in range(8):
            element += [ bits%(1<<l) ] 
            bits >>= l
    return element

# Encode element of Rq as bytes (inferred)
def encode(l,element):
    bytes =b''
    items = len(element)//8
    for i in range(32):
       bits = 0
       for j in range(8):
           bits += element[8*i+j]<<(l*j)
       bytes += bits.to_bytes(l,'little')
    return bytes

# CPAPKE Key generation (algorithm 4 page 8)
def CPAPKE_KeyGen():
    d = secrets.token_bytes(32)
    G_d = hashlib.sha3_512(d).digest()
    rho,sigma = G_d[:32],G_d[32:]
    hat_A = []
    # Generate matrix in NTT domain
    for i in range(4):
        hat_A += [[]]
        for j in range(4):
            sh128 = hashlib.shake_128(rho + j.to_bytes(1,'big') + i.to_bytes(1,'big'))
            hat_A[i] += [parse(sh128.digest(560))]  # Chernoff bound says 560 bytes suffices with prob. 9994/10000 
    # Sample s from centred binomial
    s = []
    for N in range(4):
        sh256 = hashlib.shake_256(sigma)
        sh256.update(N.to_bytes(1,'big'))
        s += [ cbd(sh256.digest(128)) ]
    # Sample e from centred binomial
    e = []
    for N in range(4):
        sh256 = hashlib.shake_256(sigma)
        sh256.update(N.to_bytes(1,'big'))
        e += [ cbd(sh256.digest(128)) ]
    hat_s = [ NTT(element) for element in s ]
    hat_e = [ NTT(element) for element in e ]
    hat_t = []
    for i in range(4):
         hat_t += [[]]
         element = [0]*256
         for j in range(4):                         # ith row of hat_A times hat_s...
             element = Rq_add(element,NTT_mul(hat_s[j],hat_A[i][j]))
         element = Rq_add(element,hat_e[i])         # ... add in ith component of hat_e...
         hat_t[i] += element                        # ... to make the ith entry of hat_t
    # pk = As + e
    public = b''.join(encode(12,element) for element in hat_t)
    public += rho
    # sk = s
    private = b''.join(encode(12,element) for element in hat_s)
    return public, private

# CPAPKE encryption (algorithm 5 page 9)    
def CPAPKE_Enc(pk,m,r):
    N = 0
    hatt_enc,rho = pk[:1536],pk[1536:]
    hat_t = [decode(12,hatt_enc[384*i:384*(i+1)]) for i in range(4)]
    # Generate transpose matrix in NTT domain
    hat_AT = []
    for i in range(4):
        hat_AT += [[]]
        for j in range(4):
            sh128 = hashlib.shake_128(rho + i.to_bytes(1,'big') + j.to_bytes(1,'big'))
            hat_AT[i] += [parse(sh128.digest(560))] 
    # Sample  vector r 
    rr = []
    for i in range(4):
        sh256 = hashlib.shake_256(r)
        sh256.update(N.to_bytes(1,'big'))
        rr += [ cbd(sh256.digest(128)) ]
        N += 1
    # Sample e1
    e1 = []
    for i in range(4):
        sh256 = hashlib.shake_256(r)
        sh256.update(N.to_bytes(1,'big'))
        e1 += [ cbd(sh256.digest(128)) ]
        N += 1
    # Sample e2
    sh256 = hashlib.shake_256(r)
    sh256.update(N.to_bytes(1,'big'))
    e2 = cbd(sh256.digest(128)) 
    hat_r = [ NTT(element) for element in rr ]
    # Vector u = A^T r + e1
    uu = [[]]*4
    for i in range(4):
         element = [0]*256
         for j in range(4):                         # ith row of hat_AT times hat_r...
             element = Rq_add(element,NTT_mul(hat_r[j],hat_AT[i][j]))
         # Invert NTT
         uu[i] = NTTinv(element)
         # Add error
         uu[i] = Rq_add(uu[i],e1[i])
    # Element v = t^T r + e2 + Decompress_q(m,1)
    shared = [0] * 256
    for j in range(4):
        shared = Rq_add(shared,NTT_mul(hat_t[j],hat_r[j])) 
    shared  = NTTinv(shared)
    v = Rq_add(shared,e2)
    m_bits = decode(1,m)
    m_Rq = [ decompress(bit,1) for bit in m_bits ]
    while len(m_Rq) <256:
        m_Rq +=[0]
    v = Rq_add(v,m_Rq)
    c1 = [[compress(qint,11) for qint in element] for element in uu]
    c1 = b''.join(encode(11,short_elt) for short_elt in c1)
    c2 = [compress(qint,5) for qint in v]
    c2 = encode(5,c2)
    # Return c = Compress_q(u,11),Compress(v,5)
    return c1+c2

# CPAPKE Decryption (algorithm 6 page 9)
def CPAPKE_Dec(sk,cc):
    c1, c2 = cc[:11*128],cc[11*128:]
    uu = [[decompress(dint,11) for dint in decode(11,c1[352*i:352*(i+1)])] for i in range(4)]
    hat_u = [ NTT(element) for element in uu ]
    v = [decompress(dint,5) for dint in decode(5,c2)]
    hat_s = [decode(12,sk[384*i:384*(i+1)]) for i in range(4)]
    shared = [0]*256
    for j in range(4):                         # hat_s^T * hat_u
        shared = Rq_add(shared,NTT_mul(hat_s[j],hat_u[j]))
    shared = NTTinv(shared)
    # m = Compress_q(v - s^T u,1)
    m = Rq_add(v, [-1*qint for qint in shared ])
    m = encode(1,[compress(qint,1) for qint in m])
    return m

# CCAKEM key generation (algorithm 7 page 10)
def CCAKEM_KeyGen():
    z = secrets.token_bytes(32)
    pk, skdash = CPAPKE_KeyGen()
    H_pk = hashlib.sha3_256(pk).digest()
    sk = skdash + pk + H_pk + z
    return pk, sk

# CCAKEM encryption (algorithm 8 page 10)
def CCAKEM_Enc(pk):
    m = secrets.token_bytes(32)
    m = hashlib.sha3_256(m).digest()
    H_pk = hashlib.sha3_256(pk).digest()
    G_m = hashlib.sha3_512(m + H_pk).digest()
    Kbar, r = G_m[:32], G_m[32:]
    c = CPAPKE_Enc(pk,m,r)
    H_c = hashlib.sha3_256(c).digest()
    K = hashlib.shake_128(Kbar + H_c).digest(32)
    return c, K

# CCAKEM decryption (algorithm 9 page 10)
def CCAKEM_Dec(c,sk):
    sk,pk,h,z = sk[:1536], sk[1536:3104], sk[3104:3136], sk[3136:3168]
    mdash =  CPAPKE_Dec(sk,c) 
    G_mdash = hashlib.sha3_512(mdash + h).digest()
    Kbardash , rdash = G_mdash[:32], G_mdash[32:]
    cdash = CPAPKE_Enc(pk,mdash,rdash)
    H_c = hashlib.sha3_256(c).digest()
    if cdash == c:
        K = hashlib.shake_128(Kbardash + H_c).digest(32)
        return K
    else:
        K = hashlib.shake_128(z + H_c).digest(32)
        return K

