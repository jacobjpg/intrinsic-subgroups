def find_order(P):
    '''
    Finds order of a Q-rational point of an elliptic curve over Q.
    Makes use of Mazur's Theorem.
    '''
    
    Q = P
    for n in range(1,13):
        if Q == 0:
            return n
        Q += P
    return 0

def tate_normal_form(a1,a2,a3,a4,a6,x0,y0):
    '''
    Given coefficients of an elliptic curve in long Weierstrass form and
    coodinates of an affine point P = (x0,y0) not of order 2 or 3 on E,
    returns a tuple (a,b,phi), where (a,b) are the coefficients of a
    curve E' in Tate normal form and phi is an isomorphism E -> E' that
    sends P to (0,0). If N is the order of P, E' is given by:
    If N is not 2 or 3: y^2 + (1+a)xy + by = x^3 + bx^2;
    if N = 2: y^2 = x^3 + ax^2 + bx;
    if N = 3: y^2 + axy + by = x^3.

    TODO: implement phi as object of class EllipticCurveMorphism?
    (Currently, phi is simply a function that takes P.x() and P.y() and
    returns the coordinates of phi(P).)
    '''

    # First, check that P is on E.
    if y0^2 + a1*x0*y0 + a3*y0 != x0^3 + a2*x0^2 + a4*x0 + a6:
        raise ValueError(f'The point ({x0}, {y0}) does not lie on the curve\
            y^2 + {a1}xy + {a3}y = x^3 + {a2}x^2 + {a4}x + {a6}.')
    
    # Change of variables to bring P to (0,0): (x,y) <- (x+x0, y+y0)
    phi1 = lambda x,y : (x-x0,y-y0)
    # (y + y0)^2 + a1(y + y0)(x + x0) + a3(y + y0)    = (x + x0)^3 + a2(x + x0)^2 + a4(x + x0) + a6
    # y^2 + 2*y0 y + a1 xy + a1*y0 x + a1*x0 y + a3 y = x^3 + 3*x0 x^2 + 3*x0^2 x + a2 x^2 + 2*x0 x + a4 x
    # y^2 + (a1)xy + (2*y0 + a1*x0 + a3)y             = x^3 + (3*x0 + a2)x^2 + (3*x0^2 + 2*a2*x0 + a4 - a1*y0)x
    a1, a2, a3, a4 = a1, (3*x0 + a2), (2*y0 + a1*x0 + a3), (3*x0**2 + 2*a2*x0 + a4 - a1*y0)
    # y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x
    
    if a3 == 0:
        # P is 2-torsion iff a3 == 0.
        
        # Change of variables (x,y) <- (x, y - a1*x/2)
        phi2 = lambda x,y : (x,y + a1*x/2)
        phi = lambda x,y : phi2(*phi1(x,y))
        a, b = a2 + a1^2/2, a4
        return (a, b, phi)
    
    # Change of variables to eliminate a4: (x,y) <- (x, y + a4*x/a3)
    phi2 = lambda x,y : (x,y - a4*x/a3)
    # (y + a4/a3 * x)^2 + a1x(y + a4/a3 * x) + a3(y + a4/a3 * x) = x^3 + a2 x^2 + a4 x
    # y^2 + 2*a4/a3 xy + (a4/a3)^2 x^2 + a1 xy + (a1*a4/a3) x^2 + a3 y + a4 x = x^3 + a2 x^2 + a4 x
    # y^2 + (2*a4/a3 + a1) xy + a3 y = x^3 + (a2 - (a4/a3)^2 - a1*a4/a3) x^2
    b1, b2, b3 = (2*a4/a3 + a1), (a2 - (a4/a3)^2 - a1*a4/a3), a3
    # y^2 + b1 xy + b3 y = x^3 + b2 x^2
    
    if b2 == 0:
        # P is 3-torsion iff b2==0.
        a, b = b1, b3
        phi = lambda x,y : phi2(*phi1(x,y))
        return (a, b, phi)

    u = b3/b2
    # Change of variables: (x,y) <- (u^2 x, u^3 y)
    phi3 = lambda x,y : (u^(-2) * x, u^(-3) * y)
    phi = lambda x,y : phi3(*phi2(*phi1(x,y)))
    a, b = (b1 * b2 / b3) - 1, (b2^3 / (b3^2))
    
    return (a,b, phi)

def t0(a,b,N):
    '''
    Given (a,b) defining a curve E in Tate normal form where (0,0) has order N,
    returns t parameter defining (E,P).
    We are using the fact that curves with a point of order N = 2,...,10,12 are
    parameterized by the genus-0 curve X_1(N), and can thus be described using a
    single parameter t.
    '''
    
    # Case N = 2 or 3
    if N == 2:
        return 4*b/(a^2 - 4*b)
    if N == 3:
        return 27*b/(a^3 - 27*b)

    # Case N > 4
    if N == 4 or N == 5:
        return b
    if N == 6:
        return 1 - b/a
    if N == 7:
        return 1 - b/a
    if N == 8:
        return a/b - 1
    if N == 9:
        return (a - a^2 - b)/(a - b)
    if N == 10:
        return (a - a^2 - b)/a^2
    if N == 12:
        return -(a^3 - a*b + b^2)/(a - b)^2

    raise ValueError('Point has order not in [2,..,10,12]')

def fN(a,b,N):
    '''
    Given (a,b) defining a curve in Tate normal form where (0,0) has order N, returns fN(t).
    Here, the pairing on E(QQ)_tors is -<P,P> = fN(t) \otimes 1/N.
    '''
    t = t0(a,b,N)
    
    # Case N = 2 or 3
    if N == 2:
        if t != -1:
            return t * (1+t)
        else:
            return b
    if N == 3:
        if t != -1:
            return t * (1+t)^2
        else:
            return b

    # Case N > 4
    if N == 4 or N == 5:
        return t
    if N == 6:
        return t * (1-t)^2
    if N == 7:
        return t * (1-t)^4
    if N == 8:
        return t * (1-t)^2 * (1+t)^4
    if N == 9:
        return t * (1-t)^4 * (1-t+t^2)^3
    if N == 10:
        return t * (1-t)^2 * (1+t)^8 * (1+t-t^2)^5
    if N == 12:
        return t * (1-t)^2 * (1-t+t^2)^3 * (1+t^2)^4 * (1+t)^6

    # (If not a torsion point)
    if N == 0:
        return 0

def find_power(r):
    '''
    Given a rational number r, returns the maximal e for which
    r = q^e for some rational q.
    For the purposes of the intrinsic subgroup calculation,
    only needs to check e dividing 2^3 * 3 * 5. Will not
    detect higher powers.
    If r = 0 or 1, returns 0.
    '''
    
    if r in {0,1}: return 0
    p = 1
    if QQ(r).is_nth_power(5): p *= 5
    if QQ(r).is_nth_power(3): p *= 3
    for n in [8,4,2]:
        if QQ(r).is_nth_power(n): p *= n; break
    return p

def intrinsic_subgroup_order_cyclic_case(wCoeffs, P):
    '''
    Given wCoeffs = (a1,a2,a3,a4,a6) defining an elliptic curve E
    over QQ and a torsion point P on E, assuming P is a generator
    of E(QQ)_tors, returns (n,R) where n = #E(QQ)_tors^is and
    R is a generator of E(QQ)_tors^is.
    '''
    
    (a1,a2,a3,a4,a6) = wCoeffs
    N = find_order(P)
    x0,y0 = P.x(), P.y()

    (a,b,phi) = tate_normal_form(a1,a2,a3,a4,a6,x0,y0)
    if N == 0: return 0
    PP = fN(a,b,N)
    e = find_power(abs(PP))
    d = gcd(N, e)
    return (d, N/d * P)

def intrinsic_subgroup_order_2gens_case(wCoeffs, P, Q):
    '''
    Given wCoeffs = (a1,a2,a3,a4,a6) defining an elliptic curve E
    over Q and torsion points P, Q on E such that P, Q generate
    E(QQ)_tors and 2*Q = 0, returns (n,R) where n = #E(Q)_tors^is
    and R is a generator of E(Q)_tors^is.
    '''
    
    E = EllipticCurve(wCoeffs)
    if 2*Q != E(0): raise ValueError('Expected 2*Q == 0')
    
    N = find_order(P)
    if N in {6,8}: return (1,E(0))

    (a1,a2,a3,a4,a6) = wCoeffs
    x0,y0 = P.x(), P.y()
    xQ,yQ = Q.x(), Q.y()
    (a,b,phi) = tate_normal_form(a1,a2,a3,a4,a6,x0,y0)
    
    if N == 4:
        assert yQ^2 + a1*xQ*yQ + a3*yQ == xQ^3 + a2*xQ^2 + a4*xQ + a6
        
        (x1,y1) = phi(xQ, yQ)
        assert y1^2 + (1+a)*x1*y1 + b*y1 == x1^3 + b*x1^2
        
        u = -1 - (1/(4*x1))
        assert (a,b) == (0,u/(4*(1+u)^2))
        
        PP, QQ, PQ = 4*u*(1+u)^2, (1+u)*(1-u), 1+u
        if abs(PP).is_square():
            return (2,2*P)
        if abs(QQ).is_square() and abs(PQ).is_square():
            return (2,Q)
        if abs(QQ).is_square() and abs(PP*PQ).is_square():
            return (2,2*P+Q)
        return (1,E(0))

    if N == 2:
        (x1, y1) = phi(xQ,yQ)
        assert y1 == 0
        u = -a/x1 - 1
        assert (x1*u)^2 + a*(x1*u) + b == 0
        
        PP, QQ, PQ = u, 1-u, x1
        if abs(PP).is_square() and abs(PQ).is_square():
            return (2,P)
        if abs(QQ).is_square() and abs(PQ).is_square():
            return (2,P)
        if abs(PP*PQ).is_square() and abs(QQ*PQ).is_square():
            return (2,P+Q)
        return (1,E(0))

def intrinsic_subgroup_order(wCoeffs):
    '''
    Given the Weierstrass coefficients of an elliptic curve E/Q,
    computes its intrinsic torsion subgroup. Returns (n,R), where
    n = #E(QQ)_tors^is and R is a generator of E(QQ)_tors^is (or,
    in the case n=1, R = E(0)).

    Currently, only n is recorded in the LMFDB. R is recoverable
    from n when E(QQ)_tors is cyclic.

    Note that for curves over Q, E(QQ)_tors^is is always cyclic of
    order at most 5.
    '''
    
    E = EllipticCurve(wCoeffs)
    T = E.torsion_subgroup().gens()
    
    if len(T) == 1:
        P = E(T[0])
        return intrinsic_subgroup_order_cyclic_case(wCoeffs,P)
    
    if len(T) == 2:
        P, Q = E(T[0]), E(T[1])
        if 2*Q != 0:
            P, Q = Q, P
        return intrinsic_subgroup_order_2gens_case(wCoeffs, P, Q)

    return (1,E(0))