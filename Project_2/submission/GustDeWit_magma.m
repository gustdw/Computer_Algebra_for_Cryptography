// Author: Gust De Wit (r0948039)

// ------------------------------------------------
// Task 1
// ------------------------------------------------
// AI helped with the syntax and how to efficiently perform certain steps (e.g. generating the matrix). Furhthermore, AI did the testcode generation for timing and testing correctness.

CantorZassenhaus := function(f)
    PY := Parent(f);
    Y := BaseRing(PY);
    Q := #Y;
    e := (Q - 1) div 2;
    d := Degree(f);

    // random a with 1 <= deg a < d
    repeat
        a := PY ! [ Random(Y) : i in [1..d] ];
        a := a mod f;
    until Degree(a) ge 1;

    g1 := Gcd(a, f);
    if Degree(g1) ge 1 and Degree(g1) lt d then
        return true, g1;
    end if;

    // b = a^((Q-1)/2) mod f
    S := quo< PY | f >;
    b := PY ! ((S ! a)^e);  // Square and multiply

    g2 := Gcd(b - 1, f);
    if g2 ne 1 and g2 ne f then
        return true, g2;
    end if;

    return false, f;
end function;

FindRoot := function(f0)
    f := f0 / LeadingCoefficient(f0);
    while Degree(f) gt 1 do
        repeat
            ok, h := CantorZassenhaus(f);
        until ok;
        f := h / LeadingCoefficient(h);
    end while;
    return -Coefficient(f, 0);  // f = w - y0
end function;

FieldIsomorphism := function(f, g)
    R := Parent(f);
    Fp := BaseRing(R);
    Y := ext< Fp | g >;
    fY := ChangeRing(f, Y);
    y0 := FindRoot(fY);
    return R ! Eltseq(y0);
end function;

InverseFieldIsomorphism := function(f, g, s)
    R := Parent(f);
    Fp := BaseRing(R);
    n := Degree(f);
    Y := ext< Fp | g >;
    y0 := Evaluate(ChangeRing(s, Y), Y.1);
    M := Matrix(Fp, [ Eltseq(y0^i) : i in [0..n-1] ]);
    vy := Vector(Fp, Eltseq(Y.1));
    vt := vy * M^(-1);
    return R ! Eltseq(vt);
end function;

// Tests
print "=== small correctness test (p = 13, n = 8) ===";
p := 13; n := 8;
Fp := GF(p);
R<z> := PolynomialRing(Fp);
f := R ! RandomIrreduciblePolynomial(Fp, n);
g := R ! RandomIrreduciblePolynomial(Fp, n);

s := FieldIsomorphism(f, g);
printf "s(y) is a root of f in Y : %o\n", (Evaluate(f, s) mod g) eq 0;

t := InverseFieldIsomorphism(f, g, s);
printf "s(t(z)) = z  (mod f)     : %o\n", ((Evaluate(s, t) - z) mod f) eq 0;
printf "t(s(z)) = z  (mod g)     : %o\n", ((Evaluate(t, s) - z) mod g) eq 0;

print "";
print "=== timings (1.b): p = 2^16 + 7, n = 2^k, k = 2..6 ===";
p := 2^16 + 7;
Fp := GF(p);
R<z> := PolynomialRing(Fp);
for k in [2..6] do
    n := 2^k;
    f := R ! RandomIrreduciblePolynomial(Fp, n);
    g := R ! RandomIrreduciblePolynomial(Fp, n);
    tt := Cputime();
    s  := FieldIsomorphism(f, g);
    el := Cputime(tt);
    ok := (Evaluate(f, s) mod g) eq 0;
    printf "n = %3o : %6o s   (correct = %o)\n", n, el, ok;
end for;


// -----------------------------------------------
// Task 2
// -----------------------------------------------
// AI helped with testcode generation for timing and testing correctness.
// Task 2.a
SampleChi := function(n, alpha, beta)
    return [ Random(alpha, beta) : i in [1..n] ];
end function;

// Task 2.b
FFIPKeyGen := function(p, n, alpha, beta)
    Fp := GF(p);
    R<z> := PolynomialRing(Fp);
    d := n div 2;   // floor(n/2)
    repeat
        hc := SampleChi(d + 1, alpha, beta);    // coeffs deg 0..d
        f  := z^n + (R ! [ Fp ! c : c in hc ]); // f(z) = z^n + h(z)
    until IsIrreducible(f);
    g := R ! RandomIrreduciblePolynomial(Fp, n);
    s := FieldIsomorphism(f, g);
    t := InverseFieldIsomorphism(f, g, s);
    return f, g, s, t;
end function;

// Task 2.c
FFIPEncrypt := function(m, g, s, alpha, beta)
    R := Parent(g);
    Fp := BaseRing(R);
    n := Degree(g);
    mb := [ StringToInteger(m[i]) : i in [1..n] ];  // bit i -> coeff of x^{i-1}
    Rn := SampleChi(n, alpha, beta);
    mprime := R ! [ Fp ! (mb[i] + 2*Rn[i]) : i in [1..n] ]; // m + 2r in X
    Y := ext< Fp | g >;
    y0 := Evaluate(ChangeRing(s, Y), Y.1);  // phi(x) = s(y)
    cv := Evaluate(ChangeRing(mprime, Y), y0);  // phi(m') = m'(y0) in Y
    return R ! Eltseq(cv);
end function;

// Task 2.d
FFIPDecrypt := function(c, f, t)
    R  := Parent(f);
    Fp := BaseRing(R);
    p  := #Fp;
    n := Degree(f);
    X  := ext< Fp | f >;
    tX := Evaluate(ChangeRing(t, X), X.1);  // psi(y) = t(x)
    mp := Evaluate(ChangeRing(c, X), tX);   // psi(c) = c(t(x)) in X
    cf := Eltseq(mp);
    m := "";
    for i in [1..n] do
        ci := Integers() ! cf[i];
        if ci gt (p - 1) div 2 then ci := ci - p; end if;
        m := m cat IntegerToString(ci mod 2);
    end for;
    return m;
end function;

// Tests
p := 13; n := 64; alpha := -1; beta := 1;
f, g, s, t := FFIPKeyGen(p, n, alpha, beta);

m := "1001000110011000011110111000101001011101101100000110010011111001";
printf "message length = %o (expected %o)\n", #m, n;

c  := FFIPEncrypt(m, g, s, alpha, beta);
md := FFIPDecrypt(c, f, t);

printf "decrypted == original : %o\n", md eq m;

// -----------------------------------------------
// Task 3
// -----------------------------------------------
// AI helped with the syntax and how to efficiently perform certain steps
// (e.g. assembling the coefficient matrices). Furthermore, AI did the
// testcode generation for timing and counting failures.

// Task 3.b
KnownPlaintextNoiseAttack := function(g, cs, ms, rs)
    R  := Parent(g);
    Fp := BaseRing(R);
    n  := Degree(g);

    // coefficient column vector of length n, padded with zeros if needed
    coeffs := function(poly)
        e := Eltseq(poly);
        return [ i le #e select Fp ! e[i] else Fp ! 0 : i in [1..n] ];
    end function;

    // W has columns w_i = m_i + 2 r_i ; C has columns c_i
    Wcols := [ ];
    Ccols := [ ];
    for i in [1..n] do
        wi := [ coeffs(ms[i])[j] + 2 * coeffs(rs[i])[j] : j in [1..n] ];
        Append(~Wcols, wi);
        Append(~Ccols, coeffs(cs[i]));
    end for;

    // build matrices with the w_i / c_i as columns
    W := Transpose(Matrix(Fp, Wcols));
    C := Transpose(Matrix(Fp, Ccols));

    if Determinant(W) eq 0 then
        return R ! 0;   // failure: W singular
    end if;

    M := C * W^(-1);

    // s = phi(x) = image of the basis vector x
    s := [ M[r][2] : r in [1..n] ];
    return R ! s;
end function;

// Kahn-Komlos asymptotic failure probability 1 - prod_{i>=1}(1 - p^{-i})
PredFail := function(p, n)
    prod := 1.0;
    for i in [1..n] do
        prod := prod * (1.0 - 1.0 / (p ^ i));
    end for;
    return 1.0 - prod;
end function;

// Tests (run directly: magma known_plaintext_noise.m)
print "=== Task 3.b : n = 32, p = NextPrime(2^k), k = 1..8 ===";
n := 32; alpha := -1; beta := 1; trials := 1000;

for k in [1..8] do
    p := NextPrime(2^k);
    
    total := 0.0;
    fails := 0;
    correct := 0;
    for it in [1..trials] do
        f, g, s, t := FFIPKeyGen(p, n, alpha, beta);
        R := Parent(g);
        Fp := BaseRing(R);

        Y := ext< Fp | g >;
        sy := Evaluate(ChangeRing(s, Y), Y.1);  // phi(x) = s(y) in Y

        // generate n triples (c_i, m_i, r_i) as polynomials over Fp;
        // message bits via SampleChi(.,0,1), noise via SampleChi(.,alpha,beta)
        cs := []; ms := []; rs := [];
        for i in [1..n] do
            mb := SampleChi(n, 0, 1);          // message bits in {0,1}
            rn := SampleChi(n, alpha, beta);   // noise
            mi := R ! [ Fp ! b : b in mb ];
            ri := R ! [ Fp ! b : b in rn ];
            wi := R ! [ Fp ! (mb[j] + 2*rn[j]) : j in [1..n] ];
            ci := R ! Eltseq(Evaluate(ChangeRing(wi, Y), sy));  // phi(w_i)
            Append(~cs, ci); Append(~ms, mi); Append(~rs, ri);
        end for;

        tt := Cputime();
        srec := KnownPlaintextNoiseAttack(g, cs, ms, rs);
        total +:= Cputime(tt);

        if srec eq 0 then
            fails +:= 1;
        elif srec eq s then
            correct +:= 1;
        end if;
    end for;

    emp_fail  := RealField(6) ! fails / trials;
    pred_fail := PredFail(p, n);
    printf "k = %o  p = %6o : avg %8o s   fails %o/%o   correct %o/%o   "
         * "fail-rate emp %.4o  pred %.4o\n",
        k, p, total / trials, fails, trials, correct, trials,
        emp_fail, pred_fail;
end for;

// Task 3.d
// AI helped with the syntax (multivariate polynomial ring setup, Variety usage)
// and with the testcode generation for timing and uniqueness checks.

GrobnerBasisAttack := function(g, c, m, alpha, beta)
    R  := Parent(g);    // F_p[z]
    Fp := BaseRing(R);  // F_p
    n  := Degree(g);
    d  := n div 2;      // floor(n/2): f = z^n + h with deg h <= d

    // One unknown per coefficient of s, h and r:
    ns := n; nh := d + 1; nr := n;
    N  := ns + nh + nr; // total number of unknowns
    P  := PolynomialRing(Fp, N);

    // Give the N variables readable names (s0.., h0.., r0..); purely
    // cosmetic, helps when printing/debugging the equation system.
    AssignNames(~P, [ "s" cat IntegerToString(i) : i in [0..ns-1] ]
                  cat [ "h" cat IntegerToString(i) : i in [0..nh-1] ]
                  cat [ "r" cat IntegerToString(i) : i in [0..nr-1] ]);
    sv := [ P.(i)        : i in [1 .. ns] ];   // s-coefficients
    hv := [ P.(ns + i)   : i in [1 .. nh] ];   // h-coefficients
    rv := [ P.(ns+nh+i)  : i in [1 .. nr] ];   // r-coefficients

    // PY = P[Y]: polynomials in Y whose coefficients are unknowns from P.
    PY<Y> := PolynomialRing(P);
    gP := PY ! [ P ! Fp ! ci : ci in Eltseq(g) ];

    redmodg := function(poly)
        return poly mod gP;
    end function;

    // Symbolic polynomials with unknown coefficients:
    sY := &+[ sv[i+1] * Y^i : i in [0 .. ns-1] ];        // s(Y) = phi(x)
    fY := Y^n + &+[ hv[k+1] * Y^k : k in [0 .. nh-1] ];  // f(Y) = z^n + h

    mc := [ P ! Fp ! ci : ci in Eltseq(m) ];     // message coeffs (known)
    while #mc lt n do Append(~mc, P ! 0); end while;
    w  := [ mc[j] + 2*rv[j] : j in [1 .. n] ];   // coeffs of (m + 2r)

    // Equation set (A): the ciphertext is phi(m+2r), i.e. evaluate the
    // unknown polynomial (m+2r) at s(y) and reduce mod g. Horner's rule
    // builds w(s(y)) without ever forming high-degree intermediates.
    sYr := redmodg(sY);
    acc := PY ! 0;
    for j := n to 1 by -1 do
        acc := redmodg(acc * sYr) + (PY ! w[j]);
    end for;
    cY := PY ! [ P ! Fp ! ci : ci in Eltseq(c) ];   // ciphertext coefficients (known)

    eqs := [];
    // (A) require  (m+2r)(s(y)) - c(y) = 0  in the field: each coefficient
    //     of the difference must vanish -> n equations in the unknowns.
    diffA := acc - cY;
    for co in Coefficients(diffA) do Append(~eqs, co); end for;

    // Equation set (B): s(y) must be a root of f in the field, i.e.
    // f(s(y)) = 0 mod g. Precompute s(y)^0..s(y)^n (reduced) once, then
    // assemble f(s(y)) = s(y)^n + sum_k h_k s(y)^k.
    sPow := redmodg(PY ! 1);
    pows := [ sPow ];
    for e := 1 to n do
        sPow := redmodg(sPow * sYr);
        Append(~pows, sPow);
    end for;
    fAtS := pows[n+1];                             // s(y)^n  (reduced)
    for k := 0 to nh-1 do
        fAtS := fAtS + hv[k+1] * pows[k+1];        // + h_k * s(y)^k
    end for;
    fAtS := redmodg(fAtS);

    // (B) each coefficient of f(s(y)) must vanish -> another n equations.
    for co in Coefficients(fAtS) do Append(~eqs, co); end for;

    // Equation set (C): Arora-Ge smallness. r_j, h_k are in {-1,0,1}
    // exactly when v^3 - v = v(v-1)(v+1) = 0.
    for j := 1 to nr do Append(~eqs, rv[j]^3 - rv[j]); end for;
    for k := 1 to nh do Append(~eqs, hv[k]^3 - hv[k]); end for;

    // Solve the (now finite) system; V is the list of solution points.
    I := ideal< P | eqs >;
    V := Variety(I);

    if #V eq 0 then
        return R ! 0, R ! 0;       // attack failed: no solution
    end if;

    // Read the first solution point back into polynomials s(z), f(z).
    pt := V[1];
    scoef := [ pt[i]        : i in [1 .. ns] ];   // s-block of the point
    hcoef := [ pt[ns + i]   : i in [1 .. nh] ];   // h-block of the point
    sZ := R ! scoef;
    // Rebuild f = z^n + h(z) (pad h with zeros up to degree n-1).
    fZ := R ! ([ Fp ! hc : hc in hcoef ] cat [ Fp ! 0 : i in [nh .. n-1] ]);
    fZ := fZ + R.1^n;
    return sZ, fZ, #V;             // also return #solutions for the report
end function;

// Tests
print "=== Task 3.d : p = 2^16+7, alpha=-1, beta=1, n = 2..4 ===";
print "trials = 10 per n";
p := 2^16 + 7; alpha := -1; beta := 1; trials := 10;

for n in [2, 3, 4] do
    total    := 0.0;
    sumsol   := 0;
    validcnt := 0;
    exactcnt := 0;

    for it in [1..trials] do
        f, g, s, t := FFIPKeyGen(p, n, alpha, beta);
        R := Parent(g);
        Fp := BaseRing(R);

        mb := [ Random(0, 1) : i in [1..n] ];
        mstr := &cat[ IntegerToString(b) : b in mb ];
        cpoly := FFIPEncrypt(mstr, g, s, alpha, beta);
        mpoly := R ! [ Fp ! b : b in mb ];

        tt := Cputime();
        srec, frec, nsol := GrobnerBasisAttack(g, cpoly, mpoly, alpha, beta);
        total +:= Cputime(tt);
        sumsol +:= nsol;

        // "valid" = f irreducible of degree n, and s a genuine root of f in Y.
        okf := (Degree(frec) eq n) and IsIrreducible(frec);
        Y := ext< Fp | g >;
        sY := Evaluate(ChangeRing(srec, Y), Y.1);
        if okf and (Evaluate(ChangeRing(frec, Y), sY) eq 0) then
            validcnt +:= 1;
        end if;
        // "exact" = the returned pair is the actual secret key used.
        if (frec eq f) and (srec eq s) then
            exactcnt +:= 1;
        end if;
    end for;

    printf "n = %o : avg %8o s   avg #solutions = %o   "
         * "valid %o/%o   equals secret %o/%o\n",
        n, total / trials, RealField(4) ! sumsol / trials,
        validcnt, trials, exactcnt, trials;
end for;

// -----------------------------------------------
// Task 4
// -----------------------------------------------
// AI helped with the syntax (trace-matrix assembly, mapping coordinate
// vectors back to field elements) and with the verification testcode.

// Task 4.b
DualBasis := function(basis)
    F  := Universe(basis);  // F_{p^n}
    Fp := PrimeField(F);
    n  := Degree(F, Fp);
    th := F.1;  // power-basis generator of F over F_p

    // powers th^0 .. th^(n-1)
    thp := [ th^k : k in [0 .. n-1] ];

    // trace matrix T : T[i][k] = Tr(w_i * th^(k-1))  (over F_p)
    T := Matrix(Fp, n, n,
        [ [ Fp ! Trace(basis[i] * thp[k], Fp) : k in [1..n] ] : i in [1..n] ]);

    U := T^(-1);    // columns = dual-vector coordinates

    // rebuild w^_j = sum_k U[k][j] * th^(k-1) as a field element
    dual := [ &+[ (F ! U[k][j]) * thp[k] : k in [1..n] ] : j in [1..n] ];
    return dual;
end function;

// Tests
print "=== Task 4.b : DualBasis verification ===";

// Check Tr(w_i * w^_j) = delta_ij for several fields / bases.
CheckDual := function(F, basis)
    n  := #basis;
    Fp := PrimeField(F);
    dual := DualBasis(basis);
    ok := true;
    for i in [1..n] do
        for j in [1..n] do
            want := (i eq j) select Fp ! 1 else Fp ! 0;
            if Trace(basis[i] * dual[j], Fp) ne want then
                ok := false;
            end if;
        end for;
    end for;
    return ok;
end function;

for tup in [ <2, 8>, <3, 4>, <13, 5>, <2^16 + 7, 6> ] do
    p := tup[1]; n := tup[2];
    F := GF(p, n);
    th := F.1;

    // power basis {1, th, .., th^(n-1)}
    powb := [ th^k : k in [0..n-1] ];
    // a random basis (retry until the n elements are independent)
    repeat
        rb := [ Random(F) : i in [1..n] ];
    until IsIndependent([ Vector(Fp, Eltseq(b)) : b in rb ])
        where Fp is PrimeField(F);

    okp := CheckDual(F, powb);
    okr := CheckDual(F, rb);
    printf "p = %6o  n = %o : power-basis %o   random-basis %o\n",
        p, n, okp, okr;
end for;

// Task 4.c
// AI helped with the syntax (multivariate ring / Variety setup, recovering
// the minimal polynomial from a basis) and with the testcode generation.

// Task 4.d
SearchFFIAttack := function(samples, alpha, beta)
    Y  := Universe(samples);
    Fp := PrimeField(Y);
    n  := Degree(Y, Fp);
    N  := #samples;

    // Unknown dual image C(y) = sum_{j=0}^{n-1} d_j y^j ; one var per d_j.
    P  := PolynomialRing(Fp, n);
    yb := [ (Y.1)^j : j in [0 .. n-1] ];    // power basis of Y

    // For sample A, Tr(A * C) = sum_j ( Tr(A * y^j) ) d_j : a known linear
    // form in the d_j
    linform := function(A)
        return &+[ (P ! (Fp ! Trace(A * yb[j+1], Fp))) * P.(j+1)
                   : j in [0 .. n-1] ];
    end function;

    // prod_{v=alpha}^{beta} (L - v) = 0.
    eqs := [];
    for A in samples do
        L := linform(A);
        Append(~eqs, &*[ L - (P ! v) : v in [alpha .. beta] ]);
    end for;

    I := ideal< P | eqs >;
    V := Variety(I);    // solutions for (d_0,..,d_{n-1})

    // Each solution point -> the field element C = sum d_j y^j in Y.
    Cs := [ &+[ (Y ! pt[j+1]) * yb[j+1] : j in [0 .. n-1] ] : pt in V ];

    // Multiple solutions, keep one per independent dual image C
    basisC := [];
    coords := [];
    for C in Cs do
        if C eq 0 then continue; end if;
        v := Vector(Fp, Eltseq(C));
        if IsIndependent(coords cat [v]) then
            Append(~basisC, C);
            Append(~coords, v);
        end if;
        if #basisC eq n then break; end if;
    end for;

    if #basisC ne n then
        // not enough independent dual images recovered, attack failed
        return PolynomialRing(Fp) ! 0, #V;
    end if;

    powS := DualBasis(basisC);

    // s = phi(x) is a root of f; its minimal polynomial over F_p is f(z).
    // Try each recovered element: the genuine s has an irreducible minimal
    // polynomial of degree n with the special shape z^n + h, deg h <= n/2,
    // coefficients in {-1,0,1}.
    Rz<z> := PolynomialRing(Fp);
    d := n div 2;
    for s in powS do
        mp := MinimalPolynomial(s, Fp);
        if Degree(mp) ne n or not IsIrreducible(mp) then continue; end if;
        cf := Coefficients(mp);                       // c0..c_n, monic
        // shape check: deg h <= d and h-coeffs in {-1,0,1}
        ok := true;
        for k in [d + 2 .. n] do
            if k le n and cf[k] ne 0 then ok := false; end if;
        end for;
        if ok then
            for k in [1 .. d + 1] do
                v := Integers() ! cf[k];
                if v gt (#Fp - 1) div 2 then v := v - #Fp; end if;
                if Abs(v) gt 1 then ok := false; end if;
            end for;
        end if;
        if ok then
            return Rz ! mp, #V;
        end if;
    end for;

    return Rz ! 0, #V;        // no solution had a valid-key shape
end function;

// Tests
print "=== Task 4.d : p = 2^16+7, alpha=-1, beta=1, n = 4,8,16 ===";
p := 2^16 + 7; alpha := -1; beta := 1;

for n in [4, 8, 16] do
    f, g, s, t := FFIPKeyGen(p, n, alpha, beta);
    R  := Parent(g);
    Fp := BaseRing(R);
    Y  := ext< Fp | g >;
    sy := Evaluate(ChangeRing(s, Y), Y.1);     // phi(x) = s(y) in Y

    D := beta - alpha + 1;
    N := Binomial(n + D - 1, D);

    samples := [];
    for k in [1..N] do
        ab := SampleChi(n, alpha, beta);
        ax := R ! [ Fp ! c : c in ab ];
        Ak := Evaluate(ChangeRing(ax, Y), sy);
        Append(~samples, Ak);
    end for;

    tt := Cputime();
    frec, nsol := SearchFFIAttack(samples, alpha, beta);
    el := Cputime(tt);

    okeq := (frec ne 0) and (frec eq f);
    printf "n = %2o : N = %5o   time %8o s   #solutions = %o   "
         * "f recovered = %o   equals secret = %o\n",
        n, N, el, nsol, frec ne 0, okeq;
end for;
