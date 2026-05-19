// Author: Gust De Wit (r0948039)
// AI helped with the syntax and how to efficiently perform certain steps
// (e.g. assembling the coefficient matrices). Furthermore, AI did the
// testcode generation for timing and counting failures.

load_only := true;
load "ffip.m";

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

// Kahn-Komlos asymptotic failure probability 1 - prod_{i>=1}(1 - p^{-i}),
// truncated at i = n (remaining terms change the product by < p^{-(n+1)}).
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

quit;
