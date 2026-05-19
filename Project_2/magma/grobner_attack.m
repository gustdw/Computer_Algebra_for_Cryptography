// Author: Gust De Wit (r0948039)
// AI helped with the syntax (multivariate polynomial ring setup, Variety usage) and with the testcode generation for timing and uniqueness checks.


// Task 3.d
load_only := true;
load "ffip.m";

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

// Tests (run directly: magma grobner_attack.m)
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

quit;
