// Author: Gust De Wit (r0948039)
// AI helped with the syntax (multivariate ring / Variety setup, recovering
// the minimal polynomial from a basis) and with the testcode generation.

// Task 4.d
sfa_caller_load_only := assigned load_only;
load_only := true;
load "dual_basis.m";
load "ffip.m";
if not sfa_caller_load_only then
    delete load_only;
end if;

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

// Tests (run directly: magma search_ffi_attack.m)
if not assigned load_only then

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

quit;

end if;
