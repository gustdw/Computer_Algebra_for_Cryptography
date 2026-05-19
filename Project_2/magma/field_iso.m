// Author: Gust De Wit (r0948039)
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
if not assigned load_only then

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

quit;

end if;
