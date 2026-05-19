// Remember whether a caller asked us to stay quiet (load_only already set).
// We must set load_only for field_iso.m's own guard, then restore the
// caller's intent so that running ffip.m directly still executes its tests.
caller_load_only := assigned load_only;
load_only := true;
load "field_iso.m";
if not caller_load_only then
    delete load_only;
end if;

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
//   use elsewhere :  load_only := true;  load "ffip.m";
//   run directly  :  magma ffip.m
if not assigned load_only then

p := 13; n := 64; alpha := -1; beta := 1;
f, g, s, t := FFIPKeyGen(p, n, alpha, beta);

m := "1001000110011000011110111000101001011101101100000110010011111001";
printf "message length = %o (expected %o)\n", #m, n;

c  := FFIPEncrypt(m, g, s, alpha, beta);
md := FFIPDecrypt(c, f, t);

printf "decrypted == original : %o\n", md eq m;

quit;

end if;
