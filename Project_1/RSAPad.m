// Author: Gust De Wit, r0948039

// For this file, AI was used to help with syntax and structuring, but the core logic and implementation of the RSA padding attack were written by me.
RSAPadBreak := function(c, N, e)
    Zx<x> := PolynomialRing(Integers());
    t := 3;
    M := (2^256 - 1) * 2^(256 * t);
    S := 0;
    for i in [0..t-1] do
        S +:= 2^(256 * i);
    end for;
    ZN := IntegerRing(N);
    Si := Integers() ! (ZN ! S)^(-1);
    A := Integers() ! ((ZN ! M) * (ZN ! Si));
    C := Integers() ! ((ZN ! c) * (ZN ! Si)^e);
    f := (x + A)^e - C;
    roots := SmallRoots(f, N, 2^256);
    if #roots eq 0 then error "No roots found"; end if;
    v := roots[1];
    k := v mod 2^128;
    return k;
end function;

load "keys.m";
ka := RSAPadBreak(c2a, n2, e2a);
printf "k_a = %o\n", ka;