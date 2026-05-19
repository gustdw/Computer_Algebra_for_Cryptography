// Author: Gust De Wit (r0948039)
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
if not assigned load_only then

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

quit;

end if;
