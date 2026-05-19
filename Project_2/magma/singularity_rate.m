// Author: Gust De Wit (r0948039)
// AI helped with the syntax and the testcode generation.
//
// Direct empirical test of the failure probability of the Task 3.b attack.
//
// The attack fails exactly when the matrix W (columns w_i = m_i + 2 r_i,
// entries i.i.d. uniform on the 6-element set {-2,-1,0,1,2,3} subset Fp)
// is singular over Fp. This script estimates Pr(W singular) directly by
// sampling many such W and counting det(W) = 0, WITHOUT generating any
// field isomorphism (so it is fast even for large n).
//
// It compares the empirical rate against the Kahn-Komlos asymptotic limit
//     Pr(W singular) -> 1 - prod_{i>=1} (1 - p^{-i})   as n -> infinity,
// approximated by the finite product prod_{i=1}^{n} (1 - p^{-i}).
//
// Run directly:  magma singularity_rate.m

// limiting non-singular probability prod_{i>=1}(1 - p^{-i}),
// truncated at i = n (further terms change it by < p^{-(n+1)})
PredFail := function(p, n)
    prod := 1.0;
    for i in [1..n] do
        prod := prod * (1.0 - 1.0 / (p ^ i));
    end for;
    return 1.0 - prod;
end function;

// build one W: n columns, each entry uniform on {-2,-1,0,1,2,3} = m + 2r
// with m in {0,1}, r in {-1,0,1}; return true iff W is singular over Fp
SampleSingular := function(Fp, n)
    cols := [ ];
    for c in [1..n] do
        col := [ Fp ! (Random(0,1) + 2*Random(-1,1)) : i in [1..n] ];
        Append(~cols, col);
    end for;
    W := Matrix(Fp, cols);   // rows vs columns irrelevant for singularity
    return Determinant(W) eq 0;
end function;

// -------------------------------------------------------------------------

print "=== direct singularity-rate test : entries uniform on {-2..3} ===";
print "trials = 2000 per cell";
trials := 2000;

ns := [32, 64, 128, 256];
ks := [1, 2, 3, 4, 5, 6, 7, 8];   // p = NextPrime(2^k)

for k in ks do
    p  := NextPrime(2^k);
    Fp := GF(p);
    line := Sprintf("p = %4o |", p);
    for n in ns do
        sing := 0;
        for it in [1..trials] do
            if SampleSingular(Fp, n) then sing +:= 1; end if;
        end for;
        emp  := RealField(6) ! sing / trials;
        pred := PredFail(p, n);
        line := line cat Sprintf("  n=%o: emp %.4o pred %.4o |",
                                 n, emp, pred);
    end for;
    print line;
end for;

quit;
