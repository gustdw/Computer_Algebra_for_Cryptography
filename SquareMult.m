SquareMult := function(a, n)
    bits := Reverse(IntegerToSequence(n, 2));
    b := Parent(a) ! 1;

    for bit in bits do
        b := b^2;
        if bit eq 1 then
            b := b*a;
        end if;
    end for;
    return b;
end function;

// Test
Fp := GF(31);
Fpx<x> := PolynomialRing(Fp);
f := RandomIrreduciblePolynomial(Fp, 3);
Fp3<w> := ext<Fp | f>;
SetPowerPrinting(Fp3, false);

a := Random(Fp3);
n := Random(1, 10000);

print "a =", a;
print "n =", n;
print "SquareMult:", SquareMult(a, n);
print "Magma ^:   ", a^n;
print "Equal:", SquareMult(a, n) eq a^n;  // should print true