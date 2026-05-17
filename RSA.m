clear;

RSAKeyGen := function(b)
    p := NextPrime(Random(2^(b div 2 - 1), 2^(b div 2)) : Proof := false);
    q := NextPrime(Random(2^(b div 2 - 1), 2^(b div 2)) : Proof := false);
    N := p*q;
    euler_phi := (p-1)*(q-1);

    repeat
        e := Random(2, euler_phi-1);
    until GCD(e, euler_phi) eq 1;

    _, d, _ := XGCD(e, euler_phi);
    d := d mod euler_phi;

    return N, e, d;
end function;

RSAEncrypt := function(m, N, e)
    ZN := Integers(N);
    c := (ZN ! m)^e;
    return Integers() ! c;
end function;

FindPQ := function(N, e, d)
    k := e*d - 1;

    // Write k = 2^s * t with t odd
    s := 0;
    t := k;
    while t mod 2 eq 0 do
        t := t div 2;
        s := s + 1;
    end while;

    // Try random a until we factor N
    ZN := Integers(N);
    repeat
        a := Random(2, N-2);
        x := (ZN ! a)^t;

        // Compute sequence x, x^2, x^4, ... looking for non-trivial sqrt of 1
        prev := x;
        for i := 1 to s do
            curr := prev^2;
            if curr eq 1 and prev ne 1 and prev ne ZN ! (N-1) then
                // prev is a non-trivial square root of 1
                p := GCD(Integers() ! prev - 1, N);
                q := N div p;
                return p, q;
            end if;
            prev := curr;
        end for;
    until false;
end function;

RSADecryptCRT := function(c, N, e, d)
    p, q := FindPQ(N, e, d);

    dp := d mod (p-1);
    dq := d mod (q-1);

    mp := (Integers(p) ! c)^dp;
    mq := (Integers(q) ! c)^dq;

    m := CRT([Integers() ! mp, Integers() ! mq], [p, q]);
    return m;
end function;

// Test
N, e, d := RSAKeyGen(1024);
m := Random(2, N-1);
c := RSAEncrypt(m, N, e);
print RSADecryptCRT(c, N, e, d) eq m;  // should print true