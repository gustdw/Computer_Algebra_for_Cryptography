// Author: Gust De Wit, r0948039
// For this file, AI was used to help with syntax and structuring, but the core logic and implementation of the order-to-factors were written by me.
OrderToFactors := function(N, a, r)
    factors := [];
    stack := [<N, r>];
    exp := r;
    while #stack gt 0 do
        pair := stack[#stack];
        n := pair[1];
        exp := pair[2];
        Prune(~stack);

        if n eq 1 then
            continue; // No factors to find
        elif IsPrime(n: Proof := false) then
            Append(~factors, n);
            continue;
        end if;

        found := false;
        l := 2;
        while l lt 10^16 do
            while exp mod l eq 0 do // l divides exp, factor out l
                test_exp := exp div l;
                g := GCD(Modexp(a, test_exp, n) - 1, n);
                if g ne 1 and g ne n then
                    Append(~stack, <g, test_exp>);
                    Append(~stack, <n div g, test_exp>);
                    found := true;
                    break;
                elif g eq n then
                    exp := test_exp;
                else
                    break; // Can't factor out l, move on to the next prime
                end if;
            end while;
            if found then break; end if;
            l := NextPrime(l);
        end while;

        if not found then
            error "Failed to factor " cat IntegerToString(n);
        end if;    
    end while;
    return factors;
end function;

load "keys.m";
printf "n3a factors: %o\n", OrderToFactors(n3a, a3a, r3a);
printf "n3b factors: %o\n", OrderToFactors(n3b, a3b, r3b);
printf "n3d factors: %o\n", OrderToFactors(n3d, a3d, r3d);
printf "n3c factors: %o\n", OrderToFactors(n3c, a3c, r3c);
