// Author: Gust De Wit, r0948039
// For this file, AI was used to help with syntax and structuring, but the core logic and implementation of the Pollard's p-1 and p^2-1 algorithms were written by me.

MultiplyTwoElements := function(x, y, a, N)
    alpha1 := x[1];
    beta1 := x[2];
    alpha2 := y[1];
    beta2 := y[2];

    alpha := (alpha1*alpha2 - a*beta1*beta2) mod N;
    beta := (alpha1*beta2 + beta1*alpha2) mod N;

    return [alpha, beta];
end function;

SquareMult := function(element, k, a, N)
    bits := Reverse(IntegerToSequence(k, 2));

    b := [1, 0]; // identity element in F_{p^2}

    for bit in bits do
        b := MultiplyTwoElements(b, b, a, N);
        if bit eq 1 then
            b := MultiplyTwoElements(b, element, a, N);
        end if;
    end for;
    return b;
end function;

PollardPOne := function(N, B)
    repeat
        a := Random(2, N-2);
        alpha := Random(1, N-1);
        beta := Random(1, N-1);
        
        element := [alpha, beta];
        for p in PrimesUpTo(B) do
            e := Floor(Log(p, B)); // largest exponent such that p^e <= B
            element := SquareMult(element, p^e, a, N);
            check := GCD(element[2], N);
            if check gt 1 and check lt N then
                return check;
            elif check eq N then
                print "Check eq N, trying a new a";
                break;
            end if;
        end for;
        print "Completed without finding a factor, trying a new a";
    until false;
end function;

MultiplyTwoSquareElements := function(x, y, a, b, N)
    alpha1 := x[1];
    beta1 := x[2];
    gamma1 := x[3];
    alpha2 := y[1];
    beta2 := y[2];
    gamma2 := y[3];

    alpha := (alpha1*alpha2 - b*beta1*gamma2 - b*gamma1*beta2) mod N;
    beta := (alpha1*beta2 + beta1*alpha2 - a*beta1*gamma2 - a*gamma1*beta2 - b*gamma1*gamma2) mod N;
    gamma := (alpha1*gamma2 + gamma1*alpha2 + beta1*beta2 - a*gamma1*gamma2) mod N;
    return [alpha, beta, gamma];
end function;

SquareMultSquare := function(element, k, a, b, N)
    bits := Reverse(IntegerToSequence(k, 2));

    result := [1, 0, 0]; // identity element in F_{p^2}

    for bit in bits do
        result := MultiplyTwoSquareElements(result, result, a, b, N);
        if bit eq 1 then
            result := MultiplyTwoSquareElements(result, element, a, b, N);
        end if;
    end for;
    return result;
end function;

PollardPsquaredPOne := function(N, B)
    repeat
        a := Random(2, N-2);
        b := Random(2, N-2);
        alpha := Random(1, N-1);
        beta := Random(1, N-1);
        gamma := Random(1, N-1);
        element := [alpha, beta, gamma];
        for p in PrimesUpTo(B) do
            e := Floor(Log(p, B));
            element := SquareMultSquare(element, p^e, a, b, N);
            check := GCD(GCD(element[2], element[3]), N);
            if check gt 1 and check lt N then
                return check;
            elif check eq N then
                print "Check eq N, trying a new a and b";
                break;
            end if;
        end for;
        print "Completed without finding a factor, trying a new a and b";
    until false;
end function;

load "keys.m";
B := 1000000;
// print PollardPOne(n1a, B);
// print PollardPOne(143, 10);
// print PollardPOne(30029*30047, 13);
print PollardPsquaredPOne(n1b, B);