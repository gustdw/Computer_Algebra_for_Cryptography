k := 5;
Z26 := Integers(26);

StringToHill := function(s)
    is_all_caps, _, _ := Regexp("^[A-Z]+$", s);
    if not is_all_caps then
        error "Input contains non-capital letters:", s;
    end if;
    chars := Eltseq(s);
    a_val := StringToCode("A");

    return [Z26 ! (StringToCode(c) - a_val ) : c in chars];
end function;

HillToString := function(a)
    A_val := StringToCode("A");
    return &cat[CodeToString(Integers() ! x + A_val) : x in a];
end function;

HillKeyGen := function(s)
    if #s ne k^2 then
        error "Input is not of the correct length";
    end if;
    hillSeq := StringToHill(s);
    mtx := Matrix(Z26, k, k, hillSeq);

    if not IsInvertible(mtx) then
        error "Key matrix is not invertible over Z26. Choose a different key.";
    end if;

    return mtx;
end function;

HillEncrypt := function(s, A)
    hillSeq := StringToHill(s);
    pad_amm := #hillSeq mod k;
    for _ in [0..pad_amm] do
        Append(~hillSeq, 0);
    end for;
    print hillSeq;

    ciphertext := [];
    for i in [0..#hillSeq div k -1] do
        l := hillSeq[i*k+1..i*k+k];
        v := Transpose(Matrix(Vector(Z26, l)));
        ctc := A*v;
        ciphertext cat:= Eltseq(ctc);
    end for;
    return HillToString(ciphertext);
end function;

HillDecrypt := function(s, A)
    return HillEncrypt(s, A^-1);
end function;

A := HillKeyGen("ABXZ");
ct := HillEncrypt("COMPUTERALGEBRA", A);
print HillDecrypt(ct, A);