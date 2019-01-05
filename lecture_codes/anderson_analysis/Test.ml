let v1 = O
let v2 = S v1
let v3 = S v2

let rec mkProg = function
    [] -> Nil
  | h :: t -> Cons (h, mkProg t)

let myProg = mkProg [Allocate v1;
		     Copy (v2, v1);
		     Write (v1, v3);
		     Read (v2, v1);
		     Allocate v3;
		     Goto (S O)]

