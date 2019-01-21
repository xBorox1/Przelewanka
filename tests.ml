#load "przelewanka.cmo";;
open Przelewanka;;

let c = [||];;
assert(przelewanka c = 0);;
let c = [|(0, 0)|];;
assert(przelewanka c = 0);;
let c = [|(1, 0) ; (2, 0) ; (5, 0)|];;
assert(przelewanka c = 0);;
let c = [|(100, 0) ; (20077, 0) ; (567868, 0)|];;
assert(przelewanka c = 0);;
let c = [|(1, 1) ; (2, 2) ; (5, 0)|];;
assert(przelewanka c = 2);;
let c = [|(1, 0) ; (2, 0) ; (5, 5)|];;
assert(przelewanka c = 1);;
let c = [|(2, 1) ; (2, 1) ; (5, 1)|];;
assert(przelewanka c = -1);;
let c = [|(12, 1) ; (6, 3) ; (10, 5)|];;
assert(przelewanka c = -1);;
let c = [|(12, 12) ; (6, 3) ; (10, 5)|];;
assert(przelewanka c = -1);;
let c = [|(12, 0) ; (6, 0) ; (10, 6)|];;
assert(przelewanka c = 2);;
let c = [|(12, 12) ; (6, 0) ; (10, 1)|];;
assert(przelewanka c = -1);;
let c = [|(12, 1) ; (6, 3) ; (10, 5)|];;
assert(przelewanka c = -1);;
let c = [|(2, 1) ; (1, 0)|];;
assert(przelewanka c = 2);;
let c = [|(2, 1) ; (1, 1)|];;
assert(przelewanka c = 2);;
let c = [|(2, 2) ; (1, 1)|];;
assert(przelewanka c = 2);;
let c = [|(2, 2) ; (1, 0)|];;
assert(przelewanka c = 1);;
let c = [|(2, 1) ; (2, 1) ; (1, 0)|];;
assert(przelewanka c = 3);;

let c = [|(3,2);(3,3);(1,0);(12,1)|];;
assert ( przelewanka c = 4 );;
let c = [|(1,1);(100,99)|];;
assert ( przelewanka c = 2 );;
let c = [|(3,3);(5,4);(5,2);(6,1)|];;
assert (przelewanka c = 6);;
let c = [|(100,3);(2,1);(1,0);(6,1)|];;
assert (przelewanka c = 7);;
let c = [|(3,3);(5,5);(5,5);(6,6)|];;
assert (przelewanka c = 4);;
let c = [|(19,3);(1,1);(2,2)|];;
assert (przelewanka c = 6);;
let c = [|(14,3);(3,1);(3,0)|];;
assert (przelewanka c = 13);;
let c = [|(3,3);(4,0);(1,1);(6,6)|];;
assert (przelewanka c = 3);;
let c = [|(46,20);(23,10);(13,5);(5,0)|];;
assert (przelewanka c = 10);;
let c = [|(18,3);(3,1);(2,2)|];;
assert (przelewanka c = 4);;
let c = [|(14,3);(5,1)|];;
assert (przelewanka c = -1);;
let c = [|(14,3);(5,1);(5,0)|];;
assert (przelewanka c = 16);;


