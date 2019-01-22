(* Autor : Michał Borowski *)
(* Code Review : Wojciech Kłopotek *)

(***************************)
(*     OPERACJE OGÓLNE     *)
(***************************)

(* Sprawdza czy lista jest pusta. *)
let pusta lista =
        match lista with
        | [] -> true
        | (_ :: _) -> false

(* Największy wspólny dzielnik dwóch liczb. *)
let rec nwd x y =
        if x = 0 then y
        else if y = 0 then x
        else nwd y (x mod y)

(* Największy wspólny dzielnik liczb znajdujących się w danej tablicy. *)
let nwd_tab tab =
        let nwdt = Array.fold_left (fun x acc -> nwd acc x) 0 tab
        in if nwdt = 0 then 1
        else nwdt

(* Sprawdza czy liczby w tablicy są podzielne przez daną liczbę d. *)
let czy_podzielne tab d =
        Array.fold_left (fun acc y -> (y mod d = 0) && acc) true tab

let usun_zera tab =
        Array.fold_left (fun acc (x, y) -> if x = 0 then acc else Array.append acc [|(x, y)|]) [||] tab

(* Dzieli każdą liczbę w tablicy przez daną liczbę d. *)
let podziel tab d =
        Array.map (fun x -> x / d) tab

let iloczyny_prefiksowe tab =
        Array.fold_left (fun l x -> ((List.hd l) * (x + 1))::l ) [1] tab |> List.rev |> Array.of_list

(***************************)
(*  FUNKCJE PRZYGOTOWUJĄCE *)
(***************************)

let ile_pustych tab =
        Array.fold_left (fun acc (_, y) -> if y = 0 then (acc + 1) else acc) 0 tab

let ile_pelnych tab =
        Array.fold_left (fun acc (x, y) -> if y = x then (acc + 1) else acc) 0 tab

(* Sprawdza czy warunki konieczne są spełnione. *)
let warunki_konieczne tab =
        if ile_pustych tab = 0 && ile_pelnych tab = 0 then false
        else
                let pojemnosci = Array.map fst tab
                in let stan_koncowy = Array.map snd tab
                in let nwdt = nwd_tab pojemnosci
                in czy_podzielne stan_koncowy nwdt

(* Zwraca pojemności i stan końcowy szklanek podzielone przez największy
 * wspólny dzielnik pojemności szklanek. 
 * Zakładamy, że te liczby będą przez to podzielne. *)
let normalizuj tab =
        let pojemnosci = Array.map fst tab
        in let stan_koncowy = Array.map snd tab
        in let nwdt = nwd_tab pojemnosci
        in ((podziel pojemnosci nwdt), (podziel stan_koncowy nwdt))

(* Sprawdza czy wszystkie szklanki w stanie końcowym są puste lub pełne. 
 * Jeśli tak zwraca liczbę pełnych, jeśli nie zwraca (-1). *)
let czy_wszystkie_puste_lub_pelne tab =
        let il1 = ile_pustych tab
        in let il2 = ile_pelnych tab
        in if il1 + il2 = Array.length tab then il2
        else (-1)

(***************************)
(*     FUNKCJE GRAFOWE     *)
(***************************)

(* Wytwarza stan w postaci tablicy na podstawie danej liczby. 
 * Liczba jednoznacznie opisuje stan następująco :
 * jest to suma wyrażeń stan.(i) * iloczyny.(i), gdzie
 * stan to pojemności szklanek w danym momencie, a iloczyny
 * to iloczyny prefiksowe pojemności szklanek. *)
let stan_z_liczby n iloczyny =
        let len = Array.length iloczyny
        in let stan = Array.make (len - 1) 0
        in let l = ref n
        in begin
                for i = (len - 2) downto 0 do
                        stan.(i) <- (!l) / iloczyny.(i);
                        l := (!l) - stan.(i) * iloczyny.(i);
                done;
        end;
        stan

(* Zwraca listę stanów do których można dotrzeć z danego stanu w jeden operacji. *)        
let kolejne_stany stan numer iloczyny pojemnosci =
        let l = ref []
        in let len = (Array.length stan) - 1
        in begin
               for i = 0 to len do
                       l := (numer - stan.(i) * iloczyny.(i))::(!l);
               done;
               for i = 0 to len do
                       l := (numer + (pojemnosci.(i) - stan.(i)) * iloczyny.(i))::(!l);
               done;
               for i = 0 to len do
                       for j = 0 to len do
                               let roznica = pojemnosci.(j) - stan.(j)
                               in 
                                    if roznica < stan.(i) then
                                       l := (numer + roznica * iloczyny.(j) - roznica * iloczyny.(i))::(!l)
                                    else
                                       l := (numer + stan.(i) * iloczyny.(j) - stan.(i) * iloczyny.(i))::(!l);
                       done;
               done;
         end;
         !l

(* Sprawdza czy stan był już odwiedzony, jeśli nie to aktualizuje odległość 
 * i listę stanów do odwiedzenia. *)
let dodaj_odleglosc x odl dl l =
        let zmiana = (odl.(x) = -1) in
        if zmiana then odl.(x) <- dl;
        if zmiana then (odl, (x :: l))
        else (odl, l)
		
(* BFS, kończący się w momencie odwiedzenia stanu końcowego lub przejścia wszystkich
 * możliwych do odwiedzenia stanów. 
 * Przyjmowane argumenty to kolejno : lista wierzchołków z aktualnie przetwarzanego bloku,
 * lista wierzchołków z kolejnego bloku, odległość bloku od źródła, iloczyny prefiksowe
 * pojemności szklanek, pojemności szklanek i stan końcowy. *)
let rec bfs l1 l2 dl odl iloczyny pojemnosci koniec =
        if pusta l1 && pusta l2 then (-1)
        else match l1 with
        | [] -> bfs l2 l1 (dl + 1) odl iloczyny pojemnosci koniec
        | (h :: t) -> let stan = stan_z_liczby h iloczyny
                      in let stany = kolejne_stany stan h iloczyny pojemnosci
                      in let (odl2, l3) = List.fold_left (fun (od, l) x -> dodaj_odleglosc x od dl l) (odl, l2) stany
                      in if (odl2.(koniec) <> (-1)) then odl2.(koniec)
                      else bfs t l3 dl odl2 iloczyny pojemnosci koniec
        

let przelewanka tab =
        let tab = usun_zera tab
        in if tab = [||] then 0
        else if not (warunki_konieczne tab) then (-1)
        else let cz = czy_wszystkie_puste_lub_pelne tab
        in if cz <> (-1) then cz
        else
                let (pojemnosci, stan_koncowy) = normalizuj tab
                in let iloczyny = iloczyny_prefiksowe pojemnosci
                in let koniec = Array.fold_left (fun (kon, i) x -> (kon + x * iloczyny.(i), i + 1)) (0, 0) stan_koncowy |> fst
                in let odl = Array.make (iloczyny.((Array.length iloczyny) - 1)) (-1)
                in odl.(0) <- 0;
                bfs [0] [] 1 odl iloczyny pojemnosci koniec
