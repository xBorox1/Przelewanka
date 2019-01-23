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

(* Zwraca listę stanów do których można dotrzeć z danego stanu w jednej operacji. *)        
let kolejne_stany stan pojemnosci =
        let l = ref []
        in let len = (Array.length stan) - 1
        in let kolejny_stan = (Array.copy stan)
        in begin
               for i = 0 to len do
                       kolejny_stan.(i) <- 0;
                       l := (Array.copy kolejny_stan)::(!l);
                       kolejny_stan.(i) <- stan.(i);
               done;
               for i = 0 to len do
                       kolejny_stan.(i) <- pojemnosci.(i);
                       l := (Array.copy kolejny_stan)::(!l);
                       kolejny_stan.(i) <- stan.(i);
               done;
               for i = 0 to len do
                       for j = 0 to len do
                               let roznica = if i = j then 0 else pojemnosci.(j) - stan.(j)
                               in 
                                    if roznica < stan.(i) then begin
                                       kolejny_stan.(j) <- pojemnosci.(j);
                                       kolejny_stan.(i) <- (stan.(i) - roznica); 
                                       l := (Array.copy kolejny_stan)::(!l);
                                       kolejny_stan.(j) <- stan.(j);
                                       kolejny_stan.(i) <- stan.(i);
                                       end
                                    else begin
                                       kolejny_stan.(j) <- (stan.(j) + stan.(i));
                                       kolejny_stan.(i) <- 0; 
                                       l := (Array.copy kolejny_stan)::(!l);
                                       kolejny_stan.(j) <- stan.(j);
                                       kolejny_stan.(i) <- stan.(i);
                                    end;
                       done;
               done;
         end;
         !l

(* Sprawdza czy stan był już odwiedzony, jeśli nie to aktualizuje odległość 
 * i listę stanów do odwiedzenia. *)
let dodaj_odleglosc stan odl dl l =
        let zmiana = not (Hashtbl.mem odl stan) in
        if zmiana then Hashtbl.add odl stan dl;
        if zmiana then (odl, (stan :: l))
        else (odl, l)
		
(* BFS, kończący się w momencie odwiedzenia stanu końcowego lub przejścia wszystkich
 * możliwych do odwiedzenia stanów. 
 * Przyjmowane argumenty to kolejno : lista wierzchołków z aktualnie przetwarzanego bloku,
 * lista wierzchołków z kolejnego bloku, odległość bloku od źródła, iloczyny prefiksowe
 * pojemności szklanek, pojemności szklanek i stan końcowy. *)
let rec bfs l1 l2 dl odl pojemnosci koniec =
        if pusta l1 && pusta l2 then (-1)
        else match l1 with
        | [] -> bfs l2 l1 (dl + 1) odl pojemnosci koniec
        | (stan :: t) -> let stany = kolejne_stany stan pojemnosci
                      in let (odl2, l3) = List.fold_left (fun (od, l) x -> dodaj_odleglosc x od dl l) (odl, l2) stany
                      in if (Hashtbl.mem odl2 koniec) then (Hashtbl.find odl2 koniec)
                      else bfs t l3 dl odl2 pojemnosci koniec
        

let przelewanka tab =
        let tab = usun_zera tab
        in if tab = [||] then 0
        else if not (warunki_konieczne tab) then (-1)
        else let cz = czy_wszystkie_puste_lub_pelne tab
        in if cz <> (-1) then cz
        else
                let (pojemnosci, koniec) = normalizuj tab
                in let odl = Hashtbl.create 10000000
                in let poczatek = Array.make (Array.length pojemnosci) 0
                in Hashtbl.add odl poczatek 0;
                bfs [poczatek] [] 1 odl pojemnosci koniec
