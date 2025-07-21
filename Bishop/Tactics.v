From Ltac2 Require Import Ltac2.
From Ltac2 Require Import List.
From Ltac2 Require Import String.
From Ltac2 Require Import Int.
From Ltac2 Require Import Ltac1.

From Stdlib Require Import Unicode.Utf8 BinNat Lia Lra.
From Stdlib Require Import QArith Qabs Psatz.

Ltac2 rec get_last_digit (n : int) :=
  match ge n 0 with  
  | true =>
    match (Int.mod n 10) with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
    end
  | false => get_last_digit (abs n)
  end.

Ltac2 rec of_int (n : int) :=
  match gt n 0 with
  | true => 
    match ge n 10 with
    | true => app (of_int (Int.div n 10)) (get_last_digit n)
    | false => (get_last_digit n)
    end
  | false => 
    match equal n 0 with
    | true => "0"
    | false => app "-" (of_int (abs n))
    end
  end.

Ltac2 Eval map (fun (n:int) => app "f" (of_int n)) (seq 1 1 11).

Check ?[ x ] : ?[ W ].
Ltac2 Check '(_).

Ltac2 findp (c:constr) := Message.print (Message.of_constr c). 

