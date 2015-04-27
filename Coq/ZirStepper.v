Set Implicit Arguments.

Section Zir.

Variables S I O V : Type.

Inductive Zir :=
  | Yield : S -> O -> Zir
  | Skip : S -> Zir
  | Done : V -> Zir
  | NeedInput : (I -> S) -> Zir.

End Zir.

Arguments Yield [S I O V] _ _.
Arguments Skip [S I O V] _.
Arguments Done [S I O V] _.
Arguments NeedInput [S I O V] _.

Section Cast.

Variables S S' I O V : Type.

Definition cast (f : S -> S') (z : Zir S I O V) : Zir S' I O V :=
  match z with
    | Yield s out_val => Yield (f s) out_val
    | Skip s => Skip (f s)
    | Done val => Done val
    | NeedInput g => NeedInput (fun s => f (g s))
  end.

End Cast.                     

Section SZir.

Variables S I O V : Type.

(* NOTE: no existential state! 

   Existentially quantifying the state-type S in the definition of 'SZir', as 
   in the Haskell code, leads to a universe inconsistency in the definition 
   of 'zbind'. See [NOTE: EXISTENTIAL] below.
*)

Inductive SZir :=
  mkSZir : S -> (S -> Zir S I O V) -> SZir.

End SZir.

(* (* [NOTE: EXISTENTIAL] The following code hides the state type in 'SZir', but 
   this formulation leads to a universe inconsistency in the definition of 'zbind'. *)

Section SZir.

Variables I O V : Type.

Inductive SZir :=
  mkSZir : forall S : Type, S -> (S -> Zir S I O V) -> SZir.

(* An isomorphic alternative definition:
Definition SZir := {S : Type & (S * (S -> Zir S I O V))%type}.

Definition mkSZir (S : Type) (s : S) (f : S -> Zir S I O V) : SZir := @existT _ _ S (s, f).

Definition type_of  (z : SZir) : Type := projT1 z.
Definition state_of (z : SZir) : type_of z := fst (projT2 z).
Definition sfun_of  (z : SZir) : type_of z -> Zir (type_of z) I O V := snd (projT2 z).
*)

End SZir.

Section Bind.

Variables I O V : Type.

Definition zbind (z1 : SZir I O V) (f : V -> SZir I O V) : SZir I O V :=
  match z1 with
    | mkSZir _ s1 step1 => 
      mkSZir (inl s1) (fun e => 
        match e with
          | inl s1 => 
            match step1 s1 with
              | Skip s1' => Skip (inl s1')
              | Done val => 
                  match f val with
                    | mkSZir _ s2 step2 => 
                        cast (fun x => inr (mkSZir x step2)) (step2 s2)
                  end
              | Yield s1' out_val => Yield (inl s1') out_val
              | NeedInput h => NeedInput (fun in_val => inl (h in_val))
            end
          | inr sec => 
              match sec with
                | mkSZir _ s2 step2 => 
                  cast (fun x => inr (mkSZir x step2)) (step2 s2)
              end
        end)
  end.

(* Alternative zbind, for the isomorphic 'SZir' type. Also leads to UC. *)
Definition zbind (z1 : SZir I O V) (f : V -> SZir I O V) : SZir I O V :=
  let s1 := state_of z1 in
  let step1 := sfun_of z1 in 
    mkSZir (inl s1) (fun e => 
      match e with
        | inl s1 => 
            match step1 s1 with
              | Skip s1' => Skip (inl s1')
              | Done val => 
                  let s2 := state_of (f val) in
                  let step2 := sfun_of (f val) in 
                    cast (fun x => inr (mkSZir x step2)) (step2 s2)
              | Yield s1' out_val => Yield (inl s1') out_val
              | NeedInput h => NeedInput (fun in_val => inl (h in_val))
            end
        | inr sec => 
            let s2 := state_of sec in
            let step2 := sfun_of sec in
              cast (fun x => inr (mkSZir x step2)) (step2 s2)
      end).
*)

Section EmitTakeReturn.

Variables I O V : Type.

Definition zemit (out_val : O) : SZir bool I O unit :=
  mkSZir true (fun b : bool => if b then Yield false out_val
                               else Done tt).

Definition ztake : SZir (option I) I O I :=
  mkSZir None (fun mv : option I => 
                 match mv with
                   | None => NeedInput (fun in_val => Some in_val)
                   | Some in_val => Done in_val
                 end).

Definition zreturn (val : V) : SZir unit I O V :=
  mkSZir tt (fun u : unit => Done val).

End EmitTakeReturn.

Section Bind.

Variables S1 S2 I O V1 V2 : Type.

Definition zbind (z1 : SZir S1 I O V1) (f : V1 -> SZir S2 I O V2) 
  : SZir (S1 + SZir S2 I O V2) I O V2 :=
  match z1 with
    | mkSZir s1 step1 => 
      mkSZir (inl s1) (fun e => 
        match e with
          | inl s1 => 
            match step1 s1 with
              | Skip s1' => Skip (inl s1')
              | Done val => 
                  match f val with
                    | mkSZir s2 step2 => 
                        cast (fun x => inr (mkSZir x step2)) (step2 s2)
                  end
              | Yield s1' out_val => Yield (inl s1') out_val
              | NeedInput h => NeedInput (fun in_val => inl (h in_val))
            end
          | inr sec => 
              match sec with
                | mkSZir s2 step2 => 
                  cast (fun x => inr (mkSZir x step2)) (step2 s2)
              end
        end)
  end.

End Bind.

Section Pipe.

Variables S1 S2 I M O V : Type.

Definition zpipe (z1 : SZir S1 I M V) (z2 : SZir S2 M O V) : SZir (S1*S2) I O V :=
  match z1, z2 with
    | mkSZir s1 step1, mkSZir s2 step2 => 
      mkSZir (s1,s2) (fun p => 
        let (s1,s2) := p in 
          match step2 s2 with
            | Yield s2' out_val => Yield (s1,s2') out_val
            | Skip s2' => Skip (s1, s2')
            | Done val => Done val
            | NeedInput g2 => 
                match step1 s1 with
                  | Yield s1' m => Skip (s1', g2 m)
                  | Skip s1' => Skip (s1', s2)
                  | Done val => Done val
                  | NeedInput g1 => NeedInput (fun in_val => (g1 in_val, s2))
                end
          end)
  end.

End Pipe.

Require Import List.

Section Run.

Variables State I O V : Type.

Inductive Err : Type :=
| raiseOutOfFuel : Err
| raiseNeedInput : Err.

Definition Result : Type := (list O * ((list I * Err) + V))%type.

Fixpoint loop (fuel : nat) (acc : list O) (step : State -> Zir State I O V) 
              (in_vals : list I) (z : Zir State I O V) : Result :=
  match fuel with
    | 0 => (rev acc, inl (in_vals, raiseOutOfFuel))
    | S fuel' => 
      match z with
        | Yield s' out_val => loop fuel' (out_val :: acc) step in_vals (step s')
        | Skip s' => loop fuel' acc step in_vals (step s')
        | Done val => (rev acc, inr val)
        | NeedInput g => 
          match in_vals with
            | nil => (rev acc, inl (in_vals, raiseNeedInput))
            | i :: in_vals' => loop fuel' acc step in_vals' (step (g i))
          end
      end
  end.

Definition run (in_vals : list I) (z : SZir State I O V) : Result :=
  match z with
    | mkSZir s step => loop 1000 nil step in_vals (step s)
  end. 

End Run.

Arguments ztake [I O].
Arguments zemit [I O] out_val.
Arguments zbind [S1 S2 I O V1 V2] z1 f.

Definition test1 := zbind ztake (@zemit nat _).

Definition test2 := zbind test1 (fun _ => test1).

Definition test3 := zbind test1 (fun _ => test2).

Definition test4 := zbind test1 (fun _ => test3).

Eval compute in run (1::2::3::nil) test1.
Eval compute in run (1::2::3::nil) test2.
Eval compute in run (1::2::3::nil) test3.
Eval compute in run (1::2::3::nil) test4. (*Err: needs input*)
