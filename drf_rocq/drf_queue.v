Require Import String Arith List Lia ZArith.
Import ListNotations.
Require Import FSetFacts.
Require Import FMapInterface.
Require Import FSets.
Require Import FMapFacts.

(* m = num resources, n = num users *)
Definition vector := list nat.
Definition matrix := list (vector).

(* -------------------- COMPARATORS -------------------- *)
Fixpoint list_add (l1 l2 : list nat) : list nat :=
match l1, l2 with
| [], [] => []  
| x1 :: xs1, x2 :: xs2 => (x1 + x2) :: (list_add xs1 xs2) 
| _, _ => []
end.

Fixpoint list_leq (l1 l2 : list nat) : bool :=
match l1, l2 with
| [], [] => true 
| x1 :: xs1, x2 :: xs2 => (x1 <=? x2) && list_leq xs1 xs2 
| _, _ => false 
end.

Fixpoint list_gt (l1 l2 : list nat) : bool :=
match l1, l2 with
| [], [] => true 
| x1 :: xs1, x2 :: xs2 => (x2 <? x1) && list_gt xs1 xs2 
| _, _ => false  
end.

Fixpoint list_eq (l1 l2 : list nat) : bool :=
match l1, l2 with
| [], [] => true 
| x1 :: xs1, x2 :: xs2 => (x1 =? x2) && list_eq xs1 xs2 
| _, _ => false  
end.

Fixpoint matrix_eq (m1 m2 : matrix) : bool :=
match m1, m2 with
| [], [] => true
| r1 :: rs1, r2 :: rs2 => (list_eq r1 r2) && matrix_eq rs1 rs2 
| _, _ => false
end.


(* ------------ Q impl from https://www.cis.upenn.edu/~plclub/blog/2020-10-09-hs-to-coq/ --------- *)
Inductive Queue a : Type
  := | MkQueue (front : list a) (back : list a) : Queue a.

Arguments MkQueue {_} _ _.

Definition back {a} (arg_0__ : Queue a) :=
  let 'MkQueue _ back := arg_0__ in
  back.

Definition front {a} (arg_0__ : Queue a) :=
  let 'MkQueue front _ := arg_0__ in
  front.

(* Converted value declarations: *)
Definition push {a} : a -> Queue a -> Queue a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, MkQueue front back => MkQueue front (cons x back)
    end.

Definition pop {a} : Queue a -> option (a * Queue a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | MkQueue (cons y front) back => Some (pair y (MkQueue front back))
    | MkQueue nil back =>
        match rev back with
        | nil => None
        | cons y front => Some (pair y (MkQueue front nil))
        end
    end.

Definition empty {a} : Queue a := MkQueue nil nil.
(* ------------ END: Q impl from https://www.cis.upenn.edu/~plclub/blog/2020-10-09-hs-to-coq/ --------- *)

(* Helper fn to normalize wueue so easier to compare qs *)
Definition normalize_queue {a} (q : Queue a): Queue a :=
match q with
| MkQueue nil back => MkQueue nil back
| MkQueue front nil => MkQueue nil (rev front)
| MkQueue front back => MkQueue nil (back ++ rev front)
end.

Definition resource_capacities := vector.
Definition consumed_resources := vector.
Definition user_allocations := matrix.

Definition compare_ratios (n1 d1 n2 d2 : nat) : comparison :=
  if n1 * d2 =? n2 * d1 then Eq
  else if n1 * d2 <?  n2 * d1 then Lt
  else Gt.

Definition max_in_list (l: list nat) : nat :=
  fold_left Nat.max l 0.

Fixpoint max_in_list_ratios (num denom : list nat) (max_n max_d : nat) (max_idx : nat) (current_idx : nat) : nat :=
match num, denom with
| [], [] => max_idx
| [], _ => max_idx
| _, [] => max_idx
| n :: ns, d :: ds =>
  match compare_ratios n d max_n max_d with
  | Eq => max_in_list_ratios ns ds max_n max_d max_idx (S current_idx)
  | Lt => max_in_list_ratios ns ds max_n max_d max_idx (S current_idx)
  | Gt => max_in_list_ratios ns ds n d current_idx (S current_idx)
  end
end.

Definition max_ratio_index (numerators denominators : list nat) : nat :=
  max_in_list_ratios numerators denominators 0 1 0 0.

(*
Compares 4/9 with 2/3 -- 2/3 is the max ratio
*)
Example ex_max_ratio:
max_ratio_index [4; 2] [9; 3]  = 1.
Proof.
unfold max_ratio_index; simpl; auto.
Qed. 

Definition create_array_from_matrix (M: matrix) : list nat :=
  map max_in_list M.

(* gives index in the resource array *)
Definition get_user_dominant_share_indices (M: matrix) (R: list nat) : list nat :=
  map (fun row => max_ratio_index row R) M.

Example test_get_user_dominant_share_indices:
get_user_dominant_share_indices [[1; 4]; [3; 1]] [9; 18] = [1; 0].
Proof.
unfold get_user_dominant_share_indices; simpl; auto.
Qed.

Definition min_index (l: list nat) : option nat :=
  match l with
  | [] => None 
  | x :: xs =>
      (* fold_left: tracks minIndx and minElem *)
      Some (fst (fold_left (fun acc p =>
                            if Nat.leb p (snd acc)
                            then (fst acc + 1, p)  (* update if smaller *)
                            else acc) 
                          xs 
                          (0, x)))  (* init: (0, x0)*)
  end.

Definition min_index_ratios_helper (indices R : list nat) (M : matrix) : option (nat * nat * nat) :=
  match M, indices with
  | [], _ => None  (* No users *)
  | _, [] => None  (* No indices *)
  | row1 :: rest_rows, i1 :: rest_indices =>
      (* Initial min values (using the first row) *)
      let min_idx := 0 in
      let min_numerator := nth i1 row1 0 in
      let min_denominator := nth i1 R 1 in

      (* Fold through remaining users *)
      Some (fold_left (fun acc userI =>
                        let '(min_idx, min_numerator, min_denominator) := acc in
                        match nth_error rest_indices userI, nth_error rest_rows userI with
                        | Some resource_idx, Some numerators =>
                          let numerator := nth resource_idx numerators 0 in
                          let denominator := nth resource_idx R 1 in
                          match compare_ratios numerator denominator min_numerator min_denominator with
                          | Lt => (userI + 1, numerator, denominator)  (* Update if smaller ratio *)
                          | _  => acc  (* Keep previous min *)
                          end
                        | _, _ => acc (* Skip if out of bounds *)
                        end)
                      (seq 0 (length rest_rows))
                      (min_idx, min_numerator, min_denominator))
  end.

Definition min_index_ratios (indices R : list nat) (M : matrix) : option nat :=
  match min_index_ratios_helper indices R M with
  | Some (min_idx, _, _) => Some min_idx
  | None => None
  end.


(*
4/18 = 0.222 vs 3/9 = 0.3333 --> Choose smaller dom share: 4/18
*)
Example test_min_index_ratios:
let R := [9; 18] in
let U := [[1; 4]; [3; 1]] in 
min_index_ratios (get_user_dominant_share_indices U R) R U = Some(0).
Proof.
unfold min_index_ratios; simpl; auto.
Qed.


(* ---------- JOBQUEUE --------------- *)
Definition job := list nat.
Definition JobQueue := Queue job.
Definition user_demand_vectors := list (JobQueue).

Inductive state : Type :=
    mkState : consumed_resources -> resource_capacities -> user_allocations -> user_demand_vectors -> state.

Definition get_consumed (s : state) : consumed_resources :=
match s with
| mkState C _ _ _ => C
end.

Definition get_resources (s : state) : resource_capacities :=
match s with
| mkState _ R _ _ => R
end.
  
Definition get_allocs (s : state) : user_allocations :=
match s with
| mkState _ _ U _  => U
end.

Definition get_demands (s : state) : user_demand_vectors :=
match s with
| mkState _ _ _ D => D
end.

Definition get_alloc_for_user (s : state) (userI : nat) :=
match s with
| mkState _ _ U _  => 
  let all_allocs := get_allocs s in 
  let user_allocs_wrapped := nth_error all_allocs userI in
  match user_allocs_wrapped with 
  | Some user_alloc => user_alloc
  | None => []
  end
end.

Fixpoint set_row (m : matrix) (idx : nat) (new_row : list nat) : matrix :=
  match m with
  | [] => [] 
  | h :: t =>
      if Nat.eqb idx 0 then new_row :: t 
      else h :: set_row t (pred idx) new_row
  end.

Fixpoint set_row_queue (m : user_demand_vectors) (idx : nat) (new_queue : JobQueue) : user_demand_vectors :=
match m with
| [] => [] 
| h :: t =>
  if Nat.eqb idx 0 then new_queue :: t 
  else h :: set_row_queue t (pred idx) new_queue
end.


Definition update_state (s : state) (userI : nat) (applied_demand : list nat) (new_queue : JobQueue) : state :=
  let newConsumed := list_add (get_consumed s) (applied_demand) in
  let newUserAllocRow := list_add (get_alloc_for_user s userI) (applied_demand) in
  let newUserAllocs := (set_row (get_allocs s) userI newUserAllocRow) in
  let newDemands := set_row_queue (get_demands s) (userI) (new_queue) in 
  mkState newConsumed (get_resources s) newUserAllocs newDemands.


Definition DRF_Algorithm (s : state): state :=
    let C := (get_consumed s) in 
    let R := (get_resources s) in
    let U := (get_allocs s) in 
    let D := (get_demands s) in 
    let user_indx := min_index_ratios (get_user_dominant_share_indices U R) R U in
    match user_indx with
    | Some i => 
        let user_demands := nth_error D i in
        match user_demands with
        | Some queue => 
          let pop_result := pop queue in 
          match pop_result with 
          | Some (pair demand new_user_queue) => 
            let newC := list_add C demand in 
            if (list_leq (newC) R) then (update_state s i demand new_user_queue) else s (* Replace this none with oldQueue/oldState*)
          | None => s
          end
        | _ => s
        end
    | None => s
    end.


Definition empty_jobQueue : JobQueue := empty.
Definition example_queue : JobQueue := push [2; 5] (push [1; 4] empty_jobQueue).
Eval compute in example_queue.

(* Move all elements to back *)
Definition queue_equality (q1 q2 : JobQueue) : bool :=
let norm1 := normalize_queue q1 in
let norm2 := normalize_queue q2 in
match norm1, norm2 with 
| MkQueue nil norm1Back, MkQueue nil norm2Back => matrix_eq norm1Back norm2Back
| _, _ => false
end.


Fixpoint demands_eq (m1 m2 : user_demand_vectors) : bool :=
match m1, m2 with
| nil, nil => true 
| r1 :: rs1, r2 :: rs2 => (queue_equality r1 r2) && demands_eq rs1 rs2
| _, _ => false
end.

Definition state_equivalence (s1 s2 : state): bool :=
let matchConsumed := list_eq (get_consumed s1) (get_consumed s2) in 
let matchAllocs := matrix_eq (get_allocs s1) (get_allocs s2) in
let matchDemands := demands_eq (get_demands s1) (get_demands s2) in
matchConsumed && matchAllocs && matchDemands.

Definition terminal_state (s : state) : Prop :=
  state_equivalence (DRF_Algorithm s) s = true.

Definition init (s: state) : Prop := 
  let R := [9; 18] in 
  let C0 := [0; 0] in
  let U0 := [[0; 0]; [0; 0]] in (* user allocations *)
  let D0 := [
    push [1; 4] (push [1; 4] (push [1; 4] (push [1; 4] empty_jobQueue)));
    push [3; 1] (push [3; 1] (push [3; 1] empty_jobQueue))
  ] in
  s = mkState C0 R U0 D0.

(* -------------- FROM CS 345H Notes ----------------- *)
Definition step (s1 s2: state) := s2 = DRF_Algorithm s1.

Inductive step_star : state -> state -> Prop :=
| step_refl : forall s, step_star s s
| step_once : forall s1 s2 s3, step s1 s2 -> step_star s2 s3 -> step_star s1 s3.
(* -------------- END: FROM CS 345H Notes ----------------- *)
Fixpoint do_n_steps (s : state) (fuel: nat) : state :=
  match fuel with
  | 0 => s (* Fuel gone before finish! *)
  | S fuel_minus_1 => match (DRF_Algorithm s) with
                      | s' => do_n_steps s' fuel_minus_1
                      end
  end.

Definition paper_init : state :=
let R := [9; 18] in 
let C0 := [0; 0] in
let U0 := [[0; 0]; [0; 0]] in (* user allocations *)
let D0 := [
  push [1; 4] (push [1; 4] (push [1; 4] (push [1; 4] empty_jobQueue)));
  push [3; 1] (push [3; 1] (push [3; 1] empty_jobQueue))
] in 
(mkState C0 R U0 D0).
Compute do_n_steps paper_init 5.

Example drf_paper_example (s: state) :
let R := [9; 18] in   (* resource capacities *)
let C0 := [0; 0] in   (* consumed resources *)
let U0 := [[0; 0]; [0; 0]] in (* user allocations *)
let D0 := [           (* demand vectors *)
  push [1; 4] (push [1; 4] (push [1; 4] (push [1; 4] empty_jobQueue)));
  push [3; 1] (push [3; 1] (push [3; 1] empty_jobQueue))
] in 
let CN := [9; 14]  in 
let UN := [[3; 12]; [6; 2]] in 
let DN := [
  push [1; 4] empty_jobQueue;
  push [3; 1] empty_jobQueue
] in
let s0 := mkState C0 R U0 D0 in
let sN := mkState CN R UN DN in
  state_equivalence (do_n_steps s0 5) sN = true.
Proof.
firstorder. 
Qed.

