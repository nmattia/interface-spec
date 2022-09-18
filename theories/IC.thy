theory IC
  imports "HOL-Library.AList" "HOL-Library.List_Lexorder"
begin

(* General helper lemmas *)

lemma in_set_updD: "x \<in> set (xs[n := z]) \<Longrightarrow> x \<in> set xs \<or> x = z"
  by (meson insert_iff set_update_subset_insert subsetD)

(* Byte *)

typedef nat8 = "{n :: nat. 0 \<le> n \<and> n < 256}"
  by (auto intro: exI[of _ 0])

setup_lifting type_definition_nat8

instantiation nat8 :: equal
begin

lift_definition equal_nat8 :: "nat8 \<Rightarrow> nat8 \<Rightarrow> bool" is "(=)" .

instance
  apply standard
  subgoal for x y
    by transfer auto
  done

end

instantiation nat8 :: linorder
begin

lift_definition less_eq_nat8 :: "nat8 \<Rightarrow> nat8 \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_nat8 :: "nat8 \<Rightarrow> nat8 \<Rightarrow> bool" is "(<)" .

instance
  apply standard
  subgoal for x y
    by transfer auto
  subgoal for x
    by transfer auto
  subgoal for x y z
    by transfer auto
  subgoal for x y
    by transfer auto
  subgoal for x y
    by transfer auto
  done

end

(* Partial maps *)

typedef ('a, 'b) list_map = "{f :: ('a \<times> 'b) list. distinct (map fst f)}"
  by (auto intro: exI[of _ "[]"])

setup_lifting type_definition_list_map

lift_bnf (dead 'k, set: 'v) list_map [wits: "[] :: ('k \<times> 'v) list"] for map: map rel: rel
  by auto

hide_const (open) map set rel

lift_definition list_map_dom :: "('a, 'b) list_map \<Rightarrow> 'a set" is
  "set \<circ> map fst" .

lift_definition list_map_vals :: "('a, 'b) list_map \<Rightarrow> 'b list" is
  "map snd" .

lift_definition list_map_range :: "('a, 'b) list_map \<Rightarrow> 'b set" is
  "set \<circ> map snd" .

lemma in_set_map_filter_vals: "z \<in> set (List.map_filter g (list_map_vals f)) \<Longrightarrow> \<exists>w \<in> list_map_range f. g w = Some z"
  by transfer (force simp: List.map_filter_def)

lift_definition list_map_sum_vals :: "('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) list_map \<Rightarrow> nat" is
  "\<lambda>g. sum_list \<circ> (map (g \<circ> snd))" .

lift_definition list_map_get :: "('a, 'b) list_map \<Rightarrow> 'a \<Rightarrow> 'b option" is
  "map_of" .

lemma list_map_get_dom[dest]: "x \<in> list_map_dom f \<Longrightarrow> list_map_get f x = None \<Longrightarrow> False"
  by transfer auto

lemma list_map_get_range: "list_map_get f x = Some y \<Longrightarrow> y \<in> list_map_range f"
  by transfer force

lift_definition list_map_set :: "('a, 'b) list_map \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) list_map" is
  "\<lambda>f x y. AList.update x y f"
  by (rule distinct_update)

lemma list_map_get_set: "list_map_get (list_map_set f x y) z = (if x = z then Some y else list_map_get f z)"
  by transfer (auto simp add: update_Some_unfold update_conv)

lemma list_map_dom_set[simp]: "list_map_dom (list_map_set f x y) = list_map_dom f \<union> {x}"
  by transfer (auto simp add: dom_update)

lemma list_map_range_setD: "z \<in> list_map_range (list_map_set f x y) \<Longrightarrow> z \<in> list_map_range f \<or> z = y"
  apply transfer
  apply auto
  apply (metis distinct_update image_iff map_of_eq_Some_iff snd_eqD update_Some_unfold)
  done

lift_definition list_map_del :: "('a, 'b) list_map \<Rightarrow> 'a \<Rightarrow> ('a, 'b) list_map" is
  "\<lambda>f x. AList.delete x f"
  by (rule distinct_delete)

lemma list_map_get_del: "list_map_get (list_map_del f x) z = (if x = z then None else list_map_get f z)"
  by transfer (auto simp add: delete_conv')

lemma list_map_dom_del[simp]: "list_map_dom (list_map_del f x) = list_map_dom f - {x}"
  by transfer (simp add: delete_keys)

lemma list_map_range_del: "z \<in> list_map_range (list_map_del f x) \<Longrightarrow> z \<in> list_map_range f"
  apply transfer
  apply auto
  apply (metis Some_eq_map_of_iff delete_notin_dom distinct_delete fst_eqD imageI map_of_delete snd_eqD)
  done

lift_definition list_map_empty :: "('a, 'b) list_map" is "[]"
  by auto

lemma list_map_get_empty[simp]: "list_map_get list_map_empty x = None"
  by transfer auto

lemma list_map_empty_dom[simp]: "list_map_dom list_map_empty = {}"
  by transfer auto

lemma list_map_empty_range[simp]: "list_map_range list_map_empty = {}"
  by transfer auto

lift_definition list_map_init :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) list_map" is
  "\<lambda>xys. AList.updates (map fst xys) (map snd xys) []"
  using distinct_updates
  by force

lift_definition list_map_map :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) list_map \<Rightarrow> ('a, 'c) list_map" is
  "\<lambda>f xs. map (\<lambda>(k, v). (k, f v)) xs"
  by (auto simp: comp_def case_prod_beta)

lemma list_map_dom_map_map[simp]: "list_map_dom (list_map_map g f) = list_map_dom f"
  by transfer force

lemma list_map_range_map_map[simp]: "list_map_range (list_map_map g f) = g ` list_map_range f"
  by transfer force

lemma list_map_sum_vals_split: "(\<And>ctxt. ctxt \<in> list_map_range xs \<Longrightarrow> f (g ctxt) \<le> f ctxt) \<Longrightarrow> list_map_sum_vals f xs =
  list_map_sum_vals id
    (list_map_map (\<lambda>ctxt. if P ctxt then f ctxt - f (g ctxt) else 0) xs) +
  list_map_sum_vals f
    (list_map_map (\<lambda>ctxt. if P ctxt then g ctxt else ctxt) xs)"
  apply (transfer fixing: f g P)
  subgoal for xs
    by (induction xs) auto
  done

lemma list_map_sum_vals_filter:
  assumes "\<And>b. b \<in> list_map_range xs \<Longrightarrow> P b = None \<Longrightarrow> f b = 0" "\<And>b y. b \<in> list_map_range xs \<Longrightarrow> P b = Some y \<Longrightarrow> f b = g y"
  shows "list_map_sum_vals id (list_map_map f xs) = sum_list (map g (List.map_filter P (list_map_vals xs)))"
  using assms
  apply (transfer fixing: f g P)
  subgoal for xs
    by (induction xs) (auto simp: List.map_filter_def)
  done

lemma list_map_sum_in_ge_aux:
  fixes g :: "'a \<Rightarrow> nat"
  shows "distinct (map fst f) \<Longrightarrow> map_of f x = Some y \<Longrightarrow> g y \<le> sum_list (map g (map snd f))"
  by (induction f) (auto split: if_splits)

lemma list_map_sum_in_ge: "list_map_get f x = Some y \<Longrightarrow> list_map_sum_vals g f \<ge> g y"
  apply transfer
  using list_map_sum_in_ge_aux[OF _ map_of_is_SomeI]
  by fastforce

lemma list_map_sum_in_aux: fixes g :: "'a \<Rightarrow> nat"
  shows "distinct (map fst f) \<Longrightarrow> map_of f x = Some y \<Longrightarrow>
  sum_list (map (g \<circ> snd) (AList.update x y' f)) = sum_list (map (g \<circ> snd) f) + g y' - g y"
  apply (induction f)
   apply auto[1]
  subgoal for a f
    using list_map_sum_in_ge_aux[OF _ map_of_is_SomeI, of f x y g]
    by auto
  done

lemma list_map_sum_in: "list_map_get f x = Some y \<Longrightarrow> list_map_sum_vals g (list_map_set f x y') = list_map_sum_vals g f + g y' - g y"
  apply transfer
  using list_map_sum_in_aux
  by fastforce

lemma list_map_sum_out_aux:
  "x \<notin> set (map fst f) \<Longrightarrow> sum_list (map (g \<circ> snd) (AList.update x y f)) = sum_list (map (g \<circ> snd) f) + g y"
  by (induction f) (auto simp: add.assoc)

lemma list_map_sum_out: "x \<notin> list_map_dom f \<Longrightarrow> list_map_sum_vals g (list_map_set f x y) = list_map_sum_vals g f + g y"
  apply transfer
  using list_map_sum_out_aux
  by fastforce

lemma list_map_del_sum_aux:
  fixes g :: "'a \<Rightarrow> nat"
  shows "distinct (map fst f) \<Longrightarrow> map_of f x = Some y \<Longrightarrow> sum_list (map (g \<circ> snd) f) = sum_list (map (g \<circ> snd) (AList.delete x f)) + g y"
  by (induction f) auto

lemma list_map_del_sum: "list_map_get f x = Some y \<Longrightarrow> list_map_sum_vals g f = list_map_sum_vals g (list_map_del f x) + g y"
  apply transfer
  using list_map_del_sum_aux
  by fastforce

(* Abstract behaviour *)

(* Abstract canisters *)

type_synonym blob = "nat8 list"

type_synonym method_name = String.literal

type_synonym arg = blob
type_synonym 'p caller_id = 'p

type_synonym timestamp = nat
datatype status = Running | Stopping | Stopped
record env =
  time :: timestamp
  balance :: nat
  freezing_limit :: nat
  certificate :: "blob option"
  status :: status

type_synonym reject_code = nat
type_synonym error_code = nat
datatype response
  = Reply blob
  | Reject reject_code String.literal
datatype query_response
  = Success blob
  | Rejected reject_code String.literal error_code
record ('p, 'c) method_call =
  callee :: 'p
  method_name :: method_name
  arg :: arg
  transferred_cycles :: nat
  callback :: 'c

record 'x cycles_return =
  return :: 'x
  cycles_used :: nat
type_synonym trap_return = "unit cycles_return"
record ('w, 'p, 'c) update_return =
  new_state :: 'w
  new_calls :: "('p, 'c) method_call list"
  new_certified_data :: "blob option"
  response :: "response option"
  cycles_accepted :: nat
  cycles_used :: nat
record query_return =
  response :: "response"
  cycles_used :: nat
record 'w heartbeat_return =
  new_state :: 'w
  cycles_used :: nat
type_synonym ('w, 'p, 'c) update_func = "'w \<Rightarrow> trap_return + ('w, 'p, 'c) update_return"
type_synonym 'w query_func = "'w \<Rightarrow> trap_return + query_return"
type_synonym 'w heartbeat_func = "'w \<Rightarrow> trap_return + 'w heartbeat_return"

type_synonym available_cycles = nat
type_synonym refunded_cycles = nat

datatype inspect_method_result = Accept | Reject
record ('p, 'w, 'sm, 'c) canister_module_rec =
  init :: "'p \<times> arg \<times> 'p caller_id \<times> env \<Rightarrow> trap_return + 'w cycles_return"
  pre_upgrade :: "'w \<times> 'p \<times> env \<Rightarrow> trap_return + 'sm cycles_return"
  post_upgrade :: "'p \<times> 'sm \<times> arg \<times> 'p caller_id \<times> env \<Rightarrow> trap_return + 'w cycles_return"
  update_methods :: "(method_name, (arg \<times> 'p caller_id \<times> env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'c) update_func) list_map"
  query_methods :: "(method_name, (arg \<times> 'p caller_id \<times> env) \<Rightarrow> 'w query_func) list_map"
  heartbeat :: "env \<Rightarrow> 'w heartbeat_func"
  callbacks :: "('c \<times> response \<times> refunded_cycles \<times> env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'c) update_func"
  inspect_message :: "(method_name \<times> 'w \<times> arg \<times> 'p caller_id \<times> env) \<Rightarrow> trap_return + inspect_method_result cycles_return"
typedef ('p, 'w, 'sm, 'c) canister_module =
  "{m :: ('p, 'w, 'sm, 'c) canister_module_rec. list_map_dom (update_methods m) \<inter> list_map_dom (query_methods m) = {}}"
  by (auto intro: exI[of _ "\<lparr>init = undefined, pre_upgrade = undefined, post_upgrade = undefined,
      update_methods = list_map_empty, query_methods = list_map_empty, heartbeat = undefined, callbacks = undefined,
      inspect_message = undefined\<rparr>"])

setup_lifting type_definition_canister_module

lift_definition canister_module_init :: "('p, 'w, 'sm, 'c) canister_module \<Rightarrow> 'p \<times> arg \<times> 'p \<times> env \<Rightarrow> trap_return + 'w cycles_return" is "init" .
lift_definition canister_module_pre_upgrade :: "('p, 'w, 'sm, 'c) canister_module \<Rightarrow> 'w \<times> 'p \<times> env \<Rightarrow> trap_return + 'sm cycles_return" is pre_upgrade .
lift_definition canister_module_post_upgrade :: "('p, 'w, 'sm, 'c) canister_module \<Rightarrow> 'p \<times> 'sm \<times> arg \<times> 'p \<times> env \<Rightarrow> trap_return + 'w cycles_return" is post_upgrade .
lift_definition canister_module_update_methods :: "('p, 'w, 'sm, 'c) canister_module \<Rightarrow> (method_name, (arg \<times> 'p \<times> env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'c) update_func) list_map" is update_methods .
lift_definition canister_module_query_methods :: "('p, 'w, 'sm, 'c) canister_module \<Rightarrow> (method_name, (arg \<times> 'p \<times> env) \<Rightarrow> 'w query_func) list_map" is query_methods .
lift_definition canister_module_heartbeat :: "('p, 'w, 'sm, 'c) canister_module \<Rightarrow> env \<Rightarrow> 'w heartbeat_func" is heartbeat .
lift_definition canister_module_callbacks :: "('p, 'w, 'sm, 'c) canister_module \<Rightarrow> ('c \<times> response \<times> refunded_cycles \<times> env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'c) update_func" is callbacks .
lift_definition canister_module_inspect_message :: "('p, 'w, 'sm, 'c) canister_module \<Rightarrow> (method_name \<times> 'w \<times> arg \<times> 'p \<times> env) \<Rightarrow> trap_return + inspect_method_result cycles_return" is inspect_message .

lift_definition dispatch_method :: "method_name \<Rightarrow> ('p, 'w, 'sm, 'c) canister_module \<Rightarrow>
  (((arg \<times> 'p \<times> env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'c) update_func) + ((arg \<times> 'p \<times> env) \<Rightarrow> 'w query_func)) option" is
  "\<lambda>f m. case list_map_get (update_methods m) f of Some f' \<Rightarrow> Some (Inl f') | None \<Rightarrow> (case list_map_get (query_methods m) f of Some f' \<Rightarrow> Some (Inr f') | None \<Rightarrow> None)" .

(* Call contexts *)

record 'p request =
  nonce :: blob
  ingress_expiry :: nat
  sender :: 'p
  canister_id :: 'p
  method_name :: method_name
  arg :: arg
datatype ('p, 'c, 'cid) call_origin =
  From_user "'p request"
| From_canister "'cid" "'c"
| From_heartbeat
record ('p, 'c, 'cid) call_ctxt_rep =
  canister :: 'p
  origin :: "('p, 'c, 'cid) call_origin"
  needs_to_respond :: bool
  deleted :: bool
  available_cycles :: nat

typedef ('p, 'c, 'cid) call_ctxt = "{ctxt :: ('p, 'c, 'cid) call_ctxt_rep.
  (deleted ctxt \<longrightarrow> \<not>needs_to_respond ctxt) \<and> (\<not>needs_to_respond ctxt \<longrightarrow> available_cycles ctxt = 0)}"
  by (auto intro: exI[of _ "\<lparr>canister = undefined, origin = undefined, needs_to_respond = True, deleted = False, available_cycles = 0\<rparr>"])

setup_lifting type_definition_call_ctxt

lift_definition call_ctxt_canister :: "('p, 'c, 'cid) call_ctxt \<Rightarrow> 'p" is "canister" .
lift_definition call_ctxt_origin :: "('p, 'c, 'cid) call_ctxt \<Rightarrow> ('p, 'c, 'cid) call_origin" is "origin" .
lift_definition call_ctxt_needs_to_respond :: "('p, 'c, 'cid) call_ctxt \<Rightarrow> bool" is needs_to_respond .
lift_definition call_ctxt_deleted :: "('p, 'c, 'cid) call_ctxt \<Rightarrow> bool" is deleted .
lift_definition call_ctxt_available_cycles :: "('p, 'c, 'cid) call_ctxt \<Rightarrow> nat" is available_cycles .

lemma call_ctxt_not_needs_to_respond_available_cycles: "\<not>call_ctxt_needs_to_respond x2 \<Longrightarrow> call_ctxt_available_cycles x2 = 0"
  by transfer auto

lift_definition call_ctxt_respond :: "('p, 'c, 'cid) call_ctxt \<Rightarrow> ('p, 'c, 'cid) call_ctxt" is
  "\<lambda>ctxt. ctxt\<lparr>needs_to_respond := False, available_cycles := 0\<rparr>"
  by auto

lemma call_ctxt_respond_origin[simp]: "call_ctxt_origin (call_ctxt_respond ctxt) = call_ctxt_origin ctxt"
  by transfer auto

lemma call_ctxt_respond_needs_to_respond[dest]: "call_ctxt_needs_to_respond (call_ctxt_respond ctxt) \<Longrightarrow> False"
  by transfer auto

lemma call_ctxt_respond_available_cycles[simp]: "call_ctxt_available_cycles (call_ctxt_respond ctxt) = 0"
  by transfer auto

lift_definition call_ctxt_deduct_cycles :: "nat \<Rightarrow> ('p, 'c, 'cid) call_ctxt \<Rightarrow> ('p, 'c, 'cid) call_ctxt" is
  "\<lambda>n ctxt. ctxt\<lparr>available_cycles := available_cycles ctxt - n\<rparr>"
  by auto

lemma call_ctxt_deduct_cycles_origin[simp]: "call_ctxt_origin (call_ctxt_deduct_cycles n ctxt) = call_ctxt_origin ctxt"
  by transfer auto

lemma call_ctxt_deduct_cycles_needs_to_respond[simp]: "call_ctxt_needs_to_respond (call_ctxt_deduct_cycles n ctxt) = call_ctxt_needs_to_respond ctxt"
  by transfer auto

lemma call_ctxt_deduct_cycles_available_cycles[simp]: "call_ctxt_available_cycles (call_ctxt_deduct_cycles n ctxt) = call_ctxt_available_cycles ctxt - n"
  by transfer auto

lift_definition call_ctxt_delete :: "('p, 'c, 'cid) call_ctxt \<Rightarrow> ('p, 'c, 'cid) call_ctxt" is
  "\<lambda>ctxt. ctxt\<lparr>deleted := True, needs_to_respond := False, available_cycles := 0\<rparr>"
  by auto

lemma call_ctxt_delete_needs_to_respond[simp]: "call_ctxt_needs_to_respond (call_ctxt_delete ctxt) = False"
  by transfer auto

(* Calls and Messages *)

datatype 'p queue_origin = System | Canister 'p
datatype 'p queue = Unordered | Queue "'p queue_origin" 'p
datatype ('p, 'c) entry_point =
  Public_method "method_name" 'p blob
| Callback "'c" "response" "refunded_cycles"
| Heartbeat

datatype ('p, 'c, 'cid) message =
  Call_message "('p, 'c, 'cid) call_origin" 'p 'p method_name blob nat "'p queue"
| Func_message 'cid 'p "('p, 'c) entry_point" "'p queue"
| Response_message "('p, 'c, 'cid) call_origin" "response" nat

(* API requests *)

type_synonym path = "blob list"
record 'p StateRead =
  nonce :: blob
  ingress_expiry :: nat
  sender :: 'p
  paths :: "path list"
type_synonym 'p APIReadRequest = "'p request + 'p StateRead"

record ('p, 'pk, 'sig) sender_delegation =
  pubkey :: 'pk
  targets :: "'p list option"
  senders :: "'p list option"
  expiration :: timestamp
record ('p, 'pk, 'sig) signed_delegation =
  delegation :: "('p, 'pk, 'sig) sender_delegation"
  signature :: "'sig"

record ('p, 'pk, 'sig) envelope =
  content :: "'p request + 'p APIReadRequest"
  sender_pubkey :: "'pk option"
  sender_sig :: "'sig option"
  sender_delegation :: "('p, 'pk, 'sig) signed_delegation list"

datatype request_status = Received | Processing | Rejected reject_code String.literal | Replied blob | Done

(* The system state *)

record ('p, 'w, 'sm, 'c) can_state_rec =
  wasm_state :: 'w
  module :: "('p, 'w, 'sm, 'c) canister_module"
  raw_module :: blob
  public_custom_sections :: "(String.literal, blob) list_map"
  private_custom_sections :: "(String.literal, blob) list_map"
type_synonym ('p, 'w, 'sm, 'c) can_state = "('p, 'w, 'sm, 'c) can_state_rec option"
datatype ('p, 'c, 'cid) can_status = Running | Stopping "(('p, 'c, 'cid) call_origin \<times> nat) list" | Stopped
record ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic =
  requests :: "('p request, request_status) list_map"
  canisters :: "('p, ('p, 'w, 'sm, 'c) can_state) list_map"
  controllers :: "('p,  'p set) list_map"
  freezing_threshold :: "('p,  nat) list_map"
  canister_status :: "('p,  ('p, 'c, 'cid) can_status) list_map"
  time :: "('p,  timestamp) list_map"
  balances :: "('p,  nat) list_map"
  certified_data :: "('p,  blob) list_map"
  system_time :: timestamp
  call_contexts :: "('cid, ('p, 'c, 'cid) call_ctxt) list_map"
  messages :: "('p, 'c, 'cid) message list"
  subnets :: "('p \<times> 'pk \<times> 'sk \<times> (('p \<times> 'p) list)) list"
  public_root_key :: 'pk
  secret_root_key :: 'sk

fun simple_status :: "('p, 'c, 'cid) can_status \<Rightarrow> status" where
  "simple_status can_status.Running = status.Running"
| "simple_status (can_status.Stopping _) = status.Stopping"
| "simple_status can_status.Stopped = status.Stopped"

(* Initial state *)

definition initial_ic :: "nat \<Rightarrow> 'pk \<Rightarrow> 'sk \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "initial_ic t pk sk = \<lparr>requests = list_map_empty,
    canisters = list_map_empty,
    controllers = list_map_empty,
    freezing_threshold = list_map_empty,
    canister_status = list_map_empty,
    time = list_map_empty,
    balances = list_map_empty,
    certified_data = list_map_empty,
    system_time = t,
    call_contexts = list_map_empty,
    messages = [],
    subnets = [],
    public_root_key = pk,
    secret_root_key = sk\<rparr>"

(* Invariants *)

definition ic_can_status_inv :: "('p, 'c, 'cid) can_status set \<Rightarrow> 'cid set \<Rightarrow> bool" where
  "ic_can_status_inv st c = (\<forall>can_status \<in> st.
    case can_status of Stopping os \<Rightarrow> \<forall>(orig, cycles) \<in> set os. (case orig of
      From_canister ctxt_id _ \<Rightarrow> ctxt_id \<in> c
      | _ \<Rightarrow> True)
    | _ \<Rightarrow> True)"

lemma ic_can_status_inv_mono1: "ic_can_status_inv x y \<Longrightarrow>
  z \<subseteq> x \<union> {can_status.Running, can_status.Stopped} \<Longrightarrow>
  ic_can_status_inv z y"
  by (fastforce simp: ic_can_status_inv_def split: can_status.splits call_origin.splits)

lemma ic_can_status_inv_mono2: "ic_can_status_inv x y \<Longrightarrow>
  y \<subseteq> z \<Longrightarrow>
  ic_can_status_inv x z"
  by (force simp: ic_can_status_inv_def split: can_status.splits call_origin.splits)

lemma ic_can_status_inv_stopping: "ic_can_status_inv x y \<Longrightarrow>
  (\<And>ctxt_id c. os = From_canister ctxt_id c \<Longrightarrow> ctxt_id \<in> y) \<Longrightarrow>
  z \<subseteq> x \<union> {can_status.Stopping [(os, cyc)]} \<Longrightarrow>
  ic_can_status_inv z y"
  by (fastforce simp: ic_can_status_inv_def split: can_status.splits call_origin.splits)

lemma ic_can_status_inv_stopping_app: "ic_can_status_inv x y \<Longrightarrow>
  can_status.Stopping w \<in> x \<Longrightarrow>
  (\<And>ctxt_id c. os = From_canister ctxt_id c \<Longrightarrow> ctxt_id \<in> y) \<Longrightarrow>
  z \<subseteq> x \<union> {can_status.Stopping (w @ [(os, cyc)])} \<Longrightarrow>
  ic_can_status_inv z y"
  by (force simp: ic_can_status_inv_def split: can_status.splits call_origin.splits dest!: subsetD[where ?A=z])

lemma ic_can_status_inv_del: "ic_can_status_inv x z \<Longrightarrow>
  (\<And>os other_ctxt_id c cyc. Stopping os \<in> x \<Longrightarrow> (From_canister other_ctxt_id c, cyc) \<in> set os \<Longrightarrow> ctxt_id \<noteq> other_ctxt_id) \<Longrightarrow>
  ic_can_status_inv x (z - {ctxt_id})"
  by (fastforce simp: ic_can_status_inv_def split: can_status.splits call_origin.splits)

definition ic_inv :: "('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_inv S = ((\<forall>msg \<in> set (messages S). case msg of
    Call_message (From_canister ctxt_id _) _ _ _ _ _ _ \<Rightarrow> ctxt_id \<in> list_map_dom (call_contexts S)
  | Response_message (From_canister ctxt_id _) _ _ \<Rightarrow> ctxt_id \<in> list_map_dom (call_contexts S)
  | _ \<Rightarrow> True) \<and>
  (\<forall>ctxt \<in> list_map_range (call_contexts S). call_ctxt_needs_to_respond ctxt \<longrightarrow>
    (case call_ctxt_origin ctxt of From_canister ctxt_id _ \<Rightarrow> ctxt_id \<in> list_map_dom (call_contexts S)
    | _ \<Rightarrow> True)) \<and>
  ic_can_status_inv (list_map_range (canister_status S)) (list_map_dom (call_contexts S)))"

lemma ic_initial_inv: "ic_inv (initial_ic t pk sk)"
  by (auto simp: ic_inv_def ic_can_status_inv_def initial_ic_def split: call_origin.splits)

(* Candid *)

datatype 'p candid =
    Candid_nat nat
  | Candid_text String.literal
  | Candid_blob (candid_unwrap_blob: blob)
  | Candid_opt "'p candid"
  | Candid_vec "'p candid list"
  | Candid_record "(String.literal, 'p candid) list_map"
  | Candid_null
  | Candid_empty

fun candid_is_blob :: "'p candid \<Rightarrow> bool" where
  "candid_is_blob (Candid_blob b) = True"
| "candid_is_blob _ = False"

fun candid_lookup :: "'p candid \<Rightarrow> String.literal \<Rightarrow> 'p candid option" where
  "candid_lookup (Candid_record m) s = list_map_get m s"
| "candid_lookup _ _ = None"

(* Certification *)

datatype htree
  = Empty
  | Fork htree htree
  | Labeled blob htree
  | Leaf blob
  | Pruned blob

datatype ('p, 'sig) certificate = Certificate (cert_tree: htree) (cert_signature: 'sig) (cert_delegation: "('p, 'sig) delegation option")
and ('p, 'sig) delegation = Delegation (subnet_id: 'p) (certificate: "('p, 'sig) certificate")

datatype 'a lookup_result
  = Absent
  | Found 'a
  | Unknown
  | Error

fun flatten_forks :: "htree \<Rightarrow> htree list" where
  "flatten_forks Empty = []"
| "flatten_forks (Fork t1 t2) = flatten_forks t1 @ flatten_forks t2"
| "flatten_forks t = [t]"

inductive absent_label :: "blob \<Rightarrow> htree list \<Rightarrow> bool" where
  "l1 < l \<Longrightarrow> l < l2 \<Longrightarrow> absent_label l (xs @ Labeled l1 _ # Labeled l2 _ # ys)"
| "l < l2 \<Longrightarrow> absent_label l (Labeled l2 _ # ys)"
| "l1 < l \<Longrightarrow> absent_label l (xs @ [Labeled l1 _])"
| "absent_label l []"

fun find_label :: "blob \<Rightarrow> htree list \<Rightarrow> htree lookup_result" where
  "find_label l ts = (if absent_label l ts then Absent else fold (\<lambda>t r. case t of Labeled l1 t1 \<Rightarrow> if l = l1 then Found t1 else r | _ \<Rightarrow> r) ts Unknown)"

fun lookup_path :: "blob list \<Rightarrow> htree \<Rightarrow> blob lookup_result" where
  "lookup_path [] Empty = Absent"
| "lookup_path [] (Leaf v) = Found v"
| "lookup_path [] (Pruned _) = Unknown"
| "lookup_path [] (Labeled _ _) = Error"
| "lookup_path [] (Fork _ _) = Error"
| "lookup_path (l#ls) tree = (case find_label l (flatten_forks tree) of
    Absent \<Rightarrow> Absent
  | Unknown \<Rightarrow> Unknown
  | Error \<Rightarrow> Error
  | Found subtree \<Rightarrow> lookup_path ls subtree)"

definition lookup :: "blob list \<Rightarrow> ('p, 'sig) certificate \<Rightarrow> blob lookup_result" where
  "lookup p cert = lookup_path p (cert_tree cert)"

fun htree_measure :: "htree \<Rightarrow> nat" where
  "htree_measure Empty = 1"
| "htree_measure (Leaf v) = 1"
| "htree_measure (Pruned _) = 1"
| "htree_measure (Labeled _ t) = Suc (Suc (htree_measure t))"
| "htree_measure (Fork t1 t2) = htree_measure t1 + htree_measure t2"

fun size_list' :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "size_list' sz [] = 0"
| "size_list' sz (x # xs) = sz x + size_list' sz xs"

lemma size_list'_app[simp]: "size_list' sz (xs @ ys) = size_list' sz xs + size_list' sz ys"
  by (induction xs) auto

lemma size_list'_inD: "x \<in> set xs \<Longrightarrow> sz x \<le> size_list' sz xs"
  by (induction xs) auto

lemma size_list'_size_flatten_forks: "size_list' htree_measure (flatten_forks t) < Suc (htree_measure t)"
  by (induction t) auto

definition ssorted :: "('a :: linorder) list \<Rightarrow> bool" where
  "ssorted xs \<longleftrightarrow> sorted xs \<and> distinct xs"

function well_formed :: "htree \<Rightarrow> bool" and well_formed_forest :: "htree list \<Rightarrow> bool" where
  "well_formed t = ((case t of Leaf _ \<Rightarrow> True | _ \<Rightarrow> False) \<or> well_formed_forest (flatten_forks t))"
| "well_formed_forest ts = (ssorted (List.map_filter (\<lambda>t. case t of Labeled l _ \<Rightarrow> Some l | _ \<Rightarrow> None) ts) \<and> (\<forall>t \<in> set ts. (case t of Labeled _ t' \<Rightarrow> well_formed t')) \<and> (\<forall>t \<in> set ts. (case t of Leaf _ \<Rightarrow> False | _ \<Rightarrow> True)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>v. case v of Inl t \<Rightarrow> Suc (htree_measure t) | Inr ts \<Rightarrow> size_list' htree_measure ts)")
     (auto intro: size_list'_size_flatten_forks dest: size_list'_inD[where ?sz=htree_measure])

fun all_paths :: "path \<Rightarrow> htree \<Rightarrow> path set" where
  "all_paths p Empty = {}"
| "all_paths p (Fork t1 t2) = all_paths p t1 \<union> all_paths p t2"
| "all_paths p (Labeled l t) = all_paths (p @ [l]) t"
| "all_paths p (Leaf v) = {p}"
| "all_paths p (Pruned t) = {}"

(* Certification code *)

fun witness_pair :: "blob \<Rightarrow> htree list \<Rightarrow> bool" where
  "witness_pair l (Labeled l1 t1 # Labeled l2 t2 # ys) = ((l1 < l \<and> l < l2) \<or> witness_pair l (Labeled l2 t2 # ys))"
| "witness_pair l (x # ys) = witness_pair l ys"
| "witness_pair l [] = False"

lemma witness_pair_iff: "witness_pair l (xs :: htree list) \<longleftrightarrow> (\<exists>ys l1 t1 l2 t2 zs. xs = ys @ Labeled l1 t1 # Labeled l2 t2 # zs \<and> l1 < l \<and> l < l2)"
proof (induction xs rule: induct_list012)
  case (3 x y zs)
  have "\<exists>l1 t1 l2 t2. x = Labeled l1 t1 \<and> y = Labeled l2 t2 \<and> l1 < l \<and> l < l2" if "witness_pair l (x # y # zs)" "\<not>witness_pair l (y # zs)"
    using that
    by (cases x; cases y) auto
  moreover have "l1 < l \<Longrightarrow> l < l2 \<Longrightarrow> witness_pair l (ys @ Labeled l1 t1 # Labeled l2 t2 # zs)" for ys :: "htree list" and l1 t1 l2 t2 zs
  proof (induction ys rule: induct_list012)
    case (2 x)
    then show ?case
      by (cases x) auto
  next
    case (3 x y zs)
    then show ?case
      by (cases x; cases y) auto
  qed auto
  ultimately show ?case
    using 3(2)
    apply (cases "witness_pair l (y # zs)")
    apply (metis append_Cons)
    by fastforce
qed auto

lemma witness_pair_absent_label[intro]: "witness_pair l xs \<Longrightarrow> absent_label l xs"
  by (auto simp: witness_pair_iff intro: absent_label.intros)

definition absent_label_code :: "blob \<Rightarrow> htree list \<Rightarrow> bool" where
  "absent_label_code l xs = (case xs of [] \<Rightarrow> True
  | _ \<Rightarrow> (case hd xs of Labeled l2 _ \<Rightarrow> l < l2 | _ \<Rightarrow> False) \<or> (case last xs of Labeled l1 _ \<Rightarrow> l1 < l | _ \<Rightarrow> False) \<or> witness_pair l xs)"

lemma absent_label_code[code]: "absent_label l xs = absent_label_code l xs"
proof (rule iffI)
  assume "absent_label l xs"
  then show "absent_label_code l xs"
  proof (induction l xs rule: absent_label.induct)
    case (1 l1 l l2 xs uu uv ys)
    then have "witness_pair l (xs @ Labeled l1 uu # Labeled l2 uv # ys)"
      by (fastforce simp: witness_pair_iff)
    then show ?case
      by (auto simp: absent_label_code_def split: list.splits)
  next
    case (3 l1 l xs ux)
    then show ?case
      by (auto simp: absent_label_code_def split: list.splits) (metis htree.simps(27) last_ConsR last_snoc)
  qed (auto simp: absent_label_code_def)
next
  assume "absent_label_code l xs"
  then show "absent_label l xs"
    apply (auto simp: absent_label_code_def split: list.splits intro: absent_label.intros)
     apply (auto split: htree.splits if_splits intro: absent_label.intros)
     apply (simp add: absent_label.simps)
    by (metis absent_label.intros(3) append_butlast_last_id last_ConsR list.distinct(1))
qed



(* State transitions *)

context fixes
  CANISTER_ERROR :: reject_code
  and CANISTER_REJECT :: reject_code
  and SYS_FATAL :: reject_code
  and SYS_TRANSIENT :: reject_code
  and MAX_CYCLES_PER_MESSAGE :: nat
  and MAX_CYCLES_PER_RESPONSE :: nat
  and MAX_CANISTER_BALANCE :: nat
  and query_reject_msg :: String.literal
  and query_error_code :: error_code
  and request_error_code :: error_code
  and ic_idle_cycles_burned_rate :: "('p :: linorder, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> 'p \<Rightarrow> nat"
  and self_delimiting_blob_of_nat :: "nat \<Rightarrow> blob"
  and blob_of_nat :: "nat \<Rightarrow> blob"
  and blob_of_text :: "String.literal \<Rightarrow> blob"
  and blob_of_pk :: "'pk \<Rightarrow> blob"
  and blob_of_certificate :: "('p, 'sig) certificate \<Rightarrow> blob"
  and sha_256 :: "blob \<Rightarrow> blob"
  and hash_of_sender_delegation :: "('p, 'pk, 'sig) sender_delegation \<Rightarrow> blob"
  and hash_of_user_request :: "'p request + 'p APIReadRequest \<Rightarrow> blob"
  and blob_of_candid :: "'p candid \<Rightarrow> blob"
  and cbor_of_principals :: "'p list \<Rightarrow> blob"
  and cbor_of_canister_ranges :: "('p \<times> 'p) list \<Rightarrow> blob"
  and parse_cbor_canister_ranges :: "blob \<Rightarrow> ('p \<times> 'p) list option"
  and parse_candid :: "blob \<Rightarrow> 'p candid option"
  and parse_principal :: "blob \<Rightarrow> 'p option"
  and blob_of_principal :: "'p \<Rightarrow> blob"
  and is_system_assigned :: "'p \<Rightarrow> bool"
  and parse_wasm_mod :: "blob \<Rightarrow> ('p, 'w, 'sm, 'c) canister_module option"
  and parse_public_custom_sections :: "blob \<Rightarrow> (String.literal, blob) list_map option"
  and parse_private_custom_sections :: "blob \<Rightarrow> (String.literal, blob) list_map option"
  and principal_list_of_set :: "'p set \<Rightarrow> 'p list"
  and mk_self_authenticating_id :: "'pk \<Rightarrow> 'p"
  and mk_derived_id :: "'p \<Rightarrow> blob \<Rightarrow> 'p"
  and anonymous_id :: 'p
  and ic_principal :: 'p
  and sign :: "'sk \<Rightarrow> blob \<Rightarrow> 'sig"
  and verify_signature :: "'pk \<Rightarrow> 'sig \<Rightarrow> blob \<Rightarrow> bool"
  and verify_bls_signature :: "'pk \<Rightarrow> 'sig \<Rightarrow> blob \<Rightarrow> bool"
  and extract_der :: "blob \<Rightarrow> 'pk option"
begin

(* Candid helper functions *)

definition candid_nested_lookup :: "blob \<Rightarrow> String.literal list \<Rightarrow> 'p candid option" where
  "candid_nested_lookup b = foldl (\<lambda>c s. case c of Some c' \<Rightarrow> candid_lookup c' s | _ \<Rightarrow> None) (parse_candid b)"

definition candid_parse_nat :: "blob \<Rightarrow> String.literal list \<Rightarrow> nat option" where
  "candid_parse_nat b s = (case candid_nested_lookup b s of Some (Candid_nat n') \<Rightarrow> Some n' | _ \<Rightarrow> None)"

definition candid_parse_text :: "blob \<Rightarrow> String.literal list \<Rightarrow> String.literal option" where
  "candid_parse_text b s = (case candid_nested_lookup b s of Some (Candid_text t') \<Rightarrow> Some t' | _ \<Rightarrow> None)"

definition candid_parse_blob :: "blob \<Rightarrow> String.literal list \<Rightarrow> blob option" where
  "candid_parse_blob b s = (case candid_nested_lookup b s of Some (Candid_blob b') \<Rightarrow> Some b' | _ \<Rightarrow> None)"

definition candid_parse_cid :: "blob \<Rightarrow> 'p option" where
  "candid_parse_cid b = (case candid_parse_blob b [STR ''canister_id''] of Some b' \<Rightarrow> parse_principal b' | _ \<Rightarrow> None)"

definition candid_parse_controllers :: "blob \<Rightarrow> 'p set option" where
  "candid_parse_controllers b = (case candid_nested_lookup b [STR ''settings'', STR ''controllers''] of Some (Candid_vec xs) \<Rightarrow>
    if (\<forall>c'' \<in> set xs. candid_is_blob c'' \<and> parse_principal (candid_unwrap_blob c'') \<noteq> None) then
      Some (the ` parse_principal ` candid_unwrap_blob ` set xs)
    else None | _ \<Rightarrow> None)"

fun candid_of_status :: "status \<Rightarrow> 'p candid" where
  "candid_of_status status.Running = Candid_text (STR ''Running'')"
| "candid_of_status status.Stopping = Candid_text (STR ''Stopping'')"
| "candid_of_status status.Stopped = Candid_text (STR ''Stopped'')"

(* Cycles *)

fun carried_cycles :: "('p, 'c, 'cid) call_origin \<Rightarrow> nat" where
  "carried_cycles (From_canister _ _) = MAX_CYCLES_PER_RESPONSE"
| "carried_cycles _ = 0"

fun cycles_reserved :: "('p, 'c) entry_point \<Rightarrow> nat" where
  "cycles_reserved (entry_point.Public_method _ _ _) = MAX_CYCLES_PER_MESSAGE"
| "cycles_reserved (entry_point.Callback _ _ _) = MAX_CYCLES_PER_RESPONSE"
| "cycles_reserved (entry_point.Heartbeat) = MAX_CYCLES_PER_MESSAGE"

fun message_cycles :: "('p, 'c, 'cid) message \<Rightarrow> nat" where
  "message_cycles (Call_message orig _ _ _ _ trans_cycles q) = carried_cycles orig + trans_cycles"
| "message_cycles (Func_message _ _ ep _) = cycles_reserved ep"
| "message_cycles (Response_message orig _ ref_cycles) = carried_cycles orig + ref_cycles"

fun status_cycles :: "('p, 'c, 'cid) can_status \<Rightarrow> nat" where
  "status_cycles (Stopping os) = sum_list (map (carried_cycles \<circ> fst) os) + sum_list (map snd os)"
| "status_cycles _ = 0"

lift_definition call_ctxt_carried_cycles :: "('p, 'c, 'cid) call_ctxt \<Rightarrow> nat" is
  "\<lambda>ctxt. (if needs_to_respond ctxt
    then available_cycles ctxt + carried_cycles (origin ctxt)
    else 0)" .

lemma call_ctxt_respond_carried_cycles[simp]: "call_ctxt_carried_cycles (call_ctxt_respond ctxt) = 0"
  by transfer auto

lemma call_ctxt_carried_cycles: "call_ctxt_carried_cycles ctxt = (if call_ctxt_needs_to_respond ctxt
  then call_ctxt_available_cycles ctxt + carried_cycles (call_ctxt_origin ctxt) else 0)"
  by transfer auto

lemma call_ctxt_delete_carried_cycles[simp]: "call_ctxt_carried_cycles (call_ctxt_delete ctxt) = 0"
  by transfer auto

definition total_cycles :: "('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "total_cycles ic = (
    let cycles_in_balances = list_map_sum_vals id (balances ic) in
    let cycles_in_messages = sum_list (map message_cycles (messages ic)) in
    let cycles_in_contexts = list_map_sum_vals call_ctxt_carried_cycles (call_contexts ic) in
    let cycles_in_statuses = list_map_sum_vals status_cycles (canister_status ic) in
    cycles_in_balances + cycles_in_messages + cycles_in_contexts + cycles_in_statuses)"

(* Accessor functions *)

fun calling_context :: "('p, 'c, 'cid) call_origin \<Rightarrow> 'cid option" where
  "calling_context (From_canister c _) = Some c"
| "calling_context _ = None"

fun message_queue :: "('p, 'c, 'cid) message \<Rightarrow> 'p queue option" where
  "message_queue (Call_message _ _ _ _ _ _ q) = Some q"
| "message_queue (Func_message _ _ _ q) = Some q"
| "message_queue _ = None"

(* Effective canister IDs *)

definition is_effective_canister_id :: "'p request \<Rightarrow> 'p \<Rightarrow> bool" where
  "is_effective_canister_id r p = (if request.canister_id r = ic_principal then
    request.method_name r = STR ''provisional_create_canister_with_cycles'' \<or>
      (case candid_parse_cid (request.arg r) of Some cid \<Rightarrow> cid = p | _ \<Rightarrow> False)
    else request.canister_id r = p)"

(* Envelope Authentication *)

definition domain_sep :: "blob \<Rightarrow> blob" where
  "domain_sep b = (self_delimiting_blob_of_nat (length b)) @ b"

definition delegation_targets :: "('p, 'pk, 'sig) sender_delegation \<Rightarrow> 'p set" where
  "delegation_targets d = (case targets d of None \<Rightarrow> UNIV | Some ts \<Rightarrow> set ts)"

definition delegated_senders :: "('p, 'pk, 'sig) sender_delegation \<Rightarrow> 'p set" where
  "delegated_senders d = (case senders d of None \<Rightarrow> UNIV | Some ts \<Rightarrow> set ts)"

fun verify_delegations :: "('p, 'pk, 'sig) signed_delegation list \<Rightarrow> 'pk \<Rightarrow> nat \<Rightarrow> 'p set \<Rightarrow> 'p \<Rightarrow> ('pk \<times> ('p set)) option" where
  "verify_delegations [] pk t ts u = Some (pk, ts)"
| "verify_delegations (d # ds) pk t ts u = (
    let del = delegation d in
    (if verify_signature pk (signature d) (domain_sep (blob_of_text (STR ''ic-request-auth-delegation'')) @ hash_of_sender_delegation del) \<and>
      expiration del \<ge> t \<and> u \<in> delegated_senders del
    then verify_delegations ds (pubkey del) t (ts \<inter> delegation_targets del) u
    else None)
  )"

definition verify_envelope :: "('p, 'pk, 'sig) envelope \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'p set" where
  "verify_envelope e u t = (if u = anonymous_id then UNIV else
    (case (sender_pubkey e, sender_sig e) of (Some pk, Some sig) \<Rightarrow>
      if u = mk_self_authenticating_id pk then
        (case verify_delegations (sender_delegation e) pk t UNIV u of Some (pk', ts) \<Rightarrow>
          if verify_signature pk' sig (domain_sep (blob_of_text (STR ''ic-request'')) @ hash_of_user_request (content e)) then ts
          else {}
        | _ \<Rightarrow> {})
      else {}
    | _ \<Rightarrow> {}))"

(* Certification *)

fun reconstruct :: "htree \<Rightarrow> blob" where
  "reconstruct Empty = sha_256 (domain_sep (blob_of_text (STR ''ic-hashtree-empty'')))"
| "reconstruct (Fork t1 t2) = sha_256 (domain_sep (blob_of_text (STR ''ic-hashtree-fork'')) @ reconstruct t1 @ reconstruct t2)"
| "reconstruct (Labeled l t) = sha_256 (domain_sep (blob_of_text (STR ''ic-hashtree-labeled'')) @ l @ reconstruct t)"
| "reconstruct (Leaf v) = sha_256 (domain_sep (blob_of_text (STR ''ic-hashtree-leaf'')) @ v)"
| "reconstruct (Pruned h) = h"

function(sequential) verify_cert_impl :: "'pk \<Rightarrow> 'p option \<Rightarrow> ('p, 'sig) certificate \<Rightarrow> bool" and check_delegation :: "'pk \<Rightarrow> 'p option \<Rightarrow> ('p, 'sig) delegation option \<Rightarrow> blob option" where
  "verify_cert_impl rk ECID cert = (case check_delegation rk ECID (cert_delegation cert) of
    Some der_key \<Rightarrow> (case extract_der der_key of
      Some bls_key \<Rightarrow> verify_bls_signature bls_key (cert_signature cert) (domain_sep (blob_of_text (STR ''ic-state-root'')) @ reconstruct (cert_tree cert))
    | _ \<Rightarrow> False)
  | _ \<Rightarrow> False)"
| "check_delegation rk ECID None = Some (blob_of_pk rk)"
| "check_delegation rk ECID (Some d) =
    (case lookup [blob_of_text (STR ''subnet''), blob_of_principal (subnet_id d), blob_of_text (STR ''canister_ranges'')] (certificate d) of Found b \<Rightarrow>
      (case parse_cbor_canister_ranges b of Some rans \<Rightarrow>
        if (case ECID of Some p \<Rightarrow> \<exists>(a, b) \<in> set rans. a \<le> p \<and> p \<le> b | _ \<Rightarrow> True) \<and> verify_cert_impl rk ECID (certificate d) then
          (case lookup [blob_of_text (STR ''subnet''), blob_of_principal (subnet_id d), blob_of_text (STR ''public_key'')] (certificate d) of
            Found v \<Rightarrow> Some v
          | _ \<Rightarrow> None)
        else None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>v. case v of Inl (_, _, cert) \<Rightarrow> size cert | Inr (_, _, None) \<Rightarrow> 0 | Inr (_, _, Some d) \<Rightarrow> size d)")
  apply auto[1]
  subgoal for rk ECID cert
    by (cases cert) (auto split: option.splits)
  subgoal for rk ECID d
    by (cases d) auto
  done

definition cert_special :: "path set \<Rightarrow> 'p \<Rightarrow> 'p request \<Rightarrow> bool" where
  "cert_special ps ECID req = (
    let hreq = hash_of_user_request (Inl req) in
    ECID = ic_principal \<and>
    request.canister_id req = ic_principal \<and>
    request.method_name req = STR ''provisional_create_canister_with_cycles'' \<and>
    (\<forall>p \<in> ps. p = [blob_of_text (STR ''time'')] \<or> (case p of a # b # _ \<Rightarrow> a = blob_of_text (STR ''request_status'') \<and> b = hreq | _ \<Rightarrow> False)))"

definition verify_cert :: "'pk \<Rightarrow> 'p \<Rightarrow> 'p request option \<Rightarrow> ('p, 'sig) certificate \<Rightarrow> bool" where
  "verify_cert rk ECID r cert = (case r of None \<Rightarrow>
    verify_cert_impl rk (Some ECID) cert
  | Some req \<Rightarrow> cert_special (all_paths [] (cert_tree cert)) ECID req \<and>
      (case lookup [blob_of_text (STR ''request_status''), hash_of_user_request (Inl req), blob_of_text (STR ''reply'')] cert of
        Found v \<Rightarrow> (case candid_parse_cid v of Some ECID' \<Rightarrow> verify_cert_impl rk (Some ECID') cert | _ \<Rightarrow> False)
      | _ \<Rightarrow> verify_cert_impl rk None cert)
  )"



(* System transition: API Request submission [DONE] *)

definition ic_freezing_limit :: "('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> 'p \<Rightarrow> nat" where
  "ic_freezing_limit S cid = ic_idle_cycles_burned_rate S cid * (the (list_map_get (freezing_threshold S) cid)) div (24 * 60 * 60)"

definition request_submission_pre :: "('p, 'pk, 'sig) envelope \<Rightarrow> 'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "request_submission_pre E ECID S = (case content E of Inl req \<Rightarrow>
    request.canister_id req \<in> verify_envelope E (request.sender req) (system_time S) \<and>
    req \<notin> list_map_dom (requests S) \<and>
    system_time S \<le> request.ingress_expiry req \<and>
    is_effective_canister_id req ECID \<and>
    (
      (
        request.canister_id req = ic_principal \<and>
        (case candid_parse_cid (request.arg req) of Some cid \<Rightarrow>
          (case list_map_get (controllers S) cid of Some ctrls \<Rightarrow>
            request.sender req \<in> ctrls \<and>
            request.method_name req \<in> {STR ''install_code'', STR ''uninstall_code'', STR ''update_settings'',
              STR ''start_canister'', STR ''stop_canister'',
              STR ''canister_status'', STR ''delete_canister'',
              STR ''provisional_create_canister_with_cycles'', STR ''provisional_top_up_canister''}
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False)
      )
    \<or>
      (
        request.canister_id req \<noteq> ic_principal \<and>
        (case (list_map_get (canisters S) (request.canister_id req), list_map_get (time S) (request.canister_id req), list_map_get (balances S) (request.canister_id req), list_map_get (canister_status S) (request.canister_id req)) of
          (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
          let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S (request.canister_id req), certificate = None, status = simple_status can_status\<rparr> in
          (case canister_module_inspect_message (module can) (request.method_name req, wasm_state can, request.arg req, request.sender req, env) of Inr ret \<Rightarrow>
            cycles_return.return ret = Accept \<and> cycles_return.cycles_used ret \<le> bal
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False)
      )
    )
  | _ \<Rightarrow> False)"

definition request_submission_post :: "('p, 'pk, 'sig) envelope \<Rightarrow> 'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "request_submission_post E ECID S = (
    let req = projl (content E);
    cid = request.canister_id req;
    balances = (if cid \<noteq> ic_principal then
      (case (list_map_get (canisters S) cid, list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
        (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
        let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
        (case canister_module_inspect_message (module can) (request.method_name req, wasm_state can, request.arg req, request.sender req, env) of Inr ret \<Rightarrow>
          list_map_set (balances S) cid (bal - cycles_return.cycles_used ret)))
      else balances S) in
    S\<lparr>requests := list_map_set (requests S) req Received, balances := balances\<rparr>)"

definition request_submission_burned_cycles :: "('p, 'pk, 'sig) envelope \<Rightarrow> 'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "request_submission_burned_cycles E ECID S = (
    let req = projl (content E);
    cid = request.canister_id req in
    (if request.canister_id req \<noteq> ic_principal then
      (case (list_map_get (canisters S) (request.canister_id req), list_map_get (time S) (request.canister_id req), list_map_get (balances S) (request.canister_id req), list_map_get (canister_status S) (request.canister_id req)) of
        (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
        let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S (request.canister_id req), certificate = None, status = simple_status can_status\<rparr> in
        (case canister_module_inspect_message (module can) (request.method_name req, wasm_state can, request.arg req, request.sender req, env) of Inr ret \<Rightarrow>
          cycles_return.cycles_used ret))
      else 0))"

lemma request_submission_cycles_inv:
  assumes "request_submission_pre E ECID S"
  shows "total_cycles S = total_cycles (request_submission_post E ECID S) + request_submission_burned_cycles E ECID S"
proof -
  obtain req where req_def: "content E = Inl req"
    using assms
    by (auto simp: request_submission_pre_def split: sum.splits)
  {
    assume "request.canister_id req \<noteq> ic_principal"
    then have "(case (list_map_get (canisters S) (request.canister_id req), list_map_get (time S) (request.canister_id req), list_map_get (balances S) (request.canister_id req), list_map_get (canister_status S) (request.canister_id req)) of
      (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S (request.canister_id req), certificate = None, status = simple_status can_status\<rparr> in
      (case canister_module_inspect_message (module can) (request.method_name req, wasm_state can, request.arg req, request.sender req, env) of Inr ret \<Rightarrow>
        cycles_return.return ret = Accept \<and> cycles_return.cycles_used ret \<le> bal
      | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"
      using assms
      by (auto simp: request_submission_pre_def req_def split: option.splits sum.splits prod.splits)
    then have ?thesis
      using list_map_sum_in_ge[where ?f="balances S" and ?g=id and ?x="request.canister_id req"]
      by (auto simp: request_submission_pre_def request_submission_post_def request_submission_burned_cycles_def total_cycles_def req_def list_map_sum_in[where ?f="balances S"]
          split: option.splits sum.splits)
  }
  then show ?thesis
    by (auto simp: request_submission_pre_def request_submission_post_def request_submission_burned_cycles_def total_cycles_def req_def)
qed

lemma request_submission_ic_inv:
  assumes "request_submission_pre E ECID S" "ic_inv S"
  shows "ic_inv (request_submission_post E ECID S)"
  using assms
  by (auto simp: ic_inv_def request_submission_pre_def request_submission_post_def Let_def
      split: sum.splits message.splits call_origin.splits)



(* System transition: Request rejection [DONE] *)

definition request_rejection_pre :: "'p request \<Rightarrow> reject_code \<Rightarrow> String.literal \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "request_rejection_pre req code msg S = (list_map_get (requests S) req = Some Received \<and> (code = SYS_FATAL \<or> code = SYS_TRANSIENT))"

definition request_rejection_post :: "'p request \<Rightarrow> reject_code \<Rightarrow> String.literal \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "request_rejection_post req code msg S = S\<lparr>requests := list_map_set (requests S) req (Rejected code msg)\<rparr>"

lemma request_rejection_cycles_inv:
  assumes "request_rejection_pre req code msg S"
  shows "total_cycles S = total_cycles (request_rejection_post req code msg S)"
  by (auto simp: request_rejection_pre_def request_rejection_post_def total_cycles_def)

lemma request_rejection_ic_inv:
  assumes "request_rejection_pre req code msg S" "ic_inv S"
  shows "ic_inv (request_rejection_post req code msg S)"
  using assms
  by (auto simp: ic_inv_def request_rejection_pre_def request_rejection_post_def Let_def
      split: sum.splits message.splits call_origin.splits)



(* System transition: Initiating canister calls [DONE] *)

definition initiate_canister_call_pre :: "'p request \<Rightarrow>
  ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "initiate_canister_call_pre req S = (list_map_get (requests S) req = Some Received \<and>
    system_time S \<le> request.ingress_expiry req \<and>
    request.canister_id req \<in> list_map_dom (canisters S))"

definition initiate_canister_call_post :: "'p request \<Rightarrow>
  ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow>
  ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "initiate_canister_call_post req S =
    S\<lparr>requests := list_map_set (requests S) req Processing, messages :=
      Call_message (From_user req) (request.sender req) (request.canister_id req) (request.method_name req)
      (request.arg req) 0 Unordered # messages S\<rparr>"

lemma initiate_canister_call_cycles_inv:
  assumes "initiate_canister_call_pre R S"
  shows "total_cycles S = total_cycles (initiate_canister_call_post R S)"
  by (auto simp: initiate_canister_call_pre_def initiate_canister_call_post_def total_cycles_def)

lemma initiate_canister_call_ic_inv:
  assumes "initiate_canister_call_pre R S" "ic_inv S"
  shows "ic_inv (initiate_canister_call_post R S)"
  using assms
  by (auto simp: ic_inv_def initiate_canister_call_pre_def initiate_canister_call_post_def Let_def
      split: sum.splits message.splits call_origin.splits)



(* System transition: Calls to stopped/stopping/frozen canisters are rejected [DONE] *)

definition call_reject_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "call_reject_pre n S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      (case list_map_get (canister_status S) cee of Some Stopped \<Rightarrow> True
      | Some (Stopping l) \<Rightarrow> True
      | _ \<Rightarrow> (case list_map_get (balances S) cee of Some bal \<Rightarrow> bal < ic_freezing_limit S cee | _ \<Rightarrow> False))
    | _ \<Rightarrow> False))"

definition call_reject_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "call_reject_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (response.Reject CANISTER_ERROR (STR ''canister not running'')) trans_cycles]\<rparr>)"

lemma call_reject_cycles_inv:
  assumes "call_reject_pre n S"
  shows "total_cycles S = total_cycles (call_reject_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: call_reject_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: call_reject_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: call_reject_pre_def call_reject_post_def total_cycles_def Let_def msgs split: message.splits option.splits)
qed

lemma call_reject_ic_inv:
  assumes "call_reject_pre n S" "ic_inv S"
  shows "ic_inv (call_reject_post n S)"
  using assms
  by (auto simp: ic_inv_def call_reject_pre_def call_reject_post_def Let_def
      split: sum.splits message.splits call_origin.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"])



(* System transition: Call context creation: Public entry points [DONE] *)

definition call_context_create_pre :: "nat \<Rightarrow> 'cid
  \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "call_context_create_pre n ctxt_id S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
      (case list_map_get (canisters S) cee of Some (Some can) \<Rightarrow> True | _ \<Rightarrow> False) \<and>
      list_map_get (canister_status S) cee = Some Running \<and>
      (case list_map_get (balances S) cee of Some bal \<Rightarrow> bal \<ge> ic_freezing_limit S cee + MAX_CYCLES_PER_MESSAGE | None \<Rightarrow> False) \<and>
      ctxt_id \<notin> list_map_dom (call_contexts S)
    | _ \<Rightarrow> False))"

lift_definition create_call_ctxt :: "'p \<Rightarrow> ('p, 'c, 'cid) call_origin \<Rightarrow> nat \<Rightarrow>
  ('p, 'c, 'cid) call_ctxt" is
  "\<lambda>cee orig trans_cycles. \<lparr>canister = cee, origin = orig, needs_to_respond = True, deleted = False, available_cycles = trans_cycles\<rparr>"
  by auto

lemma create_call_ctxt_origin[simp]: "call_ctxt_origin (create_call_ctxt cee orig trans_cycles) = orig"
  by transfer auto

lemma create_call_ctxt_carried_cycles[simp]: "call_ctxt_carried_cycles (create_call_ctxt cee orig trans_cycles) = carried_cycles orig + trans_cycles"
  by transfer auto

definition call_context_create_post :: "nat \<Rightarrow> 'cid \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "call_context_create_post n ctxt_id S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    case list_map_get (balances S) cee of Some bal \<Rightarrow>
    S\<lparr>messages := list_update (messages S) n (Func_message ctxt_id cee (Public_method mn cer a) q),
      call_contexts := list_map_set (call_contexts S) ctxt_id (create_call_ctxt cee orig trans_cycles),
      balances := list_map_set (balances S) cee (bal - MAX_CYCLES_PER_MESSAGE)\<rparr>)"

lemma call_context_create_cycles_inv:
  assumes "call_context_create_pre n ctxt_id S"
  shows "total_cycles S = total_cycles (call_context_create_post n ctxt_id S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: call_context_create_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ m # younger) ! n = m"
    and msgs_upd: "(older @ Call_message orig cer cee mn a trans_cycles q # younger)[n := m] = older @ m # younger" for m
    using id_take_nth_drop[of n "messages S"] upd_conv_take_nth_drop[of n "messages S"] assms
    by (auto simp: call_context_create_pre_def msg older_def younger_def nth_append)
  show ?thesis
    using assms list_map_sum_in_ge[of "balances S" cee, where ?g=id]
    by (auto simp: call_context_create_pre_def call_context_create_post_def total_cycles_def
        list_map_sum_in[where ?g=id, simplified] list_map_sum_out msgs msgs_upd split: option.splits)
qed

lemma call_context_create_ic_inv:
  assumes "call_context_create_pre n ctxt_id S" "ic_inv S"
  shows "ic_inv (call_context_create_post n ctxt_id S)"
  using assms
  by (auto simp: ic_inv_def call_context_create_pre_def call_context_create_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD
      intro: ic_can_status_inv_mono2)



(* System transition: Call context creation: Heartbeat [DONE] *)

definition call_context_heartbeat_pre :: "'p \<Rightarrow> 'cid \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "call_context_heartbeat_pre cee ctxt_id S = (
    (case list_map_get (canisters S) cee of Some (Some can) \<Rightarrow> True | _ \<Rightarrow> False) \<and>
    list_map_get (canister_status S) cee = Some Running \<and>
    (case list_map_get (balances S) cee of Some bal \<Rightarrow> bal \<ge> ic_freezing_limit S cee + MAX_CYCLES_PER_MESSAGE | _ \<Rightarrow> False) \<and>
    ctxt_id \<notin> list_map_dom (call_contexts S))"

lift_definition create_call_ctxt_heartbeat :: "'p \<Rightarrow> ('p, 'c, 'cid) call_ctxt" is
  "\<lambda>cee. \<lparr>canister = cee, origin = From_heartbeat, needs_to_respond = False, deleted = False, available_cycles = 0\<rparr>"
  by auto

lemma create_call_ctxt_heartbeat_needs_to_respond[simp]: "call_ctxt_needs_to_respond (create_call_ctxt_heartbeat cee) = False"
  by transfer auto

lemma create_call_ctxt_heartbeat_carried_cycles[simp]: "call_ctxt_carried_cycles (create_call_ctxt_heartbeat cee) = 0"
  by transfer auto

definition call_context_heartbeat_post :: "'p \<Rightarrow> 'cid \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "call_context_heartbeat_post cee ctxt_id S =
  (case list_map_get (balances S) cee of Some bal \<Rightarrow>
    S\<lparr>messages := Func_message ctxt_id cee Heartbeat (Queue System cee) # messages S,
    call_contexts := list_map_set (call_contexts S) ctxt_id (create_call_ctxt_heartbeat cee),
    balances := list_map_set (balances S) cee (bal - MAX_CYCLES_PER_MESSAGE)\<rparr>)"

lemma call_context_heartbeat_cycles_inv:
  assumes "call_context_heartbeat_pre cee ctxt_id S"
  shows "total_cycles S = total_cycles (call_context_heartbeat_post cee ctxt_id S)"
  using assms list_map_sum_in_ge[of "balances S" cee, where ?g=id, simplified]
  by (auto simp: call_context_heartbeat_pre_def call_context_heartbeat_post_def total_cycles_def
      list_map_sum_in[where ?g=id, simplified] list_map_sum_out split: option.splits)

lemma call_context_heartbeat_ic_inv:
  assumes "call_context_heartbeat_pre cee ctxt_id S" "ic_inv S"
  shows "ic_inv (call_context_heartbeat_post cee ctxt_id S)"
  using assms
  by (auto simp: ic_inv_def call_context_heartbeat_pre_def call_context_heartbeat_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits
      dest!: in_set_takeD in_set_dropD in_set_updD list_map_range_setD
      intro: ic_can_status_inv_mono2)



(* System transition: Message execution [DONE] *)

fun query_as_update :: "((arg \<times> 'p \<times> env) \<Rightarrow> 'w query_func) \<times> arg \<times> 'p \<times> env \<Rightarrow> ('w, 'p, 'c) update_func" where
  "query_as_update (f, a, e) = (\<lambda>w. case f (a, e) w of Inl t \<Rightarrow> Inl t |
    Inr res \<Rightarrow> Inr \<lparr>update_return.new_state = w, update_return.new_calls = [], update_return.new_certified_data = None,
      update_return.response = Some (query_return.response res), update_return.cycles_accepted = 0, update_return.cycles_used = query_return.cycles_used res\<rparr>)"

fun heartbeat_as_update :: "(env \<Rightarrow> 'w heartbeat_func) \<times> env \<Rightarrow> ('w, 'p, 'c) update_func" where
  "heartbeat_as_update (f, e) = (\<lambda>w. case f e w of Inl t \<Rightarrow> Inl t |
    Inr res \<Rightarrow> Inr \<lparr>update_return.new_state = heartbeat_return.new_state res, update_return.new_calls = [], update_return.new_certified_data = None,
      update_return.response = None, update_return.cycles_accepted = 0, update_return.cycles_used = heartbeat_return.cycles_used res\<rparr>)"

fun exec_function :: "('p, 'c) entry_point \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c) canister_module \<Rightarrow> ('w, 'p, 'c) update_func" where
  "exec_function (entry_point.Public_method mn c a) e bal m = (
    case dispatch_method mn m of Some (Inl upd) \<Rightarrow> upd (a, c, e, bal)
    | Some (Inr query) \<Rightarrow> query_as_update (query, a, c, e)
    | None \<Rightarrow> undefined
  )"
| "exec_function (entry_point.Callback c resp ref_cycles) e bal m =
    canister_module_callbacks m (c, resp, ref_cycles, e, bal)"
| "exec_function (entry_point.Heartbeat) e bal m = heartbeat_as_update ((canister_module_heartbeat m), e)"

definition message_execution_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "message_execution_pre n S =
    (n < length (messages S) \<and> (case messages S ! n of Func_message ctxt_id recv ep q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    (case (list_map_get (canisters S) recv, list_map_get (balances S) recv, list_map_get (canister_status S) recv,
      list_map_get (time S) recv, list_map_get (call_contexts S) ctxt_id) of
      (Some (Some can), Some bal, Some can_status, Some t, Some ctxt) \<Rightarrow> True | _ \<Rightarrow> False)
    | _ \<Rightarrow> False))"

definition message_execution_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "message_execution_post n S = (case messages S ! n of Func_message ctxt_id recv ep q \<Rightarrow>
    (case (list_map_get (canisters S) recv, list_map_get (balances S) recv, list_map_get (canister_status S) recv,
      list_map_get (time S) recv, list_map_get (call_contexts S) ctxt_id) of
      (Some (Some can), Some bal, Some can_status, Some t, Some ctxt) \<Rightarrow> (
        let Mod = module can;
        Is_response = (case ep of Callback _ _ _ \<Rightarrow> True | _ \<Rightarrow> False);
        Env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S recv, certificate = None, status = simple_status can_status\<rparr>;
        Available = call_ctxt_available_cycles ctxt;
        F = exec_function ep Env Available Mod;
        R = F (wasm_state can);
        cyc_used = (case R of Inr res \<Rightarrow> update_return.cycles_used res | Inl trap \<Rightarrow> cycles_return.cycles_used trap);
        (cycles_accepted_res, new_calls_res) = (case R of Inr res \<Rightarrow> (update_return.cycles_accepted res, update_return.new_calls res));
        New_balance = bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)
          - (cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res));
        no_response = (case R of Inr result \<Rightarrow> update_return.response result = None) in
        if \<not>isl R \<and> cyc_used \<le> (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
          cycles_accepted_res \<le> Available \<and>
          cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res) \<le>
            bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
          New_balance \<ge> (if Is_response then 0 else ic_freezing_limit S recv) \<and>
          (no_response \<or> call_ctxt_needs_to_respond ctxt) then
          (let result = projr R;
            new_call_to_message = (\<lambda>call. Call_message (From_canister ctxt_id (method_call.callback call)) recv
              (method_call.callee call) (method_call.method_name call) (method_call.arg call) (method_call.transferred_cycles call) (Queue (Canister recv) (method_call.callee call)));
            response_messages = (case update_return.response result of None \<Rightarrow> []
              | Some resp \<Rightarrow> [Response_message (call_ctxt_origin ctxt) resp (Available - cycles_accepted_res)]);
            messages = take n (messages S) @ drop (Suc n) (messages S) @ map new_call_to_message new_calls_res @ response_messages;
            new_ctxt = (case update_return.response result of
              None \<Rightarrow> call_ctxt_deduct_cycles cycles_accepted_res ctxt
            | Some _ \<Rightarrow> call_ctxt_respond ctxt);
            certified_data = (case new_certified_data result of None \<Rightarrow> certified_data S
              | Some cd \<Rightarrow> list_map_set (certified_data S) recv cd)
            in S\<lparr>canisters := list_map_set (canisters S) recv (Some (can\<lparr>wasm_state := update_return.new_state result\<rparr>)),
              messages := messages, call_contexts := list_map_set (call_contexts S) ctxt_id new_ctxt,
              certified_data := certified_data, balances := list_map_set (balances S) recv New_balance\<rparr>)
        else S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
          balances := list_map_set (balances S) recv ((bal + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE))
            - min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE))\<rparr>))
    | _ \<Rightarrow> undefined)"

definition message_execution_burned_cycles :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "message_execution_burned_cycles n S = (case messages S ! n of Func_message ctxt_id recv ep q \<Rightarrow>
    (case (list_map_get (canisters S) recv, list_map_get (balances S) recv, list_map_get (canister_status S) recv,
      list_map_get (time S) recv, list_map_get (call_contexts S) ctxt_id) of
      (Some (Some can), Some bal, Some can_status, Some t, Some ctxt) \<Rightarrow> (
        let Mod = module can;
        Is_response = (case ep of Callback _ _ _ \<Rightarrow> True | _ \<Rightarrow> False);
        Env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S recv, certificate = None, status = simple_status can_status\<rparr>;
        Available = call_ctxt_available_cycles ctxt;
        F = exec_function ep Env Available Mod;
        R = F (wasm_state can);
        cyc_used = (case R of Inr res \<Rightarrow> update_return.cycles_used res | Inl trap \<Rightarrow> cycles_return.cycles_used trap) in
        min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)
      )))"

lemma message_execution_cycles_monotonic:
  assumes pre: "message_execution_pre n S"
  shows "total_cycles S = total_cycles (message_execution_post n S) + message_execution_burned_cycles n S"
proof -
  obtain ctxt_id recv ep q can bal can_status t ctxt where msg: "messages S ! n = Func_message ctxt_id recv ep q"
    and prod: "list_map_get (canisters S) recv = Some (Some can)"
    "list_map_get (balances S) recv = Some bal"
    "list_map_get (canister_status S) recv = Some can_status"
    "list_map_get (time S) recv = Some t"
    "list_map_get (call_contexts S) ctxt_id = Some ctxt"
    using pre
    by (auto simp: message_execution_pre_def split: message.splits option.splits)
  define Mod where "Mod = can_state_rec.module can"
  define Is_response where "Is_response = (case ep of Callback _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  define Env :: "env" where "Env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S recv, certificate = None, status = simple_status can_status\<rparr>"
  define Available where "Available = call_ctxt_available_cycles ctxt"
  define F where "F = exec_function ep Env Available Mod"
  define R where "R = F (wasm_state can)"
  define cyc_used where "cyc_used = (case R of Inr res \<Rightarrow> update_return.cycles_used res | Inl trap \<Rightarrow> cycles_return.cycles_used trap)"
  obtain cycles_accepted_res new_calls_res where res: "(cycles_accepted_res, new_calls_res) = (case R of Inr res \<Rightarrow> (update_return.cycles_accepted res, new_calls res))"
    by (cases "(case R of Inr res \<Rightarrow> (update_return.cycles_accepted res, new_calls res))") auto
  define New_balance where "New_balance = bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)
    - (cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res))"
  define no_response where "no_response = (case R of Inr result \<Rightarrow> update_return.response result = None)"
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Func_message ctxt_id recv ep q # younger"
    "take n older = older" "drop (Suc n) older = []"
    "take (n - length older) ws = []" "drop (Suc n - length older) (w # ws) = ws"
    for w and ws :: "('p, 'c, 'cid) message list"
    using id_take_nth_drop[of n "messages S"] pre
    by (auto simp: message_execution_pre_def msg older_def younger_def)
  note lm = list_map_sum_in[OF prod(2), where ?g=id, simplified] list_map_sum_in_ge[OF prod(2), where ?g=id, simplified]
    list_map_sum_in[OF prod(5), where ?g=call_ctxt_carried_cycles] list_map_sum_in_ge[OF prod(5), where ?g=call_ctxt_carried_cycles]
  define S'' where "S'' = S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
    balances := list_map_set (balances S) recv ((bal + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)) - min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE))\<rparr>"
  define cond where "cond = (\<not>isl R \<and> cyc_used \<le> (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
    cycles_accepted_res \<le> Available \<and>
    cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res) \<le>
      bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
    New_balance \<ge> (if Is_response then 0 else ic_freezing_limit S recv) \<and>
    (no_response \<or> call_ctxt_needs_to_respond ctxt))"
  have reserved: "(if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) = cycles_reserved ep"
    by (auto simp: Is_response_def split: entry_point.splits)
  show ?thesis
  proof (cases cond)
    case False
    have "message_execution_post n S = S''"
      "message_execution_burned_cycles n S = min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)"
      using False
      by (simp_all add: message_execution_post_def message_execution_burned_cycles_def Let_def msg prod
          Mod_def[symmetric] Is_response_def[symmetric] Env_def[symmetric] Available_def[symmetric] F_def[symmetric] R_def[symmetric] cyc_used_def[symmetric] res[symmetric]
          New_balance_def[symmetric] no_response_def[symmetric] S''_def[symmetric] cond_def[symmetric] del: min_less_iff_conj split del: if_split)
    then show ?thesis
      using lm(2)
      by (auto simp: total_cycles_def S''_def msgs lm(1) reserved)
  next
    case True
    define result where "result = projr R"
    have R_Inr: "R = Inr result"
      using True
      by (auto simp: cond_def result_def split: option.splits)
    define response_messages where "response_messages = (case update_return.response result of None \<Rightarrow> []
      | Some resp \<Rightarrow> [Response_message (call_ctxt_origin ctxt) resp (Available - cycles_accepted_res)])"
    define new_call_to_message :: "('p, 'c) method_call \<Rightarrow> ('p, 'c, 'cid) message" where
      "new_call_to_message = (\<lambda>call. Call_message (From_canister ctxt_id (callback call)) recv
        (callee call) (method_call.method_name call) (method_call.arg call) (transferred_cycles call) (Queue (Canister recv) (callee call)))"
    define messages where "messages = take n (ic.messages S) @ drop (Suc n) (ic.messages S) @ map new_call_to_message new_calls_res @ response_messages"
    define new_ctxt where "new_ctxt = (case update_return.response result of
        None \<Rightarrow> call_ctxt_deduct_cycles cycles_accepted_res ctxt
      | Some _ \<Rightarrow> call_ctxt_respond ctxt)"
    define certified_data where "certified_data = (case new_certified_data result of None \<Rightarrow> ic.certified_data S
      | Some cd \<Rightarrow> list_map_set (ic.certified_data S) recv cd)"
    define S' where "S' = S\<lparr>canisters := list_map_set (canisters S) recv (Some (can\<lparr>wasm_state := update_return.new_state result\<rparr>)),
      messages := messages, call_contexts := list_map_set (call_contexts S) ctxt_id new_ctxt,
      certified_data := certified_data, balances := list_map_set (balances S) recv New_balance\<rparr>"
    have cycles_accepted_res_def: "cycles_accepted_res = update_return.cycles_accepted result"
      and new_calls_res_def: "new_calls_res = new_calls result"
      using res
      by (auto simp: R_Inr)
    have no_response: "no_response = (update_return.response result = None)"
      by (auto simp: no_response_def R_Inr)
    have msg_exec: "message_execution_post n S = S'"
      and lost: "message_execution_burned_cycles n S = min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)"
      using True
      by (simp_all add: message_execution_post_def message_execution_burned_cycles_def Let_def msg prod
          Mod_def[symmetric] Is_response_def[symmetric] Env_def[symmetric] Available_def[symmetric] F_def[symmetric] R_def[symmetric] cyc_used_def[symmetric] res[symmetric]
          New_balance_def[symmetric] no_response_def[symmetric] S''_def[symmetric] cond_def[symmetric]
          messages_def[symmetric] new_ctxt_def[symmetric] certified_data_def[symmetric] S'_def[symmetric]
          result_def[symmetric] response_messages_def[symmetric] new_call_to_message_def[symmetric]
          del: min_less_iff_conj split del: if_split)
    have "message_cycles \<circ> new_call_to_message = (\<lambda>c. MAX_CYCLES_PER_RESPONSE + transferred_cycles c)" for c :: "('p, 'c) method_call"
      by (auto simp: new_call_to_message_def)
    then have A1: "sum_list (map (message_cycles \<circ> new_call_to_message) new_calls_res) = (\<Sum>x\<leftarrow>new_calls_res. MAX_CYCLES_PER_RESPONSE + transferred_cycles x)"
      by auto
    have A2: "sum_list (map local.message_cycles response_messages) = (case update_return.response result of None \<Rightarrow> 0
      | _ \<Rightarrow> carried_cycles (call_ctxt_origin ctxt) + (call_ctxt_available_cycles ctxt - update_return.cycles_accepted result))"
      by (auto simp: response_messages_def Available_def cycles_accepted_res_def split: option.splits)
    have A3: "call_ctxt_carried_cycles new_ctxt = (case update_return.response result of Some _ \<Rightarrow> 0
      | _ \<Rightarrow> if call_ctxt_needs_to_respond ctxt then carried_cycles (call_ctxt_origin ctxt) + (call_ctxt_available_cycles ctxt - update_return.cycles_accepted result) else 0)"
      by (auto simp: new_ctxt_def Available_def cycles_accepted_res_def call_ctxt_carried_cycles split: option.splits)
    have A4: "call_ctxt_carried_cycles ctxt = (if call_ctxt_needs_to_respond ctxt then carried_cycles (call_ctxt_origin ctxt) + call_ctxt_available_cycles ctxt else 0)"
      using call_ctxt_carried_cycles
      by auto
    have reserve: "cycles_reserved ep = (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)"
      by (auto simp: Is_response_def split: entry_point.splits)
    have messages_msgs: "messages = older @ younger @ map new_call_to_message new_calls_res @ response_messages"
      by (auto simp: messages_def older_def younger_def)
    show ?thesis
      using lm(2,4) True call_ctxt_not_needs_to_respond_available_cycles[of ctxt]
      by (auto simp: cond_def msg_exec S'_def total_cycles_def lm(1,3) msgs messages_msgs A1 A2 A3 A4 New_balance_def
          reserve cycles_accepted_res_def no_response_def R_Inr lost Available_def split: option.splits)
  qed
qed

lemma message_execution_ic_inv:
  assumes "message_execution_pre n S" "ic_inv S"
  shows "ic_inv (message_execution_post n S)"
proof -
  obtain ctxt_id recv ep q can bal can_status t ctxt where msg: "messages S ! n = Func_message ctxt_id recv ep q"
    and prod: "list_map_get (canisters S) recv = Some (Some can)"
    "list_map_get (balances S) recv = Some bal"
    "list_map_get (canister_status S) recv = Some can_status"
    "list_map_get (time S) recv = Some t"
    "list_map_get (call_contexts S) ctxt_id = Some ctxt"
    using assms
    by (auto simp: message_execution_pre_def split: message.splits option.splits)
  define Mod where "Mod = can_state_rec.module can"
  define Is_response where "Is_response = (case ep of Callback _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  define Env :: "env" where "Env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S recv, certificate = None, status = simple_status can_status\<rparr>"
  define Available where "Available = call_ctxt_available_cycles ctxt"
  define F where "F = exec_function ep Env Available Mod"
  define R where "R = F (wasm_state can)"
  define cyc_used where "cyc_used = (case R of Inr res \<Rightarrow> update_return.cycles_used res | Inl trap \<Rightarrow> cycles_return.cycles_used trap)"
  obtain cycles_accepted_res new_calls_res where res: "(cycles_accepted_res, new_calls_res) = (case R of Inr res \<Rightarrow> (update_return.cycles_accepted res, new_calls res))"
    by (cases "(case R of Inr res \<Rightarrow> (update_return.cycles_accepted res, new_calls res))") auto
  define New_balance where "New_balance = bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)
    - (cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res))"
  define no_response where "no_response = (case R of Inr result \<Rightarrow> update_return.response result = None)"
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Func_message ctxt_id recv ep q # younger"
    "take n older = older" "drop (Suc n) older = []"
    "take (n - length older) ws = []" "drop (Suc n - length older) (w # ws) = ws"
    for w and ws :: "('p, 'c, 'cid) message list"
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: message_execution_pre_def msg older_def younger_def)
  define S'' where "S'' = S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
    balances := list_map_set (balances S) recv ((bal + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)) - min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE))\<rparr>"
  define cond where "cond = (\<not>isl R \<and> cyc_used \<le> (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
    cycles_accepted_res \<le> Available \<and>
    cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res) \<le>
      bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
    New_balance \<ge> (if Is_response then 0 else ic_freezing_limit S recv) \<and>
    (no_response \<or> call_ctxt_needs_to_respond ctxt))"
  show ?thesis
  proof (cases cond)
    case False
    have "message_execution_post n S = S''"
      using False
      by (simp_all add: message_execution_post_def Let_def msg prod
          Mod_def[symmetric] Is_response_def[symmetric] Env_def[symmetric] Available_def[symmetric] F_def[symmetric] R_def[symmetric] cyc_used_def[symmetric] res[symmetric]
          New_balance_def[symmetric] no_response_def[symmetric] S''_def[symmetric] cond_def[symmetric])
    then show ?thesis
      using assms(2)
      apply (auto simp: ic_inv_def S''_def msgs split: message.splits call_origin.splits)
         apply force
        apply fast
       apply force
      apply fast
      done
  next
    case True
    define result where "result = projr R"
    have R_Inr: "R = Inr result"
      using True
      by (auto simp: cond_def result_def split: option.splits)
    define response_messages where "response_messages = (case update_return.response result of None \<Rightarrow> []
      | Some resp \<Rightarrow> [Response_message (call_ctxt_origin ctxt) resp (Available - cycles_accepted_res)])"
    define new_call_to_message :: "('p, 'c) method_call \<Rightarrow> ('p, 'c, 'cid) message" where
      "new_call_to_message = (\<lambda>call. Call_message (From_canister ctxt_id (callback call)) recv
        (callee call) (method_call.method_name call) (method_call.arg call) (transferred_cycles call) (Queue (Canister recv) (callee call)))"
    define messages where "messages = take n (ic.messages S) @ drop (Suc n) (ic.messages S) @ map new_call_to_message new_calls_res @ response_messages"
    define new_ctxt where "new_ctxt = (case update_return.response result of
        None \<Rightarrow> call_ctxt_deduct_cycles cycles_accepted_res ctxt
      | Some _ \<Rightarrow> call_ctxt_respond ctxt)"
    define certified_data where "certified_data = (case new_certified_data result of None \<Rightarrow> ic.certified_data S
      | Some cd \<Rightarrow> list_map_set (ic.certified_data S) recv cd)"
    define S' where "S' = S\<lparr>canisters := list_map_set (canisters S) recv (Some (can\<lparr>wasm_state := update_return.new_state result\<rparr>)),
      messages := messages, call_contexts := list_map_set (call_contexts S) ctxt_id new_ctxt,
      certified_data := certified_data, balances := list_map_set (balances S) recv New_balance\<rparr>"
    have cycles_accepted_res_def: "cycles_accepted_res = update_return.cycles_accepted result"
      and new_calls_res_def: "new_calls_res = new_calls result"
      using res
      by (auto simp: R_Inr)
    have no_response: "no_response = (update_return.response result = None)"
      by (auto simp: no_response_def R_Inr)
    have msg_exec: "message_execution_post n S = S'"
      using True
      by (simp_all add: message_execution_post_def Let_def msg prod
          Mod_def[symmetric] Is_response_def[symmetric] Env_def[symmetric] Available_def[symmetric] F_def[symmetric] R_def[symmetric] cyc_used_def[symmetric] res[symmetric]
          New_balance_def[symmetric] no_response_def[symmetric] S''_def[symmetric] cond_def[symmetric]
          messages_def[symmetric] new_ctxt_def[symmetric] certified_data_def[symmetric] S'_def[symmetric]
          result_def[symmetric] response_messages_def[symmetric] new_call_to_message_def[symmetric])
    have messages_msgs: "messages = older @ younger @ map new_call_to_message new_calls_res @ response_messages"
      by (auto simp: messages_def older_def younger_def)
    have ctxt_in_range: "ctxt \<in> list_map_range (call_contexts S)"
      using prod(5)
      by (simp add: list_map_get_range)
    have response_msgsD: "msg \<in> set response_messages \<Longrightarrow> update_return.response result \<noteq> None \<and>
      (\<exists>resp. msg = Response_message (call_ctxt_origin ctxt) resp (Available - cycles_accepted_res))" for msg
      by (auto simp: response_messages_def) metis
    have call_ctxt_origin_new_ctxt: "call_ctxt_origin new_ctxt = call_ctxt_origin ctxt"
      by (auto simp: new_ctxt_def split: option.splits)
    have call_ctxt_needs_to_respond_new_ctxtD: "call_ctxt_needs_to_respond new_ctxt \<Longrightarrow> call_ctxt_needs_to_respond ctxt"
      by (auto simp: new_ctxt_def split: option.splits)
    show ?thesis
      using assms(2) ctxt_in_range True call_ctxt_not_needs_to_respond_available_cycles[of ctxt]
      apply (auto simp: cond_def msg_exec S'_def ic_inv_def msgs messages_msgs new_call_to_message_def
          no_response_def R_Inr call_ctxt_origin_new_ctxt
          split: option.splits message.splits call_origin.splits
          dest!: list_map_range_setD response_msgsD call_ctxt_needs_to_respond_new_ctxtD
          intro: ic_can_status_inv_mono2)
             apply blast
            apply fast
           apply blast
          apply fast
         apply blast
        apply fast
       apply blast
      apply fast
      done
  qed
qed



(* System transition: Call context starvation [DONE] *)

definition call_context_starvation_pre :: "'cid \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "call_context_starvation_pre ctxt_id S =
  (case list_map_get (call_contexts S) ctxt_id of Some call_context \<Rightarrow>
    call_ctxt_needs_to_respond call_context \<and>
    call_ctxt_origin call_context \<noteq> From_heartbeat \<and>
    (\<forall>msg \<in> set (messages S). case msg of
        Call_message orig _ _ _ _ _ _ \<Rightarrow> calling_context orig \<noteq> Some ctxt_id
      | Response_message orig _ _ \<Rightarrow> calling_context orig \<noteq> Some ctxt_id
      | _ \<Rightarrow> True) \<and>
    (\<forall>other_call_context \<in> list_map_range (call_contexts S).
      call_ctxt_needs_to_respond other_call_context \<longrightarrow>
      calling_context (call_ctxt_origin other_call_context) \<noteq> Some ctxt_id)
  | None \<Rightarrow> False)"

definition call_context_starvation_post :: "'cid \<Rightarrow>
  ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "call_context_starvation_post ctxt_id S = (
    case list_map_get (call_contexts S) ctxt_id of Some call_context \<Rightarrow>
    let msg = Response_message (call_ctxt_origin call_context) (response.Reject CANISTER_ERROR (STR ''starvation'')) (call_ctxt_available_cycles call_context)
    in S\<lparr>call_contexts := list_map_set (call_contexts S) ctxt_id (call_ctxt_respond call_context),
        messages := messages S @ [msg]\<rparr>)"

lemma call_context_starvation_cycles_inv:
  assumes "call_context_starvation_pre ctxt_id S"
  shows "total_cycles S = total_cycles (call_context_starvation_post ctxt_id S)"
  using assms list_map_sum_in_ge[where ?f="call_contexts S" and ?x=ctxt_id and ?g=call_ctxt_carried_cycles]
  by (auto simp: call_context_starvation_pre_def call_context_starvation_post_def total_cycles_def
      call_ctxt_carried_cycles list_map_sum_in[where ?g=call_ctxt_carried_cycles] split: option.splits)

lemma call_context_starvation_ic_inv:
  assumes "call_context_starvation_pre ctxt_id S" "ic_inv S"
  shows "ic_inv (call_context_starvation_post ctxt_id S)"
  using assms
  by (auto simp: ic_inv_def call_context_starvation_pre_def call_context_starvation_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits
      dest!: in_set_takeD in_set_dropD in_set_updD list_map_range_setD list_map_get_range
      intro: ic_can_status_inv_mono2)



(* System transition: Call context removal [DONE] *)

definition call_context_removal_pre :: "'cid \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "call_context_removal_pre ctxt_id S = (
    (case list_map_get (call_contexts S) ctxt_id of Some call_context \<Rightarrow>
      (\<not>call_ctxt_needs_to_respond call_context \<or>
        (call_ctxt_origin call_context = From_heartbeat \<and>
          (\<forall>msg \<in> set (messages S). case msg of
            Func_message other_ctxt_id _ _ _ \<Rightarrow> other_ctxt_id \<noteq> ctxt_id
          | _ \<Rightarrow> True))) \<and>
      (\<forall>msg \<in> set (messages S). case msg of
          Call_message ctxt _ _ _ _ _ _ \<Rightarrow> calling_context ctxt \<noteq> Some ctxt_id
        | Response_message ctxt _ _ \<Rightarrow> calling_context ctxt \<noteq> Some ctxt_id
        | _ \<Rightarrow> True) \<and>
      (\<forall>other_call_context \<in> list_map_range (call_contexts S).
        call_ctxt_needs_to_respond other_call_context \<longrightarrow>
        calling_context (call_ctxt_origin other_call_context) \<noteq> Some ctxt_id) \<and>
      (\<forall>can_status \<in> list_map_range (canister_status S). case can_status of Stopping os \<Rightarrow>
        \<forall>(orig, cyc) \<in> set os. (case orig of From_canister other_ctxt_id _ \<Rightarrow> ctxt_id \<noteq> other_ctxt_id | _ \<Rightarrow> True)
      | _ \<Rightarrow> True)
    | None \<Rightarrow> False))"

definition call_context_removal_post :: "'cid \<Rightarrow>
  ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "call_context_removal_post ctxt_id S = S\<lparr>call_contexts := list_map_del (call_contexts S) ctxt_id\<rparr>"

definition call_context_removal_burned_cycles :: "'cid \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "call_context_removal_burned_cycles ctxt_id S = call_ctxt_available_cycles (the (list_map_get (call_contexts S) ctxt_id))"

lemma call_context_removal_cycles_monotonic:
  assumes "call_context_removal_pre ctxt_id S"
  shows "total_cycles S = total_cycles (call_context_removal_post ctxt_id S) + call_context_removal_burned_cycles ctxt_id S"
  using assms call_ctxt_not_needs_to_respond_available_cycles
  by (auto simp: call_context_removal_pre_def call_context_removal_post_def call_context_removal_burned_cycles_def total_cycles_def call_ctxt_carried_cycles list_map_del_sum split: option.splits)

lemma call_context_removal_ic_inv:
  assumes "call_context_removal_pre ctxt_id S" "ic_inv S"
  shows "ic_inv (call_context_removal_post ctxt_id S)"
  using assms
  by (force simp: ic_inv_def call_context_removal_pre_def call_context_removal_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits
      dest!: in_set_takeD in_set_dropD in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      intro!: ic_can_status_inv_del[where ?z="list_map_dom (call_contexts S)"])



(* System transition: IC Management Canister: Canister creation [DONE] *)

definition ic_canister_creation_pre :: "nat \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_canister_creation_pre n cid t S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      cee = ic_principal \<and>
      mn = STR ''create_canister'' \<and>
      parse_candid a \<noteq> None \<and>
      is_system_assigned cid \<and>
      cid \<notin> list_map_dom (canisters S) \<and>
      cid \<notin> list_map_dom (time S) \<and>
      cid \<notin> list_map_dom (controllers S) \<and>
      cid \<notin> list_map_dom (balances S) \<and>
      cid \<notin> list_map_dom (certified_data S) \<and>
      cid \<notin> list_map_dom (canister_status S)
    | _ \<Rightarrow> False))"

definition ic_canister_creation_post :: "nat \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_canister_creation_post n cid t S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let ctrls = (case candid_parse_controllers a of Some ctrls \<Rightarrow> ctrls | _ \<Rightarrow> {cer}) in
    S\<lparr>canisters := list_map_set (canisters S) cid None,
      time := list_map_set (time S) cid t,
      controllers := list_map_set (controllers S) cid ctrls,
      freezing_threshold := list_map_set (freezing_threshold S) cid 2592000,
      balances := list_map_set (balances S) cid trans_cycles,
      certified_data := list_map_set (certified_data S) cid [],
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid
        (Candid_record (list_map_init [(STR ''canister_id'', Candid_blob (blob_of_principal cid))])))) 0],
      canister_status := list_map_set (canister_status S) cid Running\<rparr>)"

lemma ic_canister_creation_cycles_inv:
  assumes "ic_canister_creation_pre n cid t S"
  shows "total_cycles S = total_cycles (ic_canister_creation_post n cid t S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_canister_creation_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_creation_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_creation_pre_def ic_canister_creation_post_def total_cycles_def Let_def msgs
        list_map_sum_out[where ?g=id] list_map_sum_out[where ?g=status_cycles] split: message.splits option.splits)
qed

lemma ic_canister_creation_ic_inv:
  assumes "ic_canister_creation_pre n cid t S" "ic_inv S"
  shows "ic_inv (ic_canister_creation_post n cid t S)"
  using assms
  by (auto simp: ic_inv_def ic_canister_creation_pre_def ic_canister_creation_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      intro: ic_can_status_inv_mono1)



(* System transition: IC Management Canister: Changing settings [DONE] *)

definition ic_update_settings_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_update_settings_pre n S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      cee = ic_principal \<and>
      mn = STR ''update_settings'' \<and>
      (case candid_parse_cid a of Some cid \<Rightarrow>
      (case list_map_get (controllers S) cid of Some ctrls \<Rightarrow> cer \<in> ctrls
      | _ \<Rightarrow> False) | _ \<Rightarrow> False)
    | _ \<Rightarrow> False))"

definition ic_update_settings_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_update_settings_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a);
    ctrls = (case candid_parse_controllers a of Some ctrls \<Rightarrow> list_map_set (controllers S) cid ctrls | _ \<Rightarrow> controllers S);
    freezing_thres = (case candid_nested_lookup a [STR '''settings'', STR ''freezing_threshold''] of Some (Candid_nat freeze) \<Rightarrow>
      list_map_set (freezing_threshold S) cid freeze | _ \<Rightarrow> freezing_threshold S) in
    S\<lparr>controllers := ctrls, freezing_threshold := freezing_thres, messages := take n (messages S) @ drop (Suc n) (messages S) @
        [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)"

lemma ic_update_settings_cycles_inv:
  assumes "ic_update_settings_pre n S"
  shows "total_cycles S = total_cycles (ic_update_settings_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_update_settings_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_update_settings_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_update_settings_pre_def ic_update_settings_post_def total_cycles_def Let_def msgs split: message.splits option.splits)
qed

lemma ic_update_settings_ic_inv:
  assumes "ic_update_settings_pre n S" "ic_inv S"
  shows "ic_inv (ic_update_settings_post n S)"
  using assms
  by (auto simp: ic_inv_def ic_update_settings_pre_def ic_update_settings_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del)



(* System transition: IC Management Canister: Canister status [DONE] *)

definition ic_canister_status_pre :: "nat \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_canister_status_pre n m S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''canister_status'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
      cid \<in> list_map_dom (canisters S) \<and>
      cid \<in> list_map_dom (canister_status S) \<and>
      cid \<in> list_map_dom (balances S) \<and>
      cid \<in> list_map_dom (freezing_threshold S) \<and>
    (case list_map_get (controllers S) cid of Some ctrls \<Rightarrow> cer \<in> ctrls | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_status_post :: "nat \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_canister_status_post n m S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a);
    hash = (case the (list_map_get (canisters S) cid) of None \<Rightarrow> Candid_null
      | Some can \<Rightarrow> Candid_opt (Candid_blob (sha_256 (raw_module can)))) in
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid
      (Candid_record (list_map_init [(STR ''status'', candid_of_status (simple_status (the (list_map_get (canister_status S) cid)))),
        (STR ''module_hash'', hash),
        (STR ''controllers'', Candid_vec (map (Candid_blob \<circ> blob_of_principal) (principal_list_of_set (the (list_map_get (controllers S) cid))))),
        (STR ''memory_size'', Candid_nat m),
        (STR ''cycles'', Candid_nat (the (list_map_get (balances S) cid))),
        (STR ''freezing_threshold'', Candid_nat (the (list_map_get (freezing_threshold S) cid))),
        (STR ''idle_cycles_burned_per_day'', Candid_nat (ic_idle_cycles_burned_rate S cid))])))) trans_cycles]\<rparr>)"

lemma ic_canister_status_cycles_inv:
  assumes "ic_canister_status_pre n m S"
  shows "total_cycles S = total_cycles (ic_canister_status_post n m S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_canister_status_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_status_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_status_pre_def ic_canister_status_post_def total_cycles_def Let_def msgs split: message.splits option.splits)
qed

lemma ic_canister_status_ic_inv:
  assumes "ic_canister_status_pre n m S" "ic_inv S"
  shows "ic_inv (ic_canister_status_post n m S)"
  using assms
  by (auto simp: ic_inv_def ic_canister_status_pre_def ic_canister_status_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del)



(* System transition: IC Management Canister: Code installation [DONE] *)

definition ic_code_installation_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_code_installation_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''install_code'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [STR ''mode''], candid_parse_blob a [STR ''wasm_module''], candid_parse_blob a [STR ''arg'']) of
      (Some mode, Some w, Some ar) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
      parse_public_custom_sections w \<noteq> None \<and>
      parse_private_custom_sections w \<noteq> None \<and>
    (case (list_map_get (controllers S) cid, list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some ctrls, Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      ((mode = STR ''install'' \<and> (case list_map_get (canisters S) cid of Some None \<Rightarrow> True | _ \<Rightarrow> False)) \<or> mode = STR ''reinstall'') \<and>
      cer \<in> ctrls \<and>
      (case canister_module_init m (cid, ar, cer, env) of Inl _ \<Rightarrow> False
      | Inr ret \<Rightarrow> cycles_return.cycles_used ret \<le> bal) \<and>
      list_map_dom (canister_module_update_methods m) \<inter> list_map_dom (canister_module_query_methods m) = {}
    | _ \<Rightarrow> False) | _ \<Rightarrow> False) | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_code_installation_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_code_installation_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [STR ''mode''], candid_parse_blob a [STR ''wasm_module''], candid_parse_blob a [STR ''arg'']) of
      (Some mode, Some w, Some a) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
    (case (list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr>;
      (new_state, cyc_used) = (case canister_module_init m (cid, a, cer, env) of Inr ret \<Rightarrow> (cycles_return.return ret, cycles_return.cycles_used ret)) in
    S\<lparr>canisters := list_map_set (canisters S) cid (Some \<lparr>wasm_state = new_state, module = m, raw_module = w,
        public_custom_sections = the (parse_public_custom_sections w), private_custom_sections = the (parse_private_custom_sections w)\<rparr>),
      balances := list_map_set (balances S) cid (bal - cyc_used),
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)))))"

definition ic_code_installation_burned_cycles :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "ic_code_installation_burned_cycles n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_blob a [STR ''wasm_module''], candid_parse_blob a [STR ''arg'']) of
      (Some w, Some a) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
    (case (list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      (case canister_module_init m (cid, a, cer, env) of Inr ret \<Rightarrow> cycles_return.cycles_used ret))))))"

lemma ic_code_installation_cycles_inv:
  assumes "ic_code_installation_pre n S"
  shows "total_cycles S = total_cycles (ic_code_installation_post n S) + ic_code_installation_burned_cycles n S"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_code_installation_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_code_installation_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms list_map_sum_in_ge[where ?f="balances S" and ?g=id and ?x="the (candid_parse_cid a)"]
    by (auto simp: ic_code_installation_pre_def ic_code_installation_post_def ic_code_installation_burned_cycles_def total_cycles_def Let_def msgs list_map_sum_in[where ?f="balances S"] split: message.splits option.splits sum.splits prod.splits)
qed

lemma ic_code_installation_ic_inv:
  assumes "ic_code_installation_pre n S" "ic_inv S"
  shows "ic_inv (ic_code_installation_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid mode w ar m ctrls t bal can_status where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and parse: "candid_parse_cid a = Some cid"
    "candid_parse_text a [STR ''mode''] = Some mode"
    "candid_parse_blob a [STR ''wasm_module''] = Some w"
    "candid_parse_blob a [STR ''arg''] = Some ar"
    "parse_wasm_mod w = Some m"
    and list_map_get:
    "list_map_get (controllers S) cid = Some ctrls"
    "list_map_get (time S) cid = Some t"
    "list_map_get (balances S) cid = Some bal"
    "list_map_get (canister_status S) cid = Some can_status"
    using assms
    by (auto simp: ic_code_installation_pre_def split: message.splits option.splits)
  show ?thesis
    using assms
    by (auto simp: ic_inv_def ic_code_installation_pre_def ic_code_installation_post_def msg parse list_map_get Let_def
        split: sum.splits call_origin.splits message.splits
        dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del)
qed



(* System transition: IC Management Canister: Code upgrade [DONE] *)

definition ic_code_upgrade_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_code_upgrade_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''install_code'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [STR ''mode''], candid_parse_blob a [STR ''wasm_module''], candid_parse_blob a [STR ''arg'']) of
      (Some mode, Some w, Some ar) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
      parse_public_custom_sections w \<noteq> None \<and>
      parse_private_custom_sections w \<noteq> None \<and>
    (case (list_map_get (canisters S) cid, list_map_get (controllers S) cid, list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some (Some can), Some ctrls, Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      mode = STR ''upgrade'' \<and>
      cer \<in> ctrls \<and>
      (case canister_module_pre_upgrade (module can) (wasm_state can, cer, env) of Inr pre_ret \<Rightarrow>
      (case canister_module_post_upgrade m (cid, cycles_return.return pre_ret, ar, cer, env) of Inr post_ret \<Rightarrow>
        cycles_return.cycles_used pre_ret + cycles_return.cycles_used post_ret \<le> bal
      | _ \<Rightarrow> False) | _ \<Rightarrow> False) \<and>
      list_map_dom (canister_module_update_methods m) \<inter> list_map_dom (canister_module_query_methods m) = {}
    | _ \<Rightarrow> False) | _ \<Rightarrow> False) | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_code_upgrade_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_code_upgrade_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [STR ''mode''], candid_parse_blob a [STR ''wasm_module''], candid_parse_blob a [STR ''arg'']) of
      (Some mode, Some w, Some ar) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
    (case (list_map_get (canisters S) cid, list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      (case canister_module_pre_upgrade (module can) (wasm_state can, cer, env) of Inr pre_ret \<Rightarrow>
      (case canister_module_post_upgrade m (cid, cycles_return.return pre_ret, ar, cer, env) of Inr post_ret \<Rightarrow>
    S\<lparr>canisters := list_map_set (canisters S) cid (Some \<lparr>wasm_state = cycles_return.return post_ret, module = m, raw_module = w,
        public_custom_sections = the (parse_public_custom_sections w), private_custom_sections = the (parse_private_custom_sections w)\<rparr>),
      balances := list_map_set (balances S) cid (bal - (cycles_return.cycles_used pre_ret + cycles_return.cycles_used post_ret)),
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)))))))"

definition ic_code_upgrade_burned_cycles :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "ic_code_upgrade_burned_cycles n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [STR ''mode''], candid_parse_blob a [STR ''wasm_module''], candid_parse_blob a [STR ''arg'']) of
      (Some mode, Some w, Some ar) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
    (case (list_map_get (canisters S) cid, list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      (case canister_module_pre_upgrade (module can) (wasm_state can, cer, env) of Inr pre_ret \<Rightarrow>
      (case canister_module_post_upgrade m (cid, cycles_return.return pre_ret, ar, cer, env) of Inr post_ret \<Rightarrow>
      cycles_return.cycles_used pre_ret + cycles_return.cycles_used post_ret)))))))"

lemma ic_code_upgrade_cycles_inv:
  assumes "ic_code_upgrade_pre n S"
  shows "total_cycles S = total_cycles (ic_code_upgrade_post n S) + ic_code_upgrade_burned_cycles n S"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_code_upgrade_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_code_upgrade_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms list_map_sum_in_ge[where ?f="balances S" and ?g=id and ?x="the (candid_parse_cid a)"]
    by (auto simp: ic_code_upgrade_pre_def ic_code_upgrade_post_def ic_code_upgrade_burned_cycles_def total_cycles_def Let_def msgs list_map_sum_in[where ?f="balances S"] split: message.splits option.splits sum.splits)
qed

lemma ic_code_upgrade_ic_inv:
  assumes "ic_code_upgrade_pre n S" "ic_inv S"
  shows "ic_inv (ic_code_upgrade_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid mode w ar m can ctrls t bal can_status where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and parse: "candid_parse_cid a = Some cid"
    "candid_parse_text a [STR ''mode''] = Some mode"
    "candid_parse_blob a [STR ''wasm_module''] = Some w"
    "candid_parse_blob a [STR ''arg''] = Some ar"
    "parse_wasm_mod w = Some m"
    and list_map_get:
    "list_map_get (canisters S) cid = Some (Some can)"
    "list_map_get (controllers S) cid = Some ctrls"
    "list_map_get (time S) cid = Some t"
    "list_map_get (balances S) cid = Some bal"
    "list_map_get (canister_status S) cid = Some can_status"
    using assms
    by (auto simp: ic_code_upgrade_pre_def split: message.splits option.splits)
  show ?thesis
    using assms
    by (auto simp: ic_inv_def ic_code_upgrade_pre_def ic_code_upgrade_post_def msg parse list_map_get Let_def
        split: sum.splits call_origin.splits message.splits
        dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del)
qed



(* System transition: IC Management Canister: Code uninstallation [DONE] *)

definition ic_code_uninstallation_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_code_uninstallation_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''uninstall_code'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case list_map_get (controllers S) cid of Some ctrls \<Rightarrow> cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_code_uninstallation_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_code_uninstallation_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    let call_ctxt_to_msg = (\<lambda>ctxt.
      if call_ctxt_canister ctxt = cid \<and> call_ctxt_needs_to_respond ctxt then
        Some (Response_message (call_ctxt_origin ctxt) (response.Reject CANISTER_REJECT (STR ''Canister has been uninstalled'')) (call_ctxt_available_cycles ctxt))
      else None);
    call_ctxt_to_ctxt = (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_delete ctxt else ctxt) in
    S\<lparr>canisters := list_map_set (canisters S) cid None, certified_data := list_map_set (certified_data S) cid [],
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles] @
        List.map_filter call_ctxt_to_msg (list_map_vals (call_contexts S)),
      call_contexts := list_map_map call_ctxt_to_ctxt (call_contexts S)\<rparr>))"

lemma ic_code_uninstallation_cycles_inv:
  assumes "ic_code_uninstallation_pre n S"
  shows "total_cycles S = total_cycles (ic_code_uninstallation_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_code_uninstallation_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_code_uninstallation_pre_def msg younger_def older_def nth_append)
  have F1: "list_map_sum_vals call_ctxt_carried_cycles (call_contexts S) =
    list_map_sum_vals id
      (list_map_map (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_carried_cycles ctxt else 0) (call_contexts S)) +
    list_map_sum_vals call_ctxt_carried_cycles
      (list_map_map (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_delete ctxt else ctxt) (call_contexts S))"
    using list_map_sum_vals_split[where ?f="call_ctxt_carried_cycles" and ?g="call_ctxt_delete", unfolded call_ctxt_delete_carried_cycles diff_zero]
    by auto
  show ?thesis
    using assms
    by (auto simp: ic_code_uninstallation_pre_def ic_code_uninstallation_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs F1
        split: message.splits option.splits sum.splits if_splits intro!: list_map_sum_vals_filter)
qed

lemma ic_code_uninstallation_ic_inv:
  assumes "ic_code_uninstallation_pre n S" "ic_inv S"
  shows "ic_inv (ic_code_uninstallation_post n S)"
  using assms
  by (auto simp: ic_inv_def ic_code_uninstallation_pre_def ic_code_uninstallation_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* System transition: IC Management Canister: Stopping a canister (running) [DONE] *)

definition ic_canister_stop_running_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_canister_stop_running_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''stop_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some Running, Some ctrls) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_stop_running_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_canister_stop_running_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
      canister_status := list_map_set (canister_status S) cid (Stopping [(orig, trans_cycles)])\<rparr>)"

lemma ic_canister_stop_running_cycles_inv:
  assumes "ic_canister_stop_running_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_stop_running_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_stop_running_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_stop_running_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_stop_running_pre_def ic_canister_stop_running_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_sum_in[where ?g=status_cycles] split: message.splits option.splits sum.splits can_status.splits)
qed

lemma ic_canister_stop_running_ic_inv:
  assumes "ic_canister_stop_running_pre n S" "ic_inv S"
  shows "ic_inv (ic_canister_stop_running_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_stop_running_pre_def split: message.splits option.splits)
  show ?thesis
    using assms
    by (force simp: ic_inv_def ic_canister_stop_running_pre_def ic_canister_stop_running_post_def msg Let_def
        split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
        dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del
        in_set_map_filter_vals intro!: ic_can_status_inv_stopping[where ?x="list_map_range (canister_status S)" and ?os=orig])
qed



(* System transition: IC Management Canister: Stopping a canister (stopping) [DONE] *)

definition ic_canister_stop_stopping_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_canister_stop_stopping_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''stop_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some (Stopping os), Some ctrls) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_stop_stopping_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_canister_stop_stopping_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    (case list_map_get (canister_status S) cid of Some (Stopping os) \<Rightarrow>
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
      canister_status := list_map_set (canister_status S) cid (Stopping (os @ [(orig, trans_cycles)]))\<rparr>))"

lemma ic_canister_stop_stopping_cycles_inv:
  assumes "ic_canister_stop_stopping_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_stop_stopping_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_stop_stopping_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_stop_stopping_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_stop_stopping_pre_def ic_canister_stop_stopping_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_sum_in[where ?g=status_cycles] split: message.splits option.splits sum.splits can_status.splits)
qed

lemma ic_canister_stop_stopping_ic_inv:
  assumes "ic_canister_stop_stopping_pre n S" "ic_inv S"
  shows "ic_inv (ic_canister_stop_stopping_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_stop_stopping_pre_def split: message.splits option.splits)
  show ?thesis
    using assms
    by (force simp: ic_inv_def ic_canister_stop_stopping_pre_def ic_canister_stop_stopping_post_def msg Let_def
        split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
        dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del
        in_set_map_filter_vals intro!: ic_can_status_inv_stopping_app[where ?x="list_map_range (canister_status S)" and ?os=orig])
qed



(* System transition: IC Management Canister: Stopping a canister (done stopping) [DONE] *)

definition ic_canister_stop_done_stopping_pre :: "'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_canister_stop_done_stopping_pre cid S =
    (case list_map_get (canister_status S) cid of Some (Stopping os) \<Rightarrow>
      (\<forall>ctxt \<in> list_map_range (call_contexts S). call_ctxt_deleted ctxt \<or> call_ctxt_canister ctxt \<noteq> cid)
    | _ \<Rightarrow> False)"

definition ic_canister_stop_done_stopping_post :: "'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_canister_stop_done_stopping_post cid S = (
    let orig_cycles_to_msg = (\<lambda>(or, cyc). Response_message or (Reply (blob_of_candid Candid_empty)) cyc) in
    (case list_map_get (canister_status S) cid of Some (Stopping os) \<Rightarrow>
    S\<lparr>canister_status := list_map_set (canister_status S) cid Stopped,
      messages := messages S @ map orig_cycles_to_msg os\<rparr>))"

lemma ic_canister_stop_done_stopping_cycles_inv:
  assumes "ic_canister_stop_done_stopping_pre cid S"
  shows "total_cycles S = total_cycles (ic_canister_stop_done_stopping_post cid S)"
proof -
  have F1: "(message_cycles \<circ> (\<lambda>(or, y). Response_message or (Reply (blob_of_candid Candid_empty)) y)) = (\<lambda>(or, y). carried_cycles or + y)"
    by auto
  have F2: "(\<Sum>(or, y)\<leftarrow>xs. carried_cycles or + y) = sum_list (map (carried_cycles \<circ> fst) xs) + sum_list (map snd xs)" for xs
    by (induction xs) auto
  show ?thesis
    using assms list_map_sum_in_ge[where ?g=status_cycles and ?f="canister_status S" and ?x=cid]
    by (auto simp: ic_canister_stop_done_stopping_pre_def ic_canister_stop_done_stopping_post_def total_cycles_def call_ctxt_carried_cycles Let_def
        F1 F2 list_map_sum_in[where ?g=status_cycles] split: message.splits option.splits sum.splits can_status.splits)
qed

lemma ic_canister_stop_done_stopping_ic_inv:
  assumes "ic_canister_stop_done_stopping_pre cid S" "ic_inv S"
  shows "ic_inv (ic_canister_stop_done_stopping_post cid S)"
  using assms
  by (force simp: ic_inv_def ic_can_status_inv_def ic_canister_stop_done_stopping_pre_def ic_canister_stop_done_stopping_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* System transition: IC Management Canister: Stopping a canister (stopped) [DONE] *)

definition ic_canister_stop_stopped_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_canister_stop_stopped_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''stop_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some Stopped, Some ctrls) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_stop_stopped_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_canister_stop_stopped_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)"

lemma ic_canister_stop_stopped_cycles_inv:
  assumes "ic_canister_stop_stopped_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_stop_stopped_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_stop_stopped_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_stop_stopped_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_stop_stopped_pre_def ic_canister_stop_stopped_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        split: message.splits option.splits sum.splits can_status.splits)
qed

lemma ic_canister_stop_stopped_ic_inv:
  assumes "ic_canister_stop_stopped_pre n S" "ic_inv S"
  shows "ic_inv (ic_canister_stop_stopped_post n S)"
  using assms
  by (auto simp: ic_inv_def ic_canister_stop_stopped_pre_def ic_canister_stop_stopped_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* System transition: IC Management Canister: Starting a canister (not stopping) [DONE] *)

definition ic_canister_start_not_stopping_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_canister_start_not_stopping_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''start_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some can_status, Some ctrls) \<Rightarrow>
      (can_status = Running \<or> can_status = Stopped) \<and>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_start_not_stopping_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_canister_start_not_stopping_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    S\<lparr>canister_status := list_map_set (canister_status S) cid Running,
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)"

lemma ic_canister_start_not_stopping_cycles_inv:
  assumes "ic_canister_start_not_stopping_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_start_not_stopping_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_start_not_stopping_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_start_not_stopping_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_start_not_stopping_pre_def ic_canister_start_not_stopping_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_sum_in[where ?g=status_cycles] split: message.splits option.splits sum.splits)
qed

lemma ic_canister_start_not_stopping_ic_inv:
  assumes "ic_canister_start_not_stopping_pre n S" "ic_inv S"
  shows "ic_inv (ic_canister_start_not_stopping_post n S)"
  using assms
  by (auto simp: ic_inv_def ic_canister_start_not_stopping_pre_def ic_canister_start_not_stopping_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals intro: ic_can_status_inv_mono1)



(* System transition: IC Management Canister: Starting a canister (stopping) [DONE] *)

definition ic_canister_start_stopping_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_canister_start_stopping_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''start_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some (Stopping _), Some ctrls) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_start_stopping_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_canister_start_stopping_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a);
    orig_cycles_to_msg = (\<lambda>(or, cyc). Response_message or (response.Reject CANISTER_REJECT (STR ''Canister has been restarted'')) cyc) in
    (case list_map_get (canister_status S) cid of Some (Stopping os) \<Rightarrow>
    S\<lparr>canister_status := list_map_set (canister_status S) cid Running,
      messages := take n (messages S) @ drop (Suc n) (messages S) @ Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles #
      map orig_cycles_to_msg os\<rparr>))"

lemma ic_canister_start_stopping_cycles_inv:
  assumes "ic_canister_start_stopping_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_start_stopping_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_start_stopping_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_start_stopping_pre_def msg younger_def older_def nth_append)
  have F1: "(message_cycles \<circ> (\<lambda>(or, y). Response_message or (response.Reject CANISTER_REJECT (STR ''Canister has been restarted'')) y)) = (\<lambda>(or, y). carried_cycles or + y)"
    by auto
  have F2: "(\<Sum>(or, y)\<leftarrow>xs. carried_cycles or + y) = sum_list (map (carried_cycles \<circ> fst) xs) + sum_list (map snd xs)" for xs
    by (induction xs) auto
  show ?thesis
    using assms list_map_sum_in_ge[where ?g=status_cycles and ?f="canister_status S" and ?x=cid]
    by (auto simp: ic_canister_start_stopping_pre_def ic_canister_start_stopping_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs F1 F2
        list_map_sum_in[where ?g=status_cycles and ?f="canister_status S"]
        split: message.splits option.splits sum.splits can_status.splits)
qed

lemma ic_canister_start_stopping_ic_inv:
  assumes "ic_canister_start_stopping_pre n S" "ic_inv S"
  shows "ic_inv (ic_canister_start_stopping_post n S)"
  using assms
  apply (auto simp: ic_inv_def ic_canister_start_stopping_pre_def ic_canister_start_stopping_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del in_set_map_filter_vals
      intro: ic_can_status_inv_mono1)
   apply (fastforce simp: ic_can_status_inv_def)+
  done



(* System transition: IC Management Canister: Canister deletion [DONE] *)

definition ic_canister_deletion_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_canister_deletion_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''delete_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid, list_map_get (balances S) cid) of (Some Stopped, Some ctrls, Some bal) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_deletion_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_canister_deletion_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    S\<lparr>canisters := list_map_del (canisters S) cid,
      controllers := list_map_del (controllers S) cid,
      freezing_threshold := list_map_del (freezing_threshold S) cid,
      canister_status := list_map_del (canister_status S) cid,
      time := list_map_del (time S) cid,
      balances := list_map_del (balances S) cid,
      certified_data := list_map_del (certified_data S) cid,
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)"

definition ic_canister_deletion_burned_cycles :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "ic_canister_deletion_burned_cycles n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in the (list_map_get (balances S) cid))"

lemma ic_canister_deletion_cycles_monotonic:
  assumes "ic_canister_deletion_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_deletion_post n S) + ic_canister_deletion_burned_cycles n S"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_deletion_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_deletion_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_deletion_pre_def ic_canister_deletion_post_def ic_canister_deletion_burned_cycles_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_del_sum[where ?g=id and ?f="balances S"] list_map_del_sum[where ?g=status_cycles and ?f="canister_status S"]
        split: message.splits option.splits sum.splits can_status.splits)
qed

lemma ic_canister_deletion_ic_inv:
  assumes "ic_canister_deletion_pre n S" "ic_inv S"
  shows "ic_inv (ic_canister_deletion_post n S)"
  using assms
  by (auto simp: ic_inv_def ic_canister_deletion_pre_def ic_canister_deletion_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del in_set_map_filter_vals
      intro: ic_can_status_inv_mono1)



(* System transition: IC Management Canister: Depositing cycles [DONE] *)

definition ic_depositing_cycles_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_depositing_cycles_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''deposit_cycles'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case list_map_get (balances S) cid of Some bal \<Rightarrow>
      True
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_depositing_cycles_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_depositing_cycles_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    (case list_map_get (balances S) cid of Some bal \<Rightarrow>
    S\<lparr>balances := list_map_set (balances S) cid (bal + trans_cycles),
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) 0]\<rparr>))"

lemma ic_depositing_cycles_cycles_monotonic:
  assumes "ic_depositing_cycles_pre n S"
  shows "total_cycles S = total_cycles (ic_depositing_cycles_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_depositing_cycles_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_depositing_cycles_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms list_map_sum_in_ge[where ?g=id and ?f="balances S" and ?x=cid]
    by (auto simp: ic_depositing_cycles_pre_def ic_depositing_cycles_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_sum_in[where ?g=id and ?f="balances S"] min_def split: message.splits option.splits sum.splits)
qed

lemma ic_depositing_cycles_ic_inv:
  assumes "ic_depositing_cycles_pre n S" "ic_inv S"
  shows "ic_inv (ic_depositing_cycles_post n S)"
  using assms
  by (auto simp: ic_inv_def ic_depositing_cycles_pre_def ic_depositing_cycles_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* System transition: IC Management Canister: Random numbers [DONE] *)

definition ic_random_numbers_pre :: "nat \<Rightarrow> blob \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_random_numbers_pre n b S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = STR ''raw_rand'' \<and>
    a = blob_of_candid Candid_empty \<and>
    length b = 32
  | _ \<Rightarrow> False))"

definition ic_random_numbers_post :: "nat \<Rightarrow> blob \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_random_numbers_post n b S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid (Candid_blob b))) trans_cycles]\<rparr>)"

lemma ic_random_numbers_cycles_inv:
  assumes "ic_random_numbers_pre n b S"
  shows "total_cycles S = total_cycles (ic_random_numbers_post n b S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_random_numbers_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_random_numbers_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_random_numbers_pre_def ic_random_numbers_post_def total_cycles_def call_ctxt_carried_cycles Let_def msgs)
qed

lemma ic_random_numbers_ic_inv:
  assumes "ic_random_numbers_pre n b S" "ic_inv S"
  shows "ic_inv (ic_random_numbers_post n b S)"
  using assms
  by (auto simp: ic_inv_def ic_random_numbers_pre_def ic_random_numbers_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* System transition: IC Management Canister: Canister creation with cycles [DONE] *)

definition ic_provisional_canister_creation_pre :: "nat \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_provisional_canister_creation_pre n cid t S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (case candid_parse_nat a [STR ''amount''] of Some cyc \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      cee = ic_principal \<and>
      mn = STR ''provisional_create_canister_with_cycles'' \<and>
      is_system_assigned cid \<and>
      cid \<notin> list_map_dom (canisters S) \<and>
      cid \<notin> list_map_dom (time S) \<and>
      cid \<notin> list_map_dom (controllers S) \<and>
      cid \<notin> list_map_dom (balances S) \<and>
      cid \<notin> list_map_dom (certified_data S) \<and>
      cid \<notin> list_map_dom (canister_status S)
    | _ \<Rightarrow> False) | _ \<Rightarrow> False))"

definition ic_provisional_canister_creation_post :: "nat \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_provisional_canister_creation_post n cid t S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cyc = the (candid_parse_nat a [STR ''amount'']) in
    S\<lparr>canisters := list_map_set (canisters S) cid None,
      time := list_map_set (time S) cid t,
      controllers := list_map_set (controllers S) cid {cer},
      freezing_threshold := list_map_set (freezing_threshold S) cid 2592000,
      balances := list_map_set (balances S) cid cyc,
      certified_data := list_map_set (certified_data S) cid [],
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid
        (Candid_record (list_map_init [(STR ''canister_id'', Candid_blob (blob_of_principal cid))])))) trans_cycles],
      canister_status := list_map_set (canister_status S) cid Running\<rparr>)"

definition ic_provisional_canister_creation_minted_cycles :: "nat \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "ic_provisional_canister_creation_minted_cycles n cid t S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    the (candid_parse_nat a [STR ''amount'']))"

lemma ic_provisional_canister_creation_cycles_antimonotonic:
  assumes "ic_provisional_canister_creation_pre n cid t S"
  shows "total_cycles S + ic_provisional_canister_creation_minted_cycles n cid t S  = total_cycles (ic_provisional_canister_creation_post n cid t S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_provisional_canister_creation_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_provisional_canister_creation_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_provisional_canister_creation_pre_def ic_provisional_canister_creation_post_def ic_provisional_canister_creation_minted_cycles_def total_cycles_def Let_def msgs
        list_map_sum_out[where ?g=id] list_map_sum_out[where ?g=status_cycles] split: message.splits option.splits)
qed

lemma ic_provisional_canister_creation_ic_inv:
  assumes "ic_provisional_canister_creation_pre n cid t S" "ic_inv S"
  shows "ic_inv (ic_provisional_canister_creation_post n cid t S)"
  using assms
  by (auto simp: ic_inv_def ic_provisional_canister_creation_pre_def ic_provisional_canister_creation_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del in_set_map_filter_vals
      intro: ic_can_status_inv_mono1)



(* System transition: IC Management Canister: Top up canister [DONE] *)

definition ic_top_up_canister_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "ic_top_up_canister_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (case (candid_parse_cid a, candid_parse_nat a [STR ''amount'']) of (Some cid, Some cyc) \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      cee = ic_principal \<and>
      mn = STR ''provisional_top_up_canister'' \<and>
      cid \<in> list_map_dom (balances S)
    | _ \<Rightarrow> False) | _ \<Rightarrow> False))"

definition ic_top_up_canister_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "ic_top_up_canister_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a);
    cyc = the (candid_parse_nat a [STR ''amount'']);
    bal = the (list_map_get (balances S) cid) in
    S\<lparr>balances := list_map_set (balances S) cid (bal + cyc)\<rparr>)"

definition ic_top_up_canister_minted_cycles :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "ic_top_up_canister_minted_cycles n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    the (candid_parse_nat a [STR ''amount'']))"

lemma ic_top_up_canister_cycles_antimonotonic:
  assumes "ic_top_up_canister_pre n S"
  shows "total_cycles S + ic_top_up_canister_minted_cycles n S  = total_cycles (ic_top_up_canister_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_top_up_canister_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_top_up_canister_pre_def msg younger_def older_def nth_append)
  define cid where "cid = the (candid_parse_cid a)"
  show ?thesis
    using assms
    by (cases "list_map_get (balances S) cid")
       (auto simp: ic_top_up_canister_pre_def ic_top_up_canister_post_def ic_top_up_canister_minted_cycles_def total_cycles_def Let_def msgs cid_def
        list_map_sum_in[where ?g=id] split: message.splits option.splits)
qed

lemma ic_top_up_canister_ic_inv:
  assumes "ic_top_up_canister_pre n S" "ic_inv S"
  shows "ic_inv (ic_top_up_canister_post n S)"
  using assms
  by (auto simp: ic_inv_def ic_top_up_canister_pre_def ic_top_up_canister_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* System transition: Callback invocation (not deleted) [DONE] *)

definition callback_invocation_not_deleted_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "callback_invocation_not_deleted_pre n S = (n < length (messages S) \<and> (case messages S ! n of Response_message (From_canister ctxt_id c) resp ref_cycles \<Rightarrow>
    (case list_map_get (call_contexts S) ctxt_id of Some ctxt \<Rightarrow>
      let cid = call_ctxt_canister ctxt in
      \<not>call_ctxt_deleted ctxt \<and>
      (case list_map_get (balances S) cid of Some bal \<Rightarrow> True
      | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition callback_invocation_not_deleted_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "callback_invocation_not_deleted_post n S = (case messages S ! n of Response_message (From_canister ctxt_id c) resp ref_cycles \<Rightarrow>
    (case list_map_get (call_contexts S) ctxt_id of Some ctxt \<Rightarrow>
      let cid = call_ctxt_canister ctxt in
      (case list_map_get (balances S) cid of Some bal \<Rightarrow>
        S\<lparr>balances := list_map_set (balances S) cid (bal + ref_cycles),
          messages := list_update (messages S) n (Func_message ctxt_id cid (Callback c resp ref_cycles) Unordered)\<rparr>)))"

lemma callback_invocation_not_deleted_cycles_inv:
  assumes "callback_invocation_not_deleted_pre n S"
  shows "total_cycles S = total_cycles (callback_invocation_not_deleted_post n S)"
proof -
  obtain ctxt_id c resp ref_cycles where msg: "messages S ! n = Response_message (From_canister ctxt_id c) resp ref_cycles"
    using assms
    by (auto simp: callback_invocation_not_deleted_pre_def split: message.splits option.splits call_origin.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Response_message (From_canister ctxt_id c) resp ref_cycles # younger" "(older @ w # younger) ! n = w"
    and msgs_upd: "(older @ Response_message (From_canister ctxt_id c) resp ref_cycles # younger)[n := m] = older @ m # younger" for w m
    using assms id_take_nth_drop[of n "messages S"] upd_conv_take_nth_drop[of n "messages S"] assms
    by (auto simp: callback_invocation_not_deleted_pre_def msg older_def younger_def nth_append)
  show ?thesis
    using assms
    by (auto simp: callback_invocation_not_deleted_pre_def callback_invocation_not_deleted_post_def total_cycles_def call_ctxt_carried_cycles Let_def msgs msgs_upd
        list_map_sum_in[where ?g=id and ?f="balances S"] split: option.splits)
qed

lemma callback_invocation_not_deleted_ic_inv:
  assumes "callback_invocation_not_deleted_pre n S" "ic_inv S"
  shows "ic_inv (callback_invocation_not_deleted_post n S)"
  using assms
  by (auto simp: ic_inv_def callback_invocation_not_deleted_pre_def callback_invocation_not_deleted_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD)



(* System transition: Callback invocation (deleted) [DONE] *)

definition callback_invocation_deleted_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "callback_invocation_deleted_pre n S = (n < length (messages S) \<and> (case messages S ! n of Response_message (From_canister ctxt_id c) resp ref_cycles \<Rightarrow>
    (case list_map_get (call_contexts S) ctxt_id of Some ctxt \<Rightarrow>
      let cid = call_ctxt_canister ctxt in
      call_ctxt_deleted ctxt \<and>
      (case list_map_get (balances S) cid of Some bal \<Rightarrow> True
      | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition callback_invocation_deleted_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "callback_invocation_deleted_post n S = (case messages S ! n of Response_message (From_canister ctxt_id c) resp ref_cycles \<Rightarrow>
    (case list_map_get (call_contexts S) ctxt_id of Some ctxt \<Rightarrow>
      let cid = call_ctxt_canister ctxt in
      (case list_map_get (balances S) cid of Some bal \<Rightarrow>
        S\<lparr>balances := list_map_set (balances S) cid (bal + ref_cycles + MAX_CYCLES_PER_RESPONSE),
          messages := take n (messages S) @ drop (Suc n) (messages S)\<rparr>)))"

lemma callback_invocation_deleted_cycles_inv:
  assumes "callback_invocation_deleted_pre n S"
  shows "total_cycles S = total_cycles (callback_invocation_deleted_post n S)"
proof -
  obtain ctxt_id c resp ref_cycles where msg: "messages S ! n = Response_message (From_canister ctxt_id c) resp ref_cycles"
    using assms
    by (auto simp: callback_invocation_deleted_pre_def split: message.splits option.splits call_origin.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Response_message (From_canister ctxt_id c) resp ref_cycles # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: callback_invocation_deleted_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: callback_invocation_deleted_pre_def callback_invocation_deleted_post_def total_cycles_def call_ctxt_carried_cycles Let_def msgs
        list_map_sum_in[where ?g=id and ?f="balances S"] split: option.splits)
qed

lemma callback_invocation_deleted_ic_inv:
  assumes "callback_invocation_deleted_pre n S" "ic_inv S"
  shows "ic_inv (callback_invocation_deleted_post n S)"
  using assms
  by (auto simp: ic_inv_def callback_invocation_deleted_pre_def callback_invocation_deleted_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD)



(* System transition: Respond to user request [DONE] *)

definition respond_to_user_request_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "respond_to_user_request_pre n S = (n < length (messages S) \<and> (case messages S ! n of Response_message (From_user req) resp ref_cycles \<Rightarrow>
    (case list_map_get (requests S) req of Some Processing \<Rightarrow> True
    | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition respond_to_user_request_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "respond_to_user_request_post n S = (case messages S ! n of Response_message (From_user req) resp ref_cycles \<Rightarrow>
    let req_resp = (case resp of Reply b \<Rightarrow> Replied b | response.Reject c b \<Rightarrow> Rejected c b) in
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
      requests := list_map_set (requests S) req req_resp\<rparr>)"

definition respond_to_user_request_burned_cycles :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "respond_to_user_request_burned_cycles n S = (case messages S ! n of Response_message (From_user req) resp ref_cycles \<Rightarrow>
    ref_cycles)"

lemma respond_to_user_request_cycles_monotonic:
  assumes "respond_to_user_request_pre n S"
  shows "total_cycles S = total_cycles (respond_to_user_request_post n S) + respond_to_user_request_burned_cycles n S"
proof -
  obtain req resp ref_cycles where msg: "messages S ! n = Response_message (From_user req) resp ref_cycles"
    using assms
    by (auto simp: respond_to_user_request_pre_def split: message.splits option.splits call_origin.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Response_message (From_user req) resp ref_cycles # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: respond_to_user_request_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: respond_to_user_request_pre_def respond_to_user_request_post_def respond_to_user_request_burned_cycles_def total_cycles_def call_ctxt_carried_cycles Let_def msgs
        list_map_sum_in[where ?g=id and ?f="balances S"] split: option.splits request_status.splits)
qed

lemma respond_to_user_request_ic_inv:
  assumes "respond_to_user_request_pre n S" "ic_inv S"
  shows "ic_inv (respond_to_user_request_post n S)"
  using assms
  by (auto simp: ic_inv_def respond_to_user_request_pre_def respond_to_user_request_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD nth_mem[of n "messages S"] in_set_updD)



(* System transition: Request clean up [DONE] *)

definition request_cleanup_pre :: "'p request \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "request_cleanup_pre req S = (case list_map_get (requests S) req of Some req_status \<Rightarrow>
    (case req_status of Replied _ \<Rightarrow> True | Rejected _ _ \<Rightarrow> True | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

definition request_cleanup_post :: "'p request \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "request_cleanup_post req S = (S\<lparr>requests := list_map_set (requests S) req Done\<rparr>)"

lemma request_cleanup_cycles_inv:
  assumes "request_cleanup_pre n S"
  shows "total_cycles S = total_cycles (request_cleanup_post n S)"
  by (auto simp: request_cleanup_post_def total_cycles_def)

lemma request_cleanup_ic_inv:
  assumes "request_cleanup_pre req S" "ic_inv S"
  shows "ic_inv (request_cleanup_post req S)"
  using assms
  by (auto simp: ic_inv_def request_cleanup_pre_def request_cleanup_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD in_set_updD)



(* System transition: Request clean up (expired) [DONE] *)

definition request_cleanup_expired_pre :: "'p request \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "request_cleanup_expired_pre req S = (case list_map_get (requests S) req of Some req_status \<Rightarrow>
    (case req_status of Replied _ \<Rightarrow> True | Rejected _ _ \<Rightarrow> True | Done \<Rightarrow> True | _ \<Rightarrow> False) \<and>
    request.ingress_expiry req < system_time S
    | _ \<Rightarrow> False)"

definition request_cleanup_expired_post :: "'p request \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "request_cleanup_expired_post req S = (S\<lparr>requests := list_map_del (requests S) req\<rparr>)"

lemma request_cleanup_expired_cycles_inv:
  assumes "request_cleanup_expired_pre n S"
  shows "total_cycles S = total_cycles (request_cleanup_expired_post n S)"
  by (auto simp: request_cleanup_expired_post_def total_cycles_def)

lemma request_cleanup_expired_ic_inv:
  assumes "request_cleanup_expired_pre req S" "ic_inv S"
  shows "ic_inv (request_cleanup_expired_post req S)"
  using assms
  by (auto simp: ic_inv_def request_cleanup_expired_pre_def request_cleanup_expired_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD in_set_updD)



(* System transition: Canister out of cycles [DONE] *)

definition canister_out_of_cycles_pre :: "'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "canister_out_of_cycles_pre cid S = (case list_map_get (balances S) cid of Some 0 \<Rightarrow> True
  | _ \<Rightarrow> False)"

definition canister_out_of_cycles_post :: "'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "canister_out_of_cycles_post cid S = (
    let call_ctxt_to_msg = (\<lambda>ctxt.
      if call_ctxt_canister ctxt = cid \<and> call_ctxt_needs_to_respond ctxt then
        Some (Response_message (call_ctxt_origin ctxt) (response.Reject CANISTER_REJECT (STR ''Canister has been uninstalled'')) (call_ctxt_available_cycles ctxt))
      else None);
    call_ctxt_to_ctxt = (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_delete ctxt else ctxt) in
    S\<lparr>canisters := list_map_set (canisters S) cid None, certified_data := list_map_set (certified_data S) cid [],
      messages := messages S @ List.map_filter call_ctxt_to_msg (list_map_vals (call_contexts S)),
      call_contexts := list_map_map call_ctxt_to_ctxt (call_contexts S)\<rparr>)"

lemma canister_out_of_cycles_cycles_inv:
  assumes "canister_out_of_cycles_pre cid S"
  shows "total_cycles S = total_cycles (canister_out_of_cycles_post cid S)"
proof -
  have F1: "list_map_sum_vals call_ctxt_carried_cycles (call_contexts S) =
    list_map_sum_vals id
      (list_map_map (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_carried_cycles ctxt else 0) (call_contexts S)) +
    list_map_sum_vals call_ctxt_carried_cycles
      (list_map_map (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_delete ctxt else ctxt) (call_contexts S))"
    using list_map_sum_vals_split[where ?f="call_ctxt_carried_cycles" and ?g="call_ctxt_delete", unfolded call_ctxt_delete_carried_cycles diff_zero]
    by auto
  show ?thesis
    using assms
    by (auto simp: canister_out_of_cycles_pre_def canister_out_of_cycles_post_def total_cycles_def call_ctxt_carried_cycles Let_def F1
        split: message.splits option.splits sum.splits if_splits intro!: list_map_sum_vals_filter)
qed

lemma canister_out_of_cycles_ic_inv:
  assumes "canister_out_of_cycles_pre cid S" "ic_inv S"
  shows "ic_inv (canister_out_of_cycles_post cid S)"
  using assms
  by (auto simp: ic_inv_def canister_out_of_cycles_pre_def canister_out_of_cycles_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* System transition: Time progressing and cycle consumption (canister time) [DONE] *)

definition canister_time_progress_pre :: "'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "canister_time_progress_pre cid t1 S = (case list_map_get (time S) cid of Some t0 \<Rightarrow>
      t0 < t1
    | _ \<Rightarrow> False)"

definition canister_time_progress_post :: "'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "canister_time_progress_post cid t1 S = (S\<lparr>time := list_map_set (time S) cid t1\<rparr>)"

lemma canister_time_progress_cycles_inv:
  assumes "canister_time_progress_pre cid t1 S"
  shows "total_cycles S = total_cycles (canister_time_progress_post cid t1 S)"
  by (auto simp: canister_time_progress_post_def total_cycles_def)

lemma canister_time_progress_ic_inv:
  assumes "canister_time_progress_pre cid t1 S" "ic_inv S"
  shows "ic_inv (canister_time_progress_post cid t1 S)"
  using assms
  by (auto simp: ic_inv_def canister_time_progress_pre_def canister_time_progress_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* System transition: Time progressing and cycle consumption (cycle consumption) [DONE] *)

definition cycle_consumption_pre :: "'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "cycle_consumption_pre cid b1 S = (case list_map_get (balances S) cid of Some b0 \<Rightarrow>
      0 \<le> b1 \<and> b1 < b0
    | _ \<Rightarrow> False)"

definition cycle_consumption_post :: "'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "cycle_consumption_post cid b1 S = (S\<lparr>balances := list_map_set (balances S) cid b1\<rparr>)"

definition cycle_consumption_burned_cycles :: "'p \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> nat" where
  "cycle_consumption_burned_cycles cid b1 S = the (list_map_get (balances S) cid) - b1"

lemma cycle_consumption_cycles_monotonic:
  assumes "cycle_consumption_pre cid b1 S"
  shows "total_cycles S = total_cycles (cycle_consumption_post cid b1 S) + cycle_consumption_burned_cycles cid b1 S"
  using assms list_map_sum_in_ge[where ?g=id and ?f="balances S" and ?x=cid]
  by (auto simp: cycle_consumption_pre_def cycle_consumption_post_def cycle_consumption_burned_cycles_def total_cycles_def
      list_map_sum_in[where ?g=id and ?f="balances S"] split: option.splits)

lemma cycle_consumption_ic_inv:
  assumes "cycle_consumption_pre cid b1 S" "ic_inv S"
  shows "ic_inv (cycle_consumption_post cid b1 S)"
  using assms
  by (auto simp: ic_inv_def cycle_consumption_pre_def cycle_consumption_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* System transition: Time progressing and cycle consumption (system time) [DONE] *)

definition system_time_progress_pre :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  "system_time_progress_pre t1 S = (system_time S < t1)"

definition system_time_progress_post :: "nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic" where
  "system_time_progress_post t1 S = (S\<lparr>system_time := t1\<rparr>)"

lemma system_time_progress_cycles_inv:
  assumes "system_time_progress_pre t1 S"
  shows "total_cycles S = total_cycles (system_time_progress_post t1 S)"
  by (auto simp: system_time_progress_post_def total_cycles_def)

lemma system_time_progress_ic_inv:
  assumes "system_time_progress_pre t1 S" "ic_inv S"
  shows "ic_inv (system_time_progress_post t1 S)"
  using assms
  by (auto simp: ic_inv_def system_time_progress_pre_def system_time_progress_post_def Let_def
      split: sum.splits message.splits call_origin.splits option.splits if_splits can_status.splits
      dest!: in_set_takeD in_set_dropD in_set_updD list_map_range_setD list_map_get_range list_map_range_del
      in_set_map_filter_vals)



(* State machine *)

inductive ic_steps :: "'sig itself \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow>
  nat \<Rightarrow> nat \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> bool" where
  ic_steps_refl: "ic_steps sig S 0 0 S"
| request_submission: "ic_steps sig S0 minted burned S \<Longrightarrow> request_submission_pre (E :: ('p, 'pk, 'sig) envelope) ECID S \<Longrightarrow> ic_steps sig S0 minted (burned + request_submission_burned_cycles E ECID S) (request_submission_post E ECID S)"
| request_rejection: "ic_steps sig S0 minted burned S \<Longrightarrow> request_rejection_pre req code msg S \<Longrightarrow> ic_steps sig S0 minted burned (request_rejection_post req code msg S)"
| initiate_canister_call: "ic_steps sig S0 minted burned S \<Longrightarrow> initiate_canister_call_pre req S \<Longrightarrow> ic_steps sig S0 minted burned (initiate_canister_call_post req S)"
| call_reject: "ic_steps sig S0 minted burned S \<Longrightarrow> call_reject_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (call_reject_post n S)"
| call_context_create: "ic_steps sig S0 minted burned S \<Longrightarrow> call_context_create_pre n ctxt_id S \<Longrightarrow> ic_steps sig S0 minted burned (call_context_create_post n ctxt_id S)"
| call_context_heartbeat: "ic_steps sig S0 minted burned S \<Longrightarrow> call_context_heartbeat_pre cee ctxt_id S \<Longrightarrow> ic_steps sig S0 minted burned (call_context_heartbeat_post cee ctxt_id S)"
| message_execution: "ic_steps sig S0 minted burned S \<Longrightarrow> message_execution_pre n S \<Longrightarrow> ic_steps sig S0 minted (burned + message_execution_burned_cycles n S) (message_execution_post n S)"
| call_context_starvation: "ic_steps sig S0 minted burned S \<Longrightarrow> call_context_starvation_pre ctxt_id S \<Longrightarrow> ic_steps sig S0 minted burned (call_context_starvation_post ctxt_id S)"
| call_context_removal: "ic_steps sig S0 minted burned S \<Longrightarrow> call_context_removal_pre ctxt_id S \<Longrightarrow> ic_steps sig S0 minted (burned + call_context_removal_burned_cycles ctxt_id S) (call_context_removal_post ctxt_id S)"
| ic_canister_creation: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_canister_creation_pre n cid t S \<Longrightarrow> ic_steps sig S0 minted burned (ic_canister_creation_post n cid t S)"
| ic_update_settings: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_update_settings_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (ic_update_settings_post n S)"
| ic_canister_status: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_canister_status_pre n m S \<Longrightarrow> ic_steps sig S0 minted burned (ic_canister_status_post n m S)"
| ic_code_installation: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_code_installation_pre n S \<Longrightarrow> ic_steps sig S0 minted (burned + ic_code_installation_burned_cycles n S) (ic_code_installation_post n S)"
| ic_code_upgrade: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_code_upgrade_pre n S \<Longrightarrow> ic_steps sig S0 minted (burned + ic_code_upgrade_burned_cycles n S) (ic_code_upgrade_post n S)"
| ic_code_uninstallation: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_code_uninstallation_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (ic_code_uninstallation_post n S)"
| ic_canister_stop_running: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_canister_stop_running_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (ic_canister_stop_running_post n S)"
| ic_canister_stop_stopping: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_canister_stop_stopping_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (ic_canister_stop_stopping_post n S)"
| ic_canister_stop_done_stopping: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_canister_stop_done_stopping_pre cid S \<Longrightarrow> ic_steps sig S0 minted burned (ic_canister_stop_done_stopping_post cid S)"
| ic_canister_stop_stopped: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_canister_stop_stopped_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (ic_canister_stop_stopped_post n S)"
| ic_canister_start_not_stopping: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_canister_start_not_stopping_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (ic_canister_start_not_stopping_post n S)"
| ic_canister_start_stopping: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_canister_start_stopping_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (ic_canister_start_stopping_post n S)"
| ic_canister_deletion: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_canister_deletion_pre n S \<Longrightarrow> ic_steps sig S0 minted (burned + ic_canister_deletion_burned_cycles n S) (ic_canister_deletion_post n S)"
| ic_depositing_cycles: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_depositing_cycles_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (ic_depositing_cycles_post n S)"
| ic_random_numbers: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_random_numbers_pre n b S \<Longrightarrow> ic_steps sig S0 minted burned (ic_random_numbers_post n b S)"
| ic_provisional_canister_creation: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_provisional_canister_creation_pre n cid t S \<Longrightarrow> ic_steps sig S0 (minted + ic_provisional_canister_creation_minted_cycles n cid t S) burned (ic_provisional_canister_creation_post n cid t S)"
| ic_top_up_canister: "ic_steps sig S0 minted burned S \<Longrightarrow> ic_top_up_canister_pre n S \<Longrightarrow> ic_steps sig S0 (minted + ic_top_up_canister_minted_cycles n S) burned (ic_top_up_canister_post n S)"
| callback_invocation_not_deleted: "ic_steps sig S0 minted burned S \<Longrightarrow> callback_invocation_not_deleted_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (callback_invocation_not_deleted_post n S)"
| callback_invocation_deleted: "ic_steps sig S0 minted burned S \<Longrightarrow> callback_invocation_deleted_pre n S \<Longrightarrow> ic_steps sig S0 minted burned (callback_invocation_deleted_post n S)"
| respond_to_user_request: "ic_steps sig S0 minted burned S \<Longrightarrow> respond_to_user_request_pre n S \<Longrightarrow> ic_steps sig S0 minted (burned + respond_to_user_request_burned_cycles n S) (respond_to_user_request_post n S)"
| request_cleanup: "ic_steps sig S0 minted burned S \<Longrightarrow> request_cleanup_pre req S \<Longrightarrow> ic_steps sig S0 minted burned (request_cleanup_post req S)"
| request_cleanup_expired: "ic_steps sig S0 minted burned S \<Longrightarrow> request_cleanup_expired_pre req S \<Longrightarrow> ic_steps sig S0 minted burned (request_cleanup_expired_post req S)"
| canister_out_of_cycles: "ic_steps sig S0 minted burned S \<Longrightarrow> canister_out_of_cycles_pre cid S \<Longrightarrow> ic_steps sig S0 minted burned (canister_out_of_cycles_post cid S)"
| canister_time_progress: "ic_steps sig S0 minted burned S \<Longrightarrow> canister_time_progress_pre cid t1 S \<Longrightarrow> ic_steps sig S0 minted burned (canister_time_progress_post cid t1 S)"
| cycle_consumption: "ic_steps sig S0 minted burned S \<Longrightarrow> cycle_consumption_pre cid b1 S \<Longrightarrow> ic_steps sig S0 minted (burned + cycle_consumption_burned_cycles cid b1 S) (cycle_consumption_post cid b1 S)"
| system_time_progress: "ic_steps sig S0 minted burned S \<Longrightarrow> system_time_progress_pre t1 S \<Longrightarrow> ic_steps sig S0 minted burned (system_time_progress_post t1 S)"

lemma total_cycles:
  assumes "ic_steps TYPE('sig) S0 minted burned S"
  shows "total_cycles S0 + minted = total_cycles S + burned"
  using assms
  apply (induction "TYPE('sig)" S0 minted burned S rule: ic_steps.induct)
                      apply auto[1]
  using request_submission_cycles_inv apply fastforce
  using request_rejection_cycles_inv apply fastforce
  using initiate_canister_call_cycles_inv apply fastforce
  using call_reject_cycles_inv apply fastforce
  using call_context_create_cycles_inv apply fastforce
  using call_context_heartbeat_cycles_inv apply fastforce
  using message_execution_cycles_monotonic apply fastforce
  using call_context_starvation_cycles_inv apply fastforce
  using call_context_removal_cycles_monotonic apply fastforce
  using ic_canister_creation_cycles_inv apply fastforce
  using ic_update_settings_cycles_inv apply fastforce
  using ic_canister_status_cycles_inv apply fastforce
  using ic_code_installation_cycles_inv apply fastforce
  using ic_code_upgrade_cycles_inv apply fastforce
  using ic_code_uninstallation_cycles_inv apply fastforce
  using ic_canister_stop_running_cycles_inv apply fastforce
  using ic_canister_stop_stopping_cycles_inv apply fastforce
  using ic_canister_stop_done_stopping_cycles_inv apply fastforce
  using ic_canister_stop_stopped_cycles_inv apply fastforce
  using ic_canister_start_not_stopping_cycles_inv apply fastforce
  using ic_canister_start_stopping_cycles_inv apply fastforce
  using ic_canister_deletion_cycles_monotonic apply fastforce
  using ic_depositing_cycles_cycles_monotonic apply fastforce
  using ic_random_numbers_cycles_inv apply fastforce
  using ic_provisional_canister_creation_cycles_antimonotonic apply fastforce
  using ic_top_up_canister_cycles_antimonotonic apply fastforce
  using callback_invocation_not_deleted_cycles_inv apply fastforce
  using callback_invocation_deleted_cycles_inv apply fastforce
  using respond_to_user_request_cycles_monotonic apply fastforce
  using request_cleanup_cycles_inv apply fastforce
  using request_cleanup_expired_cycles_inv apply fastforce
  using canister_out_of_cycles_cycles_inv apply fastforce
  using canister_time_progress_cycles_inv apply fastforce
  using cycle_consumption_cycles_monotonic apply fastforce
  using system_time_progress_cycles_inv apply fastforce
  done

lemma ic_inv:
  assumes "ic_steps TYPE('sig) S0 minted burned S"
  shows "ic_inv S0 \<Longrightarrow> ic_inv S"
  using assms
  apply (induction "TYPE('sig)" S0 minted burned S rule: ic_steps.induct)
                      apply auto[1]
  using request_submission_ic_inv apply fastforce
  using request_rejection_ic_inv apply fastforce
  using initiate_canister_call_ic_inv apply fastforce
  using call_reject_ic_inv apply fastforce
  using call_context_create_ic_inv apply fastforce
  using call_context_heartbeat_ic_inv apply fastforce
  using message_execution_ic_inv apply fastforce
  using call_context_starvation_ic_inv apply fastforce
  using call_context_removal_ic_inv apply fastforce
  using ic_canister_creation_ic_inv apply fastforce
  using ic_update_settings_ic_inv apply fastforce
  using ic_canister_status_ic_inv apply fastforce
  using ic_code_installation_ic_inv apply fastforce
  using ic_code_upgrade_ic_inv apply fastforce
  using ic_code_uninstallation_ic_inv apply fastforce
  using ic_canister_stop_running_ic_inv apply fastforce
  using ic_canister_stop_stopping_ic_inv apply fastforce
  using ic_canister_stop_done_stopping_ic_inv apply fastforce
  using ic_canister_stop_stopped_ic_inv apply fastforce
  using ic_canister_start_not_stopping_ic_inv apply fastforce
  using ic_canister_start_stopping_ic_inv apply fastforce
  using ic_canister_deletion_ic_inv apply fastforce
  using ic_depositing_cycles_ic_inv apply fastforce
  using ic_random_numbers_ic_inv apply fastforce
  using ic_provisional_canister_creation_ic_inv apply fastforce
  using ic_top_up_canister_ic_inv apply fastforce
  using callback_invocation_not_deleted_ic_inv apply fastforce
  using callback_invocation_deleted_ic_inv apply fastforce
  using respond_to_user_request_ic_inv apply fastforce
  using request_cleanup_ic_inv apply fastforce
  using request_cleanup_expired_ic_inv apply fastforce
  using canister_out_of_cycles_ic_inv apply fastforce
  using canister_time_progress_ic_inv apply fastforce
  using cycle_consumption_ic_inv apply fastforce
  using system_time_progress_ic_inv apply fastforce
  done



(* Query call *)

definition fold_htree_of :: "(blob \<times> htree) list \<Rightarrow> htree" where
  "fold_htree_of lts = fold (\<lambda>(lab, tree) t. let n = Labeled lab tree in case t of Empty \<Rightarrow> n | _ \<Rightarrow> Fork n t) (rev (sort_key fst lts)) Empty"

lemma lookup_path_fold_htree_of: "distinct (map fst lts) \<Longrightarrow> lookup_path (p # ps) (fold_htree_of lts) = undefined"
  oops

lemma wf_fold_htree_of: "(\<And>t. t \<in> snd ` set lts \<Longrightarrow> wf_tree t) \<Longrightarrow> distinct (map fst lts) \<Longrightarrow> wf_tree (fold_htree_of lts)"
  oops

fun request_status_tree :: "request_status \<Rightarrow> htree" where
  "request_status_tree Received = Labeled (blob_of_text (STR ''status'')) (Leaf (blob_of_text (STR ''Received'')))"
| "request_status_tree Processing = Labeled (blob_of_text (STR ''status'')) (Leaf (blob_of_text (STR ''Processing'')))"
| "request_status_tree (Rejected code msg) = fold_htree_of
    [(blob_of_text (STR ''status''), Leaf (blob_of_text (STR ''Rejected''))),
    (blob_of_text (STR ''reject_code''), Leaf (blob_of_nat code)),
    (blob_of_text (STR ''reject_message''), Leaf (blob_of_text msg)),
    (blob_of_text (STR ''error_code''), Leaf (blob_of_nat request_error_code))]"
| "request_status_tree (Replied b) = fold_htree_of [(blob_of_text (STR ''status''), Leaf (blob_of_text (STR ''Replied''))),
    (blob_of_text (STR ''reply''), Leaf b)]"
| "request_status_tree Done = Labeled (blob_of_text (STR ''status'')) (Leaf (blob_of_text (STR ''Done'')))"

definition state_tree :: "('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> htree" where
  "state_tree S = fold_htree_of
    [(blob_of_text (STR ''time''), (Leaf (blob_of_nat (system_time S)))),
    (blob_of_text (STR ''subnet''), fold_htree_of (map (\<lambda>(sid, pk, sk, rans). (blob_of_principal sid, fold_htree_of (
      [(blob_of_text (STR ''public_key''), Leaf (blob_of_pk pk)), (blob_of_text (STR ''canister_ranges''), Leaf (cbor_of_canister_ranges rans))]
    ))) (subnets S))),
    (blob_of_text (STR ''request_status''), fold_htree_of (map (\<lambda>(r, s).
      (hash_of_user_request (Inl r), request_status_tree s)
    ) (Rep_list_map (requests S)))),
    (blob_of_text (STR ''canister''), fold_htree_of (map (\<lambda>(cid, can).
      (blob_of_principal cid, fold_htree_of (
        (case can of None \<Rightarrow> [] | Some c \<Rightarrow>
          [(blob_of_text (STR ''module_hash''), Leaf (sha_256 (raw_module c)))]) @
        (case list_map_get (controllers S) cid of None \<Rightarrow> [] | Some ctrls \<Rightarrow>
          [(blob_of_text (STR ''controllers''), Leaf (cbor_of_principals (principal_list_of_set ctrls)))]) @
        (case list_map_get (certified_data S) cid of None \<Rightarrow> [] | Some data \<Rightarrow>
          [(blob_of_text (STR ''certified_data''), Leaf data)]) @
        (case can of None \<Rightarrow> [] | Some c \<Rightarrow>
          [(blob_of_text (STR ''metadata''), fold_htree_of (map (\<lambda>(name, b). (blob_of_text name, Leaf b)) (Rep_list_map (public_custom_sections c) @ Rep_list_map (private_custom_sections c))))]
        )
    ))) (Rep_list_map (canisters S))))]"

fun prune_htree :: "path list \<Rightarrow> path \<Rightarrow> htree \<Rightarrow> htree" where
  "prune_htree ps p (Empty) = Empty"
| "prune_htree ps p (Fork t1 t2) = (case (prune_htree ps p t1, prune_htree ps p t2) of (Pruned h1, Pruned h2) \<Rightarrow> Pruned (reconstruct (Fork (Pruned h1) (Pruned h2))) | (t1', t2') \<Rightarrow> Fork t1' t2')"
| "prune_htree ps p (Labeled l t) = (if p @ [l] \<in> set ps then Labeled l (prune_htree ps (p @ [l]) t) else Pruned (reconstruct (Labeled l t)))"
| "prune_htree ps p (Leaf v) = (if p \<in> set ps then Leaf v else Pruned (reconstruct (Leaf v)))"
| "prune_htree ps p (Pruned h) = Pruned h"

lemma all_paths_prune_htree: "all_paths p (prune_htree ps p t) \<subseteq> set ps"
  by (induction ps p t rule: prune_htree.induct) (auto split: htree.splits)

lemma reconstruct_prune_htree[simp]: "reconstruct (prune_htree ps p t) = reconstruct t"
  by (induction ps p t rule: prune_htree.induct) (auto split: htree.splits)

definition pruned_state_tree :: "path list \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> htree" where
  "pruned_state_tree ps S = prune_htree (ps @ [[blob_of_text (STR ''time'')]]) [] (state_tree S)"

lemma all_paths_pruned_state_tree: "all_paths [] (pruned_state_tree ps S) \<subseteq> set ps \<union> {[blob_of_text (STR ''time'')]}"
  using all_paths_prune_htree
  by (force simp: pruned_state_tree_def)

definition comp_cert :: "path list \<Rightarrow> 'p \<Rightarrow> 'p request option \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'sig) certificate option" where
  "comp_cert ps ECID r S = (
    let t = pruned_state_tree ps S;
    h = domain_sep (blob_of_text (STR ''ic-state-root'')) @ reconstruct t;
    ECID' = (case r of Some req \<Rightarrow>
      (case lookup_path [blob_of_text (STR ''request_status''), hash_of_user_request (Inl req), blob_of_text (STR ''reply'')] t of
        Found v \<Rightarrow> the (candid_parse_cid v)
      | _ \<Rightarrow> ECID)
    | _ \<Rightarrow> ECID);
    subnet = find (\<lambda>(sid, pk, sk, rans). \<exists>(a, b) \<in> set rans. a \<le> ECID' \<and> ECID' \<le> b) (subnets S);
    st = pruned_state_tree [[blob_of_text (STR ''time'')], [blob_of_text (STR ''subnet'')]] S;
    sh = domain_sep (blob_of_text (STR ''ic-state-root'')) @ reconstruct st in
    if (case r of Some req \<Rightarrow> \<not>cert_special (all_paths [] t) ECID req | _ \<Rightarrow> False) then None else
    case subnet of Some (sid, pk, sk, rans) \<Rightarrow>
      Some (Certificate t (sign sk h) (Some (Delegation sid (Certificate st (sign (secret_root_key S) sh) None))))
    | _ \<Rightarrow> (case r of Some req \<Rightarrow> Some (Certificate t (sign (secret_root_key S) h) None) | _ \<Rightarrow> None)
  )"

lemma fold_cong: "(\<And>x z. x \<in> set xs \<Longrightarrow> f x z = g x z) \<Longrightarrow> fold f xs z = fold g xs z"
  by (induction xs arbitrary: z rule: rev_induct) auto

lemma fold_propI: "(\<And>x. x \<in> set xs \<Longrightarrow> Q x \<Longrightarrow> P (f x)) \<Longrightarrow> P z \<Longrightarrow> P (fold (\<lambda>x z. if Q x then f x else z) xs z)"
  by (induction xs rule: rev_induct) auto

lemma cert_special_mono: "ps' \<subseteq> (ps \<union> {[blob_of_text (STR ''time'')]}) \<Longrightarrow> cert_special ps ECID req \<Longrightarrow> cert_special ps' ECID req"
  by (auto simp: cert_special_def)

lemma verify_cert_comp_cert:
  assumes comp_cert: "comp_cert ps ECID r S = Some cert"
    and A1: "case extract_der (blob_of_pk (public_root_key S)) of Some bls_key \<Rightarrow> \<forall>h. verify_bls_signature bls_key (sign (secret_root_key S) h) h | _ \<Rightarrow> False"
    and A2: "\<And>sid sk pk rans. (sid, pk, sk, rans) \<in> set (subnets S) \<Longrightarrow> case extract_der (blob_of_pk pk) of Some bls_key \<Rightarrow> \<forall>h. verify_bls_signature bls_key (sign sk h) h | _ \<Rightarrow> False"
  shows "verify_cert (public_root_key S) ECID r cert"
proof -
  define t where "t = pruned_state_tree ps S"
  define h where "h = domain_sep (blob_of_text (STR ''ic-state-root'')) @ reconstruct t"
  define ECID' where "ECID' = (case r of Some req \<Rightarrow>
    (case lookup_path [blob_of_text (STR ''request_status''), hash_of_user_request (Inl req), blob_of_text (STR ''reply'')] t of
      Found v \<Rightarrow> the (candid_parse_cid v)
    | _ \<Rightarrow> ECID)
  | _ \<Rightarrow> ECID)"
  have ECID_eq_ECID'_unless_req: "case r of Some req \<Rightarrow> True | _ \<Rightarrow> ECID = ECID'"
    by (auto simp: ECID'_def split: option.splits)
  define st where "st = pruned_state_tree [[blob_of_text (STR ''time'')], [blob_of_text (STR ''subnet'')]] S"
  define sh where "sh = domain_sep (blob_of_text (STR ''ic-state-root'')) @ reconstruct st"
  define subnet where "subnet = find (\<lambda>(sid, pk, sk, rans). \<exists>(a, b) \<in> set rans. a \<le> ECID' \<and> ECID' \<le> b) (subnets S)"
  have cert_tree: "cert_tree cert = t"
    using comp_cert
    by (auto simp: comp_cert_def t_def[symmetric] h_def[symmetric] ECID'_def[symmetric] st_def[symmetric] sh_def[symmetric] subnet_def[symmetric] split: option.splits if_splits)
  have "verify_cert_impl (public_root_key S) x (Certificate t (sign (secret_root_key S) h) None)" for x
    using A1
    by (auto simp: h_def split: option.splits)
  have all_paths: "all_paths [] t \<subseteq> set ps \<union> {[blob_of_text (STR ''time'')]}"
    using all_paths_pruned_state_tree
    by (auto simp: t_def)
  have cert_special_if_req: "cert_special (all_paths [] t) ECID req" if r: "r = Some req" for req
    using comp_cert
    by (auto simp: comp_cert_def t_def[symmetric] h_def[symmetric] ECID'_def[symmetric] st_def[symmetric] sh_def[symmetric] subnet_def[symmetric] split: option.splits if_splits)
       (auto simp: r)
  show ?thesis
  proof (cases subnet)
    case None
    obtain req where r: "r = Some req"
      using comp_cert
      by (auto simp: comp_cert_def t_def[symmetric] h_def[symmetric] ECID'_def[symmetric] st_def[symmetric] sh_def[symmetric] subnet_def[symmetric] None split: option.splits if_splits)
    have lup: "lookup [blob_of_text (STR ''request_status''), hash_of_user_request (Inl req), blob_of_text (STR ''reply'')] (Certificate t (sign (secret_root_key S) h) None) = Found v \<Longrightarrow>
      (case candid_parse_cid v of Some cid \<Rightarrow> True | _ \<Rightarrow> False)" for v
      apply (auto simp: lookup_def cert_tree split: lookup_result.splits option.splits if_splits)
      sorry
    show ?thesis
      using comp_cert A1 cert_special_if_req cert_special_mono[OF all_paths]
      by (auto simp: comp_cert_def t_def[symmetric] h_def[symmetric] ECID'_def[symmetric] st_def[symmetric] sh_def[symmetric] subnet_def[symmetric] verify_cert_def None
          split: option.splits if_splits lookup_result.splits)
         (auto simp: r dest!: lup split: option.splits)
  next
    case (Some s)
    obtain sid pk sk rans where s_def: "s = (sid, pk, sk, rans)"
      by (cases s) auto
    have cert: "cert = Certificate t (sign sk h) (Some (Delegation sid (Certificate st (sign (secret_root_key S) sh) None)))"
      using comp_cert
      by (auto simp: comp_cert_def t_def[symmetric] h_def[symmetric] ECID'_def[symmetric] st_def[symmetric] sh_def[symmetric] subnet_def[symmetric] Some s_def split: if_splits)
    have s_in_subnets: "(sid, pk, sk, rans) \<in> set (subnets S)" and ECID'_in_rans: "\<exists>(a, b) \<in> set rans. a \<le> ECID' \<and> ECID' \<le> b"
      using Some
      by (auto simp: subnet_def s_def find_Some_iff in_set_conv_nth)
    obtain b where b_def: "lookup [blob_of_text (STR ''subnet''), blob_of_principal sid, blob_of_text (STR ''canister_ranges'')] (Certificate st (sign (secret_root_key S) sh) (None :: ('p, 'sig) delegation option)) = Found b"
      sorry
    have parse_cbor: "parse_cbor_canister_ranges b = Some rans"
      sorry
    have lup: "lookup [blob_of_text (STR ''subnet''), blob_of_principal sid, blob_of_text (STR ''public_key'')] (Certificate st (sign (secret_root_key S) sh) (None :: ('p, 'sig) delegation option)) = Found (blob_of_pk pk)"
      sorry
    have lup_path: "lookup_path p t = lookup p (Certificate t (sign sk h) (Some (Delegation sid (Certificate st (sign (secret_root_key S) sh) None))))" for p
      by (auto simp: lookup_def)
    have cert_special: "case lookup [blob_of_text (STR ''request_status''), hash_of_user_request (Inl req), blob_of_text (STR ''reply'')]
      (Certificate t (sign sk h) (Some (Delegation sid (Certificate st (sign (secret_root_key S) sh) None)))) of
       Found v \<Rightarrow> candid_parse_cid v = Some ECID'
    | _ \<Rightarrow> ECID = ECID'" if cert_special: "cert_special (all_paths [] t) ECID req" and r: "r = Some req" for req
      using cert_special r
      apply (auto simp: ECID'_def[unfolded lup_path] split: option.splits lookup_result.splits)
      sorry
    show ?thesis
      using A1 A2[OF s_in_subnets] ECID'_in_rans ECID_eq_ECID'_unless_req cert_special_if_req
      by (auto simp: cert verify_cert_def b_def parse_cbor lup sh_def[symmetric] h_def[symmetric]
          split: option.splits lookup_result.splits dest!: cert_special)
  qed
qed

definition query_call :: "('p, 'pk, 'sig) envelope \<Rightarrow> 'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> query_response option" where
  "query_call E ECID S = (case content E of Inr (Inl q) \<Rightarrow>
    let cid = canister_id q in
    if cid \<in> verify_envelope E (request.sender q) (system_time S) \<and>
      is_effective_canister_id q ECID \<and>
      system_time S \<le> request.ingress_expiry q then
      (case (list_map_get (canisters S) cid, list_map_get (canister_status S) cid, list_map_get (balances S) cid, list_map_get (time S) cid) of
        (Some (Some can), Some Running, Some bal, Some t) \<Rightarrow>
        if bal \<ge> ic_freezing_limit S cid then
          (case list_map_get (canister_module_query_methods (module can)) (request.method_name q) of Some F \<Rightarrow>
            let Cert = the (comp_cert [[blob_of_text (STR ''time'')], [blob_of_text (STR ''canister''), blob_of_principal cid, blob_of_text (STR ''certified_data'')]] ECID None S);
            Env = \<lparr>env.time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = Some (blob_of_certificate Cert), status = status.Running\<rparr> in
            (case F (request.arg q, request.sender q, Env) (wasm_state can) of Inl _ \<Rightarrow> Some (query_response.Rejected CANISTER_ERROR query_reject_msg query_error_code)
            | Inr r \<Rightarrow>
              (case response r of Reply b \<Rightarrow> Some (query_response.Success b)
              | response.Reject code msg \<Rightarrow> Some (query_response.Rejected code msg query_error_code))
            )
          | _ \<Rightarrow> None)
        else None
      | _ \<Rightarrow> None)
    else None
  | _ \<Rightarrow> None)"



(* Certified state reads *)

definition may_read_path :: "'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> 'p \<Rightarrow> path \<Rightarrow> bool" where
  "may_read_path ECID S s p = (case p of a # bs \<Rightarrow>
    (a = blob_of_text (STR ''time'') \<and> bs = []) \<or>
    (a = blob_of_text (STR ''subnet'')) \<or>
    (a = blob_of_text (STR ''request_status'') \<and>
      (case bs of b # cs \<Rightarrow>
        \<forall>r \<in> list_map_dom (requests S). hash_of_user_request (Inl r) = b \<longrightarrow> s = request.sender r \<and> is_effective_canister_id r ECID
      | _ \<Rightarrow> False)
    ) \<or>
    (a = blob_of_text (STR ''canister'') \<and>
      (case bs of b # c # ds \<Rightarrow>
        b = blob_of_principal ECID \<and>
        (
          (c = blob_of_text (STR ''module_hash'') \<and> ds = []) \<or>
          (c = blob_of_text (STR ''controllers'') \<and> ds = []) \<or>
          (c = blob_of_text (STR ''metadata'') \<and>
            (case ds of [name] \<Rightarrow>
                (case list_map_get (canisters S) ECID of Some (Some can) \<Rightarrow>
                  (name \<in> blob_of_text ` list_map_dom (public_custom_sections can)) \<or>
                  (name \<in> blob_of_text ` list_map_dom (private_custom_sections can) \<and>
                    (case list_map_get (controllers S) ECID of Some ctrls \<Rightarrow> s \<in> ctrls
                    | _ \<Rightarrow> False)
                  )
                | _ \<Rightarrow> False)
            | _ \<Rightarrow> False)
          )
        )
      | _ \<Rightarrow> False)
    )
  | _ \<Rightarrow> False)"

definition read_state :: "('p, 'pk, 'sig) envelope \<Rightarrow> 'p \<Rightarrow> ('p, 'w, 'sm, 'c, 'cid, 'pk, 'sk) ic \<Rightarrow> ('p, 'sig) certificate option" where
  "read_state E ECID S = (case content E of (Inr (Inr req)) \<Rightarrow>
    let TS = verify_envelope E (sender req) (system_time S) in
    if system_time S \<le> ingress_expiry req \<and>
      (\<forall>p \<in> set (paths req). may_read_path ECID S (sender req) p) \<and>
      (\<forall>p \<in> set (paths req). case p of a # b # _ \<Rightarrow> a = blob_of_text (STR ''request_status'') \<longrightarrow>
        (\<exists>r \<in> list_map_dom (requests S). hash_of_user_request (Inl r) = b \<and> request.canister_id r \<in> TS)
      | _ \<Rightarrow> True)
    then comp_cert (paths req) ECID (map_option fst (find (\<lambda>(r, _). cert_special (set (paths req)) ECID r) (Rep_list_map (requests S)))) S
    else None
  | _ \<Rightarrow> None)"

end

export_code request_submission_pre request_submission_post
  request_rejection_pre request_rejection_post
  initiate_canister_call_pre initiate_canister_call_post
  call_reject_pre call_reject_post
  call_context_create_pre call_context_create_post
  call_context_heartbeat_pre call_context_heartbeat_post
  message_execution_pre message_execution_post
  call_context_starvation_pre call_context_starvation_post
  call_context_removal_pre call_context_removal_post
  ic_canister_creation_pre ic_canister_creation_post
  ic_update_settings_pre ic_update_settings_post
  ic_canister_status_pre ic_canister_status_post
  ic_code_installation_pre ic_code_installation_post
  ic_code_upgrade_pre ic_code_upgrade_post
  ic_code_uninstallation_pre ic_code_uninstallation_post
  ic_canister_stop_running_pre ic_canister_stop_running_post
  ic_canister_stop_stopping_pre ic_canister_stop_stopping_post
  ic_canister_stop_done_stopping_pre ic_canister_stop_done_stopping_post
  ic_canister_stop_stopped_pre ic_canister_stop_stopped_post
  ic_canister_start_not_stopping_pre ic_canister_start_not_stopping_post
  ic_canister_start_stopping_pre ic_canister_start_stopping_post
  ic_canister_deletion_pre ic_canister_deletion_post
  ic_depositing_cycles_pre ic_depositing_cycles_post
  ic_random_numbers_pre ic_random_numbers_post
  ic_provisional_canister_creation_pre ic_provisional_canister_creation_post
  ic_top_up_canister_pre ic_top_up_canister_post
  callback_invocation_not_deleted_pre callback_invocation_not_deleted_post
  callback_invocation_deleted_pre callback_invocation_deleted_post
  respond_to_user_request_pre respond_to_user_request_post
  request_cleanup_pre request_cleanup_post
  request_cleanup_expired_pre request_cleanup_expired_post
  canister_out_of_cycles_pre canister_out_of_cycles_post
  canister_time_progress_pre canister_time_progress_post
  cycle_consumption_pre cycle_consumption_post
  system_time_progress_pre system_time_progress_post
  query_call read_state
in Haskell module_name IC file_prefix code

end
