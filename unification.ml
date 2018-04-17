needs "cpril/kit.ml";;

type instor =
  (hol_type * hol_type) list * (term * term) list;;

module type Hunify_kernel =
  sig

    val inst_term : instor -> term -> term
    val inst_thm : instor -> thm -> thm
    val simplify : string list -> string list -> (term * term) list -> (term * string) list -> (term * term) list * (term * string) list * instor
    val hol_unify : string list -> string list -> (term * term) list -> (term * string) list -> instor option
    val hol_quick_check : (term * term) list -> (term * string) list -> bool

end;;

module Hunify : Hunify_kernel = struct

  let inst_term (tyins,tmins) tm =
    vsubst tmins (inst tyins tm)

  let inst_thm (tyins,tmins) th =
    INST tmins (INST_TYPE tyins th)

  let safe_tyins i theta =
    i::(map (fun (a,b) -> type_subst [i] a,b) theta)

  let safe_tmins i theta =
    map (fun (a,b) -> beta_eta_term (vsubst [i] a),b) theta

  let merge_ins (tyins1,tmins1) (tyins2,tmins2) =
    itlist safe_tyins tyins2 tyins1,
    itlist safe_tmins tmins2 (pmap (inst tyins2) tmins1)

  (* DONE CHECKING *)
  let type_unify (const_ty : string list) =
    let is_free_ty ty =
      match ty with
        Tyvar(name) -> not (mem name const_ty)
      | _ -> false in

    let rec tfree_in t ty =
      if is_vartype ty then Pervasives.compare t ty = 0
      else exists (tfree_in t) (snd (dest_type ty)) in

    let rec unify ty1 ty2 sofar =
      let ty1 = if is_free_ty ty1 then rev_assocd ty1 sofar ty1 else ty1 in
      let ty2 = if is_free_ty ty2 then rev_assocd ty2 sofar ty2 else ty2 in
      let ty1,ty2 = if is_free_ty ty2 then ty2,ty1 else ty1,ty2 in
      if is_free_ty ty1 then
        if is_vartype ty2 then
          if Pervasives.compare ty1 ty2 = 0 then sofar
          else safe_tyins (ty2,ty1) sofar
        else
          let ty2 = type_subst sofar ty2 in
          if tfree_in ty1 ty2 then failwith "type_unify"
          else safe_tyins (ty2,ty1) sofar
      else if is_type ty1 && is_type ty2 then
        let op1,args1 = dest_type ty1 and op2,args2 = dest_type ty2 in
        if op1 = op2 then itlist2 unify args1 args2 sofar
        else failwith "type_unify"
      else if Pervasives.compare ty1 ty2 = 0 then sofar
      else failwith "type_unify" in

    fun obj ->
      let obj = filter (fun (u,v) -> Pervasives.compare u v <> 0) obj in
      let obj1,obj2 = unzip obj in
      itlist2 unify obj1 obj2 []

  let init_data const_ty const_var (obj : (term * term) list) (rsl : (term * string) list) =
    let fvars = filter (fun v -> not (mem (name_of v) const_var)) (freesl ((let l,r = unzip obj in l @ r) @ (fst (unzip rsl)))) in
    let fnames = List.sort_uniq Pervasives.compare (map (fun x -> fst (dest_var x)) fvars) in
    if length fvars <> length fnames then failwith "init_data[fatal]: different free vars have same name"
    else try let tyins = type_unify const_ty (pmap type_of obj) in
             let obj = pmap (inst tyins) obj in
             let rsl = fst_map (inst tyins) rsl in
             let tmins = map (fun v -> let v' = inst tyins v in v',v') fvars in
             obj,rsl,(tyins,tmins)
         with Failure "type_unify" -> failwith "init_data"

  (* test whether the head symbol is a free variable of a term
   * DONE CHECKING
   *)
  let head_free const_var (tm : term) : bool =
    let bvars,tm = get_bound tm in
    let hsym = repeat rator tm in
    let name = name_of hsym in
    not (is_const hsym) && not (mem hsym bvars) && not (mem name const_var) && not (has_prefix name "mc")

  (* the type of every pairs in obj must be matched
   * the input might not be in normal forms
   *)
  let simplify const_ty const_var =
    let is_free_var v =
      is_var v && not (mem (name_of v) const_var) && not (has_prefix (name_of v) "mc") in

    let insert_tyins i theta =
      i::(map (fun (a,b) -> type_subst [i] a,b) theta) in

    let insert_tmins i theta =
      i::(map (fun (a,b) -> beta_eta_term (vsubst [i] a),b) theta) in

    (*
     * Strip off the binder \x where x does not occur in both terms
     * Then do eta-conversion to the remaining part, since bound-vars stripping
     * may generate new eta-redex
     * DONE CHECKING
     *)
    let rec bound_eta_norm (tm1,tm2) : term * term =
      match tm1,tm2 with
        Abs(bv1,bod1),Abs(bv2,bod2) ->
          let bod1,bod2 = bound_eta_norm (bod1,bod2) in
          if not (vfree_in bv1 bod1) && not (vfree_in bv2 bod2) then bod1,bod2
          else (try let f1,x1 = dest_comb bod1 in
                    if Pervasives.compare bv1 x1 = 0 && not (vfree_in bv1 f1) then f1
                    else mk_abs(bv1,bod1)
                with Failure _ -> mk_abs(bv1,bod1)),
               (try let f2,x2 = dest_comb bod2 in
                    if Pervasives.compare bv2 x2 = 0 && not (vfree_in bv2 f2) then f2
                    else mk_abs(bv2,bod2)
                with Failure _ -> mk_abs(bv2,bod2))
      | _ -> tm1,tm2 in

    (* remove unused bvars *)
    let rec remove_dummy_bvar tm =
      match tm with
        Abs(bv,bod) ->
          let bod = remove_dummy_bvar bod in
          if not (vfree_in bv bod) then bod
          else (try let f,x = dest_comb bod in
                    if Pervasives.compare bv x = 0 && not (vfree_in bv f) then f
                    else mk_abs(bv,bod)
                with Failure _ -> mk_abs(bv,bod))
      | _ -> tm in

    (* try to check rigid-rigid pairs
     * if rigid head not match then raise exception
     * else return type of pairs of const if type not match
     * DONE CHECKING
     *)
    let rec check_rr (obj : (term * term) list) : (hol_type * hol_type) list =
      match obj with
        (tm1,tm2)::t -> let bv1,(hs1,_) = decompose tm1 and bv2,(hs2,_) = decompose tm2 in
                        let bin1 = bindex hs1 bv1 and bin2 = bindex hs2 bv2 in
                        let rigid1 = is_const hs1 || bin1 >= 0 || (mem (name_of hs1) const_var) || (has_prefix (name_of hs1) "mc") in
                        let rigid2 = is_const hs2 || bin2 >= 0 || (mem (name_of hs2) const_var) || (has_prefix (name_of hs2) "mc") in
                        if rigid1 && rigid2 then
                          if bin1 < 0 && bin2 < 0 then
                            (* constant or const_var *)
                            if is_const hs1 then
                              if is_const hs2 then
                                if name_of hs1 <> name_of hs2 then failwith "check_rr"
                                else (type_of hs1,type_of hs2)::(check_rr t)
                              else failwith "check_rr"
                            else if Pervasives.compare hs1 hs2 <> 0 then failwith "check_rr"
                                 else check_rr t
                          else if bin1 <> bin2 then failwith "check_rr"
                               else check_rr t
                        else check_rr t
      | [] -> [] in

    (* obj and tmins must be in bete-eta normal form *)
    let rec work_obj obj (tyins,tmins) =
      (* Normalization
       * TODO: don't normalize in every loop, too expensive
       *)
      let obj = pmap beta_eta_term obj in
      let obj = map bound_eta_norm obj in
      (* Delete rule *)
      let obj = filter (fun (u,v) -> alphaorder u v <> 0) obj in
      (* Bind rule *)
      try let (fv,tm),obj = try pop (fun (u,v) -> is_free_var u && not (vfree_in u v)) obj
                            with Failure "pop" ->
                              let (tm,fv),obj = pop (fun (u,v) -> is_free_var v && not (vfree_in v u)) obj in
                              (fv,tm),obj in
          let tmins = insert_tmins (tm,fv) tmins in
          work_obj (pmap (vsubst [tm,fv]) obj) (tyins,tmins)
      with Failure "pop" -> 
      (* Decompose rule *)
      try let tmp_ins = type_unify const_ty (check_rr obj) in
          if length tmp_ins > 0 then
            let tyins = itlist insert_tyins tmp_ins tyins in
            let tmins = pmap (inst tmp_ins) tmins in
            work_obj (pmap (inst tmp_ins) obj) (tyins,tmins) else
          (* step S: match one rigid-rigid pair *)
          try let (tm1,tm2),obj = pop (fun (u,v) -> not (head_free const_var u) && not (head_free const_var v)) obj in
              let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
              let bv1,bv2,args1,args2 =
                let l1 = length bv1 and l2 = length bv2 in
                if l1 = l2 then bv1,bv2,args1,args2
                else if l1 < l2 then
                  let extra = Array.to_list (Array.sub (Array.of_list bv2) l1 (l2-l1)) in
                  bv1 @ extra,bv2,args1 @ extra,args2
                else
                  let extra = Array.to_list (Array.sub (Array.of_list bv1) l2 (l1-l2)) in
                  bv1,bv2 @ extra,args1,args2 @ extra in
              let obj = itlist2 (fun u1 u2 t -> (mk_term bv1 u1,mk_term bv2 u2)::t) args1 args2 obj in
              work_obj obj (tyins,tmins)
          with Failure "pop" -> obj,(tyins,tmins)
      with Failure s when s = "check_rr" || s = "type_unify" -> failwith "work_obj" in

    let rec work_rsl rsl =
      let rsl = fst_map beta_eta_term rsl in
      let rsl = fst_map remove_dummy_bvar rsl in
      try let (tm,name),rsl = pop (fun (tm,_) -> not (head_free const_var tm)) rsl in
          let bvs,(hs,args) = decompose tm in
          if is_var hs && not (mem hs bvs) && has_prefix (name_of hs) name then failwith "work_rsl"
          else let rsl = itlist (fun arg t -> (mk_term bvs arg,name)::t) args rsl in
               work_rsl rsl
      with Failure "pop" -> rsl in

    fun obj rsl ->
      try let obj,ins = work_obj obj ([],[]) in
          let rsl = fst_map (inst_term ins) rsl in
          let rsl = work_rsl rsl in
          obj,rsl,ins
      with Failure s when s = "work_obj" || s = "work_rsl" -> failwith "simplify"


  let hol_unify (const_ty : string list) (const_var : string list) =
    let vcounter = ref 0 in
    let new_name() =
     (vcounter := !vcounter + 1;
      "z" ^ (string_of_int !vcounter)) in

    (* each pair of obj must have matched type *)
    let rec work dep (obj : (term * term) list) (rsl : (term * string) list) (tyins,tmins) : (instor option) =
      if exists (fun (a,b) -> (tm_size a) >= 20) tmins then None else
      if exists (fun (a,b) -> (tm_size a) >= 100 || (tm_size b) >= 100) obj then None else (
      (* check maximum depth *)
      (*
      List.iter (fun (u,v) -> Printf.printf "0\t%d\t%d\n%!" (tm_size u) (tm_size v)) obj;
      *)
      if dep >= 30 then None else
      (* simplification *)
      try let obj,rsl,ins = simplify const_ty const_var obj rsl in
          let tyins,tmins = merge_ins (tyins,tmins) ins in
          (*
          printf "%d\n%!" dep;
          List.iter (fun (u,v) -> Printf.printf "0\t%s\t%s\n%!" (ss_term u) (ss_term v)) obj;
          List.iter (fun (u,v) -> Printf.printf "1\t%s\t%s\n%!" (ss_term u) v) rsl;
          print_endline "";
          *)
          try let tm1,tm2 = try find (fun (u,v) -> not (head_free const_var v)) obj
                            with Failure "find" ->
                              let tm2,tm1 = find (fun (u,v) -> not (head_free const_var u)) obj in
                              tm1,tm2 in
              let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
              (* step I: imitation *)
              let sofar =
                if is_const hs2 || (mem (name_of hs2) const_var) || (has_prefix (name_of hs2) "mc") then
                  let tyl1,apx1 = dest_fun (type_of hs1) and tyl2,apx2 = dest_fun (type_of hs2) in
                  let bvars = map (fun ty -> mk_var(new_name(),ty)) tyl1 in
                  let args = map (fun ty -> mk_lcomb (mk_var(new_name(),mk_fun(tyl1,ty))) bvars) tyl2 in
                  let tm = mk_term bvars (mk_lcomb hs2 args) in
                  let tmins' = safe_tmins (tm,hs1) tmins in
                  (* TODO check this heuristic *)
                  let offset = if vfree_in hs1 tm2 then 1 else 0 in
                  work (dep+offset) (pmap (vsubst [tm,hs1]) obj) (fst_map (vsubst [tm,hs1]) rsl) (tyins,tmins')
                else None in
              if sofar <> None then sofar else
              (* step T_P and P: projection *)
              let tyl1,apx1 = dest_fun (type_of hs1) in
              let bvars = map (fun ty -> mk_var(new_name(),ty)) tyl1 in
              let noname (k : int) sofar =
                if sofar <> None then sofar else
                let pvar = el k bvars in
                let tyl2,apx2 = dest_fun (type_of pvar) in
                (* unify type apx1 and apx2 *)
                try let tty = type_unify const_ty [apx1,apx2] in
                    let args = map (fun ty -> mk_lcomb (mk_var(new_name(),mk_fun(tyl1,ty))) bvars) tyl2 in
                    let tm = mk_term bvars (mk_lcomb pvar args) in
                    let t,x = inst tty tm,inst tty hs1 in
                    let tyins' = itlist safe_tyins tty tyins in
                    let tmins' = safe_tmins (t,x) (pmap (inst tty) tmins) in
                    work (dep+1) (pmap ((vsubst [t,x]) o (inst tty)) obj) (fst_map ((vsubst [t,x]) o (inst tty)) rsl) (tyins',tmins')
                with Failure "type_unify" -> None in
              itlist noname (0--((length bvars)-1)) None
          with Failure "find" -> (
            let tml = (let ps1,ps2 = unzip obj in ps1 @ ps2) @ (let sl,_ = unzip rsl in sl) in
            let fvars = filter (fun v -> not (has_prefix (name_of v) "mc")) (freesl tml) in
            let constantize v =
              let tyl,apex = dest_fun (type_of v) in
              let bvs = List.mapi (fun i ty -> mk_var("u" ^ (string_of_int i),ty)) tyl in
              let hs = mk_var("z",apex) in
              mk_term bvs hs in
            let tmins = itlist (fun v tmins -> safe_tmins (constantize v,v) tmins) fvars tmins in
            Some(tyins,tmins))
      with Failure "simplify" -> None) in

    fun (obj : (term * term) list) (rsl : (term * string) list) ->
      try let obj,rsl,ins = init_data const_ty const_var obj rsl in
          (try let obj',rsl',ins' = simplify const_ty const_var obj rsl in
               List.iter (fun (u,v) -> Printf.printf "0\t%s\t%s\n%!" (ss_term u) (ss_term v)) obj';
               List.iter (fun (u,v) -> Printf.printf "0\t%s\t%s\n%!" (ss_term u) v) rsl';
               print_endline ""
           with Failure _ -> ());
          work 0 obj rsl ins
      with Failure "init_data" -> None

  let hol_quick_check obj rsl =
    try let obj,rsl,ins = init_data [] [] obj rsl in
        (ignore (simplify [] [] obj rsl); true)
    with Failure s when s = "init_data" || s = "simplify" -> false

end;;

include Hunify;;
